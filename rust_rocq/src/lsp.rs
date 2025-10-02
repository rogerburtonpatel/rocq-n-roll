use serde_json::json;
use std::io::{BufRead, BufReader, Read, Write};
use std::process::{ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::thread;
use std::time::Duration;

pub const INIT: u64 = 1;
pub const COQ_LSP_STEP_OFFSET: u64 = 100;

/// Read a single LSP message from a buffered reader
pub fn read_lsp_message(reader: &mut BufReader<impl std::io::Read>) -> Option<serde_json::Value> {
    let mut header = String::new();
    if reader.read_line(&mut header).ok()? == 0 {
        return None;
    }

    if !header.starts_with("Content-Length:") {
        return None;
    }

    let content_length: usize = header
        .trim_start_matches("Content-Length:")
        .trim()
        .parse()
        .ok()?;

    let mut empty = String::new();
    reader.read_line(&mut empty).ok()?;

    let mut content = vec![0; content_length];
    reader.read_exact(&mut content).ok()?;

    let msg_str = String::from_utf8(content).ok()?;
    serde_json::from_str(&msg_str).ok()
}

pub struct RocqLSP {
    stdin: ChildStdin,
    rx: Receiver<serde_json::Value>,
    pub lsp_position_offset: usize,
}

impl RocqLSP {
    pub fn start() -> Result<Self, Box<dyn std::error::Error>> {
        let mut child = std::process::Command::new("coq-lsp")
            .stdout(Stdio::piped())
            .stdin(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;

        let stdin = child.stdin.take().expect("Failed to open stdin");
        let stdout = child.stdout.take().expect("Failed to open stdout");
        let stderr = BufReader::new(child.stderr.take().expect("Failed to open stderr"));

        let (tx, rx) = mpsc::channel();

        // stderr handler
        thread::spawn(move || {
            for line in stderr.lines() {
                if let Ok(line) = line {
                    eprintln!("Coq LSP stderr: {}", line);
                }
            }
        });

        // stdout handler
        let tx_clone = tx.clone();
        thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            loop {
                let mut header = String::new();

                if reader.read_line(&mut header).is_err() {
                    break;
                }
                if !header.starts_with("Content-Length:") {
                    continue;
                }
                let len = header
                    .trim_start_matches("Content-Length:")
                    .trim()
                    .parse::<usize>()
                    .unwrap();
                let mut empty_line = String::new();
                reader.read_line(&mut empty_line).unwrap();
                let mut buf = vec![0; len];
                if reader.read_exact(&mut buf).is_err() {
                    break;
                }
                if let Ok(msg_str) = String::from_utf8(buf) {
                    if let Ok(msg) = serde_json::from_str::<serde_json::Value>(&msg_str) {
                        let _ = tx_clone.send(msg);
                    }
                }
            }
        });

        Ok(Self {
            stdin,
            rx,
            lsp_position_offset: 0,
        })
    }

    pub fn initialize(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let init_params = json!({
            "processId": null,
            "clientInfo": {"name": "rust-coq-stepper"},
            "rootUri": null,
            "capabilities": {}
        });

        self.send_request(INIT, "initialize", &init_params)?;
        while let Ok(msg) = self.rx.recv() {
            if msg.get("id").and_then(|id| id.as_u64()) == Some(INIT) && msg.get("result").is_some()
            {
                break;
            }
        }
        self.send_notification("initialized", &json!({}))?;

        let config =  &json!({
                "coq-lsp": {
                    "mem_stats": true,
                    "check_only_on_request": false,
                    "messages_follow_goal": true,
                    "show_coq_info_messages": true
                }
        });
    self.send_notification("workspace/didChangeConfiguration", &config)?;

        Ok(())
    }

    pub fn send_request(
        &mut self,
        id: u64,
        method: &str,
        params: &serde_json::Value,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let req = json!({
            "jsonrpc": "2.0",
            "id": id,
            "method": method,
            "params": params
        });
        self.write_json(&req)?;
        Ok(())
    }

    pub fn send_notification(
        &mut self,
        method: &str,
        params: &serde_json::Value,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let notif = json!({
            "jsonrpc": "2.0",
            "method": method,
            "params": params
        });
        self.write_json(&notif)?;
        Ok(())
    }

    fn write_json(&mut self, value: &serde_json::Value) -> Result<(), Box<dyn std::error::Error>> {
        let s = serde_json::to_string(value)?;
        let len = s.len();
        self.stdin
            .write_all(format!("Content-Length: {}\r\n\r\n{}", len, s).as_bytes())?;
        self.stdin.flush()?;
        Ok(())
    }

    pub fn recv(&self, timeout: Duration) -> Option<serde_json::Value> {
        self.rx.recv_timeout(timeout).ok()
    }
}

/// VscoqLSP handles communication with vscoqtop language server
pub struct VscoqLSP {
    stdin: ChildStdin,
    rx: Receiver<serde_json::Value>,
}

impl VscoqLSP {
    /// Start a new vscoqtop process and set up communication channels
    pub fn start() -> Result<Self, Box<dyn std::error::Error>> {
        let mut vscoq = Command::new("vscoqtop")
            .stdout(Stdio::piped())
            .stdin(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| {
                if e.to_string().contains("No such file") {
                    format!("Error: vscoqtop executable not found. Did you run `opam install vscoq-language-server`?\nOriginal error: {}", e)
                } else {
                    format!("Failed to start vscoqtop: {}", e)
                }
            })?;

        let stdin = vscoq.stdin.take().expect("Failed to open stdin");
        let stdout = vscoq.stdout.take().expect("Failed to open stdout");
        let stderr = BufReader::new(vscoq.stderr.take().expect("Failed to open stderr"));

        let (tx, rx) = mpsc::channel();

        // Handle stderr
        thread::spawn(move || {
            for line in stderr.lines() {
                if let Ok(line) = line {
                    eprintln!("vscoqtop stderr: {}", line);
                }
            }
        });

        // Handle stdout and parse LSP messages
        let tx_clone = tx.clone();
        thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            loop {
                if let Some(msg) = read_lsp_message(&mut reader) {
                    if tx_clone.send(msg).is_err() {
                        break;
                    }
                } else {
                    thread::sleep(Duration::from_millis(50));
                }
            }
        });

        Ok(Self { stdin, rx })
    }

    /// Initialize the LSP connection with vscoqtop
    pub fn initialize(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        // Send initialize request
        self.send_message(&json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "processId": std::process::id(),
                "rootUri": format!("file://{}", std::env::current_dir()?.display()),
                "capabilities": {
                    "workspace": {"configuration": true}
                }
            }
        }))?;

        // Wait for initialize response
        println!("Waiting for vscoqtop initialization...");
        self.rx.recv_timeout(Duration::from_secs(2))?;

        // Send initialized notification
        self.send_message(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        }))?;

        // Handle workspace/configuration request
        while let Ok(msg) = self.rx.recv_timeout(Duration::from_millis(1000)) {
            if let Some(id) = msg.get("id") {
                if msg.get("method").and_then(|m| m.as_str()) == Some("workspace/configuration") {
                    self.send_message(&json!({
                        "jsonrpc": "2.0",
                        "id": id,
                        "result": [{
                            "path": "/Users/clairewang/.opam/default/bin/vscoqtop",
                            "proof": {"mode": 0},
                            "goals": {
                                "messages": {
                                    "full": true
                                }
                            }
                        }]
                    }))?;
                    break;
                }
            }
        }

        thread::sleep(Duration::from_millis(500));
        println!("vscoqtop connected successfully");

        Ok(())
    }

    /// Send a JSON message to vscoqtop
    pub fn send_message(&mut self, msg: &serde_json::Value) -> std::io::Result<()> {
        let msg_str = msg.to_string();
        let full_message = format!("Content-Length: {}\r\n\r\n{}", msg_str.len(), msg_str);
        self.stdin.write_all(full_message.as_bytes())?;
        self.stdin.flush()?;
        Ok(())
    }

    /// Receive a message with a timeout
    pub fn recv(&self, timeout: Duration) -> Option<serde_json::Value> {
        self.rx.recv_timeout(timeout).ok()
    }

    /// Get a reference to the receiver for advanced usage
    pub fn get_receiver(&self) -> &Receiver<serde_json::Value> {
        &self.rx
    }

    /// Open a document in vscoqtop
    pub fn open_document(
        &mut self,
        uri: &str,
        text: &str,
        version: u64,
    ) -> std::io::Result<()> {
        self.send_message(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didOpen",
            "params": {
                "textDocument": {
                    "uri": uri,
                    "languageId": "coq",
                    "version": version,
                    "text": text
                }
            }
        }))
    }

    /// Close a document in vscoqtop
    pub fn close_document(&mut self, uri: &str) -> std::io::Result<()> {
        self.send_message(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didClose",
            "params": {
                "textDocument": {"uri": uri}
            }
        }))
    }

    /// Send vscoq/interpretToPoint request
    pub fn interpret_to_point(
        &mut self,
        uri: &str,
        version: u64,
        line: usize,
        character: usize,
    ) -> std::io::Result<()> {
        self.send_message(&json!({
            "jsonrpc": "2.0",
            "method": "vscoq/interpretToPoint",
            "params": {
                "textDocument": {
                    "uri": uri,
                    "version": version
                },
                "position": {
                    "line": line,
                    "character": character
                }
            }
        }))
    }
}
