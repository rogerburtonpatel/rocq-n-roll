use log::debug;
use serde_json::json;
use std::io::{BufRead, BufReader, Read, Write};
use std::process::{ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::thread;
use std::time::Duration;

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
    #[allow(dead_code)]
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
    // todo try prover/stepForward
    /// Send vscoq/interpretToPoint request
    pub fn interpret_to_point(
        &mut self,
        uri: String,
        version: u64,
        line: usize,
        character: usize,
    ) -> std::io::Result<()> {
         let interpret_msg = json!({
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
    });

        debug!("Sending interpretToPoint: {}", interpret_msg);
        self.send_message(&interpret_msg)
    }
}
