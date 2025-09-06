use serde_json::json;
use std::io::{BufRead, BufReader, Read, Write};
use std::process::{Child, ChildStdin, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::thread;
use std::time::Duration;

pub const INIT: u64 = 1;
pub const COQ_LSP_STEP_OFFSET: u64 = 100;

pub struct RocqLSP {
    child: Child,
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
                if reader.read_line(&mut header).unwrap_or(0) == 0 {
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
            child,
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
