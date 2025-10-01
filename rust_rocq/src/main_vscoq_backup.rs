// TODOS:
// clean up rest of constants & magic nums
// lsp to gui
// midi off fade out- stop_all_notes
// vscoqtop version - work in progress

use clap::Parser;
use serde_json::json;
use std::fs;
use std::io::{self, BufRead, BufReader, Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

mod midi;
mod formatting;

use midi::{MidiOutput, process_tactic_to_midi, play_proof_sequence};
use formatting::format_goals;

#[derive(Parser)]
#[command(name = "rust_rocq")]
#[command(about = "Interactive Coq proof stepper with MIDI integration")]
struct Args {
    #[arg(help = "Path to the Coq (.v) file to process")]
    file: PathBuf,
    #[arg(long, help = "MIDI device ID (-1 to list devices)", allow_hyphen_values = true)]
    midi_device: Option<i32>,
    #[arg(long, help = "Play entire proof automatically with delays")]
    auto_play: bool,
    #[arg(long, help = "Debug mode: Print full response output with each command.")]
    debug: bool,
}

const JSON_VERSION: u64 = 1;
const MIDI_TEST_NOTE_DURATION_DEFAULT: u64 = 1100;

pub struct ProofStepperState {
    current_step: usize,
    total_steps: usize,
    last_goals_state: serde_json::Value,
    proof_lines: Vec<(usize, String)>,
    document_uri: String,
    midi_output: MidiOutput,
    lsp_stdin: std::process::ChildStdin,
    message_rx: mpsc::Receiver<serde_json::Value>,
}

impl ProofStepperState {
    fn new(
        proof_lines: Vec<(usize, String)>,
        document_uri: String,
        midi_output: MidiOutput,
        lsp_stdin: std::process::ChildStdin,
        message_rx: mpsc::Receiver<serde_json::Value>,
    ) -> Self {
        Self {
            current_step: 0,
            total_steps: proof_lines.len(),
            last_goals_state: serde_json::Value::Null,
            proof_lines,
            document_uri,
            midi_output,
            lsp_stdin,
            message_rx,
        }
    }

    fn is_complete(&self) -> bool {
        self.current_step >= self.total_steps
    }

    fn get_current_tactic(&self) -> Option<&(usize, String)> {
        self.proof_lines.get(self.current_step)
    }

    fn advance_step(&mut self) {
        if self.current_step < self.total_steps {
            self.current_step += 1;
        }
    }

    fn reset(&mut self) {
        self.current_step = 0;
        self.last_goals_state = serde_json::Value::Null;
    }

    fn skip_to_end(&mut self) {
        self.current_step = self.total_steps;
    }

    fn send_message(&mut self, msg: &serde_json::Value) -> std::io::Result<()> {
        let msg_str = msg.to_string();
        let full_message = format!("Content-Length: {}\r\n\r\n{}", msg_str.len(), msg_str);
        self.lsp_stdin.write_all(full_message.as_bytes())?;
        self.lsp_stdin.flush()?;
        Ok(())
    }
}

// Command handlers
fn handle_quit() -> bool {
    println!("Exiting...");
    true
}

fn handle_help() -> bool {
    println!("\nCommands:");
    println!("  Enter    - Execute current step");
    println!("  q        - Quit");
    println!("  h        - Display this help");
    println!("  e        - Explain current tactic");
    println!("  replay   - Replay current note");
    println!("  reset    - Reset to beginning");
    println!("  s        - Skip to end");
    println!("  m        - MIDI test (generate MIDI for current state)");
    println!("");
    false
}

fn handle_explain(state: &mut ProofStepperState) -> bool {
    if let Some((_, line_text)) = state.get_current_tactic() {
        println!("\nExplanation of tactic: {}", line_text);
        println!("(Generic explanation not available for this tactic)");
    } else {
        println!("No current tactic to explain");
    }
    println!("");
    false
}

fn handle_replay(state: &mut ProofStepperState) -> bool {
    println!("\nReplaying current note...");
    let last_goals_state = state.last_goals_state.clone();

    if state.last_goals_state != serde_json::Value::Null {
        if let Some((_, current_line_text)) = state.get_current_tactic() {
            process_tactic_to_midi(&state.midi_output, current_line_text, &last_goals_state, Some(Duration::from_millis(MIDI_TEST_NOTE_DURATION_DEFAULT)));
        }
    } else {
        println!("No current step to replay.");
    }
    println!("");
    false
}

fn handle_reset(state: &mut ProofStepperState) -> bool {
    println!("\nResetting to beginning of proof...");
    state.midi_output.stop_all_notes(None);
    state.reset();
    false
}

fn handle_skip(state: &mut ProofStepperState) -> bool {
    println!("\nSkipping to end of proof...");
    state.skip_to_end();
    false
}

fn handle_midi_test(midi_output: &mut MidiOutput) -> bool {
    println!("\nTesting MIDI Out: Emitting NOTE ON...");
    midi_output.play_note(90, 100, Some(Duration::from_millis(MIDI_TEST_NOTE_DURATION_DEFAULT)));
    println!("");
    false
}

fn handle_execute_step(
    state: &mut ProofStepperState,
    debug: bool,
) -> Result<bool, Box<dyn std::error::Error>> {
    if state.is_complete() {
        println!("Proof already complete!");
        return Ok(false);
    }

    let (line_num, line_text) = state.get_current_tactic().map(|(n, t)| (*n, t.clone())).unwrap_or((0, String::new()));
    println!("\nExecuting step {}/{}...", state.current_step + 1, state.total_steps);

    // Send vscoq/interpretToPoint request
    state.send_message(&json!({
        "jsonrpc": "2.0",
        "method": "vscoq/interpretToPoint",
        "params": {
            "textDocument": {
                "uri": state.document_uri.clone(),
                "version": JSON_VERSION
            },
            "position": {
                "line": line_num,
                "character": 999
            }
        }
    }))?;

    // Wait for proofView response
    let timeout = std::time::Instant::now();
    let mut found_proof_view = false;

    while timeout.elapsed() < Duration::from_secs(2) {
        match state.message_rx.recv_timeout(Duration::from_millis(100)) {
            Ok(msg) => {
                if debug {
                    println!("Received message: {:#?}", msg);
                }

                let method = msg.get("method").and_then(|m| m.as_str()).unwrap_or("");

                if method == "vscoq/proofView" {
                    if let Some(params) = msg.get("params") {
                        println!("State after executing '{}':", line_text);
                        println!("{}", format_goals(params, debug));

                        state.last_goals_state = params.clone();
                        process_tactic_to_midi(&state.midi_output, &line_text, params,
                            Some(Duration::from_millis(MIDI_TEST_NOTE_DURATION_DEFAULT)));

                        found_proof_view = true;
                        break;
                    }
                }
            }
            Err(_) => {
                if found_proof_view {
                    break;
                }
            }
        }
    }

    if !found_proof_view {
        println!("No proof view received for this step");
    }

    println!("\n{}\n", "-".repeat(60));
    state.advance_step();

    Ok(false)
}

pub fn extract_proof_steps(coq_content: &str) -> Vec<(usize, String)> {
    let mut cleaned = String::new();
    let mut comment_depth = 0usize;
    let mut chars = coq_content.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '(' && chars.peek() == Some(&'*') {
            chars.next();
            comment_depth += 1;
            continue;
        } else if c == '*' && chars.peek() == Some(&')') {
            chars.next();
            if comment_depth > 0 {
                comment_depth -= 1;
            }
            continue;
        }

        if comment_depth == 0 {
            cleaned.push(c);
        }
    }

    let lines: Vec<&str> = cleaned.lines().collect();
    let mut proof_steps = Vec::new();

    for (line_num, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        if trimmed == "Proof." {
            continue;
        }

        if trimmed == "Qed."
            || trimmed == "Defined."
            || trimmed.starts_with("Qed")
            || trimmed.starts_with("Defined")
        {
            break;
        }

        if !trimmed.is_empty() {
            proof_steps.push((line_num, trimmed.to_string()));
        }
    }

    proof_steps
}

fn read_lsp_message(reader: &mut BufReader<impl std::io::Read>) -> Option<serde_json::Value> {
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

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let args = Args::parse();

    // Validate file extension
    if let Some(ext) = args.file.extension() {
        if ext != "v" {
            eprintln!("Warning: File does not have .v extension. Expected a Coq file.");
        }
    } else {
        eprintln!("Warning: File has no extension. Expected a Coq (.v) file.");
    }

    // Read the Coq file
    let coq_file = fs::read_to_string(&args.file)
        .map_err(|e| format!("Failed to read file '{}': {}", args.file.display(), e))?;

    // Initialize MIDI output
    let midi_output = MidiOutput::new(args.midi_device)?;

    // Start vscoqtop process
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

    // Set up communication channels
    let mut lsp_stdin = vscoq.stdin.take().expect("Failed to open stdin");
    let lsp_stdout = vscoq.stdout.take().expect("Failed to open stdout");
    let lsp_stderr = BufReader::new(vscoq.stderr.take().expect("Failed to open stderr"));

    // Channel for parsed messages
    let (tx, rx) = mpsc::channel();

    // Handle stderr
    thread::spawn(move || {
        for line in lsp_stderr.lines() {
            if let Ok(line) = line {
                eprintln!("vscoqtop stderr: {}", line);
            }
        }
    });

    // Handle stdout and parse LSP messages
    let tx_clone = tx.clone();
    thread::spawn(move || {
        let mut reader = BufReader::new(lsp_stdout);
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

    // Helper function to send messages
    let mut send_message = |msg: &serde_json::Value| -> std::io::Result<()> {
        let msg_str = msg.to_string();
        let full_message = format!("Content-Length: {}\r\n\r\n{}", msg_str.len(), msg_str);
        lsp_stdin.write_all(full_message.as_bytes())?;
        lsp_stdin.flush()?;
        Ok(())
    };

    // Initialize the LSP connection
    send_message(&json!({
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
    rx.recv_timeout(Duration::from_secs(2))?;

    // Send initialized notification
    send_message(&json!({
        "jsonrpc": "2.0",
        "method": "initialized",
        "params": {}
    }))?;

    // Handle workspace/configuration request
    while let Ok(msg) = rx.recv_timeout(Duration::from_millis(1000)) {
        if let Some(id) = msg.get("id") {
            if msg.get("method").and_then(|m| m.as_str()) == Some("workspace/configuration") {
                send_message(&json!({
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

    // Display the proof file
    println!("\nCoq proof to step through:");
    let lines: Vec<&str> = coq_file.lines().collect();
    for (i, line) in lines.iter().enumerate() {
        println!("{:2}: {}", i, line);
    }

    let document_uri = format!("file://{}", args.file.canonicalize()?.display());

    // Open the document
    send_message(&json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": document_uri.clone(),
                "languageId": "coq",
                "version": JSON_VERSION,
                "text": coq_file
            }
        }
    }))?;

    // Wait for document to be parsed
    println!("Waiting for document to be parsed...");
    let mut highlights_count = 0;
    while highlights_count < 3 {
        if let Ok(msg) = rx.recv_timeout(Duration::from_millis(2000)) {
            let method = msg.get("method").and_then(|m| m.as_str()).unwrap_or("");
            if method == "vscoq/updateHighlights" {
                highlights_count += 1;
            }
        } else {
            break;
        }
    }

    // Extract proof steps
    let proof_lines = extract_proof_steps(&coq_file);
    if proof_lines.is_empty() {
        println!("No proof steps found in the file. Make sure the file contains a proof with 'Proof.' and 'Qed.' markers.");
        return Ok(());
    }

    // Auto-play mode
    if args.auto_play {
        play_proof_sequence(&proof_lines, &midi_output);
        return Ok(());
    }

    let mut state = ProofStepperState::new(proof_lines, document_uri.clone(), midi_output, lsp_stdin, rx);

    // Display initial state
    println!("\nInteractive Coq Proof Stepper with MIDI");
    println!("-------------------------------------");
    println!("Press Enter to step through the proof");
    println!("Type 'q' to quit, 'h' for help");
    println!("-------------------------------------\n");

    println!("\n{}\n", "-".repeat(60));

    // Main interaction loop
    let stdin = io::stdin();
    let mut user_input = String::new();

    loop {
        if state.is_complete() {
            println!("Proof complete! All steps executed.");
            break;
        }

        if let Some((_, line_text)) = state.get_current_tactic() {
            println!("Current tactic: {}", line_text);
        }
        print!("Press Enter to execute this step, or type a command: ");
        io::stdout().flush()?;

        user_input.clear();
        stdin.lock().read_line(&mut user_input)?;
        let input = user_input.trim();

        let should_exit = match input {
            "q" | "quit" | "exit" => handle_quit(),
            "h" | "help" => handle_help(),
            "e" | "explain" => handle_explain(&mut state),
            "replay" => handle_replay(&mut state),
            "reset" => handle_reset(&mut state),
            "s" | "skip" => handle_skip(&mut state),
            "m" | "midi" => handle_midi_test(&mut state.midi_output),
            "" => handle_execute_step(&mut state, args.debug)?,
            _ => {
                println!("Unknown command: '{}'. Type 'h' for help.", input);
                false
            }
        };

        if should_exit {
            break;
        }
    }

    // Cleanup
    state.send_message(&json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didClose",
        "params": {
            "textDocument": {"uri": document_uri}
        }
    }))?;

    println!("Proof session ended.");
    println!("Press any key to stop all notes and exit.");

    stdin.lock().read_line(&mut user_input)?;

    state.midi_output.stop_all_notes(None);

    Ok(())
}
