use clap::builder::Str;
use clap::Parser;
use log::debug;
use serde_json::json;
use std::fs;
use std::io::{self, BufRead, BufReader, Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;
use regex::Regex;

mod midi;
mod gui;
mod formatting;

use midi::{MidiOutput, process_tactic_to_midi, play_proof_sequence};
use gui::run_with_gui;
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
    debug: bool
}

const COQ_LSP_STEP_OFFSET: u64 = 100;

// Extract tactic name from a proof line
fn extract_tactic_name(line: &str) -> String {
    let re = Regex::new(r"^\s*[-+*]*\s*([a-zA-Z][a-zA-Z0-9_]*)")
        .expect("Failed to compile regex");
    
    if let Some(captures) = re.captures(line) {
        captures.get(1).unwrap().as_str().to_lowercase()
    } else {
        "unknown".to_string()
    }
}

fn extract_proof_steps(coq_content: &str) -> Vec<(usize, String)> {
    let lines: Vec<&str> = coq_content.lines().collect();
    let mut proof_steps = Vec::new();
    
    for (line_num, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        
        if trimmed == "Proof." {
            continue;
        }
        
        if trimmed == "Qed." || trimmed == "Defined." || trimmed.starts_with("Qed") || trimmed.starts_with("Defined") {
            break;
        }
        
        if !trimmed.is_empty() && !trimmed.starts_with("(*") {
            proof_steps.push((line_num, trimmed.to_string()));
        }
    }
    
    proof_steps
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
    let mut midi_output = MidiOutput::new(args.midi_device)?;

    // Start the Coq LSP process
    let mut coq_lsp = match Command::new("coq-lsp")
        .stdout(Stdio::piped())
        .stdin(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(e) => {
            // common error, helps to debug 
            if let Some(2) = e.raw_os_error() {
                eprintln!("Error: coq-lsp executable not found (OS error 2). Did you run `opam install coq-lsp?`");
                return Err(Box::new(e));        
            }
        // generic error reporting 
        eprintln!("Error spawning coq-lsp process: {}", e);
        return Err(Box::new(e));
        }
    };

    // Set up communication channels
    let mut lsp_stdin = coq_lsp.stdin.take().expect("Failed to open stdin");
    let lsp_stdout = coq_lsp.stdout.take().expect("Failed to open stdout");
    let lsp_stderr = BufReader::new(coq_lsp.stderr.take().expect("Failed to open stderr"));

    // Channel for parsed messages
    let (tx, rx) = mpsc::channel();

    // Handle stderr
    thread::spawn(move || {
        for line in lsp_stderr.lines() {
            if let Ok(line) = line {
                eprintln!("Coq LSP stderr: {}", line);
            }
        }
    });

    // Handle stdout and parse LSP messages - with proper error handling
    let tx_clone = tx.clone();
    thread::spawn(move || {
        let mut reader = BufReader::new(lsp_stdout);
        loop {
            // Read LSP message headers
            let mut header = String::new();
            match reader.read_line(&mut header) {
                Ok(0) => break, // EOF
                Ok(_) => {}
                Err(e) => {
                    eprintln!("Error reading header: {}", e);
                    break;
                }
            }

            if !header.starts_with("Content-Length:") {
                continue;
            }

            // Parse content length
            let content_length = match header
                .trim_start_matches("Content-Length:")
                .trim()
                .parse::<usize>()
            {
                Ok(len) => len,
                Err(e) => {
                    eprintln!("Error parsing content length: {}", e);
                    continue;
                }
            };

            // Skip the empty line after headers
            let mut empty_line = String::new();
            if let Err(e) = reader.read_line(&mut empty_line) {
                eprintln!("Error reading empty line: {}", e);
                break;
            }

            // Read the JSON content
            let mut content = vec![0; content_length];
            if let Err(e) = reader.read_exact(&mut content) {
                eprintln!("Error reading content: {}", e);
                break;
            }

            // Parse and send the message
            let message_str = match String::from_utf8(content) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("Error converting to UTF-8: {}", e);
                    continue;
                }
            };

            let message: serde_json::Value = match serde_json::from_str(&message_str) {
                Ok(v) => v,
                Err(e) => {
                    eprintln!("Error parsing JSON: {}", e);
                    continue;
                }
            };

            if let Err(e) = tx_clone.send(message) {
                eprintln!("Error sending message: {}", e);
                break;
            }
        }
    });

    // Initialize the LSP connection with on-demand mode configuration
    let init_params = json!({
        "processId": null,
        "clientInfo": {"name": "rust-coq-stepper"},
        "rootUri": null,
        "capabilities": {}
    });

    send_request(&mut lsp_stdin, 1, "initialize", &init_params)?;

    // Wait for initialize response
    while let Ok(message) = rx.recv() {
        if let Some(id) = message.get("id") {
            if id.as_u64() == Some(1) && message.get("result").is_some() {
                break;
            }
        }
    }

    println!("Coq LSP connected successfully");

    // Send initialized notification
    send_notification(&mut lsp_stdin, "initialized", &json!({}))?;

    println!("\nCoq proof to step through:");
    let lines: Vec<&str> = coq_file.lines().collect();

    for (i, line) in lines.iter().enumerate() {
        println!("{:2}: {}", i, line);
    }

    let document_uri = format!("file://{}", args.file.canonicalize()?.display());

    // Open the document
    let open_params = json!({
        "textDocument": {
            "uri": document_uri,
            "languageId": "coq",
            "version": 1,
            "text": coq_file
        }
    });

    send_notification(&mut lsp_stdin, "textDocument/didOpen", &open_params)?;

    // Give the server time to process the document
    thread::sleep(std::time::Duration::from_secs(1));

    // Extract proof steps from the Coq file
    let proof_lines = extract_proof_steps(&coq_file);
    
    if proof_lines.is_empty() {
        println!("No proof steps found in the file. Make sure the file contains a proof with 'Proof.' and 'Qed.' markers.");
        return Ok(());
    }
    
    // Auto-play mode: play entire sequence with delays
    if args.auto_play {
        play_proof_sequence(&proof_lines, &mut midi_output);
        return Ok(());
    }

    println!("\nInteractive Coq Proof Stepper with MIDI");
    println!("-------------------------------------");
    println!("Press Enter to step through the proof");
    println!("Type 'q' to quit");
    println!("Type 'h' for help");
    println!("-------------------------------------\n");

    let stdin = io::stdin();
    let mut user_input = String::new();

    // Display the initial state before any steps
    println!("Initial state (before first tactic):");
    let initial_goals_params = json!({
        "textDocument": {
            "uri": document_uri,
            "version": 1
        },
        "position": {
            "line": 3,
            "character": 0
        }
    });

    send_request(&mut lsp_stdin, 99, "proof/goals", &initial_goals_params)?;

    // Wait for response and display
    let mut found_response = false;
    let mut initial_goals_json = serde_json::Value::Null;

    while let Ok(message) = rx.recv_timeout(std::time::Duration::from_secs(5)) {
        if let Some(id) = message.get("id") {
            if id.as_u64() == Some(99) {
                if let Some(result) = message.get("result") {
                    println!("{}", format_goals(result, args.debug));
                    initial_goals_json = result.clone();

                    // Process initial state to MIDI
                    process_tactic_to_midi(&mut midi_output, "Initial state", result, Some(Duration::from_millis(1000)));

                    found_response = true;
                    break;
                } else if let Some(error) = message.get("error") {
                    println!("Error: {}", error);
                    found_response = true;
                    break;
                }
            }
        }
    }

    if !found_response {
        println!("No response received for initial goals request");
    }

    println!("\n{}\n", "-".repeat(60));

    // Interactive stepping
    let mut current_step = 0;
    let total_steps = proof_lines.len();
    let mut last_goals_state = serde_json::Value::Null;

    'main_loop: loop {
        if current_step >= total_steps {
            println!("Proof complete! All steps executed.");
            break;
        }

        let (line_num, line_text) = &proof_lines[current_step];

        // Show the current tactic and prompt
        println!("Current tactic: {}", line_text);
        print!("Press Enter to execute this step, or type a command: ");
        io::stdout().flush()?;

        // Get user input
        user_input.clear();
        stdin.lock().read_line(&mut user_input)?;
        let input = user_input.trim();

        match input {
            "q" | "quit" | "exit" => {
                println!("Exiting...");
                break 'main_loop;
            }
            "h" | "help" => {
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
                continue;
            }
            "e" | "explain" => {
                println!("\nExplanation of tactic: {}", line_text);
                println!("(Generic explanation not available for this tactic)");
                println!("");
                continue;
            }
            "replay" => {
                println!("\nReplaying current note...");
                // Stop any current notes first
                midi_output.stop_all_notes();
                
                // Replay the current tactic note
                if last_goals_state != serde_json::Value::Null {
                    let (_, current_line_text) = &proof_lines[current_step];
                    // Use the last known goals state for accurate replay
                    process_tactic_to_midi(&mut midi_output, current_line_text, &last_goals_state, Some(Duration::from_millis(2000)));
                } else {
                    println!("No current step to replay.");
                }
                println!("");
                continue;
            }
            "reset" => {
                println!("\nResetting to beginning of proof...");
                midi_output.stop_all_notes();
                current_step = 0;
                continue;
            }
            "s" | "skip" => {
                println!("\nSkipping to end of proof...");
                current_step = total_steps;
                continue;
            }
            "m" | "midi" => {
                println!("\nGenerating MIDI test for current state...");
                // Trigger the MIDI generation with the current state if available
                if !initial_goals_json.is_null() {
                    process_tactic_to_midi(&mut midi_output, "MIDI Test", &initial_goals_json, Some(Duration::from_millis(2000)));
                } else {
                    println!("No proof state available for MIDI generation");
                }
                println!("");
                continue;
            }
            "" => {
                // Execute the current step
                println!("\nExecuting step {}/{}...", current_step + 1, total_steps);

                // Request goals at this position using the proof/goals method
                let goals_params = json!({
                    "textDocument": {
                        "uri": document_uri,
                        "version": 1
                    },
                    "position": {
                        "line": *line_num,
                        "character": 0
                    }
                });

                send_request(
                    &mut lsp_stdin,
                    current_step as u64 + COQ_LSP_STEP_OFFSET,
                    "proof/goals",
                    &goals_params,
                )?;

                // Wait for and process response
                let mut found_response = false;

                while let Ok(message) = rx.recv_timeout(std::time::Duration::from_secs(5)) {
                    if let Some(id) = message.get("id") {
                        if id.as_u64() == Some(current_step as u64 + COQ_LSP_STEP_OFFSET) {
                            println!("MESSAGE");
                            println!("{:#?}", message);
                            println!("END MESSAGE");
                            if let Some(result) = message.get("result") {
                                found_response = true;

                                println!("State after executing '{}':", line_text);
                                println!("{}", format_goals(result, args.debug));
                                
                                // Store the current goals state for replay
                                last_goals_state = result.clone();

                                // Process this proof state to MIDI - hold note until next step
                                process_tactic_to_midi(&mut midi_output, line_text, result, None);

                                break;
                            } else if let Some(error) = message.get("error") {
                                println!("Error: {}", error);
                                found_response = true;
                                break;
                            }
                        }
                    }
                }

                if !found_response {
                    println!("No response received for goals request");
                }

                println!("\n{}\n", "-".repeat(60));

                // Move to the next step
                current_step += 1;
            }
            _ => {
                println!("Unknown command: '{}'. Type 'h' for help.", input);
                continue;
            }
        }
    }

    // Clean up
    let close_params = json!({
        "textDocument": { "uri": document_uri }
    });

    send_notification(&mut lsp_stdin, "textDocument/didClose", &close_params)?;

    // Stop all MIDI notes before exiting
    midi_output.stop_all_notes();

    println!("Proof session ended.");

    Ok(())
}

// Helper function to send LSP requests
fn send_request(
    stdin: &mut std::process::ChildStdin,
    id: u64,
    method: &str,
    params: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    let request = json!({
        "jsonrpc": "2.0",
        "id": id,
        "method": method,
        "params": params
    });

    let request_str = serde_json::to_string(&request)?;
    let content_length = request_str.len();

    stdin.write_all(
        format!("Content-Length: {}\r\n\r\n{}", content_length, request_str).as_bytes(),
    )?;
    stdin.flush()?;

    Ok(())
}

// Helper function to send LSP notifications
fn send_notification(
    stdin: &mut std::process::ChildStdin,
    method: &str,
    params: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    let notification = json!({
        "jsonrpc": "2.0",
        "method": method,
        "params": params
    });

    let notification_str = serde_json::to_string(&notification)?;
    let content_length = notification_str.len();

    stdin.write_all(
        format!(
            "Content-Length: {}\r\n\r\n{}",
            content_length, notification_str
        )
        .as_bytes(),
    )?;
    stdin.flush()?;

    Ok(())
}

fn request_lsp(curr_step : i64) -> (Vec<String>, Vec<String>) {
    (todo!(), todo!())
}

fn step() {
    // (what_ran, new_proof_state) = request from lsp 
    // 
    let proof = todo!(); 
    let what_ran = todo!();
    let goals = todo!();
    let mut curr_step = 0; 
    let proof_not_over = false;
    while proof_not_over {
        disp(&proof, curr_step, &what_ran, &goals);
        play(&what_ran);
        curr_step += 1;
    }
}

fn disp(proof : &String, curr_step : i64, what_ran : &Vec<String>, goals : &Vec<String>) {
    // request 
}
fn play(what_ran : &Vec<String>) {

}