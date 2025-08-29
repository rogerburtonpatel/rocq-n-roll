use clap::Parser;
use serde_json::json;
use std::collections::HashMap;
use std::fs;
use std::io::{self, BufRead, BufReader, Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;
use regex::Regex;

extern crate portmidi as pm;
use pm::MidiMessage;

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
}

static CHANNEL: u8 = 0;

// check the proof as you get closer to the failing tactic you get more and more offtune 
// 

// Tactic to (pitch, velocity) mapping
fn create_tactic_midi_map() -> HashMap<&'static str, (u8, u8)> {
    let mut map = HashMap::new();
    
    // Basic tactics - fundamental notes
    map.insert("reflexivity", (60, 100)); // C4 - strong, conclusive
    map.insert("simpl", (67, 80));         // G4 - clean, bright
    // if you have multiple variables in intros; or variations of intros, should that sound different?
    map.insert("intros", (64, 90));        // E4 - opening, welcoming
    // apply H1, H2 - should that sound different?
    map.insert("apply", (69, 85));         // A4 - forward motion
    map.insert("rewrite", (62, 75));       // D4 - transformative
    
    // Induction/recursion - deeper notes
    map.insert("induction", (48, 110));    // C3 - deep, structural
    map.insert("elim", (50, 100));         // D3 - breaking down
    map.insert("destruct", (52, 95));      // E3 - analyzing
    
    // Advanced tactics - higher notes
    map.insert("auto", (72, 70));          // C5 - automated, light
    map.insert("tauto", (74, 75));         // D5 - logical clarity
    map.insert("omega", (76, 65));         // E5 - arithmetic magic
    
    // Proof structure - special tones
    map.insert("split", (65, 85));         // F4 - dividing
    map.insert("left", (63, 80));          // D#4 - choosing left
    map.insert("right", (68, 80));         // G#4 - choosing right
    
    // Error/incomplete - dissonant
    map.insert("admit", (42, 120));        // F#2 - low, ominous
    map.insert("admitted", (42, 120));     // F#2 - same as admit
    map.insert("sorry", (41, 127));        // F2 - even more dissonant
    map.insert("abort", (43, 120));        // G2 - failed proof
    
    map
}

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

// MIDI output wrapper
struct MidiOutput {
    context: Option<pm::PortMidi>,
    port_id: Option<i32>,
    enabled: bool,
}

impl MidiOutput {
    fn new(device_id: Option<i32>) -> Result<Self, Box<dyn std::error::Error>> {
        let context = pm::PortMidi::new()?;
        
        if let Some(id) = device_id {
            if id == -1 {
                println!("Available MIDI devices:");
                for dev in context.devices()? {
                    println!("{}", dev);
                }
                return Ok(MidiOutput { context: None, port_id: None, enabled: false });
            }
            
            // Validate device exists
            let _device = context.device(id)?;
            Ok(MidiOutput { context: Some(context), port_id: Some(id), enabled: true })
        } else {
            println!("MIDI disabled. Use --midi-device to enable.");
            Ok(MidiOutput { context: None, port_id: None, enabled: false })
        }
    }
    
    fn play_note(&mut self, pitch: u8, velocity: u8, hold_duration: Option<Duration>) {
        if !self.enabled || self.context.is_none() || self.port_id.is_none() {
            return;
        }
        
        let context = self.context.as_ref().unwrap();
        let port_id = self.port_id.unwrap();
        
        if let Ok(device) = context.device(port_id) {
            if let Ok(mut port) = context.output_port(device, 1024) {
                // Note on
                let note_on = MidiMessage {
                    status: 0x90 + CHANNEL,
                    data1: pitch,
                    data2: velocity,
                    data3: 0,
                };
                
                if let Err(e) = port.write_message(note_on) {
                    eprintln!("MIDI error: {}", e);
                    return;
                }
                
                // Hold for specified duration or until manually stopped
                if let Some(duration) = hold_duration {
                    thread::sleep(duration);
                    
                    let note_off = MidiMessage {
                        status: 0x80 + CHANNEL,
                        data1: pitch,
                        data2: 0,
                        data3: 0,
                    };
                    
                    if let Err(e) = port.write_message(note_off) {
                        eprintln!("MIDI error: {}", e);
                    }
                }
            }
        }
    }
    
    fn stop_note(&mut self, pitch: u8) {
        if !self.enabled || self.context.is_none() || self.port_id.is_none() {
            return;
        }
        
        let context = self.context.as_ref().unwrap();
        let port_id = self.port_id.unwrap();
        
        if let Ok(device) = context.device(port_id) {
            if let Ok(mut port) = context.output_port(device, 1024) {
                let note_off = MidiMessage {
                    status: 0x80 + CHANNEL,
                    data1: pitch,
                    data2: 0,
                    data3: 0,
                };
                
                if let Err(e) = port.write_message(note_off) {
                    eprintln!("MIDI error: {}", e);
                }
            }
        }
    }
    
    fn stop_all_notes(&mut self) {
        if !self.enabled {
            return;
        }
        
        // Send all notes off on this channel
        for note in 0..128 {
            self.stop_note(note);
        }
    }
}

// Real MIDI processing function
fn process_tactic_to_midi(
    midi_output: &mut MidiOutput, 
    line_text: &str, 
    goals_json: &serde_json::Value,
    hold_duration: Option<Duration>
) {
    let tactic_map = create_tactic_midi_map();
    let tactic_name = extract_tactic_name(line_text);
    
    println!("\n[MIDI] Processing tactic: '{}' -> '{}'", line_text, tactic_name);
    
    // Get base note for the tactic
    let (mut pitch, mut velocity) = tactic_map.get(tactic_name.as_str())
        .copied()
        .unwrap_or((55, 60)); // Default: G3, medium velocity
    
    // Modify based on proof state complexity
    if let Some(goals_config) = goals_json.get("goals") {
        if let Some(goals) = goals_config.get("goals") {
            if let Some(goals_array) = goals.as_array() {
                let num_goals = goals_array.len();
                
                // More goals = higher pitch (urgency)
                pitch = (pitch as i16 + (num_goals as i16 * 2)).min(127) as u8;
                
                // Count total hypotheses for velocity adjustment
                let mut total_hyps = 0;
                for goal in goals_array {
                    if let Some(hyps) = goal.get("hyps") {
                        if let Some(hyps_array) = hyps.as_array() {
                            total_hyps += hyps_array.len();
                        }
                    }
                }
                
                // More hypotheses = higher velocity (complexity)
                velocity = (velocity as i16 + (total_hyps as i16 * 3)).min(127) as u8;
                
                println!("[MIDI] Goals: {}, Hypotheses: {}, Final note: {} @ {}", 
                         num_goals, total_hyps, pitch, velocity);
            }
        }
    }
    
    // Play the note
    midi_output.play_note(pitch, velocity, hold_duration);
    
    // Add harmonic context based on proof state
    play_harmonic_context(midi_output, goals_json, pitch);
}

// Add harmonic context based on proof correctness
fn play_harmonic_context(midi_output: &mut MidiOutput, goals_json: &serde_json::Value, base_pitch: u8) {
    if let Some(goals_config) = goals_json.get("goals") {
        if let Some(goals) = goals_config.get("goals") {
            if let Some(goals_array) = goals.as_array() {
                match goals_array.len() {
                    0 => {
                        // Proof complete! Play a perfect major chord
                        println!("[MIDI] Proof complete - playing major chord!");
                        play_chord(midi_output, base_pitch, &[0, 4, 7], 80); // Major triad
                    }
                    1 => {
                        // One goal - add a perfect fifth (stable)
                        midi_output.play_note(base_pitch + 7, 60, None);
                    }
                    2..=3 => {
                        // Multiple goals - add tension with minor intervals
                        midi_output.play_note(base_pitch + 3, 50, None); // Minor third
                    }
                    _ => {
                        // Many goals - create dissonance
                        midi_output.play_note(base_pitch + 1, 70, None); // Dissonant second
                        midi_output.play_note(base_pitch + 6, 60, None); // Tritone
                    }
                }
            }
        }
    }
    
    // Check for error messages - play dissonant clusters
    if let Some(messages) = goals_json.get("messages") {
        if let Some(messages_array) = messages.as_array() {
            for message in messages_array {
                let msg_text = text_of_message(message);
                if msg_text.contains("error") || msg_text.contains("Error") {
                    println!("[MIDI] Error detected - playing dissonant cluster!");
                    play_dissonant_cluster(midi_output, base_pitch);        
                }
            }
        }
    }
}

fn text_of_message(message: &Value) -> String {
    let msg_text = if let Some(text) = message.get("text") {
        text.as_str().unwrap_or(&text.to_string()).to_string()
    } else if let Some(s) = message.as_str() {
        s.to_string()
    } else {
        message.to_string()
    };
    msg_text
}

// Play a chord with given intervals
fn play_chord(midi_output: &mut MidiOutput, root: u8, intervals: &[u8], velocity: u8) {
    for &interval in intervals {
        let note = (root as i16 + interval as i16).min(127) as u8;
        midi_output.play_note(note, velocity, None);
    }
}

// Play dissonant cluster for errors
fn play_dissonant_cluster(midi_output: &mut MidiOutput, base_pitch: u8) {
    // Play cluster of semitones - very dissonant
    for i in 0..4 {
        let note = (base_pitch as i16 + i).min(127) as u8;
        midi_output.play_note(note, 90, Some(Duration::from_millis(500)));
    }
}

// Play entire proof sequence with delays
fn play_proof_sequence(proof_steps: &[(usize, String)], midi_output: &mut MidiOutput) {
    println!("\n[MIDI] Playing entire proof sequence with delays...");
    
    let tactic_map = create_tactic_midi_map();
    
    for (i, (_, line_text)) in proof_steps.iter().enumerate() {
        let tactic_name = extract_tactic_name(line_text);
        let (pitch, velocity) = tactic_map.get(tactic_name.as_str())
            .copied()
            .unwrap_or((55, 60));
        
        println!("[MIDI] Step {}: {} -> Note {} @ {}", i + 1, line_text, pitch, velocity);
        
        // Play note for 800ms with 200ms gap
        midi_output.play_note(pitch, velocity, Some(Duration::from_millis(800)));
        thread::sleep(Duration::from_millis(10000));
    }
    
    println!("[MIDI] Proof sequence complete!");
}

fn extract_proof_steps(coq_content: &str) -> Vec<(usize, String)> {
    let lines: Vec<&str> = coq_content.lines().collect();
    let mut proof_steps = Vec::new();
    // let mut in_proof = false;
    // let _ = run_with_gui(lines.clone().into_iter().map(String::from).collect());
    
    for (line_num, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        
        if trimmed == "Proof." {
            // in_proof = true;
            continue;
        }
        
        if trimmed == "Qed." || trimmed == "Defined." || trimmed.starts_with("Qed") || trimmed.starts_with("Defined") {
            // in_proof = false;
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
    let mut coq_lsp = Command::new("coq-lsp")
        .stdout(Stdio::piped())
        .stdin(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

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
    // let mut initialize_response = None;
    while let Ok(message) = rx.recv() {
        if let Some(id) = message.get("id") {
            if id.as_u64() == Some(1) && message.get("result").is_some() {
                // initialize_response = Some(message.clone());
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
                    println!("{}", format_goals(result));
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
                if current_step < total_steps {
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
                    100 + current_step as u64,
                    "proof/goals",
                    &goals_params,
                )?;

                // Wait for and process response
                let mut found_response = false;
                // let current_goals_json = serde_json::Value::Null;

                while let Ok(message) = rx.recv_timeout(std::time::Duration::from_secs(5)) {
                    if let Some(id) = message.get("id") {
                        if id.as_u64() == Some(100 + current_step as u64) {
                            if let Some(result) = message.get("result") {
                                println!("State after executing '{}':", line_text);
                                println!("{}", format_goals(result));
                                
                                // Store the current goals state for replay
                                last_goals_state = result.clone();

                                // Process this proof state to MIDI - hold note until next step
                                process_tactic_to_midi(&mut midi_output, line_text, result, None);

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
                    println!("No response received for goals request");
                }

                println!("\n{}\n", "-".repeat(60));

                // Stop previous notes before moving to next step
              //  midi_output.stop_all_notes();

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

// Function to display goals in a readable format based on the documentation
// TODO 1: 
// rocq proof thigns to show up in right order 
// get these to show up on gui. 
// return a string that gets put on the gui, along with a pointer to where 
// in the proof we are
use serde_json::Value;

pub fn format_goals(result: &Value) -> String {
    let mut output = String::new();

    // Check if there are any goals
    if let Some(goals_config) = result.get("goals") {
        // Format foreground goals
        format_main_goals(&mut output, goals_config);

        // Format shelved goals if any
        if let Some(shelf) = goals_config.get("shelf") {
            format_shelved_goals(&mut output, shelf);
        }

        // Format given up goals if any
        if let Some(given_up) = goals_config.get("given_up") {
            format_given_up_goals(&mut output, given_up);
        }
    } else {
        // If no goals, just print the raw response
        output.push_str("Displaying raw response: \n");
        output.push_str(&serde_json::to_string_pretty(result).unwrap_or_default());
        output.push('\n');
    }

    // Format any messages
    if let Some(messages) = result.get("messages") {
        format_messages(&mut output, messages);
    }

    output
}

fn format_messages(output: &mut String, messages: &Value) {
    if let Some(messages_array) = messages.as_array() {
        if !messages_array.is_empty() {
            output.push_str("Messages:\n");
            for message in messages_array {
                let msg_text = if let Some(text) = message.get("text") {
                    text.as_str().unwrap_or(&text.to_string()).to_string()
                } else if let Some(s) = message.as_str() {
                    s.to_string()
                } else {
                    message.to_string()
                };
                output.push_str(&format!("  {}\n", msg_text));
            }
            output.push('\n');
        }
    }
}

fn format_given_up_goals(output: &mut String, given_up: &Value) {
    if let Some(given_up_array) = given_up.as_array() {
        if !given_up_array.is_empty() {
            output.push_str("Given up goals:\n");
            for (i, goal) in given_up_array.iter().enumerate() {
                let ty_str = if let Some(ty) = goal.get("ty") {
                    ty.as_str().unwrap_or(&ty.to_string()).to_string()
                } else {
                    "".to_string()
                };
                output.push_str(&format!("  [{}] {}\n", i + 1, ty_str));
            }
            output.push('\n');
        }
    }
}

fn format_shelved_goals(output: &mut String, shelf: &Value) {
    if let Some(shelf_array) = shelf.as_array() {
        if !shelf_array.is_empty() {
            output.push_str("Shelved goals:\n");
            for (i, goal) in shelf_array.iter().enumerate() {
                let ty_str = if let Some(ty) = goal.get("ty") {
                    ty.as_str().unwrap_or(&ty.to_string()).to_string()
                } else {
                    "".to_string()
                };
                output.push_str(&format!("  [{}] {}\n", i + 1, ty_str));
            }
            output.push('\n');
        }
    }
}

fn format_main_goals(output: &mut String, goals_config: &Value) {
    if let Some(goals) = goals_config.get("goals") {
        if let Some(goals_array) = goals.as_array() {
            if goals_array.is_empty() {
                output.push_str("No active goals.\n");
            } else {
                for (i, goal) in goals_array.iter().enumerate() {
                    output.push_str(&format!("================= Goal {} =================\n", i + 1));

                    // Display hypotheses
                    if let Some(hyps) = goal.get("hyps") {
                        if let Some(hyps_array) = hyps.as_array() {
                            for hyp in hyps_array {
                                // Extract hypothesis name(s)
                                let names = if let Some(names) = hyp.get("names") {
                                    if let Some(names_array) = names.as_array() {
                                        names_array
                                            .iter()
                                            .filter_map(|n| n.as_str().map(|s| s.to_string()))
                                            .collect::<Vec<String>>()
                                            .join(", ")
                                    } else {
                                        names.to_string()
                                    }
                                } else {
                                    "".to_string()
                                };

                                // Extract hypothesis type
                                let ty_str = if let Some(ty) = hyp.get("ty") {
                                    ty.as_str().unwrap_or(&ty.to_string()).to_string()
                                } else {
                                    "".to_string()
                                };

                                output.push_str(&format!("{:<12}: {}\n", names, ty_str));
                            }
                        }
                    }

                    // Display goal type
                    let ty_str = if let Some(ty) = goal.get("ty") {
                        ty.as_str().unwrap_or(&ty.to_string()).to_string()
                    } else {
                        "".to_string()
                    };

                    output.push_str(&format!("\n-------------------------------------------\n{}\n\n", ty_str));
                }
            }
        }
    }
}


/////////////////////////////// BEGIN GUI ////////////////////////////////

// Cargo.toml dependencies needed:
// [dependencies]
// eframe = "0.24"
// egui = "0.24"
// rand = "0.8"
// winit = "0.28"

use eframe::egui;
use egui::{Color32, FontId, Pos2, Rect, Stroke, Vec2};
use rand::Rng;
use std::time::Instant;

#[derive(Clone)]
struct TreePattern {
    origin: Pos2,
    branches: Vec<Branch>,
    color: Color32,
    birth_time: Instant,
    life_duration: Duration,
}

#[derive(Clone)]
struct Branch {
    start: Pos2,
    end: Pos2,
    thickness: f32,
    children: Vec<Branch>,
}

#[derive(Clone)]
struct FlickerMessage {
    text: String,
    start_time: Instant,
    duration: Duration,
}

pub struct RocqVisualizer {
    // Proof text management
    proof_lines: Vec<String>,
    current_line_index: usize,
    visible_lines: usize,
    
    // Visual effects
    tree_patterns: Vec<TreePattern>,
    flicker_message: Option<FlickerMessage>,
    
    // Input handling
    last_frame_keys: std::collections::HashSet<egui::Key>,
    
    // Animation
    last_update: Instant,
}

impl Default for RocqVisualizer {
    fn default() -> Self {
        Self {
            proof_lines: generate_sample_proof(),
            current_line_index: 0,
            visible_lines: 10,
            tree_patterns: Vec::new(),
            flicker_message: None,
            last_frame_keys: std::collections::HashSet::new(),
            last_update: Instant::now(),
        }
    }
}

impl RocqVisualizer {
    pub fn new(proof: Vec<String>, _cc: &eframe::CreationContext<'_>) -> Self {
        Self {
            proof_lines: proof,
            current_line_index: 0,
            visible_lines: 10,
            tree_patterns: Vec::new(),
            flicker_message: None,
            last_frame_keys: std::collections::HashSet::new(),
            last_update: Instant::now(),
        }
    }

    fn handle_input(&mut self, ctx: &egui::Context) {
        let input = ctx.input(|i| i.clone());
        let current_keys: std::collections::HashSet<egui::Key> = input.keys_down.clone();
        
        // Check for newly pressed keys (not held from last frame)
        for key in &current_keys {
            if !self.last_frame_keys.contains(key) {
                match key {
                    egui::Key::ArrowDown => {
                        if self.current_line_index < self.proof_lines.len().saturating_sub(1) {
                            self.current_line_index += 1;
                            self.spawn_tree_pattern(ctx);
                            // TODO 2: lsp update via display functions
                        }
                    }
                    egui::Key::A => {
                        self.show_flicker_message("THEY RENAMED COQ SO WE COULD ROCQ".to_string());
                    }
                    egui::Key::S => {
                        self.show_flicker_message("RAISE THE (P)ROOF".to_string());
                    }
                    egui::Key::D => {
                        self.show_flicker_message("THE SOUND OF SOUNDNESS".to_string());
                    }
                    egui::Key::F => {
                        self.show_flicker_message("Frank Pfenning".to_string());
                    }
                    _ => {}
                }
            }
        }
        
        self.last_frame_keys = current_keys;
    }

    fn show_flicker_message(&mut self, text: String) {
        self.flicker_message = Some(FlickerMessage {
            text,
            start_time: Instant::now(),
            duration: Duration::from_secs(2),
        });
    }

    fn spawn_tree_pattern(&mut self, ctx: &egui::Context) {
        let screen_rect = ctx.screen_rect();
        let mut rng = rand::thread_rng();
        
        let origin = Pos2::new(
            rng.gen_range(screen_rect.width() * 0.3..screen_rect.width() * 0.9),
            rng.gen_range(screen_rect.height() * 0.3..screen_rect.height() * 0.9),
        );
        
        let color = Color32::from_rgb(
            rng.gen_range(100..255),
            rng.gen_range(100..255),
            rng.gen_range(100..255),
        );
        
        let tree = TreePattern {
            origin,
            branches: self.generate_tree_branches(origin, 5, 80.0),
            color,
            birth_time: Instant::now(),
            life_duration: Duration::from_secs_f32(rng.gen_range(3.0..6.0)),
        };
        
        self.tree_patterns.push(tree);
    }

    fn generate_tree_branches(&self, start: Pos2, depth: u32, length: f32) -> Vec<Branch> {
        if depth == 0 || length < 10.0 {
            return Vec::new();
        }
        
        let mut rng = rand::thread_rng();
        let mut branches = Vec::new();
        
        let num_branches = rng.gen_range(2..5);
        
        for _ in 0..num_branches {
            let angle = rng.gen_range(0.0..std::f32::consts::TAU);
            let branch_length = length * rng.gen_range(0.6..0.9);
            
            let end = Pos2::new(
                start.x + angle.cos() * branch_length,
                start.y + angle.sin() * branch_length,
            );
            
            let children = self.generate_tree_branches(end, depth - 1, branch_length * 0.7);
            
            branches.push(Branch {
                start,
                end,
                thickness: length * 0.05,
                children,
            });
        }
        
        branches
    }

    fn draw_branch(&self, painter: &egui::Painter, branch: &Branch, alpha: f32, base_color: Color32) {
        let color = Color32::from_rgba_premultiplied(
            base_color.r(),
            base_color.g(),
            base_color.b(),
            (alpha * 255.0) as u8,
        );
        
        painter.line_segment(
            [branch.start, branch.end],
            Stroke::new(branch.thickness, color),
        );
        
        for child in &branch.children {
            self.draw_branch(painter, child, alpha, base_color);
        }
    }

    fn update_animations(&mut self) {
        let now = Instant::now();
        
        // Remove expired tree patterns
        self.tree_patterns.retain(|tree| {
            now.duration_since(tree.birth_time) < tree.life_duration
        });
        
        // Remove expired flicker message
        if let Some(ref flicker) = self.flicker_message {
            if now.duration_since(flicker.start_time) > flicker.duration {
                self.flicker_message = None;
            }
        }
    }

    fn render_proof_text(&self, ctx: &egui::Context) {
        let screen_rect = ctx.screen_rect();
        let proof_area = Rect::from_min_size(
            Pos2::new(20.0, 20.0),
            Vec2::new(400.0, 300.0),
        );
        
        let painter = ctx.layer_painter(egui::LayerId::new(egui::Order::Foreground, egui::Id::new("proof_text")));
        
        let start_line = self.current_line_index.saturating_sub(self.visible_lines / 2);
        let end_line = (start_line + self.visible_lines).min(self.proof_lines.len());
        
        for (i, line_idx) in (start_line..end_line).enumerate() {
            let y_offset = i as f32 * 20.0;
            let pos = Pos2::new(proof_area.min.x, proof_area.min.y + y_offset);
            
            let color = if line_idx == self.current_line_index {
                Color32::from_rgb(255, 255, 100) // Highlight current line
            } else {
                Color32::from_rgb(200, 200, 200)
            };
            
            painter.text(
                pos,
                egui::Align2::LEFT_TOP,
                &self.proof_lines[line_idx],
                FontId::monospace(12.0),
                color,
            );
        }
    }

    fn render_tree_patterns(&self, ctx: &egui::Context) {
        let painter = ctx.layer_painter(egui::LayerId::new(egui::Order::Background, egui::Id::new("tree_patterns")));
        let now = Instant::now();
        
        for tree in &self.tree_patterns {
            let elapsed = now.duration_since(tree.birth_time).as_secs_f32();
            let life_ratio = elapsed / tree.life_duration.as_secs_f32();
            
            // Fade in and out
            let alpha = if life_ratio < 0.2 {
                life_ratio / 0.2 // Fade in
            } else if life_ratio > 0.8 {
                (1.0 - life_ratio) / 0.2 // Fade out
            } else {
                1.0
            };
            
            for branch in &tree.branches {
                self.draw_branch(&painter, branch, alpha, tree.color);
            }
        }
    }

    fn render_flicker_message(&self, ctx: &egui::Context) {
        if let Some(ref flicker) = self.flicker_message {
            let elapsed = Instant::now().duration_since(flicker.start_time).as_secs_f32();
            let flicker_frequency = 10.0; // Hz
            
            // Create flickering effect
            if (elapsed * flicker_frequency).sin() > 0.0 {
                let screen_rect = ctx.screen_rect();
                let painter = ctx.layer_painter(egui::LayerId::new(egui::Order::Tooltip, egui::Id::new("flicker_message")));
                
                let text_size = 48.0;
                let font = FontId::proportional(text_size);
                
                // Calculate text size for centering
                let galley = painter.layout_no_wrap(
                    flicker.text.clone(),
                    font.clone(),
                    Color32::WHITE,
                );
                
                let text_rect = Rect::from_min_size(
                    Pos2::new(
                        screen_rect.center().x - galley.size().x / 2.0,
                        screen_rect.center().y - galley.size().y / 2.0,
                    ),
                    galley.size(),
                );
                
                // Draw background box
                painter.rect_filled(
                    text_rect.expand(20.0),
                    10.0,
                    Color32::from_rgba_unmultiplied(0, 0, 0, 200),
                );
                
                painter.rect_stroke(
                    text_rect.expand(20.0),
                    10.0,
                    Stroke::new(2.0, Color32::WHITE),
                );
                
                // Draw text
                painter.text(
                    text_rect.center(),
                    egui::Align2::CENTER_CENTER,
                    &flicker.text,
                    font,
                    Color32::WHITE,
                );
            }
        }
    }
}

impl eframe::App for RocqVisualizer {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        // Set black background
        ctx.set_visuals(egui::Visuals {
            panel_fill: Color32::BLACK,
            window_fill: Color32::BLACK,
            ..egui::Visuals::dark()
        });
        
        self.handle_input(ctx);
        self.update_animations();
        
        // Create a full-screen central panel
        egui::CentralPanel::default()
            .frame(egui::Frame::none().fill(Color32::BLACK))
            .show(ctx, |ui| {
                // Make the UI area cover the entire screen
                ui.expand_to_include_rect(ctx.screen_rect());
            });
        
        // Render all visual elements
        self.render_tree_patterns(ctx);
        self.render_proof_text(ctx);
        self.render_flicker_message(ctx);
        
        // Request continuous repainting for animations
        ctx.request_repaint();
    }
}

fn generate_sample_proof() -> Vec<String> {
    vec![
        "Theorem plus_comm : forall n m : nat, n + m = m + n.".to_string(),
        "Proof.".to_string(),
        "  intros n m.".to_string(),
        "  induction n as [| n' IHn'].".to_string(),
        "  - (* n = 0 *)".to_string(),
        "    simpl.".to_string(),
        "    rewrite <- plus_n_O.".to_string(),
        "    reflexivity.".to_string(),
        "  - (* n = S n' *)".to_string(),
        "    simpl.".to_string(),
        "    rewrite IHn'.".to_string(),
        "    rewrite plus_n_Sm.".to_string(),
        "    reflexivity.".to_string(),
        "Qed.".to_string(),
        "".to_string(),
        "Theorem mult_comm : forall n m : nat, n * m = m * n.".to_string(),
        "Proof.".to_string(),
        "  intros n m.".to_string(),
        "  induction n as [| n' IHn'].".to_string(),
        "  - (* n = 0 *)".to_string(),
        "    simpl.".to_string(),
        "    rewrite <- mult_n_O.".to_string(),
        "    reflexivity.".to_string(),
        "  - (* n = S n' *)".to_string(),
        "    simpl.".to_string(),
        "    rewrite IHn'.".to_string(),
        "    rewrite mult_n_Sm.".to_string(),
        "    rewrite plus_comm.".to_string(),
        "    reflexivity.".to_string(),
        "Qed.".to_string(),
    ]
}

fn run_with_gui(proof: Vec<String>) -> Result<(), eframe::Error> {
    let options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default()
            .with_inner_size([1200.0, 800.0])
            .with_title("RocqNRoll")
            .with_decorations(false) // Remove window decorations for full-screen feel
            .with_fullscreen(true)
            .with_resizable(true),
            // centered: true,
        ..Default::default()
    };
    
    eframe::run_native(
        "Rocq Proof Visualizer",
        options,
        Box::new(|cc| Box::new(RocqVisualizer::new(proof, cc))),
    )
}