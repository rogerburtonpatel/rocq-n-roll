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
            if !messages_array.is_empty() {
                println!("[MIDI] Error detected - playing dissonant cluster!");
                play_dissonant_cluster(midi_output, base_pitch);
            }
        }
    }
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
        thread::sleep(Duration::from_millis(200));
    }
    
    println!("[MIDI] Proof sequence complete!");
}

fn extract_proof_steps(coq_content: &str) -> Vec<(usize, String)> {
    let lines: Vec<&str> = coq_content.lines().collect();
    let mut proof_steps = Vec::new();
    let mut in_proof = false;
    
    for (line_num, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        
        if trimmed == "Proof." {
            in_proof = true;
            continue;
        }
        
        if trimmed == "Qed." || trimmed == "Defined." || trimmed.starts_with("Qed") || trimmed.starts_with("Defined") {
            in_proof = false;
            break;
        }
        
        if in_proof && !trimmed.is_empty() && !trimmed.starts_with("(*") {
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
    let mut initialize_response = None;
    while let Ok(message) = rx.recv() {
        if let Some(id) = message.get("id") {
            if id.as_u64() == Some(1) && message.get("result").is_some() {
                initialize_response = Some(message.clone());
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
                    display_goals(result);
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
                let mut current_goals_json = serde_json::Value::Null;

                while let Ok(message) = rx.recv_timeout(std::time::Duration::from_secs(5)) {
                    if let Some(id) = message.get("id") {
                        if id.as_u64() == Some(100 + current_step as u64) {
                            if let Some(result) = message.get("result") {
                                println!("State after executing '{}':", line_text);
                                display_goals(result);
                                
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
                midi_output.stop_all_notes();

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
fn display_goals(result: &serde_json::Value) {
    // Check if there are any goals
    if let Some(goals_config) = result.get("goals") {
        // Display foreground goals
        if let Some(goals) = goals_config.get("goals") {
            if let Some(goals_array) = goals.as_array() {
                if goals_array.is_empty() {
                    println!("No active goals.");
                } else {
                    println!("Active goals:");
                    for (i, goal) in goals_array.iter().enumerate() {
                        println!("Goal {}:", i + 1);

                        // Display hypotheses
                        if let Some(hyps) = goal.get("hyps") {
                            if let Some(hyps_array) = hyps.as_array() {
                                if !hyps_array.is_empty() {
                                    println!("  Hypotheses:");
                                    for hyp in hyps_array {
                                        // Extract hypothesis name(s)
                                        let names = if let Some(names) = hyp.get("names") {
                                            if let Some(names_array) = names.as_array() {
                                                let name_strings: Vec<String> = names_array
                                                    .iter()
                                                    .map(|n| {
                                                        if let Some(s) = n.as_str() {
                                                            s.to_string()
                                                        } else {
                                                            n.to_string()
                                                        }
                                                    })
                                                    .collect();
                                                name_strings.join(", ")
                                            } else {
                                                names.to_string()
                                            }
                                        } else {
                                            "".to_string()
                                        };

                                        // Extract hypothesis type
                                        let ty_str = if let Some(ty) = hyp.get("ty") {
                                            if let Some(s) = ty.as_str() {
                                                s.to_string()
                                            } else {
                                                ty.to_string()
                                            }
                                        } else {
                                            "".to_string()
                                        };

                                        println!("    {}: {}", names, ty_str);
                                    }
                                }
                            }
                        }

                        // Display goal type
                        let ty_str = if let Some(ty) = goal.get("ty") {
                            if let Some(s) = ty.as_str() {
                                s.to_string()
                            } else {
                                ty.to_string()
                            }
                        } else {
                            "".to_string()
                        };

                        println!("  Goal: {}", ty_str);
                        println!();
                    }
                }
            }
        }

        // Display shelved goals if any
        if let Some(shelf) = goals_config.get("shelf") {
            if let Some(shelf_array) = shelf.as_array() {
                if !shelf_array.is_empty() {
                    println!("Shelved goals:");
                    for (i, goal) in shelf_array.iter().enumerate() {
                        println!("Shelved goal {}:", i + 1);
                        let ty_str = if let Some(ty) = goal.get("ty") {
                            if let Some(s) = ty.as_str() {
                                s.to_string()
                            } else {
                                ty.to_string()
                            }
                        } else {
                            "".to_string()
                        };
                        println!("  {}", ty_str);
                    }
                    println!();
                }
            }
        }

        // Display given up goals if any
        if let Some(given_up) = goals_config.get("given_up") {
            if let Some(given_up_array) = given_up.as_array() {
                if !given_up_array.is_empty() {
                    println!("Given up goals:");
                    for (i, goal) in given_up_array.iter().enumerate() {
                        println!("Given up goal {}:", i + 1);
                        let ty_str = if let Some(ty) = goal.get("ty") {
                            if let Some(s) = ty.as_str() {
                                s.to_string()
                            } else {
                                ty.to_string()
                            }
                        } else {
                            "".to_string()
                        };
                        println!("  {}", ty_str);
                    }
                    println!();
                }
            }
        }
    } else {
        // If no goals, just print the raw response
        println!(
            "{}",
            serde_json::to_string_pretty(result).unwrap_or_default()
        );
    }

    // Display any messages
    if let Some(messages) = result.get("messages") {
        if let Some(messages_array) = messages.as_array() {
            if !messages_array.is_empty() {
                println!("Messages:");
                for message in messages_array {
                    let msg_text = if let Some(text) = message.get("text") {
                        if let Some(s) = text.as_str() {
                            s.to_string()
                        } else {
                            text.to_string()
                        }
                    } else if let Some(s) = message.as_str() {
                        s.to_string()
                    } else {
                        message.to_string()
                    };
                    println!("  {}", msg_text);
                }
                println!();
            }
        }
    }
}
