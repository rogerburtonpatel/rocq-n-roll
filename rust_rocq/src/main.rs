// TODOS: 
// clean up rest of constants & magic nums 
// lsp to gui 
// midi off fade out- stop_all_notes

use clap::Parser;
use serde_json::json;
use std::{fs, thread};
use std::io::{self, BufRead, Write};
use std::path::PathBuf;
use std::time::Duration;

mod lsp;
mod midi;
mod gui;
mod formatting;

use lsp::VscoqLSP;
use midi::{MidiOutput, process_tactic_to_midi_with_proof_state, autoplay_proof_sequence, ProofStateDiff};
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
    debug: bool,
    #[arg(long, help = "Run with GUI. Warning: pretty f*ckin sweet")]
    gui: bool
}

const JSON_VERSION: u64 = 1;
const MIDI_TEST_NOTE_DURATION_DEFAULT: Option<Duration> = Some(Duration::from_millis(1100));

#[derive(Clone, Debug)]
pub struct ProofStateSnapshot {
    pub goals_count: usize,
    pub shelved_count: usize,
    pub unfocused_count: usize,
}

impl ProofStateSnapshot {
    fn from_proof_view(proof_view: &serde_json::Value) -> Self {
        if let Some(proof) = proof_view.get("proof") {
            let goals_count = proof.get("goals")
                .and_then(|g| g.as_array())
                .map(|a| a.len())
                .unwrap_or(0);
            let shelved_count = proof.get("shelvedGoals")
                .and_then(|g| g.as_array())
                .map(|a| a.len())
                .unwrap_or(0);
            let unfocused_count = proof.get("unfocusedGoals")
                .and_then(|g| g.as_array())
                .map(|a| a.len())
                .unwrap_or(0);

            ProofStateSnapshot {
                goals_count,
                shelved_count,
                unfocused_count,
            }
        } else {
            ProofStateSnapshot {
                goals_count: 0,
                shelved_count: 0,
                unfocused_count: 0,
            }
        }
    }
}
const ARPEGGIATION_SLEEP_TIME: u32 = 200_000_000; // nanoseconds. lovely unit to work with

pub struct ProofStepperState {
    current_step: usize,
    total_steps: usize,
    previous_proof_state: Option<ProofStateSnapshot>,
    current_proof_state: Option<ProofStateSnapshot>,
    last_goals_state: serde_json::Value,
    proof_lines: Vec<(usize, String)>,
    document_uri: String,
    midi_output: MidiOutput,
    vscoq_lsp: VscoqLSP,
}

impl ProofStepperState {
    fn new(
        proof_lines: Vec<(usize, String)>,
        document_uri: String,
        midi_output: MidiOutput,
        vscoq_lsp: VscoqLSP,
    ) -> Self {
        Self {
            current_step: 0,
            total_steps: proof_lines.len(),
            previous_proof_state: None,
            current_proof_state: None,
            last_goals_state: serde_json::Value::Null,
            proof_lines,
            document_uri,
            midi_output,
            vscoq_lsp,
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
        self.previous_proof_state = None;
        self.current_proof_state = None;
        self.last_goals_state = serde_json::Value::Null;
    }

    fn skip_to_end(&mut self) {
        self.current_step = self.total_steps;
    }

    fn send_message(&mut self, msg: &serde_json::Value) -> std::io::Result<()> {
        self.vscoq_lsp.send_message(msg)
    }
}

// Command handlers
fn handle_quit() -> bool {
    println!("Exiting...");
    true // Signal to exit
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
            // Stop previous notes so OP-1 retriggers (comment this line to undo)
            state.midi_output.stop_all_notes(None);

            // Create proof state diff if we have previous state
            let proof_diff = if let (Some(prev), Some(curr)) = (&state.previous_proof_state, &state.current_proof_state) {
                Some(ProofStateDiff {
                    prev_goals: prev.goals_count,
                    prev_shelved: prev.shelved_count,
                    prev_unfocused: prev.unfocused_count,
                    curr_goals: curr.goals_count,
                    curr_shelved: curr.shelved_count,
                    curr_unfocused: curr.unfocused_count,
                    step_number: state.current_step + 1,
                    total_steps: state.total_steps,
                })
            } else {
                None
            };

            process_tactic_to_midi_with_proof_state(&state.midi_output, current_line_text, &last_goals_state,
                MIDI_TEST_NOTE_DURATION_DEFAULT,
                proof_diff);
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
    midi_output.play_note(90, 100, MIDI_TEST_NOTE_DURATION_DEFAULT);
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
    let interpret_msg = json!({
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
    });

    if debug {
        println!("Sending interpretToPoint: {}", interpret_msg);
    }

    state.send_message(&interpret_msg)?;

    // Wait for proofView response
    let timeout = std::time::Instant::now();
    let mut found_proof_view = false;

    while timeout.elapsed() < Duration::from_secs(2) {
        if let Some(msg) = state.vscoq_lsp.recv(Duration::from_millis(100)) {
            if debug {
                println!("Received message: {:#?}", msg);
            }

            let method = msg.get("method").and_then(|m| m.as_str()).unwrap_or("");

            if method == "vscoq/proofView" {
                println!("{}", msg);
                if let Some(params) = msg.get("params") {
                    println!("State after executing '{}':", line_text);
                    println!("{}", format_goals(params, debug));

                    // Parse and display goal counts
                    if let Some(proof) = params.get("proof") {
                        let goals_count = proof.get("goals")
                            .and_then(|g| g.as_array())
                            .map(|a| a.len())
                            .unwrap_or(0);
                        let shelved_count = proof.get("shelvedGoals")
                            .and_then(|g| g.as_array())
                            .map(|a| a.len())
                            .unwrap_or(0);
                        let unfocused_count = proof.get("unfocusedGoals")
                            .and_then(|g| g.as_array())
                            .map(|a| a.len())
                            .unwrap_or(0);

                        println!("[GOALS] Active: {}, Shelved: {}, Unfocused: {}",
                                 goals_count, shelved_count, unfocused_count);
                    }

                    state.last_goals_state = params.clone();

                    // Update proof state snapshots for diff tracking
                    state.previous_proof_state = state.current_proof_state.clone();
                    state.current_proof_state = Some(ProofStateSnapshot::from_proof_view(params));

                    // Parse semicolons first
                    let tactics = parse_semicolon_tactics(&line_text);
                    println!("[PARSE] Line '{}' split by semicolon -> {} tactic(s): {:?}",
                             line_text, tactics.len(), tactics);

                    // Build final list of tactics to send
                    let mut tactics_to_send = Vec::new();

                    for tactic in tactics {
                        // If this tactic contains "auto", replace it with extracted tactics
                        if tactic.contains("auto") {
                            if let Some(messages) = params.get("messages") {
                                if let Some(extracted_tactics) = parse_info_message(messages) {
                                    println!("[INFO] Replacing '{}' with {} extracted tactics: {:?}",
                                             tactic, extracted_tactics.len(), extracted_tactics);
                                    tactics_to_send.extend(extracted_tactics);
                                } else {
                                    tactics_to_send.push(tactic);
                                }
                            } else {
                                tactics_to_send.push(tactic);
                            }
                        } else {
                            // Not an auto tactic, use as-is
                            tactics_to_send.push(tactic);
                        }
                    }

                    println!("[PARSE] Final tactics to send: {:?}", tactics_to_send);

                    // Stop previous notes so OP-1 retriggers (comment this line to undo)
                    state.midi_output.stop_all_notes(None);

                    // Create proof state diff if we have previous state
                    let proof_diff = if let (Some(prev), Some(curr)) = (&state.previous_proof_state, &state.current_proof_state) {
                        Some(ProofStateDiff {
                            prev_goals: prev.goals_count,
                            prev_shelved: prev.shelved_count,
                            prev_unfocused: prev.unfocused_count,
                            curr_goals: curr.goals_count,
                            curr_shelved: curr.shelved_count,
                            curr_unfocused: curr.unfocused_count,
                            step_number: state.current_step + 1,
                            total_steps: state.total_steps,
                        })
                    } else {
                        None
                    };

                    // Send each tactic to MIDI with proof state diff
                    let arpeggiation_sleep : Duration =
                    if tactics_to_send.len() > 1 {
                        Duration::new(0, ARPEGGIATION_SLEEP_TIME)
                    } else {
                        Duration::new(0, 0)
                    };
                    // Send each tactic to MIDI
                    for tactic in tactics_to_send {
                        println!("[MIDI] Sending to MIDI: '{}'", tactic);
                        process_tactic_to_midi_with_proof_state(&state.midi_output, &tactic, params,
                            MIDI_TEST_NOTE_DURATION_DEFAULT,
                            proof_diff.clone());
                        thread::sleep(arpeggiation_sleep);
                    }

                    found_proof_view = true;
                    break;
                }
            }
        } else if found_proof_view {
            break;
        }
    }

    if !found_proof_view {
        println!("No proof view received for this step");
    }

    println!("\n{}\n", "-".repeat(60));
    state.advance_step();

    Ok(false)
}

/// Parse a tactic statement that may contain semicolon combinators
/// e.g., "intros; auto." -> ["intros", "auto."]
pub fn parse_semicolon_tactics(tactic: &str) -> Vec<String> {
    let trimmed = tactic.trim();

    // Split by semicolon and collect non-empty parts
    trimmed.split(';')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .collect()
}

/// Extract text from a Ppcmd structure recursively
/// Use newline as separator for Ppcmd_force_newline
fn extract_ppcmd_text(value: &serde_json::Value) -> String {
    match value {
        serde_json::Value::String(s) => s.clone(),
        serde_json::Value::Array(arr) => {
            if arr.is_empty() {
                return String::new();
            }

            // Check if this is a Ppcmd command
            if let Some(cmd) = arr[0].as_str() {
                match cmd {
                    "Ppcmd_string" => {
                        if arr.len() > 1 {
                            arr[1].as_str().unwrap_or("").to_string()
                        } else {
                            String::new()
                        }
                    }
                    "Ppcmd_force_newline" => {
                        "\n".to_string()
                    }
                    "Ppcmd_glue" => {
                        if arr.len() > 1 {
                            if let Some(inner_arr) = arr[1].as_array() {
                                inner_arr.iter()
                                    .map(|v| extract_ppcmd_text(v))
                                    .collect::<Vec<_>>()
                                    .join("")
                            } else {
                                String::new()
                            }
                        } else {
                            String::new()
                        }
                    }
                    "Ppcmd_tag" => {
                        // Tag has format: ["Ppcmd_tag", "tag_name", content]
                        if arr.len() > 2 {
                            extract_ppcmd_text(&arr[2])
                        } else {
                            String::new()
                        }
                    }
                    _ => {
                        // For other commands, try to extract from remaining elements
                        arr.iter().skip(1)
                            .map(|v| extract_ppcmd_text(v))
                            .collect::<Vec<_>>()
                            .join("")
                    }
                }
            } else {
                // Array without command string, process all elements
                arr.iter()
                    .map(|v| extract_ppcmd_text(v))
                    .collect::<Vec<_>>()
                    .join("")
            }
        }
        _ => String::new(),
    }
}

/// Parse info messages (like "info auto") from proof view messages
/// Returns a list of tactic strings extracted from the info message
pub fn parse_info_message(messages: &serde_json::Value) -> Option<Vec<String>> {
    // Messages can be an array of message entries
    if let Some(msg_array) = messages.as_array() {
        for msg_entry in msg_array {
            // Each entry is typically [level, ppcmd_content]
            if let Some(entry_arr) = msg_entry.as_array() {
                if entry_arr.len() >= 2 {
                    let text = extract_ppcmd_text(&entry_arr[1]);

                    // Check if this is an info message
                    if text.contains("(* info") {
                        // Extract the tactic part (everything after the comment marker)
                        // The actual tactic is in the next message or continuation
                        continue;
                    } else if !text.trim().is_empty() && !text.starts_with("(*") {
                        // This is the tactic content
                        // Split by newlines and periods to get individual tactics
                        let mut tactics = Vec::new();

                        for line in text.lines() {
                            let trimmed = line.trim();
                            if trimmed.is_empty() {
                                continue;
                            }

                            // Remove trailing period
                            let without_period = trimmed.trim_end_matches('.');

                            // Split by semicolon and take only the main tactic (before ';')
                            if let Some(main_tactic) = without_period.split(';').next() {
                                let tactic = main_tactic.trim();
                                if !tactic.is_empty() {
                                    tactics.push(tactic.to_string());
                                }
                            }
                        }

                        if !tactics.is_empty() {
                            return Some(tactics);
                        }
                    }
                }
            }
        }
    }

    None
}

pub fn extract_proof_steps(coq_content: &str) -> Vec<(usize, String)> {
    let mut cleaned = String::new();
    let mut comment_depth = 0usize;
    let mut chars = coq_content.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '(' && chars.peek() == Some(&'*') {
            // Start of comment
            chars.next();
            comment_depth += 1;
            continue;
        } else if c == '*' && chars.peek() == Some(&')') {
            // End of comment
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
    let mut in_proof = false;

    for (line_num, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        // Start of a proof
        if trimmed == "Proof." {
            in_proof = true;
            continue;
        }

        // not skipping currently, keeping around in case needed. 
        if trimmed == "Qed."
            || trimmed == "Defined."
            || trimmed.starts_with("Qed")
            || trimmed.starts_with("Defined")
        {
            
        }

        // Only collect steps that are inside proofs
        if in_proof && !trimmed.is_empty() {
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
    let midi_output = MidiOutput::new(args.midi_device)?;

    // Start and initialize vscoqtop LSP
    let mut vscoq_lsp = VscoqLSP::start()?;
    vscoq_lsp.initialize()?;

    // Display the proof file
    println!("\nCoq proof to step through:");
    let lines: Vec<&str> = coq_file.lines().collect();
    for (i, line) in lines.iter().enumerate() {
        println!("{:2}: {}", i, line);
    }

    let document_uri = format!("file://{}", args.file.canonicalize()?.display());

    // Open the document
    vscoq_lsp.open_document(&document_uri, &coq_file, JSON_VERSION)?;

    // Wait for document to be parsed
    println!("Waiting for document to be parsed...");
    let mut highlights_count = 0;
    while highlights_count < 3 {
        if let Some(msg) = vscoq_lsp.recv(Duration::from_millis(2000)) {
            let method = msg.get("method").and_then(|m| m.as_str()).unwrap_or("");
            if method == "vscoq/updateHighlights" {
                highlights_count += 1;
            }
        } else {
            break;
        }
    }

    // Initialize proof stepper state
    let proof_lines = extract_proof_steps(&coq_file);
    if proof_lines.is_empty() {
        println!("No proof steps found in the file. Make sure the file contains a proof with 'Proof.' and 'Qed.' markers.");
        return Ok(());
    }

    // Auto-play mode
    if args.auto_play {
        autoplay_proof_sequence(&proof_lines, &midi_output);
        return Ok(());
    }

    let mut state = ProofStepperState::new(proof_lines, document_uri.clone(), midi_output, vscoq_lsp);

    if args.gui {
        // todo: gui steps interactively with a ProofStepperState.
        // ProofStepperState may be a substruct of RocqVisualizer.
        // down arrow -> call lsp, get result. play sound based on result. do viz based on result. 
        // honestly, we want to go up and down. TODO: go back. 
        run_with_gui(state, args.debug)?;
        return Ok(());
    }

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
        std::io::BufRead::read_line(&mut stdin.lock(), &mut user_input)?;
        let input = user_input.trim();

        let should_exit = match input {
            "q" | "quit" | "exit" => handle_quit(),
            "h" | "help"          => handle_help(),
            "e" | "explain"       => handle_explain(&mut state),
            "replay"              => handle_replay(&mut state),
            "reset"               => handle_reset(&mut state),
            "s" | "skip"          => handle_skip(&mut state),
            "m" | "midi"          => handle_midi_test(&mut state.midi_output),
            ""                    => handle_execute_step(&mut state, args.debug)?,
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
    state.vscoq_lsp.close_document(&document_uri)?;

    println!("Proof session ended.");
    println!("Press any key to stop all notes and exit.");

    stdin.lock().read_line(&mut user_input)?;

    state.midi_output.stop_all_notes(None);

    Ok(())
}