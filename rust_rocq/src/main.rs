// TODOS: 
// clean up rest of constants & magic nums 
// lsp to gui 
// midi off fade out- stop_all_notes

use clap::Parser;
use serde_json::json;
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use std::time::Duration;

mod lsp;
mod midi;
mod gui;
mod formatting;

use lsp::RocqLSP;
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
    debug: bool,
    #[arg(long, help = "Run with GUI. Warning: pretty f*ckin sweet")]
    gui: bool
}

const JSON_VERSION: u64 = 1;
const MIDI_TEST_NOTE_DURATION_DEFAULT: u64 = 1100;

// State management for the proof stepper, with careful consideration 
// for the LSP's 'invisible step' when entering Proof Mode. 
// Can't #[derive(Debug)] bc PortMidi doesn't have it, and I'm lazy 
pub struct ProofStepperState {
    current_step: usize,
    total_steps: usize,
    last_goals_state: serde_json::Value,
    proof_lines: Vec<(usize, String)>,

    // MIDI - would be nice to keep external, but Rust's impl rules demand we 
    // pass it in via RocqVisualizer, which MIDI should _definitely_ not be a 
    // member of. 
    midi_output: MidiOutput,
    rocq_lsp: RocqLSP,
}

impl ProofStepperState {
    fn new(proof_lines: Vec<(usize, String)>, midi_device: MidiOutput, rocq_lsp: RocqLSP) -> Self {
        Self {
            current_step: 0,
            total_steps: proof_lines.len(),
            last_goals_state: serde_json::Value::Null,
            proof_lines,
            midi_output: midi_device,
            rocq_lsp: rocq_lsp,
        }
    }

    fn is_complete(&self) -> bool {
        self.current_step >= self.total_steps
    }

    fn get_current_tactic(&self) -> Option<&(usize, String)> {
        self.proof_lines.get(self.current_step)
    }

    fn get_lsp_line_number(&self, lsp: &RocqLSP) -> usize {
        if let Some((line_num, _)) = self.get_current_tactic() {
            *line_num + lsp.lsp_position_offset
        } else {
            0
        }
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
    state.rocq_lsp.lsp_position_offset = 0;
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
    document_uri: &str,
    debug: bool,
) -> Result<bool, Box<dyn std::error::Error>> {
    if state.is_complete() {
        println!("Proof already complete!");
        return Ok(false);
    }

    let line_text = state.get_current_tactic().map(|(_, t)| t.clone()).unwrap_or_default();
    println!("\nExecuting step {}/{}...", state.current_step + 1, state.total_steps);

    // Request goals at the LSP position (accounting for any offset)
    let lsp_line = state.get_lsp_line_number(&state.rocq_lsp);
    let goals_params = json!({
        "textDocument": {
            "uri": document_uri,
            "version": JSON_VERSION
        },
        "position": {
            "line": lsp_line,
            "character": 0
        }
    });

    let request_id = state.current_step as u64 + lsp::COQ_LSP_STEP_OFFSET;
    state.rocq_lsp.send_request(request_id, "proof/goals", &goals_params)?;

    // Wait for and process response
    let mut found_response = false;
    let mut responses_received = 0;

    while let Some(message) = state.rocq_lsp.recv(Duration::from_secs(5)) {
        if let Some(id) = message.get("id") {
            const INVIS_STEP_OFFSET: u64 = 1000;
            if id.as_u64() == Some(request_id) {
                responses_received += 1;

                if debug {
                    println!("MESSAGE {}", responses_received);
                    println!("{:#?}", message);
                    println!("END MESSAGE");
                }

                // Check if this is an invisible transition step
                if is_invisible_transition(&message) {
                    println!("Detected invisible proof transition, adjusting offset...");
                    state.rocq_lsp.lsp_position_offset += 1;
                    
                    // Make another request with the adjusted position
                    let adjusted_goals_params = json!({
                        "textDocument": {
                            "uri": document_uri,
                            "version": JSON_VERSION
                        },
                        "position": {
                            "line": state.get_lsp_line_number(&state.rocq_lsp),
                            "character": 0
                        }
                    });

                    state.rocq_lsp.send_request(
                        request_id + INVIS_STEP_OFFSET,
                        "proof/goals",
                        &adjusted_goals_params,
                    )?;
                    continue;
                }

                if let Some(result) = message.get("result") {
                    found_response = true;

                    println!("State after executing '{}':", line_text);
                    println!("{}", format_goals(result, debug));
                    
                    // Store the current goals state for replay
                    state.last_goals_state = result.clone();

                    // Process this proof state to MIDI
                    process_tactic_to_midi(&state.midi_output, &line_text, result, None);

                    break;
                    
                } else if let Some(error) = message.get("error") {
                    println!("Error: {}", error);
                    found_response = true;
                    break;
                }
            }
            // Handle the adjusted request response
            else if id.as_u64() == Some(request_id + INVIS_STEP_OFFSET) {
                if let Some(result) = message.get("result") {
                    found_response = true;

                    println!("State after executing '{}':", line_text);
                    println!("{}", format_goals(result, debug));
                    
                    state.last_goals_state = result.clone();
                    process_tactic_to_midi(&state.midi_output, &line_text, result, None);

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

    // Advance to next step only after successful execution
    state.advance_step();

    Ok(false)
}

// Detect invisible proof transition based on the response pattern
fn is_invisible_transition(message: &serde_json::Value) -> bool {
    if let Some(result) = message.get("result") {
        // Check for the pattern: no range, position offset -1, goals unchanged from forall form
        if let Some(position) = result.get("position") {
            if let Some(offset) = position.get("offset") {
                if offset.as_i64() == Some(-1) && result.get("range").is_none() {
                    // Additional check: if goals contain forall (typical of proof entry)
                    if let Some(goals_obj) = result.get("goals") {
                        if let Some(goals_array) = goals_obj.get("goals") {
                            if let Some(goals_list) = goals_array.as_array() {
                                return goals_list.iter().any(|goal| {
                                    if let Some(ty) = goal.get("ty") {
                                        if let Some(ty_str) = ty.as_str() {
                                            return ty_str.trim().starts_with("forall");
                                        }
                                    }
                                    false
                                });
                            }
                        }
                    }
                }
            }
        }
    }
    false
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

    // Start the LSP
    let mut lsp = RocqLSP::start().map_err(|e| {
        if e.to_string().contains("No such file") {
            format!("Error: coq-lsp executable not found. Did you run `opam install coq-lsp`?\nOriginal error: {}", e)
        } else {
            format!("Failed to start coq-lsp: {}", e)
        }
    })?;

    println!("Coq LSP connected successfully");
    
    // Initialize the LSP
    lsp.initialize()?;

    // Display the proof file
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
            "version": JSON_VERSION, 
            "text": coq_file
        }
    });

    lsp.send_notification("textDocument/didOpen", &open_params)?;
    std::thread::sleep(Duration::from_secs(1));

    // Initialize proof stepper state
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

    let mut state = ProofStepperState::new(proof_lines, midi_output, lsp);

    if args.gui {
        // todo: gui steps interactively with a ProofStepperState.
        // ProofStepperState may be a substruct of RocqVisualizer.
        // down arrow -> call lsp, get result. play sound based on result. do viz based on result. 
        // honestly, we want to go up and down. TODO: go back. 
        run_with_gui(state)?;
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
            "h" | "help" => handle_help(),
            "e" | "explain" => handle_explain(&mut state),
            "replay" => handle_replay(&mut state),
            "reset" => handle_reset(&mut state),
            "s" | "skip" => handle_skip(&mut state),
            "m" | "midi" => handle_midi_test(&mut state.midi_output),
            "" => handle_execute_step(&mut state, &document_uri, args.debug)?,
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
    let close_params = json!({ "textDocument": { "uri": document_uri } });
    state.rocq_lsp.send_notification("textDocument/didClose", &close_params)?;
    println!("Proof session ended.");
    println!("Press any key to stop all notes and exit.");

    std::io::BufRead::read_line(&mut stdin.lock(), &mut user_input)?;
    
    state.midi_output.stop_all_notes(None);

    Ok(())
}