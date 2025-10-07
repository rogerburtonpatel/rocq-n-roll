use std::collections::HashMap;
use std::thread;
use std::time::Duration;
use rand::Rng;
use serde_json::Value;

extern crate portmidi as pm;
use pm::MidiMessage;

type Pitch        = u8; 
type Velocity     = u8;
type MidiChannel  = u8; 
type MidiStatus   = u8; 
type Note         = (Pitch, Velocity);
type NoteDuration = u64;

const CHANNEL: MidiChannel = 0;
const NOTE_ON_STATUS  : MidiStatus = 0x90;
const NOTE_OFF_STATUS : MidiStatus = 0x80;

const OUTPUT_PORT_BUF_SIZE: usize = 1024;

const DEFAULT_NOTE : Note = (55, 60);
const MAX_PITCH : Pitch = 127;

// Length notes held and unheld for --auto-play
const AUTOPLAY_NOTE_LENGTH  : NoteDuration = 200;
const AUTOPLAY_PAUSE_LENGTH : NoteDuration = 200;

// When getting dissonant (bad proof state), how much to play and how long 
const NUM_DISSONANT_NOTES_IN_CLUSTER: i16 = 4;
const DISSONANCE_HOLD_TIME: u64 = 500;

// MIDI output wrapper
pub struct MidiOutput {
    context: Option<pm::PortMidi>,
    port_id: Option<i32>,
    enabled: bool,
}

#[derive(Debug)]
pub enum MidiError {
    UserRequestedDeviceList,
    MidiDisabled,
    Other(Box<dyn std::error::Error>),
}

impl std::fmt::Display for MidiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MidiError::UserRequestedDeviceList => write!(f, "User requested available MIDI devices; exiting."),
            MidiError::Other(e) => write!(f, "{}", e),
            MidiError::MidiDisabled => write!(f, "MIDI disabled. Use --midi-device <device num> to enable."),
        }
    }
}

impl std::error::Error for MidiError {}

impl MidiOutput {
    pub fn new(device_id: Option<i32>) -> Result<Self, Box<dyn std::error::Error>> {
        let context = pm::PortMidi::new()?;
        
        if let Some(id) = device_id {
            if id == -1 {
                println!("Available MIDI devices:");
                for dev in context.devices()? {
                    println!("{}", dev);
                }
                return Err(Box::new(MidiError::UserRequestedDeviceList));
            }
            
            // Validate device exists
            let _device = context.device(id)?;
            Ok(MidiOutput { context: Some(context), port_id: Some(id), enabled: true })
        } else {
            eprintln!("MIDI disabled. Use --midi-device to enable.");
            if let Ok(devices) = context.devices() {
                eprintln!("Available MIDI devices:");
                    for dev in devices {
                        println!("{}", dev);
                    }
            }
            return Err(Box::new(MidiError::MidiDisabled));
        }
    }
    
    pub fn play_note(&self, pitch: u8, velocity: u8, hold_duration: Option<Duration>) {
        if !self.enabled || self.context.is_none() || self.port_id.is_none() {
            return;
        }
        let context = self.context.as_ref().unwrap();
        let port_id = self.port_id.unwrap();
        
        if let Ok(device) = context.device(port_id) {
            if let Ok(mut port) = context.output_port(device, OUTPUT_PORT_BUF_SIZE) {
                let note_on = MidiMessage {
                    status: NOTE_ON_STATUS + CHANNEL,
                    data1: pitch,
                    data2: velocity,
                    data3: 0,
                };

                if let Err(e) = port.write_message(note_on) {
                    eprintln!("MIDI error: {}", e);
                    return;
                }
                if let Some(duration) = hold_duration {
                    thread::sleep(duration);
                     let note_off = MidiMessage {
                        status: NOTE_OFF_STATUS + CHANNEL,
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
    
    pub fn stop_note(&self, pitch: u8) {
        if !self.enabled || self.context.is_none() || self.port_id.is_none() {
            return;
        }

        let context = self.context.as_ref().unwrap();
        let port_id = self.port_id.unwrap();
        
        if let Ok(device) = context.device(port_id) {
                if let Ok(mut port) = context.output_port(device, OUTPUT_PORT_BUF_SIZE) {
                    let note_off = MidiMessage {
                        status: NOTE_OFF_STATUS + CHANNEL,
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
    
    pub fn stop_all_notes(&self, after_delay: Option<Duration>) {
        if !self.enabled {
            return;
        }
        if let Some(delay) = after_delay {
            thread::sleep(delay);
        }
        
        for note in 0..=MAX_PITCH {
            self.stop_note(note);
        }
    }
}

// TODO redo this completely with deautomation. 
// Tactic to (pitch, velocity) mapping
pub fn create_tactic_midi_map() -> HashMap<&'static str, Note> {
    let mut map = HashMap::new();
    
    // Basic tactics - fundamental notes
    map.insert("reflexivity", (60, 100)); // C4 - strong, conclusive
    map.insert("simpl", (67, 80));         // G4 - clean, bright
    map.insert("intros", (64, 90));        // E4 - opening, welcoming
    map.insert("apply", (69, 85));         // A4 - forward motion
    map.insert("rewrite", (62, 75));       // D4 - transformative
    map.insert("simple apply", (65,80)); 
    
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
// Handles multi-word tactics like "simple apply"
pub fn extract_tactic_name(line: &str) -> String {
    let trimmed = line.trim_start_matches(|c: char| c.is_whitespace() || c == '-' || c == '+' || c == '*');
    let trimmed = trimmed.trim_start();

    // Try to match multi-word tactics first (up to 3 words)
    let words: Vec<&str> = trimmed.split_whitespace().take(3).collect();

    // Try matching from longest to shortest
    for n in (1..=words.len()).rev() {
        let candidate = words[..n].join(" ").to_lowercase();
        let tactic_map = create_tactic_midi_map();
        if tactic_map.contains_key(candidate.as_str()) {
            return candidate;
        }
    }

    // Fall back to first word if no match found
    if let Some(first_word) = words.first() {
        first_word.to_lowercase()
    } else {
        "unknown".to_string()
    }
}

#[derive(Clone, Debug)]
pub struct Goal {
    pub text: String,
    pub hypotheses: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct ProofStateDiff {
    pub prev_goals: usize,
    pub prev_shelved: usize,
    pub prev_unfocused: usize,
    pub curr_goals: usize,
    pub curr_shelved: usize,
    pub curr_unfocused: usize,
    pub step_number: usize,
    pub total_steps: usize,
    pub prev_goals_list: Vec<Goal>,
    pub curr_goals_list: Vec<Goal>,
}

// Modify based on proof state complexity
fn adjust_note_using_context (mut pitch : u8, mut velocity : u8, goals_json : &serde_json::Value) -> (u8, u8) {    
    if let Some(goals_config) = goals_json.get("goals") {
        if let Some(goals) = goals_config.get("goals") {
            if let Some(goals_array) = goals.as_array() {
                let num_goals = goals_array.len();
                
                // More goals = higher pitch (urgency)
                pitch = (pitch as i16 + (num_goals as i16 * 2)).min(MAX_PITCH as i16) as u8;
                
                // Count total hypotheses for velocity adjustment
                let mut total_hyps = 0;
                for goal in goals_array {
                    if let Some(hyps) = goal.get("hypotheses") {
                        if let Some(hyps_array) = hyps.as_array() {
                            total_hyps += hyps_array.len();
                        }
                    }
                }
                
                // More hypotheses = higher velocity (complexity)
                velocity = (velocity as i16 + (total_hyps as i16 * 3)).min(MAX_PITCH as i16) as u8;
                
                println!("[MIDI] Goals: {}, Hypotheses: {}, Final note: {} @ {}", 
                         num_goals, total_hyps, pitch, velocity);
            }
        }
    }
    (pitch, velocity)
}

// Real MIDI processing function
pub fn process_tactic_to_midi(
    midi_output: &MidiOutput,
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
        .unwrap_or(DEFAULT_NOTE); // Default: G3, medium velocity
    
    (pitch, velocity) = adjust_note_using_context(pitch, velocity, goals_json);
    // Play the note
    midi_output.play_note(pitch, velocity, hold_duration);

    // Add harmonic context based on proof state

    // play_harmonic_context(midi_output, goals_json, pitch);
}

// MIDI processing with proof state diff tracking (to undo, use process_tactic_to_midi instead)
pub fn process_tactic_to_midi_with_proof_state(
    midi_output: &MidiOutput,
    line_text: &str,
    goals_json: &serde_json::Value,
    hold_duration: Option<Duration>,
    proof_diff: Option<ProofStateDiff>
) {
    let tactic_map = create_tactic_midi_map();
    let tactic_name = extract_tactic_name(line_text);

    println!("\n[MIDI] Processing tactic: '{}' -> '{}'", line_text, tactic_name);

    // Print proof state diff
    if let Some(diff) = &proof_diff {
        let goals_diff = diff.curr_goals as i32 - diff.prev_goals as i32;
        let shelved_diff = diff.curr_shelved as i32 - diff.prev_shelved as i32;
        let unfocused_diff = diff.curr_unfocused as i32 - diff.prev_unfocused as i32;

        println!("[PROOF STATE DIFF] Step {}/{}", diff.step_number, diff.total_steps);
        println!("  Previous: goals={}, shelved={}, unfocused={}",
                 diff.prev_goals, diff.prev_shelved, diff.prev_unfocused);

        if !diff.prev_goals_list.is_empty() {
            println!("    Previous goals:");
            for (i, goal) in diff.prev_goals_list.iter().enumerate() {
                println!("      {}: {}", i + 1, goal.text);
            }
        }

        println!("  Current:  goals={}, shelved={}, unfocused={}",
                 diff.curr_goals, diff.curr_shelved, diff.curr_unfocused);

        if !diff.curr_goals_list.is_empty() {
            println!("    Current goals:");
            for (i, goal) in diff.curr_goals_list.iter().enumerate() {
                println!("      {}: {}", i + 1, goal.text);
            }
        }

        println!("  Delta:    goals={:+}, shelved={:+}, unfocused={:+}",
                 goals_diff, shelved_diff, unfocused_diff);
    }

    // Get base note for the tactic
    let (mut pitch, mut velocity) = tactic_map.get(tactic_name.as_str())
        .copied()
        .unwrap_or(DEFAULT_NOTE); // Default: G3, medium velocity

    // Modify based on proof state complexity
    if let Some(goals_config) = goals_json.get("goals") {
        if let Some(goals) = goals_config.get("goals") {
            if let Some(goals_array) = goals.as_array() {
                let num_goals = goals_array.len();

                // More goals = higher pitch (urgency)
                pitch = (pitch as i16 + (num_goals as i16 * 2)).min(MAX_PITCH as i16) as u8;

                // Count total hypotheses for velocity adjustment
                let mut total_hyps = 0;
                for goal in goals_array {
                    if let Some(hyps) = goal.get("hypotheses") {
                        if let Some(hyps_array) = hyps.as_array() {
                            total_hyps += hyps_array.len();
                        }
                    }
                }

                // More hypotheses = higher velocity (complexity)
                velocity = (velocity as i16 + (total_hyps as i16 * 3)).min(MAX_PITCH as i16) as u8;

                println!("[MIDI] Goals: {}, Hypotheses: {}, Final note: {} @ {}",
                         num_goals, total_hyps, pitch, velocity);
            }
        }
    }

    // Play the note
    midi_output.play_note(pitch, velocity, hold_duration);

    // Add harmonic context based on proof state

    // play_harmonic_context(midi_output, goals_json, pitch);
}

// TODO change this completely. do it based on diff with last goal. 
// Add harmonic context based on proof correctness
fn play_harmonic_context(midi_output: &MidiOutput, goals_json: &serde_json::Value, base_pitch: u8) {
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
fn play_chord(midi_output: &MidiOutput, root: u8, intervals: &[u8], velocity: u8) {
    for &interval in intervals {
        let note = (root as i16 + interval as i16).min(MAX_PITCH as i16) as u8;
        midi_output.play_note(note, velocity, None);
    }
}

// Play dissonant cluster for errors
fn play_dissonant_cluster(midi_output: &MidiOutput, base_pitch: u8) {
    // Play cluster of semitones - very dissonant
    for i in 0..NUM_DISSONANT_NOTES_IN_CLUSTER {
        let note = (base_pitch as i16 + i).min(MAX_PITCH as i16) as u8;
        midi_output.play_note(note, 90, Some(Duration::from_millis(DISSONANCE_HOLD_TIME)));
    }
}

// Play entire proof sequence with delays
pub fn autoplay_proof_sequence(proof_steps: &[(usize, String)], midi_output: &MidiOutput) {
    println!("\n[MIDI] Playing entire proof sequence with delays...");
    
    let tactic_map = create_tactic_midi_map();
    
    for (i, (_, line_text)) in proof_steps.iter().enumerate() {
        let tactic_name = extract_tactic_name(line_text);
        let (mut pitch, mut velocity) = tactic_map.get(tactic_name.as_str())
            .copied()
            .unwrap_or(DEFAULT_NOTE);

        // RANDOMIZATION: REMOVE
        let mut rng = rand::thread_rng();
        let offset: i8 = rng.gen_range(-5..=5); // Small random value between -5 and 5
        let offset2: i8 = rng.gen_range(-5..=5); // Small random value between -5 and 5
    
        pitch = pitch.saturating_add_signed(offset);
        velocity = velocity.saturating_add_signed(offset2);
        
        // END RANDOMIZATION 

        println!("[MIDI] Step {}: {} -> Note {} @ {}", i + 1, line_text, pitch, velocity);
        
        midi_output.play_note(pitch, velocity, 
            Some(Duration::from_millis(AUTOPLAY_NOTE_LENGTH))
        );
        
        thread::sleep(Duration::from_millis(AUTOPLAY_PAUSE_LENGTH));

    }
    midi_output.stop_all_notes(None);
    
    println!("[MIDI] Proof sequence complete!");
}