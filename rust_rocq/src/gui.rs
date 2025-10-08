use eframe::egui;
use egui::{Color32, FontId, Pos2, Rect, Stroke, Vec2};
use log::debug;
use rand::Rng;
use std::{thread, time::{Duration, Instant}};

use crate::{formatting::format_goals, midi::{process_tactic_to_midi_with_proof_state, ProofStateDiff}, parse_info_message, parse_semicolon_tactics, req_lsp_and_play_midi, ProofStateSnapshot, ProofStepperState, ARPEGGIATION_SLEEP_TIME, JSON_VERSION, MAX_LINE_LENGTH, MIDI_NOTE_DURATION_DEFAULT};

// Adjust 
const PROOF_FONT_SIZE    : f32 = 36.0;
const PROOF_AREA_START_X : f32 = 20.0;
const PROOF_AREA_START_Y : f32 = 20.0;
const PROOF_AREA_WIDTH   : f32 = 400.0;
const PROOF_AREA_HEIGHT  : f32 = 300.0;
const SPACE_BETWEEN_PROOF_LINES : f32 = 42.0;
const VISIBLE_PROOF_LINES : usize = 10;



const PROOF_LINE_HIGHLIGHT_COLOR : (u8, u8, u8) = (255, 255, 100);
const PROOF_LINE_DEFAULT_COLOR   : (u8, u8, u8) = (200, 200, 200);


// Adjust the size of gui trees. 
const TREE_LENGTH : f32 = 300.0;
const TREE_DEPTH  : u32 = 50;


// Begin Randomized Value Parameters // 

// Characteristics of a tree (number of branches, lifetime on screen, etc.)
// are randomly selected at runtime between two values. 
// These values live in this section. 
// Make them equal to set a static characteristic of a tree. 

// Adjust the display lifetime of a tree before it dissapears. 
const TREE_LIFETIME_MIN: f32 = 3.0;
const TREE_LIFETIME_MAX: f32 = 6.0;

// Adjust the number of branches a tree might have. 
const MIN_TREE_BRANCHES: i32 = 2;
const MAX_TREE_BRANCHES: i32 = 5;

// Adjust the branch length of a tree. 
const MIN_BRANCH_LENGTH: f32 = 0.6;
const MAX_BRANCH_LENGTH: f32 = 0.9;

// End Randomized Value Parameters // 


// These values are all relative to the width of the screen. 
// E.g. a MIN_TREE_START_X of 0.03 means a tree can start no further left 
// than 0.03 screen-widths from the leftmost screen border. 
const MIN_TREE_START_X: f32 = 0.03;
const MAX_TREE_START_X: f32 = 0.9;
const MIN_TREE_START_Y: f32 = 0.03;
const MAX_TREE_START_Y: f32 = 0.9;

// Adjust how small trees can get, and how much to reduce branches on each 
// recursive call to generate_tree_branches. 
// WARNING: Lowering MIN_TREE_BRANCH LENGTH too much can make really, 
// REALLY bristly (and expensive) trees. Play around at your own risk. 
// A good baseline is 
// MIN_TREE_BRANCH LENGTH = 10.0
// TREE_BRANCH_REDUCTION_FACTOR = 0.05.
const MIN_TREE_BRANCH_LENGTH: f32 = 10.0;
const TREE_BRANCH_REDUCTION_FACTOR: f32 = 0.05;


#[derive(Clone)]
struct TreePattern {
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
    // Single Point of Truth on the Proof
    proof_state: ProofStepperState,

    // Proof text management
    visible_lines: usize,
    
    // Visual effects
    tree_patterns: Vec<TreePattern>,
    flicker_message: Option<FlickerMessage>,
    
    // Input handling
    last_frame_keys: std::collections::HashSet<egui::Key>,
}


impl RocqVisualizer {
    pub fn new(proof_state: ProofStepperState, _cc: &eframe::CreationContext<'_>) -> Self {
        Self {
            visible_lines: VISIBLE_PROOF_LINES,
            tree_patterns: Vec::new(),
            flicker_message: None,
            last_frame_keys: std::collections::HashSet::new(),
            proof_state: proof_state,
        }
    }

    fn handle_input(&mut self, ctx: &egui::Context) {
        let input = ctx.input(|i| i.clone());
        let current_keys: std::collections::HashSet<egui::Key> = input.keys_down.clone();
        
        // Check for newly pressed keys (not held from last frame)
        for key in &current_keys {
            if !self.last_frame_keys.contains(key) {
                match key {
                    egui::Key::ArrowDown | egui::Key::Enter => {
                        if self.proof_state.current_step < self.proof_state.proof_lines.len() {

                            self.spawn_tree_pattern(ctx);
                            

                            // todo tree pattern based on goals
                            // todo show goals in gui
                            {
                                let state: &mut ProofStepperState = &mut self.proof_state;

                                let (line_num, line_text) = state.get_current_tactic().map(|(n, t)| (*n, t.clone())).unwrap_or((0, String::new()));
                                debug!("\nExecuting step {}/{}...", state.current_step + 1, state.total_steps);

                             // Send vscoq/interpretToPoint request
                                    if let Err(e) = state.vscoq_lsp.interpret_to_point(
                                            state.document_uri.clone(), 
                                            JSON_VERSION, 
                                            line_num, 
                                            MAX_LINE_LENGTH) {
                                        eprintln!("Error sending interpretToPoint: {e}");
                                        return;
                                    }

                                // Wait for proofView response
                                let timeout = std::time::Instant::now();
                                let mut found_proof_view = false;

                                while timeout.elapsed() < Duration::from_secs(2) {
                                    if let Some(msg) = state.vscoq_lsp.recv(Duration::from_millis(100)) {

                                        debug!("Received message: {:#?}", msg);

                                        let method = msg.get("method").and_then(|m| m.as_str()).unwrap_or("");

                                        if method == "vscoq/proofView" {
                                            debug!("{}", msg);
                                            if let Some(params) = msg.get("params") {
                                                println!("State after executing '{}':", line_text);
                                                println!("{}", format_goals(params));

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

                                                // Print stored goals from snapshot
                                                if let Some(snapshot) = &state.current_proof_state {
                                                    if !snapshot.goals.is_empty() {
                                                        debug!("[STORED] Snapshot contains {} goal(s):", snapshot.goals.len());
                                                        for (i, goal) in snapshot.goals.iter().enumerate() {
                                                            println!("  Stored Goal {}: {}", i + 1, goal.text);
                                                            if !goal.hypotheses.is_empty() {
                                                                println!("    Stored Hypotheses: {}", goal.hypotheses.len());
                                                                for hyp in &goal.hypotheses {
                                                                    println!("      {}", hyp);
                                                                }
                                                            }
                                                        }
                                                    }
                                                }

                                                // Parse semicolons first
                                                let tactics = parse_semicolon_tactics(&line_text);
                                                debug!("[PARSE] Line '{}' split by semicolon -> {} tactic(s): {:?}",
                                                         line_text, tactics.len(), tactics);

                                                // Build final list of tactics to send
                                                let mut tactics_to_send = Vec::new();

                                                let mut has_auto : bool = false; 

                                                for tactic in tactics {
                                                    // If this tactic contains "auto", replace it with extracted tactics
                                                    if tactic.contains("auto") {
                                                        has_auto = true;
                                                        if let Some(messages) = params.get("messages") {
                                                            if let Some(extracted_tactics) = parse_info_message(messages) {
                                                                debug!("[INFO] Replacing '{}' with {} extracted tactics: {:?}",
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

                                                debug!("[PARSE] Final tactics to send: {:?}", tactics_to_send);

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
                                                        prev_goals_list: prev.goals.clone(),
                                                        curr_goals_list: curr.goals.clone(),
                                                    })
                                                } else {
                                                    None
                                                };

                                                // Send each tactic to MIDI with proof state diff
                                                let arpeggiation_sleep : Duration =
                                                if tactics_to_send.len() > 1 && has_auto {
                                                    Duration::new(0, ARPEGGIATION_SLEEP_TIME)
                                                } else {
                                                    Duration::new(0, 0)
                                                };
                                                // Send each tactic to MIDI
                                                for tactic in tactics_to_send {
                                                    println!("[MIDI] Sending to MIDI: '{}'", tactic);
                                                    process_tactic_to_midi_with_proof_state(&state.midi_output, &tactic, params,
                                                        MIDI_NOTE_DURATION_DEFAULT,
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
                            };
                            
                            self.proof_state.advance_step();
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
                    egui::Key::Escape => {
                            if let Err(e) = self.proof_state.vscoq_lsp.close_document(&self.proof_state.document_uri) {
                                eprintln!("Error closing vscoq document: {e}");
                            }
                            self.proof_state.midi_output.stop_all_notes(None);
                            ctx.send_viewport_cmd(egui::ViewportCommand::Close);
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
            rng.gen_range(screen_rect.width()  * MIN_TREE_START_X..screen_rect.width()  * MAX_TREE_START_X),
            rng.gen_range(screen_rect.height() * MIN_TREE_START_Y..screen_rect.height() * MAX_TREE_START_Y),
        );
        
        let color = Color32::from_rgb(
            rng.gen_range(100..255),
            rng.gen_range(100..255),
            rng.gen_range(100..255),
        );
        

        let tree_life_duration = rng.gen_range(TREE_LIFETIME_MIN..TREE_LIFETIME_MAX);
        
        let tree = TreePattern {
            branches: self.generate_tree_branches(origin, TREE_DEPTH, TREE_LENGTH),
            color,
            birth_time: Instant::now(),
            life_duration: Duration::from_secs_f32(tree_life_duration),
        };
        
        self.tree_patterns.push(tree);
    }

    fn generate_tree_branches(&self, start: Pos2, depth: u32, length: f32) -> Vec<Branch> {
        if depth == 0 || length < MIN_TREE_BRANCH_LENGTH {
            return Vec::new();
        }
        
        let mut rng = rand::thread_rng();
        let mut branches = Vec::new();
        

        let num_branches = rng.gen_range(MIN_TREE_BRANCHES..MAX_TREE_BRANCHES);
        
        for _ in 0..num_branches {
            let angle = rng.gen_range(0.0..std::f32::consts::TAU);

            let branch_length = length * rng.gen_range(MIN_BRANCH_LENGTH..MAX_BRANCH_LENGTH);
            
            let end = Pos2::new(
                start.x + angle.cos() * branch_length,
                start.y + angle.sin() * branch_length,
            );
            
            let children = self.generate_tree_branches(end, depth - 1, branch_length * 0.8);
            
            branches.push(Branch {
                start,
                end,
                thickness: length * TREE_BRANCH_REDUCTION_FACTOR,
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
    let proof_area = Rect::from_min_size(
        Pos2::new(PROOF_AREA_START_X, PROOF_AREA_START_Y),
        Vec2::new(PROOF_AREA_WIDTH, PROOF_AREA_HEIGHT),
    );

    // Keep proof text in the Foreground so it draws above trees (trees are Background).
    let painter = ctx.layer_painter(egui::LayerId::new(egui::Order::Foreground, egui::Id::new("proof_text")));

    let start_line = self.proof_state.current_step.saturating_sub(self.visible_lines / 2);
    let end_line = (start_line + self.visible_lines).min(self.proof_state.proof_lines.len());

    for (i, line_idx) in (start_line..end_line).enumerate() {
        let y_offset = i as f32 * SPACE_BETWEEN_PROOF_LINES;
        let pos = Pos2::new(proof_area.min.x, proof_area.min.y + y_offset);

        let line_text = &self.proof_state.proof_lines[line_idx].1;
        let font = FontId::monospace(PROOF_FONT_SIZE);

        // Measure text so we can draw a background rectangle exactly behind it.
        let galley = painter.layout_no_wrap(line_text.clone(), font.clone(), Color32::WHITE);
        let text_size = galley.size();

        // Rectangle anchored at pos (LEFT_TOP) with a little padding.
        let text_rect = Rect::from_min_size(pos, text_size);
        let bg_rect = text_rect.expand(0.1);

        // Faint gray background; current line a bit brighter.
        let base_bg = Color32::from_rgba_unmultiplied(60, 60, 60, 150); // faint gray
        let current_bg = Color32::from_rgba_unmultiplied(90, 90, 90, 190); // slightly stronger
        let bg_color = if line_idx == self.proof_state.current_step { current_bg } else { base_bg };

        painter.rect_filled(bg_rect, 2.0, bg_color);

        // Decide text color as before.
        let color = if line_idx == self.proof_state.current_step {
            Color32::from_rgb(PROOF_LINE_HIGHLIGHT_COLOR.0, PROOF_LINE_HIGHLIGHT_COLOR.1, PROOF_LINE_HIGHLIGHT_COLOR.2)
        } else {
            Color32::from_rgb(PROOF_LINE_DEFAULT_COLOR.0, PROOF_LINE_DEFAULT_COLOR.1, PROOF_LINE_DEFAULT_COLOR.2)
        };

        // Draw the text slightly inset to match the padding.
        let text_pos = Pos2::new(text_rect.min.x + 6.0, text_rect.min.y + 2.0);
        painter.text(
            text_pos,
            egui::Align2::LEFT_TOP,
            line_text,
            font,
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

pub fn run_with_gui(proof_state: ProofStepperState) -> Result<(), eframe::Error> {
    let options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default()
            .with_inner_size([1200.0, 800.0])
            .with_title("RocqNRoll")
            .with_decorations(false) // Remove window decorations for full-screen feel
            .with_fullscreen(true)
            .with_resizable(true),
        ..Default::default()
    };
    
    eframe::run_native(
        "Rocq Proof Visualizer",
        options,
        Box::new(|cc| Box::new(RocqVisualizer::new(proof_state, cc))),
    )
}