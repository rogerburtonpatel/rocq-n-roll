use eframe::egui;
use egui::{panel, Color32, FontId, Frame, LayerId, Order, Pos2, Rect, RichText, Rounding, Stroke, Ui, Vec2};
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
const TREE_DEPTH  : u32 = 10;


// Begin Randomized Value Parameters // 

// Characteristics of a tree (number of branches, lifetime on screen, etc.)
// are randomly selected at runtime between two values. 
// These values live in this section. 
// Make them equal to set a static characteristic of a tree. 

// Adjust the display lifetime of a tree before it dissapears. 
const TREE_LIFETIME_MIN: f32 = 2.0;
const TREE_LIFETIME_MAX: f32 = 3.5;

// Adjust the number of branches a tree might have. 
const MIN_TREE_BRANCHES: i32 = 1;
const MAX_TREE_BRANCHES: i32 = 3;

// Adjust the branch length of a tree. 
const MIN_BRANCH_LENGTH: f32 = 0.7;
const MAX_BRANCH_LENGTH: f32 = 1.0;


// End Randomized Value Parameters // 


// These values are all relative to the width of the screen. 
// E.g. a MIN_TREE_START_X of 0.03 means a tree can start no further left 
// than 0.03 screen-widths from the leftmost screen border. 
const MIN_TREE_START_X: f32 = 0.25;
const MAX_TREE_START_X: f32 = 0.75;
const MIN_TREE_START_Y: f32 = 0.25;
const MAX_TREE_START_Y: f32 = 0.75;

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
pub struct Branch {
    pub start: Pos2,
    pub end: Pos2,
    pub thickness: f32,
    pub children: Vec<Branch>,
    pub start_time: f32,
    pub end_time: f32,
    pub color: Color32, // new: branch color based on goal status
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
    flash_message: Option<FlickerMessage>,
    
    // Input handling
    last_frame_keys: std::collections::HashSet<egui::Key>,
}


impl RocqVisualizer {
    pub fn new(proof_state: ProofStepperState, _cc: &eframe::CreationContext<'_>) -> Self {
        Self {
            visible_lines: VISIBLE_PROOF_LINES,
            tree_patterns: Vec::new(),
            flicker_message: None,
            flash_message: None,
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

                            // todo show goals in gui
                            {
                                let (line_num, line_text) = self.proof_state.get_current_tactic().map(|(n, t)| (*n, t.clone())).unwrap_or((0, String::new()));
                                debug!("\nExecuting step {}/{}...", self.proof_state.current_step + 1, self.proof_state.total_steps);

                             // Send vscoq/interpretToPoint request
                                    if let Err(e) = self.proof_state.vscoq_lsp.interpret_to_point(
                                            self.proof_state.document_uri.clone(), 
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
                                    if let Some(msg) = self.proof_state.vscoq_lsp.recv(Duration::from_millis(100)) {

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

                                                self.proof_state.last_goals_state = params.clone();

                                                // Update proof state snapshots for diff tracking
                                                self.proof_state.previous_proof_state = self.proof_state.current_proof_state.clone();
                                                self.proof_state.current_proof_state = Some(ProofStateSnapshot::from_proof_view(params));

                                                // Print stored goals from snapshot
                                                if let Some(snapshot) = &self.proof_state.current_proof_state {
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
                                                let mut has_bad : bool = false; 
                                                
                                                for tactic in tactics {
                                                    if tactic.contains("admit") || tactic.contains("admitted") || tactic.contains("shelve") 
                                                    || tactic.contains("admit.") || tactic.contains("admitted.") || tactic.contains("shelve.") 
                                                    || tactic.contains("Admitted.") || tactic.contains("Admitted.") 
                                                    {
                                                        has_bad = true;
                                                    }

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
                                                
                                                
                                                // here be trees
                                                self.spawn_tree_pattern(ctx, has_bad, tactics_to_send.len());



                                                // Stop previous notes so OP-1 retriggers (comment this line to undo)
                                                self.proof_state.midi_output.stop_all_notes(None);

                                                // Create proof state diff if we have previous state
                                                let proof_diff = if let (Some(prev), Some(curr)) = (&self.proof_state.previous_proof_state, &self.proof_state.current_proof_state) {
                                                    Some(ProofStateDiff {
                                                        prev_goals: prev.goals_count,
                                                        prev_shelved: prev.shelved_count,
                                                        prev_unfocused: prev.unfocused_count,
                                                        curr_goals: curr.goals_count,
                                                        curr_shelved: curr.shelved_count,
                                                        curr_unfocused: curr.unfocused_count,
                                                        step_number: self.proof_state.current_step + 1,
                                                        total_steps: self.proof_state.total_steps,
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
                                                    process_tactic_to_midi_with_proof_state(&self.proof_state.midi_output, &tactic, params,
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
                        self.show_flash_message("THEY RENAMED COQ SO WE COULD ROCQ".to_string());
                    }
                    egui::Key::S => {
                        self.show_flash_message("RAISE THE PROOF".to_string());
                    }
                    egui::Key::D => {
                        self.show_flash_message("THE SOUND OF SOUNDNESS".to_string());
                    }
                    egui::Key::F => {
                        self.show_flash_message("LEO DE MOURA".to_string());
                    }


                    egui::Key::Num1 => {
                        self.show_flicker_message("WELCOME TO ROCQNROLL.".to_string());
                    }

                    egui::Key::Num2 => {
                        self.show_flicker_message("WE JAM WITH OUR PROOFS HERE.".to_string());
                    }

                    egui::Key::Num3 => {
                        self.show_flicker_message("TACTICS MAKE NOTES.".to_string());
                    }

                    egui::Key::Num4 => {
                        self.show_flicker_message("SEMICOLON MAKES CHORDS.".to_string());
                    }

                    egui::Key::Num5 => {
                        self.show_flicker_message("AUTO MAKES SEQUENCES.".to_string());
                    }

                    egui::Key::Num6 => {
                        self.show_flicker_message("MORE GOALS MAKES MORE MUSIC.".to_string());
                    }

                    egui::Key::Num7 => {
                        self.show_flicker_message("THAT WAS FUN.".to_string());
                    }

                    egui::Key::Num8 => {
                        self.show_flicker_message("LET'S PLAY ANOTHER SHORT EXAMPLE.".to_string());
                    }

                    egui::Key::Num9 => {
                        self.show_flicker_message("HOW ABOUT".to_string());
                    }

                    egui::Key::Num0 => {
                        self.show_flash_message("VELLVM".to_string());
                        self.proof_state.midi_output.play_note(40, 100, None);
                        self.proof_state.midi_output.play_note(47, 100, None);
                        self.proof_state.midi_output.play_note(52, 100, None);
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
            duration: Duration::from_millis(2500)
        });
    }

    fn show_flash_message(&mut self, text: String) {
        self.flash_message = Some(FlickerMessage {
            text,
            start_time: Instant::now(),
            duration: Duration::from_secs(2), // Not used - remove? 
        });
    }


fn spawn_tree_pattern(&mut self, ctx: &egui::Context, has_bad : bool,  tactic_count: usize) {
    let screen_rect = ctx.screen_rect();
    let mut rng = rand::thread_rng();

    
    if let Some(s) = &self.proof_state.current_proof_state {
        for _ in 0..s.goals_count.max(1) {
            let origin = Pos2::new(
                rng.gen_range(screen_rect.width() * MIN_TREE_START_X..screen_rect.width() * MAX_TREE_START_X),
                rng.gen_range(screen_rect.height() * MIN_TREE_START_Y..screen_rect.height() * MAX_TREE_START_Y),
            );
        
            
            let color = 
            if has_bad { Color32::from_rgb(255, 0, 0) } else {
                Color32::from_rgb(
                    rng.gen_range(100..255),
                    rng.gen_range(100..255),
                    rng.gen_range(100..255),
                )
            };

            let depth = tactic_count;
            let tree_life_duration = rng.gen_range(TREE_LIFETIME_MIN..TREE_LIFETIME_MAX);
            let tree = TreePattern {
                branches: self.generate_tree_branches(origin, 
                        depth, TREE_LENGTH, 0.0, tree_life_duration * 0.5, tactic_count),
                color,
                birth_time: Instant::now(),
                life_duration: Duration::from_secs_f32(tree_life_duration),
            };
            self.tree_patterns.push(tree);
        }
    }


}


fn generate_tree_branches(
    &self,
    start: Pos2,
    depth: usize,
    length: f32,
    t0: f32,
    duration: f32,
    tactic_count: usize,
) -> Vec<Branch> {
    if depth == 0 || length < MIN_TREE_BRANCH_LENGTH {
        return Vec::new();
    }

    let snapshot = match &self.proof_state.current_proof_state {
        Some(s) => s,
        None => return Vec::new(),
    };

    let mut branches = Vec::new();
    let mut rng = rand::thread_rng();

    // Number of branches depends on tactic_count now
    let num_branches = tactic_count.max(1) as i32;
    let num_branches = num_branches.clamp(MIN_TREE_BRANCHES, MAX_TREE_BRANCHES);

    for i in 0..num_branches {
        let angle_offset = (i as f32 / num_branches as f32 - 0.5) * std::f32::consts::PI / 2.0;
        let base_angle = rng.gen_range(0.0..std::f32::consts::TAU);
        let angle = base_angle + angle_offset;

        let branch_length = length * rng.gen_range(MIN_BRANCH_LENGTH..MAX_BRANCH_LENGTH)
            + tactic_count as f32 * 2.0;

        let end = Pos2::new(
            start.x + angle.cos() * branch_length,
            start.y + angle.sin() * branch_length,
        );

        let child_t0 = t0 + (i as f32 / num_branches as f32) * duration;
        let child_duration = duration * 0.6;

        let children = self.generate_tree_branches(end, depth - 1, length * 0.7, child_t0, child_duration, tactic_count);

        // Determine color based on proof snapshot
        let color = if snapshot.shelved_count > 0 {
            Color32::from_rgb(220, 60, 60)
        } else if snapshot.goals_count > 0 {
            println!("HERE");
            Color32::from_rgb(220, 200, 0)
        } else {
            println!("HERE2");
            Color32::from_rgb(120, 220, 120)
        };

        branches.push(Branch {
            start,
            end,
            thickness: length * TREE_BRANCH_REDUCTION_FACTOR,
            children,
            start_time: t0,
            end_time: t0 + duration,
            color,
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
        // if let Some(ref flicker) = self.flicker_message {
        //     if now.duration_since(flicker.start_time) > flicker.duration {
        //         self.flicker_message = None;
        //     }
        // }
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

pub fn render_proof_state(ui: &mut Ui, proof_state: &Option<ProofStateSnapshot>) {
    let ctx = ui.ctx();
    let screen_rect = ctx.screen_rect();

    // --- Layout bounds -----------------------------------------------------
    let screen_height = screen_rect.height();
    let panel_height = screen_height * 0.25;
    let panel_margin = 16.0;

    let panel_rect = egui::Rect::from_min_max(
        egui::pos2(screen_rect.min.x + panel_margin, screen_rect.max.y - panel_height - panel_margin),
        egui::pos2(screen_rect.max.x - panel_margin, screen_rect.max.y - panel_margin),
    );

    // --- Visual style ------------------------------------------------------
    let bg = Color32::from_rgba_premultiplied(40, 40, 40, 220); // semi-opaque dark grey
    let border = Color32::from_gray(120);
    let sidebar = Color32::from_gray(200);
    let white = Color32::from_rgb(255, 255, 255);
    let grey = Color32::from_gray(160);
    let font_size = 42.0;

    // --- Background Layer --------------------------------------------------
    let painter_bg = ctx.layer_painter(egui::LayerId::new(
        egui::Order::Background,
        egui::Id::new("proof_panel_bg"),
    ));
    painter_bg.rect_filled(panel_rect, 6.0, bg);
    painter_bg.rect_stroke(panel_rect, 6.0, Stroke::new(1.0, border));

    // --- Foreground text layer ---------------------------------------------
    egui::Area::new("proof_panel")
        .fixed_pos(panel_rect.min)
        .show(ctx, |ui| {
            ui.set_min_size(panel_rect.size());
            ui.set_clip_rect(panel_rect);

            ui.vertical(|ui| {
                if let Some(snapshot) = proof_state {
                    // Header (Goals | Shelved | Unfocused)
                    ui.horizontal(|ui| {
                        ui.add_space(8.0);
                        ui.colored_label(
                            white,
                            RichText::new(format!("Goals: {}", snapshot.goals_count))
                                .monospace()
                                .size(font_size)
                                .strong(),
                        );
                        ui.add_space(32.0);
                        ui.colored_label(
                            white,
                            RichText::new(format!("Shelved: {}", snapshot.shelved_count))
                                .monospace()
                                .size(font_size),
                        );
                        ui.add_space(32.0);
                        ui.colored_label(
                            white,
                            RichText::new(format!("Unfocused: {}", snapshot.unfocused_count))
                                .monospace()
                                .size(font_size),
                        );
                    });

                    ui.add_space(12.0);
                    ui.separator();

                    if snapshot.goals.is_empty() {
                        ui.add_space(12.0);
                        ui.colored_label(
                            grey,
                            RichText::new("No goals.")
                                .monospace()
                                .size(font_size)
                                .italics(),
                        );
                    } else {
                        for (i, goal) in snapshot.goals.iter().enumerate() {
                            ui.add_space(12.0);

                            ui.horizontal(|ui| {

                                ui.label(
                                    RichText::new(&goal.text)
                                        .monospace()
                                        .size(font_size)
                                        .color(white),
                                );
                            });

                            if i < snapshot.goals.len() - 1 {
                                ui.add_space(6.0);
                                ui.separator();
                            }
                        }
                    }
                } else {
                    ui.add_space(12.0);
                    ui.colored_label(
                        grey,
                        RichText::new("No current proof state")
                            .monospace()
                            .size(font_size)
                            .italics(),
                    );
                }
            });
        });
}





fn render_tree_patterns(&self, ctx: &egui::Context) {
    let painter = ctx.layer_painter(egui::LayerId::new(egui::Order::Background, egui::Id::new("tree_patterns")));
    let now = Instant::now();

    for tree in &self.tree_patterns {
        let elapsed = now.duration_since(tree.birth_time).as_secs_f32();
        let life_ratio = (elapsed / tree.life_duration.as_secs_f32()).clamp(0.0, 1.0);

        let alpha = if life_ratio < 0.2 {
            life_ratio / 0.2
        } else if life_ratio > 0.8 {
            (1.0 - life_ratio) / 0.2
        } else {
            1.0
        };

        for branch in &tree.branches {
            self.draw_branch_partial(&painter, branch, elapsed, alpha);
        }
    }
}



fn draw_branch_partial(
    &self,
    painter: &egui::Painter,
    branch: &Branch,
    tree_elapsed: f32,
    alpha: f32,
) {
    let branch_growth = ((tree_elapsed - branch.start_time) / (branch.end_time - branch.start_time))
        .clamp(0.0, 1.0);

    if branch_growth <= 0.0 {
        return;
    }

    // Control point for curve (adds slight randomness)
    let mid = Pos2::new(
        (branch.start.x + branch.end.x) / 2.0 + (branch.end.y - branch.start.y) * 0.2,
        (branch.start.y + branch.end.y) / 2.0 - (branch.end.x - branch.start.x) * 0.2,
    );

    let color = 
    branch.color;
    // match &self.proof_state.current_proof_state {
    //     Some(s) if s.goals_count > 0 =>
    //      Color32::from_rgb(220, 200, 0),
    //     | _ => 
    //     branch.color
    // };

    let steps = 8;
    for i in 0..steps {
        let t0 = (i as f32 / steps as f32) * branch_growth;
        let t1 = ((i + 1) as f32 / steps as f32) * branch_growth;

        let p0 = quadratic_bezier(branch.start, mid, branch.end, t0);
        let p1 = quadratic_bezier(branch.start, mid, branch.end, t1);

        painter.line_segment([p0, p1], Stroke::new(branch.thickness, color.linear_multiply(alpha)));
    }

    for child in &branch.children {
        self.draw_branch_partial(painter, child, tree_elapsed, alpha);
    }
}


fn render_flash_text(&self, ctx: &egui::Context) {
    if let Some(ref flash) = self.flash_message {
        // 🔧 Controls
        let bpm: f32 = 170.0;
        let beats_per_word: f32 = 2.0;
        let per_word_time = (60.0 / bpm) * beats_per_word;
        let time_held_on_screen: f32 = 1.5;
        let fade_out_time: f32 = 1.0;

        let elapsed = Instant::now().duration_since(flash.start_time).as_secs_f32();

        // Split message into words
        let words: Vec<&str> = flash.text.split_whitespace().collect();
        if words.is_empty() {
            return;
        }

        // Calculate timing
        let total_reveal_time = words.len() as f32 * per_word_time;
        let full_display_time = total_reveal_time + time_held_on_screen;
        let total_lifetime = full_display_time + fade_out_time;

        // Stop rendering entirely after fade-out
        if elapsed > total_lifetime {
            return;
        }

        // Determine how many words should currently be visible (precise timing)
        let mut visible_count = (elapsed / per_word_time).floor() as usize + 1;
        visible_count = visible_count.min(words.len());

        // Build visible text
        let visible_text = words[..visible_count].join(" ");
        if visible_text.is_empty() {
            return;
        }

   // 🎨 Color cycling
let last_word_reveal_time = (words.len() - 1) as f32 * per_word_time;
let color = if elapsed < last_word_reveal_time {
    // normal slow cycle during reveal
    let t = elapsed * 2.0; // slow
    let r = (t.sin() * 0.5 + 0.5) * 255.0;
    let g = ((t + 2.0).sin() * 0.5 + 0.5) * 255.0;
    let b = ((t + 4.0).sin() * 0.5 + 0.5) * 255.0;
    Color32::from_rgba_unmultiplied(r as u8, g as u8, b as u8, 255)
} else {
    // beat-drop fast color cycle - starts exactly when last word appears
    let fast_t = elapsed * 20.0; // super fast
    let r = (fast_t.sin() * 0.5 + 0.5) * 255.0;
    let g = ((fast_t + 2.0).sin() * 0.5 + 0.5) * 255.0;
    let b = ((fast_t + 4.0).sin() * 0.5 + 0.5) * 255.0;
    Color32::from_rgba_unmultiplied(r as u8, g as u8, b as u8, 255)
};

        // ✨ Smooth fade out after hold time
        let alpha_factor = if elapsed > full_display_time {
            let fade_elapsed = elapsed - full_display_time;
            (1.0 - fade_elapsed / fade_out_time).clamp(0.0, 1.0)
        } else {
            1.0
        };
        let alpha = (255.0 * alpha_factor) as u8;
        let color = Color32::from_rgba_unmultiplied(color.r(), color.g(), color.b(), alpha);

        // Make it BIG
        let text_size = 74.0;
        let font = FontId::proportional(text_size);

        let screen_rect = ctx.screen_rect();
        let painter = ctx.layer_painter(egui::LayerId::new(
            egui::Order::Tooltip,
            egui::Id::new("flash_text"),
        ));

        let galley = painter.layout_no_wrap(visible_text.clone(), font.clone(), color);

        let text_rect = Rect::from_min_size(
            Pos2::new(
                screen_rect.center().x - galley.size().x / 2.0,
                screen_rect.center().y - galley.size().y / 2.0,
            ),
            galley.size(),
        );

        // 🌈 Background pulse
        let bg_pulse = ((elapsed * 3.0).sin() * 0.5 + 0.5) * 150.0 + 50.0;
        let bg_color = Color32::from_rgba_unmultiplied(
            (color.r() as f32 * 0.3) as u8,
            (color.g() as f32 * 0.3) as u8,
            (color.b() as f32 * 0.3) as u8,
            (bg_pulse as u8).saturating_mul((alpha_factor * 255.0) as u8 / 255),
        );

        // Draw background box
        painter.rect_filled(text_rect.expand(60.0), 30.0, bg_color);

        // Draw shifting border
        painter.rect_stroke(
            text_rect.expand(60.0),
            30.0,
            Stroke::new(5.0, color),
        );

        // Draw animated text
        painter.text(
            text_rect.center(),
            egui::Align2::CENTER_CENTER,
            visible_text,
            font,
            color,
        );

                // Request repaint for smooth animation
        if elapsed < total_lifetime {
            ctx.request_repaint();
        }
    }
}


    fn render_flicker_message(&self, ctx: &egui::Context) {
        if let Some(ref flicker) = self.flicker_message {
            let elapsed = Instant::now().duration_since(flicker.start_time).as_secs_f32();
            let flicker_frequency = 100.0; // Hz

            if elapsed > flicker.duration.as_secs_f32() {
                return;
            }
            
            // Create flickering effect
            if (elapsed * flicker_frequency).sin() > 0.0 {
                let screen_rect = ctx.screen_rect();
                let painter = ctx.layer_painter(egui::LayerId::new(egui::Order::Tooltip, egui::Id::new("flicker_message")));
                
                let text_size = 76.0;
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
        egui::CentralPanel::default().show(ctx, |ui| {
            // ui.heading("Rocq Proof State");
            ui.add_space(8.0);

            Self::render_proof_state(ui, &self.proof_state.current_proof_state);
        });
        self.render_flash_text(ctx);
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

fn quadratic_bezier(p0: Pos2, p1: Pos2, p2: Pos2, t: f32) -> Pos2 {
    let u = 1.0 - t;
    Pos2::new(
        u * u * p0.x + 2.0 * u * t * p1.x + t * t * p2.x,
        u * u * p0.y + 2.0 * u * t * p1.y + t * t * p2.y,
    )
}