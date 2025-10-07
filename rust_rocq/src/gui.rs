use eframe::egui;
use egui::{Color32, FontId, Pos2, Rect, Stroke, Vec2};
use rand::Rng;
use serde_json::json;
use std::time::{Duration, Instant};

use crate::{formatting::format_goals, midi::process_tactic_to_midi, ProofStepperState, JSON_VERSION, MIDI_TEST_NOTE_DURATION_DEFAULT};

// Adjust 
const PROOF_FONT_SIZE    : f32 = 12.0;
const PROOF_AREA_START_X : f32 = 20.0;
const PROOF_AREA_START_Y : f32 = 20.0;
const PROOF_AREA_WIDTH   : f32 = 400.0;
const PROOF_AREA_HEIGHT  : f32 = 300.0;
const SPACE_BETWEEN_PROOF_LINES : f32 = 20.0;
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
    current_line_index: usize, // TODO replace all instances with proof_state.curr_line
    visible_lines: usize,
    
    // Visual effects
    tree_patterns: Vec<TreePattern>,
    flicker_message: Option<FlickerMessage>,
    
    // Input handling
    last_frame_keys: std::collections::HashSet<egui::Key>,
    debug: bool,
}


impl RocqVisualizer {
    pub fn new(proof_state: ProofStepperState, _cc: &eframe::CreationContext<'_>, debug: bool) -> Self {
        Self {
            current_line_index: 0,
            visible_lines: VISIBLE_PROOF_LINES,
            tree_patterns: Vec::new(),
            flicker_message: None,
            last_frame_keys: std::collections::HashSet::new(),
            proof_state: proof_state,
            debug: debug,
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
                        if self.current_line_index < self.proof_state.proof_lines.len().saturating_sub(1) {
                            // TODO: sync sound and viz with actual proof 
                            // let (new_proof_state, ...) = self.req_lsp_and_play_midi();
                            // self.proof_state.advance_step(new_proof_state); // sm like this 
                            // self.spawn_tree_pattern(ctx); // base off of new state 
                            self.req_lsp_and_play_midi();
                            self.proof_state.advance_step();                            
                            self.current_line_index += 1;
                            self.spawn_tree_pattern(ctx);
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

    fn req_lsp_and_play_midi(&mut self) {
        let (line_num, line_text) = self.proof_state.get_current_tactic()
            .map(|(n, t)| (*n, t.clone()))
            .unwrap_or((0, String::new()));

        println!("\nExecuting step {}/{}...", self.proof_state.current_step + 1, self.proof_state.total_steps);

        // Send vscoq/interpretToPoint request
        if let Err(e) = self.proof_state.send_message(&json!({
            "jsonrpc": "2.0",
            "method": "vscoq/interpretToPoint",
            "params": {
                "textDocument": {
                    "uri": self.proof_state.document_uri.clone(),
                    "version": JSON_VERSION
                },
                "position": {
                    "line": line_num,
                    "character": 999
                }
            }
        })) {
            eprintln!("Error sending interpretToPoint: {e}");
            return;
        }

        // Wait for proofView response
        let timeout = std::time::Instant::now();
        let mut found_proof_view = false;

        while timeout.elapsed() < Duration::from_secs(2) {
            if let Some(msg) = self.proof_state.vscoq_lsp.recv(Duration::from_millis(100)) {
                let method = msg.get("method").and_then(|m| m.as_str()).unwrap_or("");

                if method == "vscoq/proofView" {
                    if let Some(params) = msg.get("params") {
                        println!("State after executing '{}':", line_text);
                        println!("{}", format_goals(params, false));

                        self.proof_state.last_goals_state = params.clone();

                        // Process this proof state to MIDI
                        process_tactic_to_midi(&self.proof_state.midi_output, &line_text, params,
                            MIDI_TEST_NOTE_DURATION_DEFAULT);

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
        
        let painter = ctx.layer_painter(egui::LayerId::new(egui::Order::Foreground, egui::Id::new("proof_text")));
        
        let start_line = self.current_line_index.saturating_sub(self.visible_lines / 2);
        let end_line = (start_line + self.visible_lines).min(self.proof_state.proof_lines.len());
        
        for (i, line_idx) in (start_line..end_line).enumerate() {
            let y_offset = i as f32 * SPACE_BETWEEN_PROOF_LINES;
            let pos = Pos2::new(proof_area.min.x, proof_area.min.y + y_offset);
            
            let color = if line_idx == self.current_line_index {
                // Highlight current line
                Color32::from_rgb(PROOF_LINE_HIGHLIGHT_COLOR.0,
                                  PROOF_LINE_HIGHLIGHT_COLOR.1, 
                                  PROOF_LINE_HIGHLIGHT_COLOR.2) 
            } else {
                Color32::from_rgb(PROOF_LINE_DEFAULT_COLOR.0,
                                  PROOF_LINE_DEFAULT_COLOR.1, 
                                  PROOF_LINE_DEFAULT_COLOR.2)
            };
            
            painter.text(
                pos,
                egui::Align2::LEFT_TOP,
                &self.proof_state.proof_lines[line_idx].1,
                FontId::monospace(PROOF_FONT_SIZE),
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

pub fn generate_sample_proof() -> Vec<(usize, String)> {
    let mut line_no : usize = 0; 
    vec![
         "Theorem plus_comm : forall n m : nat, n + m = m + n.",
         "Proof.",
         "  intros n m.",
         "  induction n as [| n' IHn'].",
         "  - simpl.",
         "    rewrite <- plus_n_O.",
         "    reflexivity.",
         "  - simpl.",
         "    rewrite IHn'.",
         "    rewrite plus_n_Sm.",
         "    reflexivity.",
         "Qed.",
         "",
         "Theorem mult_comm : forall n m : nat, n * m = m * n.",
         "Proof.",
         "  intros n m.",
         "  induction n as [| n' IHn'].",
         "  - simpl.",
         "    rewrite <- mult_n_O.",
         "    reflexivity.",
         "  - simpl.",
         "    rewrite IHn'.",
         "    rewrite mult_n_Sm.",
         "    rewrite plus_comm.",
         "    reflexivity.",
         "Qed.",
    ].iter().map(
        |s| { 
        let old_line_no = line_no; 
        line_no += 1; // mutating map! yay for safety! 
        (old_line_no, s.to_string()) 
    }).collect()
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
        Box::new(move |cc| Box::new(RocqVisualizer::new(proof_state, cc, debug))),
    )
}