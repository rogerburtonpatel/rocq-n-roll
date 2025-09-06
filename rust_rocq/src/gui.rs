use eframe::egui;
use egui::{Color32, FontId, Pos2, Rect, Stroke, Vec2};
use rand::Rng;
use std::time::{Duration, Instant};

use crate::{midi::process_tactic_to_midi, ProofStepperState};

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
}

// impl Default for RocqVisualizer {
//     fn default() -> Self {
//         Self {
//             current_line_index: 0,
//             visible_lines: 10,
//             tree_patterns: Vec::new(),
//             flicker_message: None,
//             last_frame_keys: std::collections::HashSet::new(),
//             proof_state: Default::default()
//         }
//     }
// }

impl RocqVisualizer {
    pub fn new(proof_state: ProofStepperState, _cc: &eframe::CreationContext<'_>) -> Self {
        Self {
            current_line_index: 0,
            visible_lines: 10,
            tree_patterns: Vec::new(),
            flicker_message: None,
            last_frame_keys: std::collections::HashSet::new(),
            proof_state: proof_state
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
                            // here we are. 
                            // send request to lsp 
                            // update proof with response 
                            // process_tactic_to_midi(midi_output, &line_text, result, None);
                            // 



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
        let proof_area = Rect::from_min_size(
            Pos2::new(20.0, 20.0),
            Vec2::new(400.0, 300.0),
        );
        
        let painter = ctx.layer_painter(egui::LayerId::new(egui::Order::Foreground, egui::Id::new("proof_text")));
        
        let start_line = self.current_line_index.saturating_sub(self.visible_lines / 2);
        let end_line = (start_line + self.visible_lines).min(self.proof_state.proof_lines.len());
        
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
                &self.proof_state.proof_lines[line_idx].1,
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

pub fn generate_sample_proof() -> Vec<(usize, String)> {
    let mut line_no : usize = 0; 
    vec![
         "Theorem plus_comm : forall n m : nat, n + m = m + n.",
         "Proof.",
         "  intros n m.",
         "  induction n as [| n' IHn'].",
         "  - (* n = 0 *)",
         "    simpl.",
         "    rewrite <- plus_n_O.",
         "    reflexivity.",
         "  - (* n = S n' *)",
         "    simpl.",
         "    rewrite IHn'.",
         "    rewrite plus_n_Sm.",
         "    reflexivity.",
         "Qed.",
         "",
         "Theorem mult_comm : forall n m : nat, n * m = m * n.",
         "Proof.",
         "  intros n m.",
         "  induction n as [| n' IHn'].",
         "  - (* n = 0 *)",
         "    simpl.",
         "    rewrite <- mult_n_O.",
         "    reflexivity.",
         "  - (* n = S n' *)",
         "    simpl.",
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
        Box::new(|cc| Box::new(RocqVisualizer::new(proof_state, cc))),
    )
}