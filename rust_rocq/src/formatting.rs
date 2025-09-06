use serde_json::Value;

// Function to display goals in a readable format based on the documentation
pub fn format_goals(result: &Value, debug: bool) -> String {
    let mut output = String::new();
    
    if debug {
        output.push_str("Raw Response:\n");
        output.push_str(&serde_json::to_string_pretty(result).unwrap_or_default());
        output.push('\n');
    }

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