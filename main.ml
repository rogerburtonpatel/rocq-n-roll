(* String utilities *)
module StringUtils = struct
  (* Check if string starts with prefix *)
  let starts_with s prefix =
    String.length s >= String.length prefix &&
    String.sub s 0 (String.length prefix) = prefix
  
  (* Check if a string contains a substring *)
end

(* MIDI generation module with enhanced feedback *)
module MidiGen = struct
  (* Generate MIDI for tactics *)
  let tactic_to_midi tactic =
    match tactic with
    | "intros" -> print_endline "🎹 MIDI: Rising arpeggio in C major (C-E-G-C') for intros"
    | "induction" -> print_endline "🎹 MIDI: Dramatic chord progression (Dm7-G7-Cmaj7) for induction"
    | "simpl" -> print_endline "🎹 MIDI: Bell-like sound (A-E) for simpl"
    | "rewrite" -> print_endline "🎹 MIDI: Flowing sequence (D-E-F#-A) for rewrite"
    | "reflexivity" -> print_endline "🎹 MIDI: Resolving cadence (G7-C) for reflexivity"
    | _ -> print_endline ("🎹 MIDI: Generic motif for " ^ tactic)
  
  (* Generate MIDI for line types *)
  let line_to_midi line =
    let trimmed = String.trim line in
    
    (* Check different line types *)
    if String.length trimmed = 0 then
      print_endline "🎹 MIDI: Soft rest (silence)"
    else if StringUtils.starts_with trimmed "Theorem" then
      print_endline "🎹 MIDI: Majestic opening chord (Cmaj9) for theorem declaration"
    else if StringUtils.starts_with trimmed "Lemma" then
      print_endline "🎹 MIDI: Light opening chord (Am7) for lemma declaration"
    else if trimmed = "Proof." then
      print_endline "🎹 MIDI: Anticipatory motif (C-D-E) for proof start"
    else if trimmed = "Qed." then
      print_endline "🎹 MIDI: Triumphant final chord (C6/9) for proof completion"
    else if StringUtils.starts_with trimmed "-" then
      print_endline "🎹 MIDI: Transitional sound (E-D) for bullet point"
    else
      print_endline "🎹 MIDI: Ambient placeholder sound"
end

(* Helper function to convert a path to a URI *)

(* Helper to read file contents *)
let read_file filename =
  let ic = open_in filename in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.to_string s

(* Process a Coq file with enhanced MIDI feedback *)
let process_coq_file filename =
  try
    (* Read the file content *)
    let content = read_file filename in
    
    (* Split into lines *)
    let lines = Array.of_list (
      let rec split_lines acc pos =
        try
          let newline_pos = String.index_from content pos '\n' in
          let line = String.sub content pos (newline_pos - pos) in
          split_lines (line :: acc) (newline_pos + 1)
        with Not_found ->
          if pos < String.length content then
            let last_line = String.sub content pos (String.length content - pos) in
            List.rev (last_line :: acc)
          else
            List.rev acc
      in
      split_lines [] 0
    ) in
    
    (* Known Coq tactics for detection *)
    let tactics = [
      "intros"; "induction"; "simpl"; "rewrite"; "reflexivity";
      "discriminate"; "destruct"; "apply"; "assumption"; "exact";
      "constructor"; "auto"; "eauto"; "tauto"; "split"
    ] in
    
    (* Find a tactic in a line *)
    let find_tactic line =
      let line = String.trim line in
      let found = ref None in
      List.iter (fun tactic ->
        if !found = None then begin
          (* Check if line is a tactic *)
          if String.length line >= String.length tactic && 
             String.sub line 0 (String.length tactic) = tactic &&
             (String.length line = String.length tactic || 
              line.[String.length tactic] = ' ' || 
              line.[String.length tactic] = '.') then
            found := Some tactic
        end
      ) tactics;
      !found
    in
    
    (* Main interaction loop *)
    Printf.printf "\n🎵 Interactive Coq Stepper with MIDI Sonification 🎵\n\n";
    Printf.printf "Commands: n (next step), q (quit)\n\n";
    
    let current_line = ref 0 in
    let continue = ref true in
    
    (* Display formatted code context with syntax highlighting *)
    let display_context () =
      Printf.printf "\n----- Code Context -----\n";
      
      let start_line = max 0 (!current_line - 2) in
      let end_line = min (Array.length lines - 1) (!current_line + 2) in
      
      for i = start_line to end_line do
        if i = !current_line then
          Printf.printf "-> %2d: %s\n" i lines.(i)  (* Current line *)
        else
          Printf.printf "   %2d: %s\n" i lines.(i)
      done;
      
      Printf.printf "------------------------\n\n"
    in
    
    while !continue && !current_line < Array.length lines do
      display_context ();
      
      Printf.printf "> ";
      flush stdout;
      let cmd = input_line stdin in
      
      match cmd with
      | "n" | "next" ->
          let line = Array.get lines !current_line in
          
          (* Generate MIDI feedback for the line *)
          MidiGen.line_to_midi line;
          
          (* Check for tactics to provide additional feedback *)
          (match find_tactic line with
          | Some tactic ->
              Printf.printf "🎵 Detected tactic: %s\n" tactic;
              MidiGen.tactic_to_midi tactic;
          | None -> ());
          
          (* Add some space for readability *)
          print_newline ();
          
          incr current_line
          
      | "q" | "quit" ->
          Printf.printf "Quitting...\n";
          continue := false
          
      | _ ->
          Printf.printf "Unknown command. Use 'n' for next step or 'q' to quit.\n"
    done;
    
    if !current_line >= Array.length lines then
      Printf.printf "\n🎵 End of file reached. Proof stepping complete! 🎵\n"
    
  with e ->
    Printf.printf "Error: %s\n" (Printexc.to_string e);
    Printf.printf "Stack trace: %s\n" (Printexc.get_backtrace ())

(* Main entry point *)
let () =
  Printexc.record_backtrace true;
  
  if Array.length Sys.argv < 2 then begin
    Printf.printf "Usage: %s <coq_file.v>\n" Sys.argv.(0);
    exit 1
  end else begin
    process_coq_file Sys.argv.(1)
  end
