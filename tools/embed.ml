let () =
  let channel = open_in_bin Sys.argv.(1) in
  let source = Fun.protect ~finally:(fun () -> close_in channel) (fun () -> really_input_string channel (in_channel_length channel)) in
  let start = Str.search_forward (Str.regexp "^module Heap") source 0 in
  let imports = Str.search_forward (Str.regexp "^import ") source start in
  let prelude = String.sub source 0 start ^ "module Main where\n\n" ^ String.sub source imports (String.length source - imports) in
  Printf.printf "let source = %S\nlet version = %S\n" prelude Sys.argv.(2)
