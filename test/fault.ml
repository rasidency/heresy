let () =
  if Array.length Sys.argv = 2 && Sys.argv.(1) = "--numeric-version" then print_endline "9.6.7"
  else match Sys.getenv_opt "HERESY_FAULT" with
  | Some "timeout" -> Unix.sleep 10
  | Some "overflow" -> while true do print_string (String.make 16384 'x'); flush stdout done
  | Some "ordinary" -> print_endline "clang version 21.1.0"
  | _ -> exit 42
