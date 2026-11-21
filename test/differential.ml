let read path = In_channel.with_open_bin path In_channel.input_all

let lines text = List.filter (( <> ) "") (String.split_on_char '\n' text)

let pick list = List.nth list (Random.int (List.length list))

let script () =
  let buffer = Buffer.create 512 in
  let line format = Printf.kbprintf (fun buffer -> Buffer.add_char buffer '\n') buffer format in
  let sizes = ref [||] and live = ref [||] and slots = Hashtbl.create 16 in
  let push size = sizes := Array.append !sizes [| size |]; live := Array.append !live [| true |] in
  let entry ?(least = 1) () =
    let alive = List.filter (fun index -> !live.(index) && !sizes.(index) >= least) (List.init (Array.length !sizes) Fun.id) in
    if alive = [] || Random.int 40 = 0 then Random.int (Array.length !sizes) else pick alive
  in
  let offset index width =
    let size = !sizes.(index) in
    match Random.int 60 with
    | 0 -> -1
    | 1 -> size - width + 1
    | _ -> if size < width then 0 else Random.int (size - width + 1)
  in
  let width index = pick (List.filter (fun w -> w <= max 1 !sizes.(index)) [1; 2; 4; 8]) in
  let word width =
    if width = 8 then Printf.sprintf "%Lu" (Random.bits64 ())
    else string_of_int (Random.full_int (1 lsl (8 * width)))
  in
  let alloc () = let size = pick [8; 16; 16; 24; 33; 64; 64; 1; 0] in line "alloc %d" size; push size in
  let slot index = if Random.int 40 = 0 then 4 else 8 * (max 0 (offset index 8) / 8) in
  alloc ();
  for _ = 1 to 10 + Random.int 40 do
    let p = entry () in
    match Random.int 24 with
    | 0 | 1 | 2 -> alloc ()
    | 3 | 4 -> line "storebyte %d %d %d" p (offset p 1) (Random.int 256)
    | 5 | 6 -> line "loadbyte %d %d" p (offset p 1)
    | 7 | 8 | 9 -> let w = width p in line "storeword %d %d %d %s" p (offset p w) w (word w)
    | 10 | 11 | 12 -> let w = width p in line "loadword %d %d %d" p (offset p w) w
    | 13 | 14 | 15 ->
        let p = entry ~least:8 () in
        let o = slot p and q = entry () in
        line "storepointer %d %d %d" p o q;
        Hashtbl.replace slots (p, o) q
    | 16 | 17 | 18 ->
        let known = Hashtbl.fold (fun key target found -> (key, target) :: found) slots [] in
        let (p, o), target = if known <> [] && Random.int 5 > 0 then pick known else let p = entry ~least:8 () in (p, slot p), p in
        line "loadpointer %d %d" p o;
        push !sizes.(target);
        !live.(Array.length !live - 1) <- !live.(target)
    | 19 | 20 | 21 ->
        let d = entry () in
        let n = Random.int (1 + min !sizes.(p) !sizes.(d)) in
        line "copy %d %d %d %d %d" p (offset p n) d (offset d n) n
    | _ -> if Random.int 3 = 0 then (line "free %d" p; !live.(p) <- false) else alloc ()
  done;
  Buffer.contents buffer

let run ?(arguments = []) directory program input =
  let output = Filename.concat directory "output" and errors = Filename.concat directory "errors" in
  let descriptor path = Unix.openfile path [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC; Unix.O_CLOEXEC ] 0o600 in
  let out = descriptor output and err = descriptor errors in
  let code = Fun.protect ~finally:(fun () -> Unix.close out; Unix.close err) (fun () ->
    Process.run ~timeout:60. ~stdout:out ~stderr:err "sh" ([ "-c"; "input=$1; shift; cd \"$(dirname \"$0\")\" && exec \"./$(basename \"$0\")\" \"$@\" < \"$input\""; program; input ] @ arguments)) in
  code, lines (read output), read errors

let () =
  match Sys.argv with
  | [| _; lean; runtime; harness |] ->
      let seed = Option.fold ~none:1 ~some:int_of_string (Sys.getenv_opt "HERESY_SEED") in
      let cases = Option.fold ~none:400 ~some:int_of_string (Sys.getenv_opt "HERESY_CASES") in
      Random.init seed;
      let directory = Filename.temp_dir "differential" "" in
      let haskell = Filename.concat directory "replay" in
      let code = Process.run ~timeout:600. "ghc" [ "-v0"; "-O0"; "-package-env"; "-"; "-hide-all-packages";
        "-package"; "base"; "-package"; "bytestring"; "-package"; "containers"; "-package"; "mtl";
        "-i" ^ runtime; "-outputdir"; directory; "-o"; haskell; harness ] in
      if code <> 0 then (prerr_endline "differential: ghc failed to build the replay harness"; exit 1);
      let input = Filename.concat directory "script" in
      let faults = ref 0 and steps = ref 0 in
      for case = 1 to cases do
        let text = script () in
        Out_channel.with_open_bin input (fun channel -> output_string channel text);
        let status, observed, errors = run directory haskell input in
        let cursor = match observed with
          | first :: _ when String.starts_with ~prefix:"pointer " first -> [ String.sub first 8 (String.length first - 8) ]
          | _ -> [] in
        let model, expected, model_errors = run ~arguments:cursor directory lean input in
        if model <> 0 || status <> 0 || expected <> observed then begin
          Printf.eprintf "differential: case %d with seed %d disagrees\n%s\nmodel (status %d):\n%s%s\nruntime (status %d):\n%s%s\n"
            case seed text model (String.concat "\n" expected) model_errors status (String.concat "\n" observed) errors;
          exit 1
        end;
        steps := !steps + List.length expected;
        faults := !faults + List.length (List.filter (( = ) "fault") expected)
      done;
      Printf.printf "differential: %d scripts and %d effects agree, %d of them faults\n" cases !steps !faults
  | _ ->
      prerr_endline "usage: differential LEAN-REPLAY RUNTIME-DIRECTORY HARNESS";
      exit 2
