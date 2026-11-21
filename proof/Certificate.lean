import Checker

set_option warningAsError true

open Lean

private def schedule_inputs (steps : String) (inputs : List String) : IO (Except String (Option (List Nat) × List String)) := do
  match inputs with
  | "--schedule" :: file :: frontends =>
    let text ← IO.FS.readFile file
    return do
      let threads : List Nat ← Lean.fromJson? (← Lean.Json.parse text)
      let some budget := steps.toNat? | throw "expected a numeric step budget"
      unless threads.length ≤ budget do throw "thread schedule exceeds the step budget"
      unless !frontends.isEmpty do throw "expected a typed frontend"
      return (some threads, frontends)
  | "--schedule" :: _ | [] => return .error "expected a schedule file and a typed frontend"
  | frontends => return .ok (none, frontends)

private def event_bytes (node : Lean.Json) : Except String (List UInt8) := do
  if let .str text := node then return text.toUTF8.toList
  let values : List Nat ← Lean.fromJson? node
  unless values.all (· < 256) do throw "file event contains an out-of-range byte"
  return values.map UInt8.ofNat

private def file_event (node : Lean.Json) : Except String Heresy.FileEvent := do
  let fields ← node.getArr?
  match fields.toList with
  | [.str "open", path, mode, ok] => return .opened (← event_bytes path) (← event_bytes mode) (← ok.getBool?)
  | [.str "read", handle, size, data] =>
    let payload ← if data == .null then pure none else some <$> event_bytes data
    return .input (← handle.getNat?) (← size.getNat?) payload
  | [.str "write", handle, data, ok] => return .output (← handle.getNat?) (← event_bytes data) (← ok.getBool?)
  | [.str "close", handle, ok] => return .closed (← handle.getNat?) (← ok.getBool?)
  | _ => throw "expected an open, read, write or close file event"

private def observation_inputs (steps : String) (inputs : List String) :
    IO (Except String (List Heresy.FileEvent × Option (List Nat) × List String)) := do
  match inputs with
  | "--file-events" :: file :: rest =>
    let text ← IO.FS.readFile file
    let scheduled ← schedule_inputs steps rest
    return do
      let events ← (← (← Lean.Json.parse text).getArr?).toList.mapM file_event
      return (events, ← scheduled)
  | _ => return (← schedule_inputs steps inputs).map (fun result => ([], result))

private def check_observation (runtime haskell steps status stdout : String) (frontends : List String)
    (invocation : Heresy.Ordinary.Invocation) (witness : Option (List Nat) := none) : IO UInt32 := do
  match steps.toNat?, status.toNat? with
  | some budget, some observedStatus =>
    match Heresy.validate_ordinary (← IO.FS.readFile runtime)
        (← frontends.mapM (fun (path : String) => IO.FS.readFile path)) (← IO.FS.readFile haskell) with
    | .error message => IO.eprintln message; pure 1
    | .ok program =>
      if witness.isSome && !program.parallel then
        IO.eprintln "an explicit schedule requires a threaded program"; return 1
      if Heresy.matches_invocation program budget invocation observedStatus (← IO.FS.readBinFile stdout).data.toList witness then
        IO.println "checked the linked program's exit status and stdout"
        pure 0
      else
        IO.eprintln "ordinary observation disagrees with supplied exit status or stdout, or exceeded its step budget"
        pure 1
  | _, _ => IO.eprintln "ordinary observation requires a step budget and numeric exit status"; pure 1

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | "module" :: runtime :: haskell :: ast :: rest =>
    match Heresy.validate_module (← IO.FS.readFile runtime)
        (← (ast :: rest).mapM (fun (path : String) => IO.FS.readFile path)) (← IO.FS.readFile haskell) with
    | .ok count =>
      IO.println s!"checked complete runtime, linkage of {count} function(s) and dispatch structure"
      pure 0
    | .error message => IO.eprintln message; pure 1
  | "ordinary-link" :: runtime :: haskell :: ast :: rest =>
    match Heresy.validate_ordinary (← IO.FS.readFile runtime)
        (← (ast :: rest).mapM (fun (path : String) => IO.FS.readFile path)) (← IO.FS.readFile haskell) with
    | .ok _ => IO.println "checked ordinary function bodies, calls and startup"; pure 0
    | .error message => IO.eprintln message; pure 1
  | "ordinary-observe" :: runtime :: haskell :: steps :: status :: stdout :: ast :: rest =>
    check_observation runtime haskell steps status stdout (ast :: rest) {}
  | "ordinary-observe-argv" :: runtime :: haskell :: steps :: status :: stdout :: argv :: inputs =>
    match ← observation_inputs steps inputs with
    | .error why => IO.eprintln why; pure 1
    | .ok (events, witness, frontends) =>
      match Heresy.Ordinary.Invocation.decode (← IO.FS.readBinFile argv).data.toList events with
      | some invocation => check_observation runtime haskell steps status stdout frontends invocation witness
      | none => IO.eprintln "expected NUL-terminated argv entries, including argv[0]"; pure 1
  | "ordinary-ready-argv" :: runtime :: haskell :: steps :: argv :: inputs =>
    match ← observation_inputs steps inputs with
    | .error why => IO.eprintln why; pure 1
    | .ok (events, witness, frontends) =>
      match steps.toNat?, Heresy.Ordinary.Invocation.decode (← IO.FS.readBinFile argv).data.toList events with
      | some budget, some invocation =>
        match Heresy.validate_ordinary (← IO.FS.readFile runtime)
            (← frontends.mapM (fun (path : String) => IO.FS.readFile path)) (← IO.FS.readFile haskell) with
        | .error message => IO.eprintln message; pure 1
        | .ok program =>
          if witness.isSome && !program.parallel then
            IO.eprintln "an explicit schedule requires a threaded program"; return 1
          if (Heresy.process_status (Heresy.invocation_observation program budget invocation witness).1).isSome then
            IO.println "checked the ordinary lowering and model termination for this invocation"; pure 0
          else
            IO.eprintln (if witness.isSome then "the supplied schedule did not reach a process outcome"
              else "ordinary invocation exceeded its step budget")
            pure 1
      | _, _ => IO.eprintln "expected a numeric step budget and NUL-terminated argv entries"; pure 1
  | ["ordinary", runtime, ast, haskell] =>
    match Heresy.validate_ordinary (← IO.FS.readFile runtime) [← IO.FS.readFile ast]
        (← IO.FS.readFile haskell) with
    | .ok _ => IO.println "checked ordinary function bodies, calls and startup"; pure 0
    | .error message => IO.eprintln message; pure 1
  | ["effects", runtime, ast, haskell, stdout] =>
    match Heresy.validate_ordinary (← IO.FS.readFile runtime) [← IO.FS.readFile ast]
        (← IO.FS.readFile haskell) with
    | .error message => IO.eprintln message; pure 1
    | .ok program =>
      let (outcome, visible) := program.observation 256 false
      if outcome = .fault (.access .dead) && (← IO.FS.readBinFile stdout).data.toList == visible then
        IO.println "checked the decoded program's stale alias fault and stdout"
        pure 0
      else
        IO.eprintln "ordinary program does not predict the stale alias fault and supplied stdout"
        pure 1
  | ["effects", stdout] =>
    let observed := (Heresy.copied_alias_run 65).snapshot.observation
    let overlap := Heresy.copied_alias_uses_overlapping_snapshot
    let _ := overlap
    if observed.1 = .fault (.access .dead) &&
        (← IO.FS.readBinFile stdout).data.toList == observed.2 then
      IO.println "checked overlapping copy, pointer shadow, release fault and visible stdout"
      pure 0
    else
      IO.eprintln "stdout differs from the copied-alias model"
      pure 1
  | ["shared", name, ast, haskell] =>
    match Heresy.validate_shared name (← IO.FS.readFile ast) (← IO.FS.readFile haskell) with
    | .ok () => IO.println s!"checked shared conditional in {name}"; pure 0
    | .error message => IO.eprintln message; pure 1
  | "linkage" :: haskell :: ast :: rest =>
    match Heresy.validate_linkage (← (ast :: rest).mapM (fun (path : String) => IO.FS.readFile path)) (← IO.FS.readFile haskell) with
    | .ok count => IO.println s!"checked {count} linked function bindings, label symbols and startup"; pure 0
    | .error message => IO.eprintln message; pure 1
  | ["dispatch", haskell] =>
    match Heresy.validate_dispatches (← IO.FS.readFile haskell) with
    | .ok count => IO.println s!"checked dispatch equations and {count} emitted control-flow graph(s)"; pure 0
    | .error message => IO.eprintln message; pure 1
  | ["process", haskell] =>
    if Heresy.validates_process (← IO.FS.readFile haskell) then
      IO.println "checked stream operations, process termination and cleanup equations"; pure 0
    else
      IO.eprintln "stream operations, process termination or cleanup differ from the model"; pure 1
  | ["memory", haskell] =>
    let generated ← IO.FS.readFile haskell
    if !Heresy.validates_access generated then
      IO.eprintln "memory access differs from the model"; pure 1
    else if !Heresy.validates_pointer_arithmetic generated then
      IO.eprintln "pointer arithmetic differs from the model"; pure 1
    else if !Heresy.validates_release generated then
      IO.eprintln "memory release differs from the model"; pure 1
    else if !Heresy.validates_allocation generated then
      IO.eprintln "memory allocation differs from the model"; pure 1
    else if !Heresy.validates_copy generated then
      IO.eprintln "memory copy differs from the model"; pure 1
    else if !Heresy.validates_aggregate_memory generated then
      IO.eprintln "aggregate memory differs from the model"; pure 1
    else if !Heresy.validates_atomic_memory generated then
      IO.eprintln "atomic memory differs from the model"; pure 1
    else if !Heresy.validates_scalar_memory generated then
      IO.eprintln "scalar memory differs from the model"; pure 1
    else if !Heresy.validates_pointer_memory generated then
      IO.eprintln "pointer memory differs from the model"; pure 1
    else if !Heresy.validates_freeze generated then
      IO.eprintln "read-only transition differs from the model"; pure 1
    else if !Heresy.validates_synchronisation generated then
      IO.eprintln "synchronisation differs from the model"; pure 1
    else if !Heresy.validates_argument_slots generated then
      IO.eprintln "argument slot layout differs from the model"; pure 1
    else if !Heresy.validates_invocation generated then
      IO.eprintln "call routing differs from the model"; pure 1
    else IO.println "checked memory, calls and synchronisation equations"; pure 0
  | ["program", ast, haskell] =>
    match Heresy.validate_program (← IO.FS.readFile ast) (← IO.FS.readFile haskell) with
    | .ok () => IO.println "checked emitted closed program and exit status"; pure 0
    | .error message => IO.eprintln message; pure 1
  | ["text", source, haskell] =>
    match Heresy.validate_closed_text (← IO.FS.readFile source) (← IO.FS.readFile haskell) with
    | .ok body => IO.println s!"checked closed C source and lowering, exit status {Heresy.source_status body}"; pure 0
    | .error message => IO.eprintln message; pure 1
  | ["text-compile", source] =>
    match Heresy.compile_closed_text (← IO.FS.readFile source) with
    | .ok generated => IO.print generated; pure 0
    | .error message => IO.eprintln message; pure 1
  | ["native-compile", source] =>
    match Heresy.Native.compile (← IO.FS.readFile source) with
    | .ok image => (← IO.getStdout).write ⟨image.toArray⟩; pure 0
    | .error message => IO.eprintln message; pure 1
  | ["native-verify", source, executable] =>
    match Heresy.Native.verify (← IO.FS.readFile source) (← IO.FS.readBinFile executable).data.toList with
    | .ok () => IO.println "checked the complete ELF image against the closed C source"; pure 0
    | .error message => IO.eprintln message; pure 1
  | [ast, haskell] =>
    let frontend ← IO.FS.readFile ast
    let generated ← IO.FS.readFile haskell
    match Heresy.validate_kernels frontend generated with
    | .ok count => IO.println s!"checked {count} emitted integer kernel(s)"; pure 0
    | .error message => IO.eprintln message; pure 1
  | _ =>
    IO.eprintln "usage: certificate [program] AST.json Module.hs | certificate text SOURCE.c Module.hs | certificate (text-compile|native-compile) SOURCE.c | certificate native-verify SOURCE.c ELF | certificate shared FUNCTION AST.json Module.hs | certificate (dispatch|memory|process) Module.hs | certificate linkage Module.hs AST.json ... | certificate module Heap.hs Module.hs AST.json ... | certificate ordinary Heap.hs AST.json Module.hs | certificate ordinary-link Heap.hs Module.hs AST.json ... | certificate ordinary-ready-argv Heap.hs Module.hs STEPS ARGV [--file-events FILE] [--schedule FILE] AST.json ... | certificate ordinary-observe Heap.hs Module.hs STEPS STATUS STDOUT AST.json ... | certificate ordinary-observe-argv Heap.hs Module.hs STEPS STATUS STDOUT ARGV [--file-events FILE] [--schedule FILE] AST.json ... | certificate effects [Heap.hs AST.json Module.hs] STDOUT"
    pure 2
