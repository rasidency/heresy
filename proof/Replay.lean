import Runtime

open Heresy

private def located (table : Array Pointer) (index offset : String) : Option Pointer := do
  let pointer ← table[← index.toNat?]?
  pure ⟨pointer.capability, pointer.address + (← offset.toInt?)⟩

private def effect (table : Array Pointer) : List String → Option HeapEffect
  | ["alloc", size] => do pure (.allocate (← size.toNat?))
  | ["loadbyte", p, o] => do pure (.loadByte (← located table p o))
  | ["storebyte", p, o, v] => do pure (.storeByte (← located table p o) (UInt8.ofNat (← v.toNat?)))
  | ["loadword", p, o, w] => do pure (.loadWord (← located table p o) (← w.toNat?))
  | ["storeword", p, o, w, v] => do pure (.storeWord (← located table p o) (← w.toNat?) (← v.toInt?))
  | ["loadpointer", p, o] => do pure (.loadPointer (← located table p o))
  | ["storepointer", p, o, q] => do pure (.storePointer (← located table p o) (← table[← q.toNat?]?))
  | ["copy", s, so, d, o, n] => do pure (.copy (← located table s so) (← located table d o) (← n.toNat?))
  | ["free", p] => do pure (.release (← table[← p.toNat?]?))
  | _ => none

partial def replay (stdin : IO.FS.Stream) (state : HeapState) (table : Array Pointer) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then return 0
  let words := (line.trim.splitOn " ").filter (· ≠ "")
  let some request := effect table words
    | IO.eprintln s!"malformed request: {line.trim}"; return 2
  match heap_effect state request with
  | .error _ =>
    IO.println "fault"
    match request with
    | .allocate .. | .loadPointer _ => replay stdin state (table.push ⟨0, 0⟩)
    | _ => replay stdin state table
  | .ok edit =>
    let state := apply_heap_edit state edit
    match edit.reply with
    | .pointer pointer => IO.println s!"pointer {pointer.address}"; replay stdin state (table.push pointer)
    | .byte value => IO.println s!"value {value.toNat}"; replay stdin state table
    | .word value => IO.println s!"value {value}"; replay stdin state table
    | _ => IO.println "done"; replay stdin state table

def main (arguments : List String) : IO UInt32 := do
  let cursor := (arguments.head?.bind String.toNat?).getD 4096
  replay (← IO.getStdin) { objects := fun _ => none, counter := ⟨1, cursor⟩ } #[]
