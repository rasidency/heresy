import Surface

set_option warningAsError true

namespace Heresy.Native

private def le_bytes : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, value => UInt8.ofNat value :: le_bytes width (value / 256)

private def read_le : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * read_le rest

private def field (bytes : List UInt8) (offset width : Nat) : Nat :=
  read_le ((bytes.drop offset).take width)

private def identification : List UInt8 :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0] ++ List.replicate 8 0

private def base : Nat := 0x400000
private def code_offset : Nat := 120
private def file_size : Nat := 132

private def header : List UInt8 := List.flatten [
  identification, le_bytes 2 2, le_bytes 2 62, le_bytes 4 1,
  le_bytes 8 (base + code_offset), le_bytes 8 64, le_bytes 8 0,
  le_bytes 4 0, le_bytes 2 64, le_bytes 2 56, le_bytes 2 1,
  le_bytes 2 0, le_bytes 2 0, le_bytes 2 0,
  le_bytes 4 1, le_bytes 4 5, le_bytes 8 0, le_bytes 8 base,
  le_bytes 8 base, le_bytes 8 file_size, le_bytes 8 file_size, le_bytes 8 4096]

private def load_header (bytes : List UInt8) : Option (Nat × Nat) := do
  guard (bytes.length == code_offset && bytes.take 16 == identification &&
    field bytes 16 2 == 2 && field bytes 18 2 == 62 && field bytes 20 4 == 1 &&
    field bytes 32 8 == 64 && field bytes 40 8 == 0 && field bytes 48 4 == 0 &&
    field bytes 52 2 == 64 && field bytes 54 2 == 56 && field bytes 56 2 == 1 &&
    field bytes 58 6 == 0 && field bytes 64 4 == 1 && field bytes 68 4 == 5)
  let entry := field bytes 24 8
  let offset := field bytes 72 8
  let address := field bytes 80 8
  let size := field bytes 96 8
  guard (offset == 0 && address == base && size == field bytes 104 8 &&
    field bytes 112 8 == 4096 && address % 4096 == offset % 4096 &&
    address ≤ entry && code_offset ≤ offset + (entry - address) && entry < address + size)
  return (offset + (entry - address), offset + size)

private def load_entry (file : List UInt8) : Option (List UInt8) := do
  let (entry, stop) ← load_header (file.take code_offset)
  guard (file.length == stop)
  return file.drop entry

inductive Instruction where
  | moveEDI (value : Nat)
  | moveEAX (value : Nat)
  | syscall

structure Registers where
  rdi : Nat
  rax : Nat

private def decode : List UInt8 → Option (List Instruction)
  | [movEDI, a, b, c, d, movEAX, e, f, g, h, escape, syscall] => do
    guard (movEDI == 0xbf && movEAX == 0xb8 && escape == 0x0f && syscall == 0x05)
    return [.moveEDI (read_le [a, b, c, d]), .moveEAX (read_le [e, f, g, h]), .syscall]
  | _ => none

private def run : List Instruction → Registers → Option Nat
  | .moveEDI value :: rest, regs => run rest { regs with rdi := value }
  | .moveEAX value :: rest, regs => run rest { regs with rax := value }
  | [.syscall], regs => if regs.rax = 60 then some (regs.rdi % 256) else none
  | _, _ => none

def execute (file : List UInt8) (initial : Registers) : Option Nat := do
  let instructions ← decode (← load_entry file)
  run instructions initial

private def code (status : UInt8) : List UInt8 :=
  [0xbf, status, 0, 0, 0, 0xb8, 60, 0, 0, 0, 0x0f, 0x05]

def image (status : UInt8) : List UInt8 := header ++ code status

private theorem load_image (status : UInt8) : load_entry (image status) = some (code status) := by
  have extent : header.length = code_offset := by decide
  have layout : load_header header = some (code_offset, file_size) := by decide
  unfold load_entry image
  rw [List.take_left' extent, layout]
  simp [bind, Option.bind, guard, List.length_append, extent, code, code_offset, file_size]

theorem execute_image (status : UInt8) (initial : Registers) :
    execute (image status) initial = some status.toNat := by
  have fits := status.toNat_lt
  simp [execute, load_image, decode, code, read_le, run, bind, Option.bind, guard,
    Nat.mod_eq_of_lt fits]

def compile (input : String) : Except String (List UInt8) := do
  let body ← Surface.parse input
  return image (UInt8.ofNat (source_status body).toNat)

private theorem result_observation (body : Source) (status : Int) :
    source_observes (.result body) status ↔ status = source_status body := by
  constructor
  · rintro ⟨outcome, steps, result⟩
    change Executes id write_local (.result (fun locals => source_eval locals body)) (fun _ => 0) outcome at steps
    cases steps
    exact result
  · intro result
    exact ⟨.returned (source_eval (fun _ => 0) body), .result, result⟩

def observes (input : String) (status : Int) : Prop :=
  ∃ tokens body, Surface.Tokens input.toList tokens ∧ Surface.ProgramSyntax tokens body ∧
    source_observes (.result body) status

theorem compile_correct (input : String) (file : List UInt8) (compiled : compile input = .ok file)
    (initial : Registers) (status : Int) :
    (Int.ofNat <$> execute file initial) = some status ↔ observes input status := by
  cases parsed : Surface.parse input with
  | error why => simp [compile, parsed, bind, Except.bind] at compiled
  | ok body =>
    simp [compile, parsed, bind, Except.bind, pure, Except.pure] at compiled
    subst file
    have bounds : 0 ≤ source_status body ∧ source_status body < 256 :=
      unsigned_bounds 8 (signed 32 (source_eval (fun _ => 0) body))
    have fits : (source_status body).toNat < 256 := by omega
    rw [execute_image]
    have status_eq : ((UInt8.ofNat (source_status body).toNat).toNat : Int) = source_status body := by
      change Int.ofNat ((source_status body).toNat % 256) = source_status body
      rw [Nat.mod_eq_of_lt fits]
      exact Int.toNat_of_nonneg bounds.1
    change some ((UInt8.ofNat (source_status body).toNat).toNat : Int) = some status ↔ _
    rw [status_eq]
    constructor
    · intro exits
      obtain ⟨tokens, lexed, derives⟩ := (Surface.parse_correct input body).mp parsed
      exact ⟨tokens, body, lexed, derives, (result_observation _ _).mpr (Option.some.inj exits).symm⟩
    · rintro ⟨tokens, observed, lexed, derives, result⟩
      have parsed_also := (Surface.parse_correct input observed).mpr ⟨tokens, lexed, derives⟩
      have same := Except.ok.inj (parsed_also.symm.trans parsed)
      subst observed
      rw [(result_observation _ _).mp result]

def verify (input : String) (file : List UInt8) : Except String Unit := do
  let expected ← compile input
  unless expected == file do throw "native executable differs from the verified source lowering"

theorem verify_iff_compiled (input : String) (file : List UInt8) :
    verify input file = .ok () ↔ compile input = .ok file := by
  cases compiled : compile input with
  | error why => simp [verify, compiled, bind, Except.bind]
  | ok expected =>
    by_cases same : expected = file <;> simp [verify, compiled, same, bind, Except.bind, pure, Except.pure]

theorem verify_iff_derives (input : String) (file : List UInt8) :
    verify input file = .ok () ↔
      ∃ tokens body, Surface.Tokens input.toList tokens ∧ Surface.ProgramSyntax tokens body ∧
        file = image (UInt8.ofNat (source_status body).toNat) := by
  rw [verify_iff_compiled]
  constructor
  · intro compiled
    cases parsed : Surface.parse input with
    | error why => simp [compile, parsed, bind, Except.bind] at compiled
    | ok body =>
      obtain ⟨tokens, lexed, derives⟩ := (Surface.parse_correct input body).mp parsed
      exact ⟨tokens, body, lexed, derives, (by simpa [compile, parsed, bind, Except.bind, pure, Except.pure]
        using compiled : image (UInt8.ofNat (source_status body).toNat) = file).symm⟩
  · rintro ⟨tokens, body, lexed, derives, rfl⟩
    have parsed := (Surface.parse_correct input body).mpr ⟨tokens, lexed, derives⟩
    simp [compile, parsed, bind, Except.bind, pure, Except.pure]

theorem verify_correct (input : String) (file : List UInt8) (accepted : verify input file = .ok ())
    (initial : Registers) (status : Int) :
    (Int.ofNat <$> execute file initial) = some status ↔ observes input status :=
  compile_correct input file ((verify_iff_compiled input file).mp accepted) initial status

end Heresy.Native

#print axioms Heresy.Native.execute_image
#print axioms Heresy.Native.compile_correct
#print axioms Heresy.Native.verify_iff_derives
#print axioms Heresy.Native.verify_correct
