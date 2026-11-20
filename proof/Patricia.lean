import Proof
import Std.Tactic.BVDecide

set_option warningAsError true

namespace Heresy.Patricia

structure Branch where
  left : Int → Bool
  pivot : Int
  sign : Bool

def Branch.ofMask (pref mask : BitVec 64) : Branch :=
  let sign := mask.msb
  ⟨fun key => (BitVec.ofInt 64 key &&& mask) == 0,
    if sign then 0 else (pref + mask).toInt, sign⟩

private abbrev Word := BitVec 64

def maskPrefix (key mask : Word) : Word := key &&& ((0 - mask) ^^^ mask)

def SingleBit (m : Word) : Prop := m ≠ 0 ∧ m &&& (m - 1) = 0

private theorem pivot_bits (key pref m : Word) (single : SingleBit m)
    (matched : maskPrefix key m = pref) :
    (key.slt (if m.msb then 0 else pref + m) = true) ↔
      ((key &&& m = 0) ↔ m.msb = false) := by
  unfold SingleBit at single
  unfold maskPrefix at matched
  obtain ⟨nonzero, bit⟩ := single
  cases hm : m.msb <;> simp only [Bool.false_eq_true, ↓reduceIte, iff_true] <;> bv_decide

theorem nested_bits (key child small large : Word)
    (ss : SingleBit small) (sl : SingleBit large) (shorter : small.ult large)
    (hkey : maskPrefix key small = child) :
    maskPrefix key large = maskPrefix child large ∧ key &&& large = child &&& large := by
  simp only [SingleBit, maskPrefix] at *
  obtain ⟨_, _⟩ := ss
  obtain ⟨_, _⟩ := sl
  bv_decide

inductive Tree (α : Type) where
  | nil
  | tip (key : Int) (value : α)
  | bin (branch : Branch) (left right : Tree α)

def lookup (key : Int) : Tree α → Option α
  | .nil => none
  | .tip k x => if key = k then some x else none
  | .bin b l r => if b.left key then lookup key l else lookup key r

def bin (b : Branch) : Tree α → Tree α → Tree α
  | l, .nil => l
  | .nil, r => r
  | l, r => .bin b l r

def Supported (t : Tree α) (p : Int → Prop) : Prop :=
  ∀ k, lookup k t ≠ none → p k

theorem absent {t : Tree α} {p : Int → Prop} (support : Supported t p) {k : Int}
    (outside : ¬ p k) : lookup k t = none :=
  Classical.byContradiction (fun found => outside (support k found))

theorem lookup_bin (b : Branch) (l r : Tree α) (k : Int)
    (left : Supported l (fun x => b.left x = true))
    (right : Supported r (fun x => b.left x = false)) :
    lookup k (bin b l r) = lookup k (.bin b l r) := by
  have low (side : b.left k = false) : lookup k l = none := absent left (by simp [side])
  have high (side : b.left k = true) : lookup k r = none := absent right (by simp [side])
  cases l <;> cases r <;> cases side : b.left k <;> simp_all [bin, lookup]

inductive WellFormed : Tree α → Prop where
  | nil : WellFormed .nil
  | tip : WellFormed (.tip k x)
  | bin : WellFormed l → WellFormed r →
      Supported l (fun k => b.left k = true ∧ (k < b.pivot ↔ b.sign = false)) →
      Supported r (fun k => b.left k = false ∧ (k < b.pivot ↔ b.sign = true)) →
      WellFormed (.bin b l r)

def FitsKey (k : Int) : Prop := -9223372036854775808 ≤ k ∧ k ≤ 9223372036854775807

def InPrefix (pref mask : BitVec 64) (k : Int) : Prop :=
  FitsKey k ∧ maskPrefix (BitVec.ofInt 64 k) mask = pref

theorem nested_route {t : Tree α} (child pref small large : BitVec 64)
    (smallBit : SingleBit small) (largeBit : SingleBit large) (shorter : small.ult large)
    (within : maskPrefix child large = pref)
    (support : Supported t (InPrefix child small)) :
    Supported t (fun k => InPrefix pref large k ∧
      (Branch.ofMask pref large).left k = (Branch.ofMask pref large).left child.toInt) := by
  intro k found
  obtain ⟨fits, matching⟩ := support k found
  obtain ⟨samePrefix, sameSide⟩ := nested_bits _ child small large smallBit largeBit shorter matching
  exact ⟨⟨fits, samePrefix.trans within⟩, by simp [Branch.ofMask, sameSide]⟩

inductive Encoded : Tree α → Prop where
  | nil : Encoded .nil
  | tip : FitsKey k → Encoded (.tip k x)
  | bin : Encoded l → Encoded r → SingleBit mask →
      Supported l (fun k => InPrefix pref mask k ∧ (Branch.ofMask pref mask).left k = true) →
      Supported r (fun k => InPrefix pref mask k ∧ (Branch.ofMask pref mask).left k = false) →
      Encoded (.bin (Branch.ofMask pref mask) l r)

theorem int_pivot {k : Int} {pref mask : BitVec 64}
    (single : SingleBit mask) (member : InPrefix pref mask k) :
    k < (Branch.ofMask pref mask).pivot ↔
      ((Branch.ofMask pref mask).left k = true ↔ mask.msb = false) := by
  obtain ⟨⟨lower, upper⟩, matching⟩ := member
  have key : (BitVec.ofInt 64 k).toInt = k :=
    BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)
  have relative := pivot_bits (BitVec.ofInt 64 k) pref mask single matching
  cases sign : mask.msb <;>
    simpa [Branch.ofMask, sign, BitVec.slt_iff_toInt_lt, key] using relative

theorem encoded_wellFormed {t : Tree α} (encoded : Encoded t) : WellFormed t := by
  induction encoded with
  | nil => exact .nil
  | tip => exact .tip
  | @bin l r mask pref _ _ single left right il ir =>
    apply WellFormed.bin il ir
    · intro k h
      obtain ⟨member, branch⟩ := left k h
      have pivot := int_pivot single member
      simp only [branch, true_iff] at pivot
      exact ⟨branch, pivot⟩
    · intro k h
      obtain ⟨member, branch⟩ := right k h
      refine ⟨branch, ?_⟩
      have pivot := int_pivot single member
      simp only [branch, Bool.false_eq_true, false_iff] at pivot
      cases sign : mask.msb <;> simpa [Branch.ofMask, sign] using pivot

def filter (p : Int → α → Bool) : Tree α → Tree α
  | .nil => .nil
  | .tip k x => if p k x then .tip k x else .nil
  | .bin b l r => bin b (filter p l) (filter p r)

theorem lookup_filter (p : Int → α → Bool) {t : Tree α} (valid : WellFormed t) :
    ∀ k, lookup k (filter p t) = (lookup k t).filter (p k) := by
  induction valid with
  | nil => intro k; rfl
  | @tip key val =>
    intro k
    by_cases same : k = key
    · subst k; cases h : p key val <;> simp [filter, lookup, Option.filter, h]
    · cases h : p key val <;> simp [filter, lookup, h, same]
  | @bin l r b _ _ left right il ir =>
    intro k
    rw [filter, lookup_bin]
    · cases side : b.left k <;> simp [lookup, side, il, ir]
    · intro x found
      exact (left x (by intro missing; simp [il, missing] at found)).1
    · intro x found
      exact (right x (by intro missing; simp [ir, missing] at found)).1

def trim (take : Bool) (cut : Int) : Tree α → Tree α
  | .nil => .nil
  | .tip k x => if decide (k < cut) == take then .tip k x else .nil
  | .bin b l r =>
    if b.sign then
      if b.pivot < cut then
        if take then bin b (trim take cut l) r else trim take cut l
      else
        if take then trim take cut r else bin b l (trim take cut r)
    else
      if b.pivot < cut then
        if take then bin b l (trim take cut r) else trim take cut r
      else
        if take then trim take cut l else bin b (trim take cut l) r

theorem lookup_trim (take : Bool) (cut : Int) {t : Tree α} (valid : WellFormed t) :
    ∀ k, lookup k (trim take cut t) =
      if decide (k < cut) == take then lookup k t else none := by
  induction valid with
  | nil => intro k; simp [trim, lookup]
  | @tip key val =>
    intro k
    by_cases same : k = key
    · subst k; split <;> simp_all [trim, lookup]
    · by_cases keep : decide (key < cut) == take <;> simp [trim, lookup, keep, same]
  | @bin l r b _ _ left right il ir =>
    intro k
    have rl : Supported l (fun x => b.left x = true) := fun x h => (left x h).1
    have rr : Supported r (fun x => b.left x = false) := fun x h => (right x h).1
    have tl : Supported (trim take cut l) (fun x => b.left x = true) :=
      fun x h => rl x (by intro missing; simp [il, missing] at h)
    have tr : Supported (trim take cut r) (fun x => b.left x = false) :=
      fun x h => rr x (by intro missing; simp [ir, missing] at h)
    have al (found : lookup k l ≠ none) := left k found
    have ar (found : lookup k r ≠ none) := right k found
    have bl := lookup_bin b (trim take cut l) r k tl rr
    have br := lookup_bin b l (trim take cut r) k rl tr
    cases sign : b.sign <;> by_cases pivot : b.pivot < cut <;>
      cases side : b.left k <;> by_cases bound : k < cut <;> cases take <;>
      simp_all only [trim, lookup, Bool.false_eq_true, Bool.true_eq_false,
        ↓reduceIte, beq_iff_eq, decide_true, decide_false, true_and, false_and, iff_true, iff_false] <;>
      by_cases h : k < b.pivot <;> simp_all <;> omega

theorem trim_preserves (take : Bool) (cut : Int) {t : Tree α} (valid : WellFormed t) :
    WellFormed (trim take cut t) := by
  have subset {u : Tree α} {p : Int → Prop} (wf : WellFormed u) (support : Supported u p) :
      Supported (trim take cut u) p :=
    fun k h => support k (by intro missing; simp [lookup_trim take cut wf, missing] at h)
  have well_bin {b : Branch} {l r : Tree α} (wl : WellFormed l) (wr : WellFormed r)
      (left : Supported l (fun k => b.left k = true ∧ (k < b.pivot ↔ b.sign = false)))
      (right : Supported r (fun k => b.left k = false ∧ (k < b.pivot ↔ b.sign = true))) :
      WellFormed (bin b l r) := by
    cases l <;> cases r <;> first | exact wl | exact wr | exact .bin wl wr left right
  induction valid with
  | nil => exact .nil
  | tip => unfold trim; split; exact .tip; exact .nil
  | @bin l r b wl wr left right il ir =>
    have bl := well_bin (b := b) il wr (subset wl left) right
    have br := well_bin (b := b) wl ir left (subset wr right)
    cases sign : b.sign <;> by_cases pivot : b.pivot < cut <;> cases take <;>
      simp only [trim, sign, pivot, Bool.false_eq_true, ↓reduceIte] <;> assumption

def Routes (b : Branch) (l r : Tree α) : Prop :=
  Supported l (fun k => b.left k = true) ∧ Supported r (fun k => b.left k = false)

inductive Link : Tree α → Tree α → Tree α → Prop where
  | left : Routes b l r → Link l r (.bin b l r)
  | right : Routes b r l → Link l r (.bin b r l)

theorem Link.lookup_or {l r t : Tree α} (linked : Link l r t) (k : Int) :
    lookup k t = (lookup k l).or (lookup k r) := by
  cases linked with
  | @left b l r route =>
    cases side : b.left k
    · rw [show lookup k l = none from absent route.1 (by simp [side])]
      simp [lookup, side]
    · rw [show lookup k r = none from absent route.2 (by simp [side])]
      simp [lookup, side]
  | @right b r l route =>
    cases side : b.left k
    · rw [show lookup k r = none from absent route.1 (by simp [side])]
      simp [lookup, side]
    · rw [show lookup k l = none from absent route.2 (by simp [side])]
      simp [lookup, side]

theorem Link.disjoint {l r t : Tree α} (joined : Link l r t) (k : Int) :
    lookup k l = none ∨ lookup k r = none := by
  cases joined with
  | @left b _ _ routed =>
    cases side : b.left k
    · exact .inl (absent routed.1 (by simp [side]))
    · exact .inr (absent routed.2 (by simp [side]))
  | @right b _ _ routed =>
    cases side : b.left k
    · exact .inr (absent routed.1 (by simp [side]))
    · exact .inl (absent routed.2 (by simp [side]))

inductive Merge : Tree α → Tree α → Tree α → Prop where
  | nilLeft : Merge .nil r r
  | nilRight : Merge l .nil l
  | sameTip : Merge (.tip key x) (.tip key y) (.tip key x)
  | link : Link l r t → Merge l r t
  | branches : Routes b l₁ r₁ → Routes b l₂ r₂ →
      Merge l₁ l₂ l → Merge r₁ r₂ r →
      Merge (bin b l₁ r₁) (bin b l₂ r₂) (.bin b l r)

theorem lookup_merge {l r t : Tree α} (merged : Merge l r t) (k : Int) :
    lookup k t = (lookup k l).or (lookup k r) := by
  induction merged with
  | nilLeft => rfl
  | nilRight => simp [lookup]
  | @sameTip key _ _ => by_cases same : k = key <;> simp [lookup, same]
  | link joined => exact joined.lookup_or k
  | @branches b l₁ r₁ l₂ r₂ l r first second _ _ il ir =>
    rw [lookup_bin _ _ _ _ first.1 first.2, lookup_bin _ _ _ _ second.1 second.2]
    cases side : b.left k <;> simp [lookup, side, il, ir]

private def ascending : Tree α → List (Int × α)
  | .nil => []
  | .tip key x => [(key, x)]
  | .bin _ l r => ascending l ++ ascending r

def entries : Tree α → List (Int × α)
  | .bin b l r => if b.sign then ascending r ++ ascending l else ascending l ++ ascending r
  | t => ascending t

private theorem lookup_append (k : Int) (xs ys : List (Int × α)) :
    (xs ++ ys).lookup k = (xs.lookup k).or (ys.lookup k) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, List.lookup_cons, List.lookup_cons]
    split <;> simp [ih]

private theorem ascending_lookup {t : Tree α} (valid : WellFormed t) (k : Int) :
    (ascending t).lookup k = lookup k t := by
  induction valid with
  | nil => rfl
  | @tip key val => by_cases same : k = key <;> simp [ascending, lookup, same, List.lookup_cons, beq_eq_false_iff_ne.mpr]
  | @bin l r b _ _ left right il ir =>
    rw [ascending, lookup_append, il, ir]
    cases side : b.left k
    · rw [show lookup k l = none from absent (fun x h => (left x h).1) (by simp [side])]
      simp [lookup, side]
    · rw [show lookup k r = none from absent (fun x h => (right x h).1) (by simp [side])]
      simp [lookup, side]

theorem entries_lookup {t : Tree α} (valid : WellFormed t) (k : Int) :
    (entries t).lookup k = lookup k t := by
  cases valid with
  | nil => rfl
  | @tip key val => by_cases same : k = key <;> simp [entries, ascending, lookup, same, List.lookup_cons, beq_eq_false_iff_ne.mpr]
  | @bin l r b wl wr left right =>
    simp only [entries]
    split
    · rw [lookup_append, ascending_lookup wr, ascending_lookup wl]
      cases side : b.left k
      · rw [show lookup k l = none from absent (fun x h => (left x h).1) (by simp [side])]
        simp [lookup, side]
      · rw [show lookup k r = none from absent (fun x h => (right x h).1) (by simp [side])]
        simp [lookup, side]
    · rw [lookup_append, ascending_lookup wl, ascending_lookup wr]
      cases side : b.left k
      · rw [show lookup k l = none from absent (fun x h => (left x h).1) (by simp [side])]
        simp [lookup, side]
      · rw [show lookup k r = none from absent (fun x h => (right x h).1) (by simp [side])]
        simp [lookup, side]

inductive UnsignedBranches : Tree α → Prop where
  | nil : UnsignedBranches .nil
  | tip : UnsignedBranches (.tip k x)
  | bin {b l r} : b.sign = false → UnsignedBranches l → UnsignedBranches r → UnsignedBranches (.bin b l r)

def trimWorker (take : Bool) (cut : Int) : Tree α → Tree α
  | .nil => .nil
  | .tip k x => if decide (k < cut) == take then .tip k x else .nil
  | .bin b l r =>
    if b.pivot < cut then
      if take then bin b l (trimWorker take cut r) else trimWorker take cut r
    else
      if take then trimWorker take cut l else bin b (trimWorker take cut l) r

def trimRoot (take : Bool) (cut : Int) : Tree α → Tree α
  | t@(.bin b l r) =>
    if b.sign then
      if 0 < cut then
        if take then bin b (trimWorker take cut l) r else trimWorker take cut l
      else
        if take then trimWorker take cut r else bin b l (trimWorker take cut r)
    else trimWorker take cut t
  | t => trimWorker take cut t

private theorem trim_worker_eq (take : Bool) (cut : Int) {t : Tree α}
    (noSign : UnsignedBranches t) : trimWorker take cut t = trim take cut t := by
  induction noSign with
  | nil => rfl
  | tip => rfl
  | bin sign _ _ il ir => simp [trimWorker, trim, sign, il, ir]

theorem trim_root_eq (take : Bool) (cut : Int) (t : Tree α)
    (root : ∀ b l r, t = .bin b l r → UnsignedBranches l ∧ UnsignedBranches r ∧
      (b.sign = true → b.pivot = 0)) : trimRoot take cut t = trim take cut t := by
  cases t with
  | nil => rfl
  | tip => rfl
  | bin b l r =>
    obtain ⟨left, right, pivot⟩ := root b l r rfl
    cases sign : b.sign
    · simp [trimRoot, sign, trim_worker_eq take cut (.bin sign left right)]
    · simp [trimRoot, trim, sign, pivot sign, trim_worker_eq take cut left, trim_worker_eq take cut right]

theorem lookup_trim_root (take : Bool) (cut : Int) {t : Tree α} (valid : WellFormed t)
    (root : ∀ b l r, t = .bin b l r → UnsignedBranches l ∧ UnsignedBranches r ∧
      (b.sign = true → b.pivot = 0)) (k : Int) :
    lookup k (trimRoot take cut t) = if decide (k < cut) == take then lookup k t else none := by
  rw [trim_root_eq take cut t root, lookup_trim take cut valid]


private theorem ascending_present {t : Tree α} (valid : WellFormed t) {entry : Int × α}
    (inList : entry ∈ ascending t) : lookup entry.1 t ≠ none := by
  intro missing
  rw [← ascending_lookup valid, List.lookup_eq_none_iff] at missing
  simpa using missing entry inList

private theorem separated_ascending {l r : Tree α} (wl : WellFormed l) (wr : WellFormed r)
    (pivot : Int) (left : Supported l (· < pivot)) (right : Supported r (pivot ≤ ·))
    (ascendingLeft : (ascending l).Pairwise (fun a b => a.1 < b.1))
    (ascendingRight : (ascending r).Pairwise (fun a b => a.1 < b.1)) :
    (ascending l ++ ascending r).Pairwise (fun a b => a.1 < b.1) :=
  List.pairwise_append.mpr ⟨ascendingLeft, ascendingRight, fun a ha b hb =>
    Int.lt_of_lt_of_le (left a.1 (ascending_present wl ha)) (right b.1 (ascending_present wr hb))⟩

private theorem ascending_sorted {t : Tree α} (noSign : UnsignedBranches t) (valid : WellFormed t) :
    (ascending t).Pairwise (fun a b => a.1 < b.1) := by
  induction noSign with
  | nil => simp [ascending]
  | tip => simp [ascending]
  | @bin b l r sign _ _ il ir =>
    cases valid with
    | bin wl wr left right =>
      exact separated_ascending wl wr b.pivot
        (fun k h => (left k h).2.mpr sign)
        (fun k h => Int.le_of_not_gt (fun low => by have wrong := (right k h).2.mp low; simp [sign] at wrong))
        (il wl) (ir wr)

theorem entries_sorted {t : Tree α} (valid : WellFormed t)
    (noSignBelowRoot : ∀ b l r, t = .bin b l r → UnsignedBranches l ∧ UnsignedBranches r) :
    (entries t).Pairwise (fun a b => a.1 < b.1) := by
  cases valid with
  | nil => simp [entries, ascending]
  | tip => simp [entries, ascending]
  | @bin l r b wl wr left right =>
    obtain ⟨leftNoSign, rightNoSign⟩ := noSignBelowRoot b l r rfl
    simp only [entries]
    split
    · rename_i sign
      exact separated_ascending wr wl b.pivot
        (fun k h => (right k h).2.mpr sign)
        (fun k h => Int.le_of_not_gt (fun low => by have wrong := (left k h).2.mp low; simp [sign] at wrong))
        (ascending_sorted rightNoSign wr) (ascending_sorted leftNoSign wl)
    · rename_i notSign
      have sign := Bool.eq_false_iff.mpr notSign
      exact separated_ascending wl wr b.pivot
        (fun k h => (left k h).2.mpr sign)
        (fun k h => Int.le_of_not_gt (fun low => by have wrong := (right k h).2.mp low; simp [sign] at wrong))
        (ascending_sorted leftNoSign wl) (ascending_sorted rightNoSign wr)

theorem shifted_entries_sorted (delta : Int) {t : Tree α} (valid : WellFormed t)
    (noSignBelowRoot : ∀ b l r, t = .bin b l r → UnsignedBranches l ∧ UnsignedBranches r) :
    ((entries t).map (fun (k,x) => (k + delta,x))).Pairwise (fun a b => a.1 < b.1) :=
  (entries_sorted valid noSignBelowRoot).map _ (fun a b h => by dsimp; omega)


private def highest_mask (x : Word) : Word := 1#64 <<< (63 - x.clz.toNat)

private theorem highest_nat (x : Word) :
    (highest_mask x).toNat = 2 ^ (63 - x.clz.toNat) := by
  have step : 63 - x.clz.toNat < 64 := by omega
  rw [highest_mask, BitVec.toNat_shiftLeft]
  change (1 <<< (63 - x.clz.toNat)) % (2^64) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) step)]

private theorem highest_pair (a b : Word) (different : a ≠ b) :
    let m := highest_mask (a ^^^ b)
    SingleBit m ∧ maskPrefix a m = maskPrefix b m ∧ (a &&& m = 0 ↔ b &&& m ≠ 0) := by
  dsimp only
  generalize ax : a ^^^ b = x
  have hx : x ≠ 0 := by
    intro h
    apply different
    bv_decide
  generalize maskEq : highest_mask x = m
  have natM : m.toNat = 2 ^ (63 - x.clz.toNat) := maskEq ▸ highest_nat x
  have posM : 0 < m.toNat := by rw [natM]; exact Nat.two_pow_pos _
  have signed : SingleBit m := by
    constructor
    · intro eq
      simp [eq] at posM
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_and]
      have pred : (m - 1).toNat = m.toNat - 1 := BitVec.toNat_sub_of_le (by exact posM)
      rw [pred, natM, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
      rfl
  have dx : x.clz.toNat < 64 := by
    have le : x.clz < (64#64) := BitVec.clz_lt_iff_ne_zero.mpr hx
    exact le
  have low : m.toNat ≤ x.toNat := by
    rw [natM]
    exact BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by decide) hx
  have high : x.toNat < 2 * m.toNat := by
    rw [natM, show 2 * 2 ^ (63 - x.clz.toNat) = 2 ^ (64 - x.clz.toNat) by
      rw [show 64 - x.clz.toNat = (63 - x.clz.toNat) + 1 by omega, Nat.pow_succ, Nat.mul_comm]]
    exact BitVec.toNat_lt_two_pow_sub_clz
  have lt : m.ule x = true := by simpa [BitVec.ule] using low
  have ht : m.msb = true ∨ x.ult (m + m) = true := by
    by_cases sign : m.msb
    · exact Or.inl sign
    · right
      have doubleFits := BitVec.toNat_lt_of_msb_false (Bool.eq_false_iff.mpr sign)
      have bv : (m + m).toNat = 2 * m.toNat := by
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
        omega
      have inRange : x.toNat < (m + m).toNat := by omega
      simpa [BitVec.ult] using inRange
  obtain ⟨mnonzero, mbit⟩ := signed
  constructor
  · exact ⟨mnonzero, mbit⟩
  · clear maskEq natM posM dx low high
    unfold maskPrefix
    bv_decide

def branchingMask (first second : Int) : BitVec 64 :=
  highest_mask (BitVec.ofInt 64 first ^^^ BitVec.ofInt 64 second)

theorem branching_mask (first second : Int) (firstFits : FitsKey first) (secondFits : FitsKey second)
    (different : first ≠ second) :
    let m := branchingMask first second
    let x := BitVec.ofInt 64 first
    let y := BitVec.ofInt 64 second
    SingleBit m ∧ maskPrefix x m = maskPrefix y m ∧ (x &&& m = 0 ↔ y &&& m ≠ 0) := by
  apply highest_pair
  intro equal
  have firstKey : (BitVec.ofInt 64 first).toInt = first :=
    BitVec.toInt_ofInt_eq_self (by decide) (by exact firstFits.1) (by have := firstFits.2; omega)
  have secondKey : (BitVec.ofInt 64 second).toInt = second :=
    BitVec.toInt_ofInt_eq_self (by decide) (by exact secondFits.1) (by have := secondFits.2; omega)
  exact different (firstKey.symm.trans ((congrArg BitVec.toInt equal).trans secondKey))

def sameRegion (bound : BitVec 64) (first second : Int) : Prop :=
  maskPrefix (BitVec.ofInt 64 first) bound = maskPrefix (BitVec.ofInt 64 second) bound

def splice (mask : BitVec 64) (rep : Int) (l r : Tree α) : Tree α :=
  let b := Branch.ofMask (maskPrefix (BitVec.ofInt 64 rep) mask) mask
  if b.left rep then .bin b l r else .bin b r l

def SpliceRoutes (mask : BitVec 64) (rep : Int) (l r : Tree α) : Prop :=
  let b := Branch.ofMask (maskPrefix (BitVec.ofInt 64 rep) mask) mask
  if b.left rep then Routes b l r else Routes b r l

theorem splice_joins {l r : Tree α} {mask : BitVec 64} {rep : Int}
    (routed : SpliceRoutes mask rep l r) : Link l r (splice mask rep l r) := by
  unfold SpliceRoutes at routed
  unfold splice
  dsimp only at routed ⊢
  split
  · rename_i h
    exact .left (by simpa only [h, ↓reduceIte] using routed)
  · rename_i h
    exact .right (by simpa only [h, ↓reduceIte] using routed)

inductive BelowMask (parent : BitVec 64) (rep : Int) : Tree α → Prop where
  | tip : FitsKey rep → BelowMask parent rep (.tip rep x)
  | subtree : SingleBit mask → mask.ult parent →
      Supported t (InPrefix (maskPrefix (BitVec.ofInt 64 rep) mask) mask) → BelowMask parent rep t

theorem below_mask_routes {t : Tree α} {rep : Int} {pref parent : BitVec 64}
    (side : BelowMask parent rep t) (parentBit : SingleBit parent) :
    Supported t (fun k => (Branch.ofMask pref parent).left k = (Branch.ofMask pref parent).left rep) := by
  cases side with
  | tip _ =>
    intro k found
    by_cases same : k = rep
    · simp [same]
    · simp [lookup, same] at found
  | subtree single shorter region =>
    intro k found
    obtain ⟨_, matching⟩ := region k found
    have routed := nested_bits _ _ _ _ single parentBit shorter matching
    have representative := nested_bits (BitVec.ofInt 64 rep) _ _ _ single parentBit shorter rfl
    exact congrArg (· == 0) (routed.2.trans representative.2.symm)

theorem branching_splice {l r : Tree α} {first second : Int}
    (firstFits : FitsKey first) (secondFits : FitsKey second) (different : first ≠ second)
    (left : BelowMask (branchingMask first second) second l)
    (right : BelowMask (branchingMask first second) first r) :
    SpliceRoutes (branchingMask first second) second l r := by
  obtain ⟨single, _, opposite⟩ := branching_mask first second firstFits secondFits different
  let mask := branchingMask first second
  let p := maskPrefix (BitVec.ofInt 64 second) mask
  let b := Branch.ofMask p mask
  have a : Supported l (fun k => b.left k = b.left second) :=
    below_mask_routes (pref := p) left single
  have c : Supported r (fun k => b.left k = b.left first) :=
    below_mask_routes (pref := p) right single
  have sides : b.left first = !b.left second := by
    change (BitVec.ofInt 64 first &&& mask == 0) = !(BitVec.ofInt 64 second &&& mask == 0)
    by_cases secondZero : BitVec.ofInt 64 second &&& mask = 0
    · have firstNotZero : BitVec.ofInt 64 first &&& mask ≠ 0 :=
        fun h => (opposite.mp h) secondZero
      rw [beq_eq_false_iff_ne.mpr firstNotZero, beq_iff_eq.mpr secondZero]
      rfl
    · have firstZero : BitVec.ofInt 64 first &&& mask = 0 := opposite.mpr secondZero
      rw [beq_iff_eq.mpr firstZero, beq_eq_false_iff_ne.mpr secondZero]
      rfl
  change if b.left second then Routes b l r else Routes b r l
  cases test : b.left second
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨fun k h => by simpa [sides, test] using c k h, fun k h => by simpa [test] using a k h⟩
  · simp only [↓reduceIte]
    exact ⟨fun k h => by simpa [test] using a k h, fun k h => by simpa [sides, test] using c k h⟩

inductive AscendingBuilder : Option (BitVec 64) → Int → Tree α → List (Int × α) →
    Tree α → List (Int × α) → Prop where
  | done : AscendingBuilder bound rep acc [] acc []
  | stop : ¬ sameRegion bound rep key →
      AscendingBuilder (some bound) rep acc ((key, x) :: rest) acc ((key, x) :: rest)
  | advance {bound rep key acc x rest part pending output tail} :
      (∀ scope, bound = some scope → sameRegion scope rep key) →
      AscendingBuilder (some (branchingMask rep key)) key (.tip key x) rest part pending →
      FitsKey rep → FitsKey key → rep ≠ key →
      BelowMask (branchingMask rep key) key part → BelowMask (branchingMask rep key) rep acc →
      AscendingBuilder bound rep (splice (branchingMask rep key) key part acc) pending output tail →
      AscendingBuilder bound rep acc ((key, x) :: rest) output tail

theorem ascending_builder_lookup {bound : Option (BitVec 64)} {rep : Int}
    {acc output : Tree α} {pending tail : List (Int × α)}
    (built : AscendingBuilder bound rep acc pending output tail) :
    ∃ consumed, pending = consumed ++ tail ∧ ∀ k,
      lookup k output = (lookup k acc).or (consumed.lookup k) := by
  induction built with
  | done => exact ⟨[], rfl, fun k => by simp⟩
  | stop => exact ⟨[], rfl, fun k => by simp⟩
  | @advance bound rep key acc x rest part pending output tail _ _ repFits keyFits distinct partBelow accBelow _ ihPart ihRest =>
    obtain ⟨first, eqFirst, firstLookup⟩ := ihPart
    obtain ⟨second, eqSecond, secondLookup⟩ := ihRest
    refine ⟨(key, x) :: (first ++ second), by simp only [eqFirst, eqSecond, List.cons_append, List.append_assoc], ?_⟩
    intro k
    have joined := splice_joins (branching_splice repFits keyFits distinct partBelow accBelow)
    have linked := joined.lookup_or k
    rw [secondLookup, linked, firstLookup, List.lookup_cons, lookup_append]
    have disjoint := joined.disjoint k
    rw [firstLookup] at disjoint
    by_cases same : k = key
    · subst key
      simp [lookup] at disjoint ⊢
      simp [disjoint]
    · simp [lookup, same, beq_eq_false_iff_ne.mpr same]
      cases found : lookup k acc <;> cases firstFound : first.lookup k <;>
        simp_all

inductive DistinctAscending : List (Int × α) → Tree α → Prop where
  | empty : DistinctAscending [] .nil
  | start : AscendingBuilder none first (.tip first value) rest output [] →
      DistinctAscending ((first, value) :: rest) output

theorem lookup_distinctAscending {xs : List (Int × α)} {t : Tree α}
    (built : DistinctAscending xs t) (k : Int) :
    lookup k t = xs.lookup k := by
  cases built with
  | empty => rfl
  | @start first value rest output run =>
    obtain ⟨consumed, eq, observed⟩ := ascending_builder_lookup run
    simp only [List.append_nil] at eq
    subst rest
    rw [observed, List.lookup_cons]
    by_cases same : k = first <;> simp [lookup, same, beq_eq_false_iff_ne.mpr]

private theorem lookup_rekey (f : Int → Int) (injective : Function.Injective f)
    (xs : List (Int × α)) (key : Int) :
    (xs.map (fun (k, x) => (f k, x))).lookup (f key) = xs.lookup key := by
  induction xs with
  | nil => rfl
  | cons entry xs ih =>
    obtain ⟨k, x⟩ := entry
    by_cases same : key = k
    · subst k; simp
    · have diff : f key ≠ f k := fun eq => same (injective eq)
      simp [List.lookup_cons, beq_eq_false_iff_ne.mpr diff, beq_eq_false_iff_ne.mpr same, ih]

private theorem lookup_shift (xs : List (Int × α)) (delta k : Int) :
    (xs.map (fun (key, x) => (key + delta, x))).lookup k = xs.lookup (k - delta) := by
  have shifted : k - delta + delta = k := by omega
  conv => lhs; rw [← shifted]
  exact lookup_rekey (· + delta) (fun a b h => by change a + delta = b + delta at h; omega) xs (k - delta)

def Shift (delta : Int) (t u : Tree α) : Prop :=
  DistinctAscending ((entries t).map (fun (k, x) => (k + delta, x))) u

theorem lookup_mapKeysMonotonic (valid : WellFormed (t : Tree α))
    (shifted : Shift delta t u) (k : Int) : lookup k u = lookup (k - delta) t := by
  rw [lookup_distinctAscending shifted, lookup_shift, entries_lookup valid]

def window (s width : Int) (t : Tree α) : Tree α :=
  trim true (s + width) (trim false s t)

theorem lookup_window (s width : Int) {t : Tree α} (valid : WellFormed t) (k : Int) :
    lookup k (window s width t) = if s ≤ k ∧ k < s + width then lookup k t else none := by
  rw [window, lookup_trim true _ (trim_preserves false _ valid), lookup_trim false _ valid]
  by_cases low : k < s <;> by_cases high : k < s + width <;> simp [low, high, Int.not_lt.mp, Int.not_le.mpr]

structure Transfer (s d width : Int) (t result : Tree α) : Prop where
  relative : ∃ relative : Tree α, Shift (-s) (window s width t) relative ∧
    WellFormed relative ∧ Shift d relative result

theorem lookup_transfer (valid : WellFormed (t : Tree α))
    (moved : Transfer s d width t u) (k : Int) :
    lookup k u = if d ≤ k ∧ k < d + width then lookup (s + (k - d)) t else none := by
  obtain ⟨relative, first, validRelative, second⟩ := moved.relative
  rw [lookup_mapKeysMonotonic validRelative second,
    lookup_mapKeysMonotonic (trim_preserves true _ (trim_preserves false _ valid)) first]
  change lookup (k - d - -s) (window s width t) = _
  rw [lookup_window _ _ valid]
  have index : k - d - -s = s + (k - d) := by omega
  have range : (s ≤ k - d - -s ∧ k - d - -s < s + width) ↔ (d ≤ k ∧ k < d + width) := by omega
  by_cases inside : d ≤ k ∧ k < d + width
  · rw [if_pos (range.mpr inside), if_pos inside, index]
  · rw [if_neg (fun h => inside (range.mp h)), if_neg inside]

theorem copy_payload {source destination moved untouched result : Tree Int}
    (s d : Int) (count : Nat)
    (src : WellFormed source) (dst : WellFormed destination)
    (transferred : Transfer s d (count : Int) source moved)
    (retained : Merge (trim true d destination) (trim false (d + count) destination) untouched)
    (combined : Merge moved untouched result) (k : Int) :
    lookup k result = intmap_payload_copy (fun j => lookup j source) (fun j => lookup j destination) s d count k := by
  rw [lookup_merge combined, lookup_transfer src transferred, lookup_merge retained,
    lookup_trim true d dst, lookup_trim false (d + count) dst]
  unfold intmap_payload_copy
  by_cases low : k < d
  · have outside : ¬ d ≤ k := by omega
    have beforeEnd : ¬ d + (count : Int) ≤ k := by omega
    simp [low, outside, beforeEnd]
  · have after : d ≤ k := by omega
    by_cases high : k < d + (count : Int)
    · have outside : ¬ d + (count : Int) ≤ k := by omega
      simp [low, high, after, outside]
    · have beyond : d + (count : Int) ≤ k := by omega
      simp [low, high, beyond]

theorem copy_shadow {source destination moved result : Tree α}
    (s d : Int) (count : Nat) (nonzero : count ≠ 0)
    (src : WellFormed source) (dst : WellFormed destination)
    (transferred : if s % 8 = d % 8 then
      Transfer s d (max 0 ((count : Int) - 7)) source moved else moved = .nil)
    (combined : Merge moved (filter (fun slot _ => decide (slot ≤ d - 8 ∨ d + count ≤ slot)) destination) result)
    (k : Int) :
    lookup k result =
      capability_shadow_copy (fun j => lookup j source) (fun j => lookup j destination) s d count k := by
  rw [← shadow_copy_refines _ _ _ _ _ _ (by omega), lookup_merge combined, lookup_filter _ dst]
  have nonzeroInt : (count : Int) ≠ 0 := by omega
  have preserved :
      (lookup k destination).filter (fun _ => decide (k ≤ d - 8 ∨ d + count ≤ k)) =
        if k ≤ d - 8 ∨ d + count ≤ k then lookup k destination else none := by
    cases found : lookup k destination <;>
      by_cases outside : k ≤ d - 8 ∨ d + count ≤ k <;> simp [Option.filter, outside]
  rw [preserved]
  unfold intmap_shadow_copy
  rw [if_neg nonzeroInt]
  by_cases aligned : s % 8 = d % 8
  · rw [if_pos aligned] at transferred
    rw [lookup_transfer src transferred]
    simp only [aligned, and_true]
  · rw [if_neg aligned] at transferred
    subst moved
    simp [lookup, aligned]

theorem copy_payload_refines {source destination moved untouched result : Tree Int}
    (s d : Int) (count : Nat)
    (src : WellFormed source) (dst : WellFormed destination)
    (transferred : Transfer s d (count : Int) source moved)
    (retained : Merge (trim true d destination) (trim false (d + count) destination) untouched)
    (combined : Merge moved untouched result) (k : Int) :
    lookup k result = if d ≤ k ∧ k < d + count then lookup (s + (k - d)) source
      else lookup k destination := by
  rw [copy_payload s d count src dst transferred retained combined, payload_copy_refines]

theorem checked_copy_ranges (memory : Memory) (source destination : Pointer)
    (s d count : Nat) (hostMax : Int) (src dst : Object)
    (offsets : runtime_copy_offsets memory source destination count = .ok (some (s, d)))
    (sourceCell : memory source.capability = some src)
    (destinationCell : memory destination.capability = some dst)
    (sourceFits : (src.size : Int) ≤ hostMax) (destinationFits : (dst.size : Int) ≤ hostMax) :
    (s : Int) + count ≤ hostMax ∧ (d : Int) + count ≤ hostMax := by
  obtain ⟨src', dst', read, write, sourceAccess, destinationAccess, _, sourceOffset, destinationOffset⟩ :=
    copy_offsets_sound memory source destination count s d offsets
  have srcEq := Option.some.inj (read.symm.trans sourceCell)
  have dstEq := Option.some.inj (write.symm.trans destinationCell)
  subst src'
  subst dst'
  unfold accessible at sourceAccess destinationAccess
  have sourceNonnegative : 0 ≤ source.address - src.base := by omega
  have destinationNonnegative : 0 ≤ destination.address - dst.base := by omega
  constructor
  · rw [sourceOffset, Int.toNat_of_nonneg sourceNonnegative]
    omega
  · rw [destinationOffset, Int.toNat_of_nonneg destinationNonnegative]
    omega

theorem copy_key_arithmetic (s d count : Nat) (hostMax k : Int)
    (sourceFits : (s : Int) + count ≤ hostMax) (destinationFits : (d : Int) + count ≤ hostMax)
    (inside : (s : Int) ≤ k ∧ k < s + count) :
    (s : Int) + max 0 ((count : Int) - 7) ≤ hostMax ∧
    -8 ≤ (d : Int) - 8 ∧ (d : Int) - 8 ≤ hostMax ∧
    0 ≤ k - s ∧ k - s ≤ hostMax ∧ 0 ≤ k - s + d ∧ k - s + d ≤ hostMax := by
  constructor
  · by_cases long : (7 : Int) ≤ count
    · rw [Int.max_eq_right (by omega)]
      omega
    · rw [Int.max_eq_left (by omega)]
      omega
  · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

end Heresy.Patricia

#print axioms Heresy.Patricia.lookup_filter
#print axioms Heresy.Patricia.lookup_trim
#print axioms Heresy.Patricia.lookup_merge
#print axioms Heresy.Patricia.lookup_mapKeysMonotonic
#print axioms Heresy.Patricia.copy_payload
#print axioms Heresy.Patricia.copy_shadow
#print axioms Heresy.Patricia.copy_payload_refines
#print axioms Heresy.Patricia.checked_copy_ranges
#print axioms Heresy.Patricia.encoded_wellFormed
#print axioms Heresy.Patricia.branching_splice
#print axioms Heresy.Patricia.lookup_trim_root
#print axioms Heresy.Patricia.shifted_entries_sorted
