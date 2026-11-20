import Patricia

set_option warningAsError true

namespace Heresy.Patricia

private abbrev Mask := BitVec 64

def Branch.forKey (key : Int) (mask : Mask) : Branch :=
  Branch.ofMask (maskPrefix (BitVec.ofInt 64 key) mask) mask

def SameSide (mask : Mask) (first second : Int) : Prop :=
  sameRegion mask first second ∧ (Branch.forKey first mask).left first = (Branch.forKey first mask).left second

private theorem opposite_sides {a b : Int} (fa : FitsKey a) (fb : FitsKey b) (ne : a ≠ b) :
    let m := branchingMask a b
    (Branch.forKey a m).left a ≠ (Branch.forKey a m).left b := by
  obtain ⟨_, _, different⟩ := branching_mask a b fa fb ne
  dsimp only
  intro same
  change (BitVec.ofInt 64 a &&& branchingMask a b == 0) =
    (BitVec.ofInt 64 b &&& branchingMask a b == 0) at same
  by_cases az : BitVec.ofInt 64 a &&& branchingMask a b = 0
  · rw [beq_iff_eq.mpr az, beq_eq_false_iff_ne.mpr (different.mp az)] at same
    contradiction
  · have bz : BitVec.ofInt 64 b &&& branchingMask a b = 0 := Classical.byContradiction (fun h => az (different.mpr h))
    rw [beq_eq_false_iff_ne.mpr az, beq_iff_eq.mpr bz] at same
    contradiction

private theorem same_region_above {a b : Int} {small large : Mask}
    (sm : SingleBit small) (lg : SingleBit large) (lt : small.ult large)
    (within : sameRegion small a b) : SameSide large a b := by
  let pref := maskPrefix (BitVec.ofInt 64 b) small
  have ap := nested_bits (BitVec.ofInt 64 a) pref small large sm lg lt within
  have bp := nested_bits (BitVec.ofInt 64 b) pref small large sm lg lt rfl
  exact ⟨ap.1.trans bp.1.symm, congrArg (· == 0) (ap.2.trans bp.2.symm)⟩

private theorem branching_lt {a b : Int} (fa : FitsKey a) (fb : FitsKey b) (ne : a ≠ b)
    {bound : Mask} (single : SingleBit bound) (same : SameSide bound a b) :
    (branchingMask a b).ult bound := by
  have split := branching_mask a b fa fb ne
  have opposite := opposite_sides fa fb ne
  rcases Nat.lt_trichotomy (branchingMask a b).toNat bound.toNat with lt | eq | gt
  · exact decide_eq_true lt
  · have equal : branchingMask a b = bound := BitVec.eq_of_toNat_eq eq
    rw [equal] at opposite
    exact False.elim (opposite same.2)
  · exact False.elim (opposite (same_region_above single split.1 (decide_eq_true gt) same.1).2)

private theorem branching_gt {a b : Int} (fa : FitsKey a) (fb : FitsKey b) (ne : a ≠ b)
    {old : Mask} (single : SingleBit old) (apart : ¬ sameRegion old a b) :
    old.ult (branchingMask a b) := by
  have split := branching_mask a b fa fb ne
  rcases Nat.lt_trichotomy old.toNat (branchingMask a b).toNat with lt | eq | gt
  · exact decide_eq_true lt
  · have equal : old = branchingMask a b := BitVec.eq_of_toNat_eq eq
    exact False.elim (apart (equal ▸ split.2.1))
  · exact False.elim (apart (same_region_above split.1 single (decide_eq_true gt) split.2.1).1)

private theorem sorted_halves {a b : Int} (fa : FitsKey a) (fb : FitsKey b) (lt : a < b) :
    let branch := Branch.forKey b (branchingMask a b)
    a < branch.pivot ∧ branch.pivot ≤ b := by
  have different : a ≠ b := by omega
  obtain ⟨single, prefixEq, _⟩ := branching_mask a b fa fb different
  have ha := int_pivot (pref := maskPrefix (BitVec.ofInt 64 b) (branchingMask a b)) single ⟨fa, prefixEq⟩
  have hb := int_pivot (pref := maskPrefix (BitVec.ofInt 64 b) (branchingMask a b)) single ⟨fb, rfl⟩
  have side := opposite_sides fa fb different
  let m := branchingMask a b
  let branch := Branch.forKey b m
  change branch.left a ≠ branch.left b at side
  change (a < branch.pivot ↔ (branch.left a = true ↔ m.msb = false)) at ha
  change (b < branch.pivot ↔ (branch.left b = true ↔ m.msb = false)) at hb
  change a < branch.pivot ∧ branch.pivot ≤ b
  have distinctPivot (equiv : a < branch.pivot ↔ b < branch.pivot) : False := by
    have eq : (branch.left a = true) = (branch.left b = true) := by
      apply propext
      cases msb : m.msb <;> simp_all
    exact side (by cases sa : branch.left a <;> cases sb : branch.left b <;> simp_all)
  constructor
  · exact Classical.byContradiction (fun lower => distinctPivot (by omega))
  · exact Classical.byContradiction (fun upper => distinctPivot (by omega))

private theorem later_same_side {rep key : Int} {bound : Mask}
    (single : SingleBit bound) (fr : FitsKey rep) (fk : FitsKey key)
    (later : (Branch.forKey rep bound).pivot ≤ rep) (ordered : rep < key)
    (common : sameRegion bound rep key) : SameSide bound rep key := by
  refine ⟨common, ?_⟩
  have atRep := int_pivot (pref := maskPrefix (BitVec.ofInt 64 rep) bound) single ⟨fr, rfl⟩
  have atKey := int_pivot (pref := maskPrefix (BitVec.ofInt 64 rep) bound) single ⟨fk, common.symm⟩
  change (rep < (Branch.forKey rep bound).pivot ↔ ((Branch.forKey rep bound).left rep = true ↔ bound.msb = false)) at atRep
  change (key < (Branch.forKey rep bound).pivot ↔ ((Branch.forKey rep bound).left key = true ↔ bound.msb = false)) at atKey
  have nr : ¬ rep < (Branch.forKey rep bound).pivot := by omega
  have nk : ¬ key < (Branch.forKey rep bound).pivot := by omega
  cases r : (Branch.forKey rep bound).left rep <;> cases k : (Branch.forKey rep bound).left key <;>
    cases s : bound.msb <;> simp_all

inductive Trie (α : Type) where
  | nil
  | tip (key : Int) (value : α)
  | fork (pref mask : Mask) (left right : Trie α)

def Trie.tree : Trie α → Tree α
  | .nil => .nil
  | .tip key value => .tip key value
  | .fork pref mask l r => .bin (Branch.ofMask pref mask) l.tree r.tree

structure Header where
  key : Int
  rank : Mask

def Trie.header : Trie α → Header
  | .nil => ⟨0, 0⟩
  | .tip key _ => ⟨key, 0⟩
  | .fork pref mask _ _ => ⟨pref.toInt, mask⟩

def InHalf (pref mask : Mask) (left : Bool) (key : Int) : Prop :=
  InPrefix pref mask key ∧ (Branch.ofMask pref mask).left key = left

inductive Trie.Valid : Trie α → Prop where
  | nil : Valid .nil
  | tip : FitsKey key → Valid (.tip key value)
  | fork {pref mask l r} :
      SingleBit mask → maskPrefix pref mask = pref →
      Valid l → Valid r → l ≠ .nil → r ≠ .nil →
      l.header.rank.ult mask → r.header.rank.ult mask →
      Supported l.tree (InHalf pref mask true) → Supported r.tree (InHalf pref mask false) →
      Valid (.fork pref mask l r)

private theorem word_fits (word : Mask) : FitsKey word.toInt := by
  have lower := BitVec.le_toInt (x := word)
  have upper := BitVec.toInt_lt (x := word)
  exact ⟨by exact lower, by omega⟩

theorem Trie.Valid.header_fits {t : Trie α} (valid : t.Valid) : FitsKey t.header.key := by
  cases valid with
  | nil => change FitsKey 0; unfold FitsKey; omega
  | tip fits => exact fits
  | fork => exact word_fits _

theorem Trie.Valid.encoded {t : Trie α} (valid : t.Valid) : Encoded t.tree := by
  induction valid with
  | nil => exact .nil
  | tip fit => exact .tip fit
  | fork single _ _ _ _ _ _ _ low high il ir => exact .bin il ir single low high

private theorem present {t : Trie α} (valid : t.Valid) (nonempty : t ≠ .nil) :
    ∃ k, lookup k t.tree ≠ none := by
  induction valid with
  | nil => contradiction
  | @tip key value _ => exact ⟨key, by simp [Trie.tree, lookup]⟩
  | fork _ _ _ _ leftNe _ _ _ low _ il _ =>
    obtain ⟨k, found⟩ := il leftNe
    exact ⟨k, by simpa only [Trie.tree, lookup, (low k found).2, ↓reduceIte] using found⟩

private theorem half_rank {t : Trie α} {p m : Mask} {side : Bool}
    (valid : t.Valid) (single : SingleBit m)
    (support : Supported t.tree (InHalf p m side)) :
    t.header.rank.ult m := by
  cases valid with
  | nil => exact decide_eq_true (Nat.pos_of_ne_zero (fun h => single.1 (BitVec.eq_of_toNat_eq h)))
  | tip => exact decide_eq_true (Nat.pos_of_ne_zero (fun h => single.1 (BitVec.eq_of_toNat_eq h)))
  | @fork pref mask l r one _ wl wr lne rne _ _ low high =>
    obtain ⟨a, aFound⟩ := present wl lne
    obtain ⟨b, bFound⟩ := present wr rne
    have lo := low a aFound
    have hi := high b bFound
    have ha : lookup a (.fork pref mask l r : Trie α).tree ≠ none := by
      simpa only [Trie.tree, lookup, lo.2, ↓reduceIte] using aFound
    have hb : lookup b (.fork pref mask l r : Trie α).tree ≠ none := by
      simpa only [Trie.tree, lookup, hi.2, Bool.false_eq_true, ↓reduceIte] using bFound
    have sa := support a ha
    have sb := support b hb
    have same : SameSide m a b := ⟨sa.1.2.trans sb.1.2.symm, sa.2.trans sb.2.symm⟩
    have impossible : ¬ SameSide mask a b := by
      intro both
      have sideEq : (Branch.ofMask pref mask).left a = (Branch.ofMask pref mask).left b := both.2
      rw [lo.2, hi.2] at sideEq
      contradiction
    change mask.ult m
    rcases Nat.lt_trichotomy mask.toNat m.toNat with lt | eq | gt
    · exact decide_eq_true lt
    · exact False.elim (impossible ((BitVec.eq_of_toNat_eq eq : mask = m) ▸ same))
    · exact False.elim (impossible (same_region_above single one (decide_eq_true gt) same.1))

def Narrower (root : Option Mask) (bound : Mask) : Prop :=
  ∀ m, root = some m → m.ult bound

structure Rooted (rep : Int) (root : Option Mask) (tree : Tree α) : Prop where
  fits : FitsKey rep
  encoded : Encoded tree
  reifies : ∃ raw : Trie α, raw.Valid ∧ raw.tree = tree
  region : match root with
    | none => ∃ value, tree = .tip rep value
    | some mask => SingleBit mask ∧ ∃ l r,
        tree = .bin (Branch.forKey rep mask) l r ∧
        Supported tree (InPrefix (maskPrefix (BitVec.ofInt 64 rep) mask) mask)

theorem Rooted.tip (rep : Int) (value : α) (fits : FitsKey rep) : Rooted rep none (.tip rep value) :=
  ⟨fits, .tip fits, ⟨.tip rep value, .tip fits, rfl⟩, ⟨value, rfl⟩⟩

theorem Rooted.below {rep : Int} {root : Option Mask} {t : Tree α} {parent : Mask}
    (valid : Rooted rep root t) (narrower : Narrower root parent) : BelowMask parent rep t := by
  cases root with
  | none =>
    obtain ⟨x, rfl⟩ := valid.region
    exact .tip valid.fits
  | some m =>
    obtain ⟨single, _, _, _, supported⟩ := valid.region
    exact .subtree single (narrower m rfl) supported

private theorem below_prefix {t : Tree α} {rep : Int} {parent pref : Mask}
    (below : BelowMask parent rep t) (single : SingleBit parent)
    (matching : maskPrefix (BitVec.ofInt 64 rep) parent = pref) :
    Supported t (InPrefix pref parent) := by
  cases below with
  | tip fit =>
    intro k present
    by_cases eq : k = rep
    · subst k; exact ⟨fit, matching⟩
    · simp [lookup, eq] at present
  | subtree one narrow support =>
    intro k present
    obtain ⟨fit, matchChild⟩ := support k present
    have a := nested_bits _ _ _ _ one single narrow matchChild
    have b := nested_bits (BitVec.ofInt 64 rep) _ _ _ one single narrow rfl
    exact ⟨fit, a.1.trans (b.1.symm.trans matching)⟩

private theorem rooted_bin {rep : Int} {t u : Tree α} {m : Mask} (fits : FitsKey rep)
    (single : SingleBit m) (left : Encoded t) (right : Encoded u)
    (low : Supported t (InPrefix (maskPrefix (BitVec.ofInt 64 rep) m) m))
    (high : Supported u (InPrefix (maskPrefix (BitVec.ofInt 64 rep) m) m))
    (sides : Routes (Branch.forKey rep m) t u)
    (reifies : ∃ raw : Trie α, raw.Valid ∧ raw.tree = .bin (Branch.forKey rep m) t u) :
    Rooted rep (some m) (.bin (Branch.forKey rep m) t u) := by
  refine ⟨fits, .bin left right single (fun k h => ⟨low k h, sides.1 k h⟩)
    (fun k h => ⟨high k h, sides.2 k h⟩), reifies, single, t, u, rfl, ?_⟩
  intro k found
  unfold lookup at found
  split at found
  · exact low k found
  · exact high k found

private theorem rooted_not_nil {rep : Int} {root : Option Mask} {t : Tree α} (valid : Rooted rep root t) :
    t ≠ .nil := by
  cases root with
  | none =>
    obtain ⟨value, eq⟩ := valid.region
    rw [eq]
    intro impossible
    cases impossible
  | some mask =>
    obtain ⟨_, l, r, eq, _⟩ := valid.region
    rw [eq]
    intro impossible
    cases impossible

private theorem mask_canonical (key mask : Mask) :
    maskPrefix (maskPrefix key mask) mask = maskPrefix key mask := by
  simp only [maskPrefix, BitVec.and_assoc, BitVec.and_self]

private theorem rooted_fork_raw {rep leftRep rightRep : Int} {tr ur : Option Mask}
    {t u : Tree α} {m : Mask} (left : Rooted leftRep tr t) (right : Rooted rightRep ur u)
    (single : SingleBit m)
    (low : Supported t (InPrefix (maskPrefix (BitVec.ofInt 64 rep) m) m))
    (high : Supported u (InPrefix (maskPrefix (BitVec.ofInt 64 rep) m) m))
    (sides : Routes (Branch.forKey rep m) t u) :
    ∃ raw : Trie α, raw.Valid ∧ raw.tree = .bin (Branch.forKey rep m) t u := by
  obtain ⟨l, vl, eqL⟩ := left.reifies
  obtain ⟨r, vr, eqR⟩ := right.reifies
  have ln : l ≠ .nil := fun empty => rooted_not_nil left (eqL ▸ congrArg Trie.tree empty)
  have rn : r ≠ .nil := fun empty => rooted_not_nil right (eqR ▸ congrArg Trie.tree empty)
  let pref := maskPrefix (BitVec.ofInt 64 rep) m
  have ls : Supported l.tree (InHalf pref m true) := by
    rw [eqL]
    exact fun k found => ⟨low k found, sides.1 k found⟩
  have rs : Supported r.tree (InHalf pref m false) := by
    rw [eqR]
    exact fun k found => ⟨high k found, sides.2 k found⟩
  exact ⟨.fork pref m l r, .fork single (mask_canonical _ _) vl vr ln rn
    (half_rank vl single ls) (half_rank vr single rs) ls rs, by simp only [Trie.tree, eqL, eqR, Branch.forKey, pref]⟩

private theorem splice_rooted {a b : Int} {ra rb : Option Mask} {t u : Tree α}
    (first : Rooted a ra t) (second : Rooted b rb u) (unequal : a ≠ b)
    (old : BelowMask (branchingMask a b) a t) (new : BelowMask (branchingMask a b) b u) :
    Rooted a (some (branchingMask a b)) (splice (branchingMask a b) b u t) := by
  obtain ⟨single, same, _⟩ := branching_mask a b first.fits second.fits unequal
  have route := branching_splice first.fits second.fits unequal new old
  have low := below_prefix old single rfl
  have high := below_prefix new single same.symm
  let m := branchingMask a b
  have branchEq : Branch.forKey b m = Branch.forKey a m := by
    unfold Branch.forKey
    rw [same]
  change (if (Branch.forKey b m).left b then Routes (Branch.forKey b m) u t
    else Routes (Branch.forKey b m) t u) at route
  change Rooted a (some m) (if (Branch.forKey b m).left b then .bin (Branch.forKey b m) u t
    else .bin (Branch.forKey b m) t u)
  rw [branchEq] at route ⊢
  split
  · rename_i side
    rw [if_pos side] at route
    exact rooted_bin first.fits single second.encoded first.encoded high low route (rooted_fork_raw second first single high low route)
  · rename_i side
    rw [if_neg side] at route
    exact rooted_bin first.fits single first.encoded second.encoded low high route (rooted_fork_raw first second single low high route)

def SortedKeys (todo : List (Int × α)) : Prop :=
  todo.Pairwise (fun a b => a.1 < b.1)

def FittedKeys (todo : List (Int × α)) : Prop :=
  ∀ entry ∈ todo, FitsKey entry.1

def AfterKey (rep : Int) (todo : List (Int × α)) : Prop :=
  ∀ entry ∈ todo, rep < entry.1

def FrontOutside (rep : Int) (root : Option Mask) (todo : List (Int × α)) : Prop :=
  ∀ mask, root = some mask → ∀ entry tail, todo = entry :: tail → ¬ sameRegion mask rep entry.1

def BuilderBound (rep : Int) (root bound : Option Mask) : Prop :=
  ∀ mask, bound = some mask → SingleBit mask ∧ (Branch.forKey rep mask).pivot ≤ rep ∧ Narrower root mask

def StoppedAt (rep : Int) (bound : Option Mask) (remainder : List (Int × α)) : Prop :=
  ∀ entry tail, remainder = entry :: tail → ∃ m, bound = some m ∧ ¬ sameRegion m rep entry.1

inductive BuilderRun : Option Mask → Int → Tree α → List (Int × α) → Tree α → List (Int × α) → Prop where
  | done : BuilderRun bound rep acc [] acc []
  | stop : ¬ sameRegion bound rep key →
      BuilderRun (some bound) rep acc ((key, value) :: rest) acc ((key, value) :: rest)
  | advance {bound rep key acc value rest part pending output tail} :
      (∀ scope, bound = some scope → sameRegion scope rep key) →
      BuilderRun (some (branchingMask rep key)) key (.tip key value) rest part pending →
      BuilderRun bound rep (splice (branchingMask rep key) key part acc) pending output tail →
      BuilderRun bound rep acc ((key, value) :: rest) output tail

theorem BuilderRun.consumes {bound : Option Mask} {rep : Int} {acc output : Tree α} {input remainder}
    (execution : BuilderRun bound rep acc input output remainder) :
    ∃ prefixEntries, input = prefixEntries ++ remainder := by
  induction execution with
  | done => exact ⟨[], rfl⟩
  | stop => exact ⟨[], rfl⟩
  | @advance bound rep key acc value rest part pending output tail _ _ _ first next =>
    obtain ⟨chunk, consumed⟩ := first
    obtain ⟨finish, restEq⟩ := next
    exact ⟨(key, value) :: (chunk ++ finish), by simp only [consumed, restEq, List.cons_append, List.append_assoc]⟩

theorem BuilderRun.stopped {bound : Option Mask} {rep : Int} {acc output : Tree α} {input remainder}
    (execution : BuilderRun bound rep acc input output remainder) : StoppedAt rep bound remainder := by
  induction execution with
  | done => intro e rest eq; cases eq
  | @stop bound rep key value rest acc different =>
    intro entry tail equal
    obtain ⟨rfl, rfl⟩ := List.cons.inj equal
    exact ⟨bound, rfl, different⟩
  | advance _ _ _ _ stop => exact stop

theorem builder_run_exists (bound : Option Mask) (rep : Int) (acc : Tree α) (input : List (Int × α)) :
    ∃ output rest, BuilderRun bound rep acc input output rest := by
  induction length : input.length using Nat.strongRecOn generalizing input bound rep acc with
  | ind n ih =>
    cases input with
    | nil => exact ⟨acc, [], .done⟩
    | cons head rest =>
      obtain ⟨key, value⟩ := head
      by_cases allowed : ∀ scope, bound = some scope → sameRegion scope rep key
      · have short : rest.length < n := by simp at length; omega
        obtain ⟨part, pending, built⟩ := ih rest.length short (some (branchingMask rep key)) key (.tip key value) rest rfl
        obtain ⟨chunk, consumed⟩ := built.consumes
        have shorter : pending.length < n := by rw [consumed, List.length_append] at short; omega
        obtain ⟨output, tail, continued⟩ :=
          ih pending.length shorter bound rep (splice (branchingMask rep key) key part acc) pending rfl
        exact ⟨output, tail, .advance allowed built continued⟩
      · cases bound with
        | none => simp at allowed
        | some scope =>
          have apart : ¬ sameRegion scope rep key := by simpa using allowed
          exact ⟨acc, (key, value) :: rest, .stop apart⟩

theorem builder_run_refines {bound root : Option Mask} {rep : Int} {acc output : Tree α} {input remainder}
    (execution : BuilderRun bound rep acc input output remainder)
    (valid : Rooted rep root acc)
    (scope : BuilderBound rep root bound)
    (outside : FrontOutside rep root input)
    (ordered : SortedKeys input) (fitted : FittedKeys input) (after : AfterKey rep input) :
    AscendingBuilder bound rep acc input output remainder ∧
      ∃ newRoot, Rooted rep newRoot output ∧ BuilderBound rep newRoot bound := by
  induction execution generalizing root with
  | done => exact ⟨.done, root, valid, scope⟩
  | stop missed => exact ⟨.stop missed, root, valid, scope⟩
  | @advance bound rep key acc value rest part pending output tail allowed built continued ihPart ihRest =>
    have headFits : FitsKey key := fitted (key, value) (by simp)
    have headAfter : rep < key := after (key, value) (by simp)
    have unique : rep ≠ key := by omega
    let m := branchingMask rep key
    obtain ⟨single, prefixEq, _⟩ := branching_mask rep key valid.fits headFits unique
    have late : (Branch.forKey key m).pivot ≤ key := (sorted_halves valid.fits headFits headAfter).2
    obtain ⟨tailAfter, tailOrdered⟩ := List.pairwise_cons.mp ordered
    have tailFits : FittedKeys rest := fun entry mem => fitted entry (List.mem_cons_of_mem _ mem)
    have tailAfterKey : AfterKey key rest := tailAfter
    obtain ⟨refined, rootPart, validPart, partBound⟩ :=
      ihPart (root := none) (Rooted.tip key value headFits)
        (by intro mask eq; cases eq; exact ⟨single, late, by simp [Narrower]⟩)
        (by simp [FrontOutside]) tailOrdered tailFits tailAfterKey
    have partBelow := validPart.below (partBound m rfl).2.2
    have accBelow : BelowMask m rep acc := valid.below fun current eq =>
      branching_gt valid.fits headFits unique (by rw [eq] at valid; exact valid.region.1)
        (outside current eq (key, value) rest rfl)
    have newValid := splice_rooted valid validPart unique accBelow partBelow
    have newBound : BuilderBound rep (some m) bound := by
      intro parent eqScope
      obtain ⟨bit, later, _⟩ := scope parent eqScope
      refine ⟨bit, later, ?_⟩
      intro child eq
      cases eq
      exact branching_lt valid.fits headFits unique bit
        (later_same_side bit valid.fits headFits later headAfter (allowed parent eqScope))
    have nextOutside : FrontOutside rep (some m) pending := by
      intro mask eq entry remain eqPending
      cases eq
      obtain ⟨actual, equal, apart⟩ := built.stopped entry remain eqPending
      cases equal
      intro inRep
      exact apart (prefixEq.symm.trans inRep)
    obtain ⟨chunk, chunkEq⟩ := built.consumes
    have remainingOrdered : SortedKeys pending := (List.pairwise_append.mp (chunkEq ▸ tailOrdered)).2.1
    have remainingMem (entry : Int × α) (member : entry ∈ pending) : entry ∈ (key, value) :: rest := by
      apply List.mem_cons_of_mem
      rw [chunkEq]
      exact List.mem_append_right _ member
    obtain ⟨refinedTail, stamp, validResult, boundResult⟩ :=
      ihRest newValid newBound nextOutside remainingOrdered
        (fun entry mem => fitted entry (remainingMem entry mem))
        (fun entry mem => after entry (remainingMem entry mem))
    exact ⟨.advance allowed refined valid.fits headFits unique partBelow accBelow refinedTail,
      stamp, validResult, boundResult⟩

inductive DistinctRun : List (Int × α) → Tree α → Prop where
  | empty : DistinctRun [] .nil
  | start : BuilderRun none key (.tip key value) tail output [] →
      DistinctRun ((key, value) :: tail) output

theorem distinct_run_refines {entries : List (Int × α)} {output : Tree α}
    (run : DistinctRun entries output) (sorted : SortedKeys entries) (fitted : FittedKeys entries) :
    DistinctAscending entries output ∧ ∃ raw : Trie α, raw.Valid ∧ raw.tree = output := by
  cases run with
  | empty => exact ⟨.empty, .nil, .nil, rfl⟩
  | @start key value tail output run =>
    have fit := fitted (key, value) (by simp)
    obtain ⟨after, restSorted⟩ := List.pairwise_cons.mp sorted
    obtain ⟨refined, _, rooted, _⟩ := builder_run_refines run (Rooted.tip key value fit)
      (by simp [BuilderBound]) (by simp [FrontOutside]) restSorted
      (fun entry mem => fitted entry (List.mem_cons_of_mem _ mem)) after
    exact ⟨.start refined, rooted.reifies⟩

theorem distinct_run_exists (entries : List (Int × α)) : ∃ output, DistinctRun entries output := by
  cases entries with
  | nil => exact ⟨.nil, .empty⟩
  | cons entry rest =>
    obtain ⟨key, value⟩ := entry
    obtain ⟨output, remainder, run⟩ := builder_run_exists none key (.tip key value) rest
    have remainderEmpty : remainder = [] := by
      cases remainder with
      | nil => rfl
      | cons entry tail =>
        obtain ⟨_, equal, _⟩ := run.stopped entry tail rfl
        cases equal
    subst remainder
    exact ⟨output, .start run⟩

theorem distinct_ascending_run (entries : List (Int × α)) (sorted : SortedKeys entries)
    (fitted : FittedKeys entries) :
    ∃ raw : Trie α, raw.Valid ∧ DistinctAscending entries raw.tree := by
  obtain ⟨output, run⟩ := distinct_run_exists entries
  obtain ⟨refined, raw, valid, rfl⟩ := distinct_run_refines run sorted fitted
  exact ⟨raw, valid, refined⟩

theorem Trie.Valid.rooted {t : Trie α} (valid : t.Valid) (nonempty : t ≠ .nil) :
    Rooted t.header.key (if t.header.rank = 0 then none else some t.header.rank) t.tree := by
  cases valid with
  | nil => contradiction
  | @tip key value fits => exact Rooted.tip key value fits
  | @fork p m l r single canonical wl wr lne rne il ir low high =>
    have branch : Branch.forKey p.toInt m = Branch.ofMask p m := by
      simp [Branch.forKey, canonical]
    have lowPrefix : Supported l.tree (InPrefix p m) := fun k h => (low k h).1
    have highPrefix : Supported r.tree (InPrefix p m) := fun k h => (high k h).1
    have valid := rooted_bin (rep := p.toInt) (m := m) (word_fits p) single
      wl.encoded wr.encoded
      (by simpa only [BitVec.ofInt_toInt, canonical] using lowPrefix)
      (by simpa only [BitVec.ofInt_toInt, canonical] using highPrefix)
      (by rw [branch]; exact ⟨fun k h => (low k h).2, fun k h => (high k h).2⟩)
      ⟨.fork p m l r, .fork single canonical wl wr lne rne il ir low high, by rw [branch]; rfl⟩
    simpa only [Trie.header, Trie.tree, if_neg single.1, branch] using valid

private theorem header_below {t : Trie α} {parent : Mask} (valid : t.Valid) (nonempty : t ≠ .nil)
    (lt : t.header.rank.ult parent) : BelowMask parent t.header.key t.tree :=
  (valid.rooted nonempty).below (by
    intro m eq
    split at eq
    · contradiction
    · cases eq; exact lt)

private theorem header_half {t : Trie α} {p m : Mask} (valid : t.Valid) (nonempty : t ≠ .nil)
    (taller : t.header.rank.ult m) (single : SingleBit m)
    (matching : maskPrefix (BitVec.ofInt 64 t.header.key) m = p) :
    Supported t.tree (InHalf p m ((Branch.ofMask p m).left t.header.key)) := by
  have below := header_below valid nonempty taller
  have prefixFit := below_prefix below single matching
  have side := below_mask_routes (pref := p) below single
  exact fun k found => ⟨prefixFit k found, side k found⟩

inductive Separate (l r : Header) : Prop where
  | tips : l.rank = 0 → r.rank = 0 → l.key ≠ r.key → Separate l r
  | left : r.rank.toNat ≤ l.rank.toNat → l.rank ≠ 0 →
      ¬ sameRegion l.rank l.key r.key → Separate l r
  | right : l.rank.ult r.rank → r.rank ≠ 0 → ¬ sameRegion r.rank l.key r.key → Separate l r

def Trie.join (l r : Trie α) : Trie α :=
  let key := l.header.key
  let mask := branchingMask key r.header.key
  let pref := maskPrefix (BitVec.ofInt 64 key) mask
  if (Branch.ofMask pref mask).left key then .fork pref mask l r else .fork pref mask r l

private theorem fork_bit {t : Trie α} (v : t.Valid) (nz : t.header.rank ≠ 0) : SingleBit t.header.rank := by
  cases v with
  | nil => exact False.elim (nz rfl)
  | tip => exact False.elim (nz rfl)
  | fork single => exact single

private theorem joining_ranks {l r : Trie α} (vl : l.Valid) (vr : r.Valid)
    (apart : Separate l.header r.header) :
    let m := branchingMask l.header.key r.header.key
    l.header.key ≠ r.header.key ∧ l.header.rank.ult m ∧ r.header.rank.ult m := by
  have split (different : l.header.key ≠ r.header.key) :=
    (branching_mask l.header.key r.header.key vl.header_fits vr.header_fits different).1
  cases apart with
  | tips zl zr distinct =>
    have p : 0 < (branchingMask l.header.key r.header.key).toNat :=
      Nat.pos_of_ne_zero (fun zero => (split distinct).1 (BitVec.eq_of_toNat_eq zero))
    exact ⟨distinct, by rw [zl]; exact decide_eq_true p, by rw [zr]; exact decide_eq_true p⟩
  | left le nz separated =>
    have ne : l.header.key ≠ r.header.key := fun eq => separated (by simp [sameRegion, eq])
    have lt := branching_gt vl.header_fits vr.header_fits ne (fork_bit vl nz) separated
    exact ⟨ne, lt, decide_eq_true (Nat.lt_of_le_of_lt le (of_decide_eq_true lt))⟩
  | right shorter nz separated =>
    have ne : l.header.key ≠ r.header.key := fun eq => separated (by simp [sameRegion, eq])
    have lt := branching_gt vl.header_fits vr.header_fits ne (fork_bit vr nz) separated
    exact ⟨ne, decide_eq_true (Nat.lt_trans (of_decide_eq_true shorter) (of_decide_eq_true lt)), lt⟩

private theorem branching_comm (a b : Int) : branchingMask a b = branchingMask b a := by
  unfold branchingMask
  rw [BitVec.xor_comm]

theorem Trie.join_refines {l r : Trie α} (vl : l.Valid) (vr : r.Valid) (ln : l ≠ .nil) (rn : r ≠ .nil)
    (apart : Separate l.header r.header) :
    (l.join r).Valid ∧ Merge l.tree r.tree (l.join r).tree := by
  obtain ⟨different, ll, rr⟩ := joining_ranks vl vr apart
  let a := l.header.key
  let b := r.header.key
  let m := branchingMask a b
  let p := maskPrefix (BitVec.ofInt 64 a) m
  let branch := Branch.ofMask p m
  obtain ⟨single, matching, _⟩ := branching_mask a b vl.header_fits vr.header_fits different
  have low : Supported l.tree (InPrefix p m) := below_prefix (header_below vl ln ll) single rfl
  have high : Supported r.tree (InPrefix p m) := below_prefix (header_below vr rn rr) single matching.symm
  have routes := branching_splice vr.header_fits vl.header_fits (Ne.symm different)
    (by rw [branching_comm b a]; exact header_below vl ln ll)
    (by rw [branching_comm b a]; exact header_below vr rn rr)
  rw [branching_comm b a] at routes
  change (if branch.left a then Routes branch l.tree r.tree else Routes branch r.tree l.tree) at routes
  change (if branch.left a then Trie.fork p m l r else Trie.fork p m r l).Valid ∧ _
  unfold Trie.join
  change (if branch.left a then Trie.fork p m l r else Trie.fork p m r l).Valid ∧
    Merge l.tree r.tree (if branch.left a then Trie.fork p m l r else Trie.fork p m r l).tree
  by_cases left : branch.left a
  · rw [if_pos left] at routes ⊢
    exact ⟨.fork single (mask_canonical _ _) vl vr ln rn ll rr
        (fun k found => ⟨low k found, routes.1 k found⟩)
        (fun k found => ⟨high k found, routes.2 k found⟩), .link (.left routes)⟩
  · rw [if_neg left] at routes ⊢
    exact ⟨.fork single (mask_canonical _ _) vr vl rn ln rr ll
        (fun k found => ⟨high k found, routes.1 k found⟩)
        (fun k found => ⟨low k found, routes.2 k found⟩), .link (.right routes)⟩

def Enclosed (pref mask : Mask) (side : Bool) (t : Trie α) : Prop :=
  t ≠ .nil ∧ t.header.rank.ult mask ∧ maskPrefix (BitVec.ofInt 64 t.header.key) mask = pref ∧
    (Branch.ofMask pref mask).left t.header.key = side

inductive MergeRun : Trie α → Trie α → Trie α → Prop where
  | nilLeft : MergeRun .nil r r
  | nilRight : MergeRun l .nil l
  | sameTip : MergeRun (.tip key x) (.tip key y) (.tip key x)
  | link : l ≠ .nil → r ≠ .nil → Separate l.header r.header → MergeRun l r (l.join r)
  | sameFork : MergeRun l₁ l₂ lo → MergeRun r₁ r₂ hi →
      MergeRun (.fork pref mask l₁ r₁) (.fork pref mask l₂ r₂) (.fork pref mask lo hi)
  | firstLow : Enclosed pref mask true t → MergeRun l t lo →
      MergeRun (.fork pref mask l r) t (.fork pref mask lo r)
  | firstHigh : Enclosed pref mask false t → MergeRun r t hi →
      MergeRun (.fork pref mask l r) t (.fork pref mask l hi)
  | secondLow : Enclosed pref mask true t → MergeRun t l lo →
      MergeRun t (.fork pref mask l r) (.fork pref mask lo r)
  | secondHigh : Enclosed pref mask false t → MergeRun t r hi →
      MergeRun t (.fork pref mask l r) (.fork pref mask l hi)

private theorem merge_support {l r t : Trie α} {p : Int → Prop} (m : Merge l.tree r.tree t.tree)
    (left : Supported l.tree p) (right : Supported r.tree p) : Supported t.tree p := by
  intro k found
  rw [lookup_merge m] at found
  cases h : lookup k l.tree with
  | none => exact right k (by simpa [h] using found)
  | some v => exact left k (by simp [h])

private theorem merge_nonempty {l r t : Trie α} (m : Merge l.tree r.tree t.tree)
    (nonempty : (∃ k, lookup k l.tree ≠ none) ∨ (∃ k, lookup k r.tree ≠ none)) : t ≠ .nil := by
  intro empty
  obtain ⟨k, left | right⟩ : ∃ k, lookup k l.tree ≠ none ∨ lookup k r.tree ≠ none := by
    rcases nonempty with ⟨k, h⟩ | ⟨k, h⟩
    · exact ⟨k, .inl h⟩
    · exact ⟨k, .inr h⟩
  · have eq := lookup_merge m k
    rw [empty, Trie.tree, lookup] at eq
    cases first : lookup k l.tree with
    | none => exact left first
    | some val => simp [first] at eq
  · have eq := lookup_merge m k
    rw [empty, Trie.tree, lookup] at eq
    cases first : lookup k l.tree with
    | none => exact right (by simpa [first] using eq.symm)
    | some val => simp [first] at eq

private theorem bin_fork {l r : Trie α} (ln : l ≠ .nil) (rn : r ≠ .nil) (pref mask : Mask) :
    bin (Branch.ofMask pref mask) l.tree r.tree = (.fork pref mask l r : Trie α).tree := by
  cases l <;> cases r <;> simp_all [bin, Trie.tree]

private theorem no_support (pred : Int → Prop) : Supported (Trie.nil : Trie α).tree pred := by
  intro k present
  exact False.elim (present rfl)

private theorem merge_fork {p m : Mask} {l₁ r₁ l₂ r₂ lo hi : Trie α}
    (single : SingleBit m) (canonical : maskPrefix p m = p)
    (left : Merge l₁.tree l₂.tree lo.tree) (right : Merge r₁.tree r₂.tree hi.tree)
    (low₁ : Supported l₁.tree (InHalf p m true)) (high₁ : Supported r₁.tree (InHalf p m false))
    (low₂ : Supported l₂.tree (InHalf p m true)) (high₂ : Supported r₂.tree (InHalf p m false))
    (validLo : lo.Valid) (validHi : hi.Valid) (nonemptyLo : lo ≠ .nil) (nonemptyHi : hi ≠ .nil) :
    (Trie.fork p m lo hi).Valid ∧
      Merge (bin (Branch.ofMask p m) l₁.tree r₁.tree) (bin (Branch.ofMask p m) l₂.tree r₂.tree)
        (Trie.fork p m lo hi).tree := by
  have low := merge_support left low₁ low₂
  have high := merge_support right high₁ high₂
  exact ⟨.fork single canonical validLo validHi nonemptyLo nonemptyHi
    (half_rank validLo single low) (half_rank validHi single high) low high,
    .branches ⟨fun k h => (low₁ k h).2, fun k h => (high₁ k h).2⟩
      ⟨fun k h => (low₂ k h).2, fun k h => (high₂ k h).2⟩ left right⟩

private theorem enclosure_support {p m : Mask} {side : Bool} {t : Trie α}
    (valid : t.Valid) (single : SingleBit m) (shape : Enclosed p m side t) :
    Supported t.tree (InHalf p m side) := by
  obtain ⟨nonempty, lt, prefixEq, sideEq⟩ := shape
  simpa only [sideEq] using header_half valid nonempty lt single prefixEq

private theorem bin_nil_right (branch : Branch) (tree : Tree α) : bin branch tree .nil = tree := by
  cases tree <;> rfl

private theorem bin_nil_left (branch : Branch) (tree : Tree α) : bin branch .nil tree = tree := by
  cases tree <;> rfl

theorem merge_run_refines {l r result : Trie α} (run : MergeRun l r result) (vl : l.Valid) (vr : r.Valid) :
    result.Valid ∧ Merge l.tree r.tree result.tree := by
  induction run with
  | nilLeft => exact ⟨vr, .nilLeft⟩
  | nilRight => exact ⟨vl, .nilRight⟩
  | sameTip => exact ⟨vl, .sameTip⟩
  | link ln rn apart => exact Trie.join_refines vl vr ln rn apart
  | sameFork _ _ il ir =>
    cases vl with
    | fork single canonical vll vlr lln lrn _ _ llo lhi =>
      cases vr with
      | fork _ _ vrl vrr rln rrn _ _ rlo rhi =>
        obtain ⟨winLo, stepLo⟩ := il vll vrl
        obtain ⟨winHi, stepHi⟩ := ir vlr vrr
        have merged := merge_fork single canonical stepLo stepHi llo lhi rlo rhi winLo winHi
          (merge_nonempty stepLo (.inl (present vll lln))) (merge_nonempty stepHi (.inl (present vlr lrn)))
        simpa only [bin_fork lln lrn, bin_fork rln rrn] using merged
  | firstLow enc _ ih =>
    cases vl with
    | fork single canonical vll vlr lln lrn _ _ lo hi =>
      obtain ⟨win, step⟩ := ih vll vr
      have merged := merge_fork (r₂ := .nil) single canonical step .nilRight lo hi
        (enclosure_support vr single enc) (no_support _) win vlr
        (merge_nonempty step (.inl (present vll lln))) lrn
      rw [bin_fork lln lrn, show (Trie.nil : Trie α).tree = Tree.nil from rfl, bin_nil_right] at merged
      exact merged
  | firstHigh enc _ ih =>
    cases vl with
    | fork single canonical vll vlr lln lrn _ _ lo hi =>
      obtain ⟨win, step⟩ := ih vlr vr
      have merged := merge_fork (l₂ := .nil) single canonical .nilRight step lo hi
        (no_support _) (enclosure_support vr single enc) vll win
        lln (merge_nonempty step (.inl (present vlr lrn)))
      simpa only [bin_fork lln lrn, Trie.tree, bin_nil_left] using merged
  | secondLow enc _ ih =>
    cases vr with
    | fork single canonical vrl vrr rln rrn _ _ lo hi =>
      obtain ⟨win, step⟩ := ih vl vrl
      have merged := merge_fork (r₁ := .nil) single canonical step .nilLeft
        (enclosure_support vl single enc) (no_support _) lo hi win vrr
        (merge_nonempty step (.inr (present vrl rln))) rrn
      rw [bin_fork rln rrn, show (Trie.nil : Trie α).tree = Tree.nil from rfl, bin_nil_right] at merged
      exact merged
  | secondHigh enc _ ih =>
    cases vr with
    | fork single canonical vrl vrr rln rrn _ _ lo hi =>
      obtain ⟨win, step⟩ := ih vl vrr
      have merged := merge_fork (l₁ := .nil) single canonical .nilLeft step
        (no_support _) (enclosure_support vl single enc) lo hi vrl win
        rln (merge_nonempty step (.inr (present vrr rrn)))
      simpa only [bin_fork rln rrn, Trie.tree, bin_nil_left] using merged

theorem merge_run_lookup {l r result : Trie α} (run : MergeRun l r result) (vl : l.Valid) (vr : r.Valid)
    (key : Int) : lookup key result.tree = (lookup key l.tree).or (lookup key r.tree) :=
  lookup_merge (merge_run_refines run vl vr).2 key

private theorem first_fork_run {pref mask : Mask} {l r t : Trie α} (nonempty : t ≠ .nil)
    (single : SingleBit mask) (canonical : maskPrefix pref mask = pref) (shorter : t.header.rank.ult mask)
    (left : ∃ result, MergeRun l t result) (right : ∃ result, MergeRun r t result) :
    ∃ result, MergeRun (.fork pref mask l r) t result := by
  by_cases fits : maskPrefix (BitVec.ofInt 64 t.header.key) mask = pref
  · cases side : (Branch.ofMask pref mask).left t.header.key
    · obtain ⟨hi, merged⟩ := right
      exact ⟨.fork pref mask l hi, .firstHigh ⟨nonempty, shorter, fits, side⟩ merged⟩
    · obtain ⟨lo, merged⟩ := left
      exact ⟨.fork pref mask lo r, .firstLow ⟨nonempty, shorter, fits, side⟩ merged⟩
  · have apart : Separate (Trie.fork pref mask l r).header t.header := by
      refine .left (Nat.le_of_lt (of_decide_eq_true shorter)) single.1 ?_
      intro same
      exact fits (by simpa only [sameRegion, Trie.header, BitVec.ofInt_toInt, canonical] using same.symm)
    exact ⟨_, .link (by intro eq; cases eq) nonempty apart⟩

private theorem second_fork_run {pref mask : Mask} {l r t : Trie α} (nonempty : t ≠ .nil)
    (single : SingleBit mask) (canonical : maskPrefix pref mask = pref) (shorter : t.header.rank.ult mask)
    (left : ∃ result, MergeRun t l result) (right : ∃ result, MergeRun t r result) :
    ∃ result, MergeRun t (.fork pref mask l r) result := by
  by_cases fits : maskPrefix (BitVec.ofInt 64 t.header.key) mask = pref
  · cases side : (Branch.ofMask pref mask).left t.header.key
    · obtain ⟨hi, merged⟩ := right
      exact ⟨.fork pref mask l hi, .secondHigh ⟨nonempty, shorter, fits, side⟩ merged⟩
    · obtain ⟨lo, merged⟩ := left
      exact ⟨.fork pref mask lo r, .secondLow ⟨nonempty, shorter, fits, side⟩ merged⟩
  · have apart : Separate t.header (Trie.fork pref mask l r).header := by
      refine .right shorter single.1 ?_
      intro same
      exact fits (by simpa only [sameRegion, Trie.header, BitVec.ofInt_toInt, canonical] using same)
    exact ⟨_, .link nonempty (by intro eq; cases eq) apart⟩

def Trie.size : Trie α → Nat
  | .nil | .tip .. => 1
  | .fork _ _ l r => 1 + l.size + r.size

theorem merge_run_exists {l r : Trie α} (vl : l.Valid) (vr : r.Valid) :
    ∃ result, MergeRun l r result := by
  induction length : l.size + r.size using Nat.strongRecOn generalizing l r with
  | ind n ih =>
    have recurse {u v : Trie α} (vu : u.Valid) (vv : v.Valid)
        (lt : u.size + v.size < l.size + r.size) : ∃ result, MergeRun u v result :=
      ih (u.size + v.size) (length ▸ lt) vu vv rfl
    cases vl with
    | nil => exact ⟨r, .nilLeft⟩
    | @tip k x fit =>
      cases vr with
      | nil => exact ⟨_, .nilRight⟩
      | @tip key value _ =>
        by_cases same : k = key
        · subst key; exact ⟨_, .sameTip⟩
        · exact ⟨_, .link (by intro eq; cases eq) (by intro eq; cases eq) (.tips rfl rfl same)⟩
      | @fork p m lo hi single canonical vlo vhi _ _ _ _ _ _ =>
        refine second_fork_run (by intro eq; cases eq) single canonical
          (decide_eq_true (Nat.pos_of_ne_zero (fun zero => single.1 (BitVec.eq_of_toNat_eq zero))))
          (recurse (.tip fit) vlo ?_) (recurse (.tip fit) vhi ?_)
        all_goals simp only [Trie.size]; omega
    | @fork p m lo hi single canonical vlo vhi ln rn sl sr low high =>
      cases vr with
      | nil => exact ⟨_, .nilRight⟩
      | @tip key value fit =>
        refine first_fork_run (by intro eq; cases eq) single canonical
          (decide_eq_true (Nat.pos_of_ne_zero (fun zero => single.1 (BitVec.eq_of_toNat_eq zero))))
          (recurse vlo (.tip fit) ?_) (recurse vhi (.tip fit) ?_)
        all_goals simp only [Trie.size]; omega
      | @fork pref mask rlo rhi one root vrlo vrhi rln rrn rl rr rlow rhigh =>
        rcases Nat.lt_trichotomy mask.toNat m.toNat with short | same | tall
        · refine first_fork_run (by intro eq; cases eq) single canonical (decide_eq_true short)
            (recurse vlo (.fork one root vrlo vrhi rln rrn rl rr rlow rhigh) ?_)
            (recurse vhi (.fork one root vrlo vrhi rln rrn rl rr rlow rhigh) ?_)
          all_goals simp only [Trie.size]; omega
        · have maskEq : mask = m := BitVec.eq_of_toNat_eq same
          subst mask
          by_cases eq : p = pref
          · subst pref
            obtain ⟨low, ml⟩ := recurse vlo vrlo (by simp only [Trie.size]; omega)
            obtain ⟨high, mh⟩ := recurse vhi vrhi (by simp only [Trie.size]; omega)
            exact ⟨.fork p m low high, .sameFork ml mh⟩
          · have apart : Separate (Trie.fork p m lo hi).header (Trie.fork pref m rlo rhi).header := by
              refine .left (Nat.le_refl _) single.1 ?_
              intro matching
              exact eq (by simpa only [sameRegion, Trie.header, BitVec.ofInt_toInt, canonical, root] using matching)
            exact ⟨_, .link (by intro eq; cases eq) (by intro eq; cases eq) apart⟩
        · refine second_fork_run (by intro eq; cases eq) one root (decide_eq_true tall)
            (recurse (.fork single canonical vlo vhi ln rn sl sr low high) vrlo ?_)
            (recurse (.fork single canonical vlo vhi ln rn sl sr low high) vrhi ?_)
          all_goals simp only [Trie.size]; omega

private theorem narrow_mask_sign {m parent : Mask} (parentBit : SingleBit parent) (above : m.ult parent) :
    m.msb = false := by
  obtain ⟨k, bound, power⟩ := single_bit_power parentBit
  have smaller : m.toNat < parent.toNat := of_decide_eq_true above
  have limit : parent.toNat ≤ 2^63 := power ▸ Nat.pow_le_pow_right (by decide) (by omega)
  rw [BitVec.msb_eq_decide]
  exact decide_eq_false (by change ¬2^63 ≤ m.toNat; omega)

private theorem unsigned_below {t : Trie α} (valid : t.Valid) (sign : t.header.rank.msb = false) :
    UnsignedBranches t.tree := by
  induction valid with
  | nil => exact .nil
  | tip => exact .tip
  | fork single _ vl vr _ _ narrowL narrowR _ _ il ir =>
    apply UnsignedBranches.bin sign
    · exact il (narrow_mask_sign single narrowL)
    · exact ir (narrow_mask_sign single narrowR)

private theorem source_root {t : Trie α} (valid : t.Valid) :
    ∀ b l r, t.tree = .bin b l r → UnsignedBranches l ∧ UnsignedBranches r ∧
      (b.sign = true → b.pivot = 0) := by
  cases valid with
  | nil | tip => intro b l r eq; cases eq
  | fork single _ vl vr _ _ narrowL narrowR _ _ =>
    intro b l r eq
    cases eq
    refine ⟨unsigned_below vl (narrow_mask_sign single narrowL),
      unsigned_below vr (narrow_mask_sign single narrowR), ?_⟩
    intro sign
    simp only [Branch.ofMask] at sign ⊢
    rw [if_pos sign]

theorem shifted_run {source : Trie α} (valid : source.Valid) (delta : Int)
    (fitted : FittedKeys ((entries source.tree).map (fun (k,x) => (k + delta,x)))) :
    ∃ result : Trie α, result.Valid ∧ Shift delta source.tree result.tree := by
  have sorted := shifted_entries_sorted delta (encoded_wellFormed valid.encoded)
    (fun b l r eq => ⟨(source_root valid b l r eq).1, (source_root valid b l r eq).2.1⟩)
  exact distinct_ascending_run _ sorted fitted

inductive Prunes : Trie α → Tree α → Prop where
  | keep : Prunes t t.tree
  | erase : Prunes t .nil
  | fork : Prunes l lo → Prunes r hi →
      Prunes (.fork p m l r) (bin (Branch.ofMask p m) lo hi)

private theorem of_pruned_fork {l r : Trie α} {p m : Mask}
    (single : SingleBit m) (canonical : maskPrefix p m = p)
    (vl : l.Valid) (vr : r.Valid)
    (lo : Supported l.tree (InHalf p m true)) (hi : Supported r.tree (InHalf p m false)) :
    ∃ raw : Trie α, raw.Valid ∧ raw.tree = bin (Branch.ofMask p m) l.tree r.tree := by
  by_cases ln : l = .nil
  · subst l; exact ⟨r, vr, (bin_nil_left _ _).symm⟩
  · by_cases rn : r = .nil
    · subst r; exact ⟨l, vl, (bin_nil_right _ _).symm⟩
    · exact ⟨.fork p m l r, .fork single canonical vl vr ln rn (half_rank vl single lo)
        (half_rank vr single hi) lo hi, (bin_fork ln rn p m).symm⟩

theorem prunes_valid {source : Trie α} {output : Tree α} (run : Prunes source output)
    (valid : source.Valid) : (∃ raw : Trie α, raw.Valid ∧ raw.tree = output) ∧
      ∀ k, lookup k output ≠ none → lookup k source.tree ≠ none := by
  induction run with
  | keep => exact ⟨⟨_, valid, rfl⟩, fun _ h => h⟩
  | erase => exact ⟨⟨.nil, .nil, rfl⟩, fun _ h => False.elim (h rfl)⟩
  | fork _ _ ilo ihi =>
    cases valid with
    | fork single canonical vl vr _ _ _ _ lo hi =>
      obtain ⟨⟨newL, vl', leq⟩, retainL⟩ := ilo vl
      obtain ⟨⟨newR, vr', req⟩, retainR⟩ := ihi vr
      have low := fun k h => lo k (retainL k h)
      have high := fun k h => hi k (retainR k h)
      have fit := of_pruned_fork single canonical vl' vr'
        (fun k h => low k (by simpa only [leq] using h))
        (fun k h => high k (by simpa only [req] using h))
      refine ⟨by simpa only [leq, req] using fit, ?_⟩
      intro k observed
      rw [lookup_bin _ _ _ _ (fun key h => (low key h).2) (fun key h => (high key h).2)] at observed
      simp only [Trie.tree, lookup] at observed ⊢
      split at observed
      · rename_i left
        rw [if_pos left]
        exact retainL k observed
      · rename_i right
        rw [if_neg right]
        exact retainR k observed

theorem filter_prunes (pred : Int → α → Bool) (source : Trie α) :
    Prunes source (filter pred source.tree) := by
  induction source with
  | nil => exact .keep
  | tip key value =>
    change Prunes (.tip key value) (if pred key value then .tip key value else .nil)
    split
    · exact .keep
    · exact .erase
  | fork _ _ _ _ il ir => exact .fork il ir

theorem trim_prunes (take : Bool) (cut : Int) (source : Trie α) :
    Prunes source (trim take cut source.tree) := by
  have left {p m : Mask} {l r : Trie α} {output : Tree α} (run : Prunes l output) :
      Prunes (.fork p m l r) output := by
    have selected : Prunes (.fork p m l r) (bin (Branch.ofMask p m) output .nil) :=
      .fork run .erase
    rw [bin_nil_right] at selected
    exact selected
  have right {p m : Mask} {l r : Trie α} {output : Tree α} (run : Prunes r output) :
      Prunes (.fork p m l r) output := by
    have selected : Prunes (.fork p m l r) (bin (Branch.ofMask p m) .nil output) :=
      .fork .erase run
    rw [bin_nil_left] at selected
    exact selected
  induction source with
  | nil => exact .keep
  | tip key value =>
    change Prunes (.tip key value) (if decide (key < cut) == take then .tip key value else .nil)
    split
    · exact .keep
    · exact .erase
  | fork p m l r il ir =>
    simp only [Trie.tree, trim]
    split <;> split <;> cases take
    · exact left il
    · exact .fork il .keep
    · exact .fork .keep ir
    · exact right ir
    · exact right ir
    · exact .fork .keep ir
    · exact .fork il .keep
    · exact left il

theorem prune_trim (take : Bool) (cut : Int) {source : Trie α} (valid : source.Valid) :
    ∃ raw : Trie α, raw.Valid ∧ raw.tree = trimRoot take cut source.tree := by
  rw [trim_root_eq take cut source.tree (source_root valid)]
  exact (prunes_valid (trim_prunes take cut source) valid).1


private theorem fitted_shift {t : Trie α} (valid : t.Valid) (delta : Int)
    (fits : Supported t.tree (fun k => FitsKey (k + delta))) :
    FittedKeys ((entries t.tree).map (fun (k,x) => (k + delta,x))) := by
  intro entry own
  obtain ⟨⟨key, value⟩, member, eq⟩ := List.mem_map.mp own
  subst entry
  apply fits key
  intro absent
  rw [← entries_lookup (encoded_wellFormed valid.encoded), List.lookup_eq_none_iff] at absent
  simpa using absent (key, value) member

theorem copy_transfer_run_exists {source : Trie α} (valid : source.Valid) (s d width : Int)
    (source_nonnegative : 0 ≤ s) (destination_nonnegative : 0 ≤ d) (width_nonnegative : 0 ≤ width)
    (source_fits : s + width ≤ 9223372036854775807)
    (destination_fits : d + width ≤ 9223372036854775807) :
    (FitsKey s ∧ FitsKey (s + width) ∧ FitsKey d ∧ FitsKey (d + width)) ∧
      ∃ moved : Trie α, moved.Valid ∧ Transfer s d width source.tree moved.tree := by
  refine ⟨by unfold FitsKey; omega, ?_⟩
  obtain ⟨suffix, suffixValid, suffixEq⟩ := (prunes_valid (trim_prunes false s source) valid).1
  obtain ⟨inside, insideValid, insideEq⟩ := (prunes_valid (trim_prunes true (s + width) suffix) suffixValid).1
  rw [suffixEq] at insideEq
  change inside.tree = window s width source.tree at insideEq
  have window_keys : Supported inside.tree (fun k => s ≤ k ∧ k < s + width) := by
    intro k found
    by_cases within : s ≤ k ∧ k < s + width
    · exact within
    · rw [insideEq, lookup_window s width (encoded_wellFormed valid.encoded), if_neg within] at found
      exact False.elim (found rfl)
  obtain ⟨relative, relativeValid, firstShift⟩ := shifted_run insideValid (-s)
    (fitted_shift insideValid (-s) (fun k h => by
      have span := window_keys k h
      unfold FitsKey
      omega))
  have relativeKeys : Supported relative.tree (fun k => 0 ≤ k ∧ k < width) := by
    intro k found
    have insideFound : lookup (k - -s) inside.tree ≠ none := by
      rw [lookup_mapKeysMonotonic (encoded_wellFormed insideValid.encoded) firstShift] at found
      exact found
    have span := window_keys _ insideFound
    omega
  obtain ⟨moved, movedValid, secondShift⟩ := shifted_run relativeValid d
    (fitted_shift relativeValid d (fun k h => by
      have span := relativeKeys k h
      unfold FitsKey
      omega))
  have windowShift : Shift (-s) (window s width source.tree) relative.tree := insideEq ▸ firstShift
  exact ⟨moved, movedValid, ⟨relative.tree, windowShift, encoded_wellFormed relativeValid.encoded, secondShift⟩⟩

theorem copy_payload_run {source destination : Trie Int} (sv : source.Valid) (dv : destination.Valid)
    (s d count : Nat) (source_fits : s + count ≤ 9223372036854775807)
    (destination_fits : d + count ≤ 9223372036854775807) :
    ∃ result : Trie Int, result.Valid ∧ ∀ k, lookup k result.tree =
      if (d : Int) ≤ k ∧ k < (d : Int) + count then lookup ((s : Int) + (k - d)) source.tree
      else lookup k destination.tree := by
  obtain ⟨_, moved, mv, transferred⟩ := copy_transfer_run_exists sv (s : Int) (d : Int) count
    (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨before, bv, be⟩ := (prunes_valid (trim_prunes true (d : Int) destination) dv).1
  obtain ⟨after, av, ae⟩ := (prunes_valid (trim_prunes false ((d : Int) + count) destination) dv).1
  obtain ⟨untouched, undo⟩ := merge_run_exists bv av
  obtain ⟨uv, retained⟩ := merge_run_refines undo bv av
  obtain ⟨result, complete⟩ := merge_run_exists mv uv
  obtain ⟨rv, combined⟩ := merge_run_refines complete mv uv
  rw [be, ae] at retained
  exact ⟨result, rv, copy_payload_refines s d count (encoded_wellFormed sv.encoded)
    (encoded_wellFormed dv.encoded) transferred retained combined⟩

theorem copy_shadow_run {source destination : Trie α} (sv : source.Valid) (dv : destination.Valid)
    (s d count : Nat) (source_fits : s + count ≤ 9223372036854775807)
    (destination_fits : d + count ≤ 9223372036854775807) :
    ∃ result : Trie α, result.Valid ∧ ∀ k, lookup k result.tree =
      capability_shadow_copy (lookup · source.tree) (lookup · destination.tree) s d count k := by
  by_cases empty : count = 0
  · subst count
    exact ⟨destination, dv, fun k => by simp [capability_shadow_copy]⟩
  let width := max 0 ((count : Int) - 7)
  have widthBound : width ≤ (count : Int) := by
    dsimp [width]
    by_cases long : 7 ≤ (count : Int)
    · rw [Int.max_eq_right (by omega)]
      omega
    · rw [Int.max_eq_left (by omega)]
      omega
  have run : ∃ moved : Trie α, moved.Valid ∧
      (if (s : Int) % 8 = (d : Int) % 8 then Transfer s d width source.tree moved.tree
       else moved.tree = .nil) := by
    by_cases aligned : (s : Int) % 8 = (d : Int) % 8
    · obtain ⟨_, shifted, valid, transfer⟩ := copy_transfer_run_exists sv s d width (by omega)
        (by omega) (by unfold width; omega) (by omega) (by omega)
      exact ⟨shifted, valid, by simpa only [if_pos aligned] using transfer⟩
    · exact ⟨.nil, .nil, by simp [aligned, Trie.tree]⟩
  obtain ⟨moved, mv, transferred⟩ := run
  let outside := fun (slot : Int) (_ : α) => decide (slot ≤ (d : Int) - 8 ∨ (d : Int) + count ≤ slot)
  obtain ⟨untouched, uv, eq⟩ := (prunes_valid (filter_prunes outside destination) dv).1
  obtain ⟨result, complete⟩ := merge_run_exists mv uv
  obtain ⟨rv, combined⟩ := merge_run_refines complete mv uv
  rw [eq] at combined
  exact ⟨result, rv, copy_shadow s d count empty (encoded_wellFormed sv.encoded)
    (encoded_wellFormed dv.encoded) transferred combined⟩

theorem aggregate_shadow_run {source destination : Trie α} (sv : source.Valid) (dv : destination.Valid)
    (s d count : Nat) (source_fits : s + count ≤ 9223372036854775807)
    (destination_fits : d + count ≤ 9223372036854775807) :
    let first := (((d : Int) + 7) / 8) * 8
    let past := max first ((d : Int) + count - 7)
    let width := max 0 ((count : Int) - 7)
    ∃ result : Trie α, result.Valid ∧ ∀ k, lookup k result.tree =
      (if (d : Int) ≤ k ∧ k < (d : Int) + width then lookup ((s : Int) + (k - d)) source.tree else none).or
        (if k < first ∨ past ≤ k then lookup k destination.tree else none) := by
  let first := (((d : Int) + 7) / 8) * 8
  let past := max first ((d : Int) + count - 7)
  let width := max 0 ((count : Int) - 7)
  have width_fits : 0 ≤ width ∧ width ≤ (count : Int) := by
    dsimp [width]
    constructor
    · exact Int.le_max_left _ _
    · by_cases long : 7 ≤ (count : Int)
      · rw [Int.max_eq_right (by omega)]
        omega
      · rw [Int.max_eq_left (by omega)]
        omega
  obtain ⟨_, moved, mv, transferred⟩ := copy_transfer_run_exists sv (s : Int) (d : Int) width
    (by omega) (by omega) width_fits.1 (by omega) (by omega)
  obtain ⟨before, bv, beforeEq⟩ := (prunes_valid (trim_prunes true first destination) dv).1
  obtain ⟨after, av, afterEq⟩ := (prunes_valid (trim_prunes false past destination) dv).1
  obtain ⟨outside, retained⟩ := merge_run_exists bv av
  obtain ⟨ov, outside_lookup⟩ := merge_run_refines retained bv av
  obtain ⟨result, complete⟩ := merge_run_exists mv ov
  refine ⟨result, (merge_run_refines complete mv ov).1, ?_⟩
  intro k
  have span : lookup k outside.tree = if k < first ∨ past ≤ k then lookup k destination.tree else none := by
    rw [lookup_merge outside_lookup, beforeEq, afterEq,
      lookup_trim true first (encoded_wellFormed dv.encoded),
      lookup_trim false past (encoded_wellFormed dv.encoded)]
    by_cases below : k < first <;> by_cases above : past ≤ k <;>
      simp [below, above, Int.not_lt.mpr, Int.lt_of_not_ge]
  rw [lookup_merge (merge_run_refines complete mv ov).2,
    lookup_transfer (encoded_wellFormed sv.encoded) transferred, span]

end Heresy.Patricia

#print axioms Heresy.Patricia.builder_run_refines
#print axioms Heresy.Patricia.distinct_ascending_run
#print axioms Heresy.Patricia.merge_run_refines
#print axioms Heresy.Patricia.merge_run_exists

#print axioms Heresy.Patricia.copy_payload_run
#print axioms Heresy.Patricia.copy_shadow_run
#print axioms Heresy.Patricia.aggregate_shadow_run
