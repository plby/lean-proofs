/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# The finite octahedral Tucker lemma

This file formalizes the signed-sequence, finite handshaking proof of
Freund--Todd in the specialization recorded by Matoušek.  No topological
principle is assumed.
-/

open Function Set

namespace Erdos921.Tucker

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A sign vector is represented by its positive and negative supports. -/
@[ext] structure SignVector (N : ℕ) where
  pos : Finset (Fin N)
  neg : Finset (Fin N)
  deriving DecidableEq

instance (N : ℕ) : Fintype (SignVector N) :=
  Fintype.ofInjective (fun X ↦ (X.pos, X.neg)) (by intro X Y h; cases X; cases Y; simp_all)

def SignVector.zero (N : ℕ) : SignVector N := ⟨∅, ∅⟩

def SignVector.negate {N : ℕ} (X : SignVector N) : SignVector N :=
  ⟨X.neg, X.pos⟩

@[simp] lemma SignVector.negate_pos {N : ℕ} (X : SignVector N) : X.negate.pos = X.neg := rfl
@[simp] lemma SignVector.negate_neg {N : ℕ} (X : SignVector N) : X.negate.neg = X.pos := rfl
@[simp] lemma SignVector.negate_negate {N : ℕ} (X : SignVector N) : X.negate.negate = X := by
  cases X
  rfl

@[simp] lemma SignVector.negate_eq_zero_iff {N : ℕ} (X : SignVector N) :
    X.negate = .zero N ↔ X = .zero N := by
  rcases X with ⟨p, n⟩
  simp only [SignVector.negate, SignVector.zero, SignVector.mk.injEq]
  aesop

def SignVector.LE {N : ℕ} (X Y : SignVector N) : Prop :=
  X.pos ⊆ Y.pos ∧ X.neg ⊆ Y.neg

instance {N : ℕ} : LE (SignVector N) := ⟨SignVector.LE⟩

@[simp] lemma SignVector.le_def {N : ℕ} {X Y : SignVector N} :
    X ≤ Y ↔ X.pos ⊆ Y.pos ∧ X.neg ⊆ Y.neg := Iff.rfl

/-- The positive and negative supports of a genuine sign vector are disjoint.
The ambient structure keeps the two finite sets separate so that prefix states
remain computationally simple; all Tucker hypotheses are restricted to this
mathematically intended subdomain. -/
def SignVector.Consistent {N : ℕ} (X : SignVector N) : Prop :=
  Disjoint X.pos X.neg

@[simp] lemma SignVector.zero_consistent (N : ℕ) :
    (SignVector.zero N).Consistent := by
  simp [SignVector.Consistent, SignVector.zero]

lemma SignVector.consistent_negate {N : ℕ} {X : SignVector N}
    (hX : X.Consistent) : X.negate.Consistent := by
  simpa [SignVector.Consistent, SignVector.negate] using hX.symm

/-- A signed coordinate.  `true` denotes the positive support. -/
abbrev Atom (N : ℕ) := Fin N × Bool

def Atom.negate {N : ℕ} (a : Atom N) : Atom N := (a.1, !a.2)

@[simp] lemma Atom.negate_fst {N : ℕ} (a : Atom N) : a.negate.1 = a.1 := rfl
@[simp] lemma Atom.negate_snd {N : ℕ} (a : Atom N) : a.negate.2 = !a.2 := rfl
@[simp] lemma Atom.negate_negate {N : ℕ} (a : Atom N) : a.negate.negate = a := by
  rcases a with ⟨i, b⟩
  cases b <;> rfl

lemma Atom.eq_or_eq_negate_of_fst_eq {N : ℕ} {a b : Atom N} (h : a.1 = b.1) :
    a = b ∨ a = b.negate := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  simp only at h
  subst j
  cases a <;> cases b <;> simp [Atom.negate]

lemma Atom.negate_ne_self {N : ℕ} (a : Atom N) : a.negate ≠ a := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [Atom.negate]

/-- The sign vector encoded by a signed list. -/
def stateOfList {N : ℕ} (l : List (Atom N)) : SignVector N where
  pos := (l.filter fun a ↦ a.2).toFinset.image Prod.fst
  neg := (l.filter fun a ↦ !a.2).toFinset.image Prod.fst

lemma stateOfList_consistent {N : ℕ} {l : List (Atom N)}
    (hl : (l.map Prod.fst).Nodup) : (stateOfList l).Consistent := by
  rw [SignVector.Consistent, Finset.disjoint_left]
  intro x hxpos hxneg
  simp only [stateOfList, Finset.mem_image, List.mem_toFinset, List.mem_filter]
    at hxpos hxneg
  obtain ⟨a, ⟨ha, hapos⟩, hax⟩ := hxpos
  obtain ⟨b, ⟨hb, hbneg⟩, hbx⟩ := hxneg
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hb
  have hij : i = j := by
    let i' : Fin (l.map Prod.fst).length := ⟨i, by simpa using i.isLt⟩
    let j' : Fin (l.map Prod.fst).length := ⟨j, by simpa using j.isLt⟩
    have hcoord : (l.get i).1 = (l.get j).1 := by
      rw [hi, hj]
      exact hax.trans hbx.symm
    have hij' : i' = j' := hl.get_inj_iff.mp (by
      simpa [i', j'] using hcoord)
    apply Fin.ext
    simpa [i', j'] using congrArg Fin.val hij'
  subst j
  have hab : a = b := hi.symm.trans hj
  subst b
  cases a.2 <;> simp_all

@[simp] lemma stateOfList_nil {N : ℕ} : stateOfList ([] : List (Atom N)) = .zero N := by
  rfl

lemma stateOfList_perm {N : ℕ} {l r : List (Atom N)} (h : l.Perm r) :
    stateOfList l = stateOfList r := by
  ext
  · simp only [stateOfList, Finset.mem_image, List.mem_toFinset, List.mem_filter]
    constructor <;> rintro ⟨a, ha, rfl⟩
    · exact ⟨a, ⟨(h.mem_iff.mp ha.1), ha.2⟩, rfl⟩
    · exact ⟨a, ⟨(h.mem_iff.mpr ha.1), ha.2⟩, rfl⟩
  · simp only [stateOfList, Finset.mem_image, List.mem_toFinset, List.mem_filter]
    constructor <;> rintro ⟨a, ha, rfl⟩
    · exact ⟨a, ⟨(h.mem_iff.mp ha.1), ha.2⟩, rfl⟩
    · exact ⟨a, ⟨(h.mem_iff.mpr ha.1), ha.2⟩, rfl⟩

def negateList {N : ℕ} (l : List (Atom N)) : List (Atom N) := l.map Atom.negate

@[simp] lemma negateList_nil {N : ℕ} : negateList ([] : List (Atom N)) = [] := rfl

@[simp] lemma negateList_negateList {N : ℕ} (l : List (Atom N)) :
    negateList (negateList l) = l := by
  change (l.map Atom.negate).map Atom.negate = l
  rw [List.map_map]
  have hfun : Atom.negate ∘ Atom.negate = (id : Atom N → Atom N) := by
    funext a
    exact Atom.negate_negate a
  rw [hfun, List.map_id]

lemma stateOfList_negateList {N : ℕ} (l : List (Atom N)) :
    stateOfList (negateList l) = (stateOfList l).negate := by
  ext
  · simp only [stateOfList, negateList, SignVector.negate_pos, SignVector.negate_neg,
      Finset.mem_image, List.mem_toFinset, List.mem_filter, List.mem_map]
    constructor
    · rintro ⟨a, ⟨⟨b, hb, rfl⟩, ha⟩, rfl⟩
      refine ⟨b, ⟨hb, ?_⟩, rfl⟩
      obtain ⟨i, sb⟩ := b
      cases sb <;> simp_all [Atom.negate]
    · rintro ⟨b, ⟨hb, hsign⟩, rfl⟩
      refine ⟨Atom.negate b, ⟨⟨b, hb, rfl⟩, ?_⟩, rfl⟩
      obtain ⟨i, sb⟩ := b
      cases sb <;> simp_all [Atom.negate]
  · simp only [stateOfList, negateList, SignVector.negate_pos, SignVector.negate_neg,
      Finset.mem_image, List.mem_toFinset, List.mem_filter, List.mem_map]
    constructor
    · rintro ⟨a, ⟨⟨b, hb, rfl⟩, ha⟩, rfl⟩
      refine ⟨b, ⟨hb, ?_⟩, rfl⟩
      obtain ⟨i, sb⟩ := b
      cases sb <;> simp_all [Atom.negate]
    · rintro ⟨b, ⟨hb, hsign⟩, rfl⟩
      refine ⟨Atom.negate b, ⟨⟨b, hb, rfl⟩, ?_⟩, rfl⟩
      obtain ⟨i, sb⟩ := b
      cases sb <;> simp_all [Atom.negate]

/-- Signed sequences never reuse an absolute coordinate. -/
def SignedSequence (N : ℕ) :=
  {l : List (Atom N) // (l.map Prod.fst).Nodup}

instance (N : ℕ) : DecidableEq (SignedSequence N) := Classical.decEq _

instance (N : ℕ) : Fintype (SignedSequence N) := by
  let e : SignedSequence N → {l : List (Atom N) // l.Nodup} := fun l ↦
    ⟨l.1, l.2.of_map Prod.fst⟩
  exact Fintype.ofInjective e (by
    intro l r h
    apply Subtype.ext
    exact congrArg (fun x : {l : List (Atom N) // l.Nodup} ↦ x.1) h)

def SignedSequence.nil (N : ℕ) : SignedSequence N := ⟨[], by simp⟩

@[simp] lemma SignedSequence.coe_nil {N : ℕ} : (SignedSequence.nil N).1 = [] := rfl

def SignedSequence.negate {N : ℕ} (s : SignedSequence N) : SignedSequence N :=
  ⟨negateList s.1, by
    have hf : Prod.fst ∘ Atom.negate = (Prod.fst : Atom N → Fin N) := by
      funext a
      rfl
    rw [negateList, List.map_map]
    simpa only [hf] using s.2⟩

@[simp] lemma SignedSequence.coe_negate {N : ℕ} (s : SignedSequence N) :
    s.negate.1 = negateList s.1 := rfl

@[simp] lemma SignedSequence.negate_negate {N : ℕ} (s : SignedSequence N) :
    s.negate.negate = s := by
  apply Subtype.ext
  exact negateList_negateList s.1

@[simp] lemma SignedSequence.length_negate {N : ℕ} (s : SignedSequence N) :
    s.negate.1.length = s.1.length := by
  simp [SignedSequence.negate, negateList]

lemma SignedSequence.length_le {N : ℕ} (s : SignedSequence N) : s.1.length ≤ N := by
  have hcard := s.2.length_le_card
  simpa using hcard

/-- The state after the first `i` signed coordinates. -/
def prefixState {N : ℕ} (s : SignedSequence N) (i : ℕ) : SignVector N :=
  stateOfList (s.1.take i)

lemma prefixState_consistent {N : ℕ} (s : SignedSequence N) (i : ℕ) :
    (prefixState s i).Consistent := by
  apply stateOfList_consistent
  rw [List.map_take]
  exact List.Nodup.sublist (List.take_sublist i _) s.2

@[simp] lemma prefixState_zero {N : ℕ} (s : SignedSequence N) :
    prefixState s 0 = .zero N := by simp [prefixState]

@[simp] lemma prefixState_length {N : ℕ} (s : SignedSequence N) :
    prefixState s s.1.length = stateOfList s.1 := by simp [prefixState]

def labelSequence {N : ℕ} (label : SignVector N → Atom N)
    (s : SignedSequence N) : List (Atom N) :=
  (List.range (s.1.length + 1)).map fun i ↦ label (prefixState s i)

@[simp] lemma length_labelSequence {N : ℕ} (label : SignVector N → Atom N)
    (s : SignedSequence N) : (labelSequence label s).length = s.1.length + 1 := by
  simp [labelSequence]

/-- Every term of the signed sequence occurs among its prefix labels. -/
def Permissible {N : ℕ} (label : SignVector N → Atom N)
    (s : SignedSequence N) : Prop :=
  ∀ a ∈ s.1, a ∈ labelSequence label s

def PermissibleSequence {N : ℕ} (label : SignVector N → Atom N) :=
  {s : SignedSequence N // Permissible label s}

instance {N : ℕ} (label : SignVector N → Atom N) :
    Fintype (PermissibleSequence label) :=
  Fintype.ofInjective (fun s ↦ s.1) Subtype.val_injective

instance {N : ℕ} (label : SignVector N → Atom N) :
    DecidableEq (PermissibleSequence label) := Classical.decEq _

lemma mem_take_mono {N : ℕ} {a : Atom N} {l : List (Atom N)} {i j : ℕ}
    (hij : i ≤ j) (ha : a ∈ l.take i) : a ∈ l.take j := by
  rw [List.mem_take_iff_getElem] at ha ⊢
  obtain ⟨q, hq, hqa⟩ := ha
  exact ⟨q, by omega, hqa⟩

lemma prefixState_mono {N : ℕ} (s : SignedSequence N) {i j : ℕ}
    (hij : i ≤ j) : prefixState s i ≤ prefixState s j := by
  constructor
  · intro x hx
    simp only [prefixState, stateOfList, Finset.mem_image, List.mem_toFinset,
      List.mem_filter] at hx ⊢
    obtain ⟨a, ⟨ha, hsign⟩, rfl⟩ := hx
    exact ⟨a, ⟨mem_take_mono hij ha, hsign⟩, rfl⟩
  · intro x hx
    simp only [prefixState, stateOfList, Finset.mem_image, List.mem_toFinset,
      List.mem_filter] at hx ⊢
    obtain ⟨a, ⟨ha, hsign⟩, rfl⟩ := hx
    exact ⟨a, ⟨mem_take_mono hij ha, hsign⟩, rfl⟩

/-- No pair of comparable sign vectors receives complementary labels. -/
def NoComplement {N : ℕ} (label : SignVector N → Atom N) : Prop :=
  ∀ {X Y : SignVector N}, X.Consistent → Y.Consistent → X ≤ Y →
    label X ≠ Atom.negate (label Y)

/-- Antipodality away from the zero sign vector. -/
def Antipodal {N : ℕ} (label : SignVector N → Atom N) : Prop :=
  ∀ X : SignVector N, X.Consistent → X ≠ .zero N →
    label X.negate = Atom.negate (label X)

/-- The fresh absolute label at zero is not used at a nonzero sign vector. -/
def ZeroUniqueMagnitude {N : ℕ} (label : SignVector N → Atom N) : Prop :=
  ∀ X : SignVector N, X.Consistent →
    (label X).1 = (label (.zero N)).1 → X = .zero N

lemma label_prefix_ne_negate {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) (s : SignedSequence N) {i j : ℕ}
    (hij : i ≤ j) :
    label (prefixState s i) ≠ Atom.negate (label (prefixState s j)) :=
  hno (prefixState_consistent s i) (prefixState_consistent s j)
    (prefixState_mono s hij)

lemma label_eq_of_fst_eq_of_mem_labelSequence
    {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) (s : SignedSequence N)
    {a b : Atom N} (ha : a ∈ labelSequence label s)
    (hb : b ∈ labelSequence label s) (hab : a.1 = b.1) : a = b := by
  simp only [labelSequence, List.mem_map, List.mem_range] at ha hb
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  rcases Atom.eq_or_eq_negate_of_fst_eq hab with heq | heq
  · exact heq
  · rcases le_total i j with hij | hji
    · exact (label_prefix_ne_negate hno s hij heq).elim
    · have hneg : label (prefixState s j) =
          Atom.negate (label (prefixState s i)) := by
        rw [heq, Atom.negate_negate]
      exact (label_prefix_ne_negate hno s hji hneg).elim

lemma labelSequence_nodup_fst_iff_nodup
    {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) (s : SignedSequence N) :
    (labelSequence label s).Nodup ↔
      ((labelSequence label s).map Prod.fst).Nodup := by
  constructor
  · intro h
    exact h.map_on fun a ha b hb hab ↦
      label_eq_of_fst_eq_of_mem_labelSequence hno s ha hb hab
  · exact List.Nodup.of_map Prod.fst

lemma atom_mem_labelSequence_of_permissible
    {N : ℕ} {label : SignVector N → Atom N}
    {s : SignedSequence N} (hs : Permissible label s) {a : Atom N}
    (ha : a ∈ s.1) : a ∈ labelSequence label s := hs a ha

abbrev LabelIndex {N : ℕ} (s : SignedSequence N) := Fin (s.1.length + 1)
abbrev EntryIndex {N : ℕ} (s : SignedSequence N) := Fin s.1.length

def prefixLabel {N : ℕ} (label : SignVector N → Atom N)
    (s : SignedSequence N) (i : LabelIndex s) : Atom N :=
  label (prefixState s i)

def entryAt {N : ℕ} (s : SignedSequence N) (i : EntryIndex s) : Atom N :=
  s.1[i]

lemma mem_labelSequence_iff {N : ℕ} {label : SignVector N → Atom N}
    {s : SignedSequence N} {a : Atom N} :
    a ∈ labelSequence label s ↔ ∃ i : LabelIndex s, prefixLabel label s i = a := by
  simp only [labelSequence, List.mem_map, List.mem_range, prefixLabel]
  constructor
  · rintro ⟨i, hi, hia⟩
    exact ⟨⟨i, hi⟩, hia⟩
  · rintro ⟨⟨i, hi⟩, hia⟩
    exact ⟨i, hi, hia⟩

lemma exists_prefixLabel_eq_entryAt_of_permissible
    {N : ℕ} {label : SignVector N → Atom N}
    {s : SignedSequence N} (hs : Permissible label s) (e : EntryIndex s) :
    ∃ i : LabelIndex s, prefixLabel label s i = entryAt s e := by
  rw [← mem_labelSequence_iff]
  exact hs _ (List.getElem_mem ..)

lemma entryAt_injective {N : ℕ} (s : SignedSequence N) :
    Function.Injective (entryAt s) := by
  intro i j hij
  apply Fin.ext
  exact (s.2.of_map Prod.fst).getElem_inj_iff.mp hij

def IsExtra {N : ℕ} (label : SignVector N → Atom N)
    (s : SignedSequence N) (i : LabelIndex s) : Prop :=
  ∀ e : EntryIndex s, prefixLabel label s i ≠ entryAt s e

def IsRepeated {N : ℕ} (label : SignVector N → Atom N)
    (s : SignedSequence N) (i : LabelIndex s) : Prop :=
  ∃ j : LabelIndex s, j ≠ i ∧ prefixLabel label s j = prefixLabel label s i

def IsRedundant {N : ℕ} (label : SignVector N → Atom N)
    (s : SignedSequence N) (i : LabelIndex s) : Prop :=
  IsExtra label s i ∨ IsRepeated label s i

/-- The elementary pigeonhole classification underlying the two-neighbor
argument: the `m+1` prefix labels cover the `m` distinct sequence entries, so
either one label is extra or exactly one entry label is repeated. -/
lemma prefixLabel_classification
    {N : ℕ} {label : SignVector N → Atom N}
    {s : SignedSequence N} (hs : Permissible label s) :
    (∃ q : LabelIndex s,
      IsExtra label s q ∧
      (∀ i, IsExtra label s i ↔ i = q) ∧
      (∀ i, IsRedundant label s i ↔ i = q)) ∨
    (∃ p q : LabelIndex s, p ≠ q ∧
      prefixLabel label s p = prefixLabel label s q ∧
      (∀ i, ¬ IsExtra label s i) ∧
      (∀ i, IsRedundant label s i ↔ i = p ∨ i = q)) := by
  let pick : EntryIndex s → LabelIndex s := fun e ↦
    Classical.choose (exists_prefixLabel_eq_entryAt_of_permissible hs e)
  have hpick (e : EntryIndex s) :
      prefixLabel label s (pick e) = entryAt s e :=
    Classical.choose_spec (exists_prefixLabel_eq_entryAt_of_permissible hs e)
  have hpickInj : Function.Injective pick := by
    intro e f hef
    apply entryAt_injective s
    rw [← hpick e, ← hpick f, hef]
  let used : Finset (LabelIndex s) := Finset.univ.image pick
  let missing : Finset (LabelIndex s) := Finset.univ \ used
  have hmissingCard : missing.card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have hused : used.card = Fintype.card (EntryIndex s) := by
      rw [show used = Finset.univ.image pick from rfl,
        Finset.card_image_of_injective _ hpickInj, Finset.card_univ]
    rw [hused]
    simp
  obtain ⟨q, hmissing⟩ := Finset.card_eq_one.mp hmissingCard
  have hqNot : q ∉ used := by
    have : q ∈ missing := by simp [hmissing]
    exact (Finset.mem_sdiff.mp this).2
  have hnotRange_iff (i : LabelIndex s) : i ∉ used ↔ i = q := by
    constructor
    · intro hi
      have : i ∈ missing := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
      simpa [hmissing] using this
    · rintro rfl
      exact hqNot
  by_cases hqExtra : IsExtra label s q
  · left
    refine ⟨q, hqExtra, ?_, ?_⟩
    · intro i
      constructor
      · intro hi
        apply (hnotRange_iff i).mp
        intro hirange
        obtain ⟨e, -, he⟩ := Finset.mem_image.mp hirange
        exact hi e (by rw [← hpick e, he])
      · rintro rfl
        exact hqExtra
    · intro i
      constructor
      · rintro (hi | hi)
        · exact (hnotRange_iff i).mp fun hirange ↦ by
            obtain ⟨e, -, he⟩ := Finset.mem_image.mp hirange
            exact hi e (by rw [← hpick e, he])
        · obtain ⟨j, hji, hlabel⟩ := hi
          have hiRange : i ∈ used := by
            by_contra hir
            have hiq := (hnotRange_iff i).mp hir
            subst i
            have hjRange : j ∈ used := by
              by_contra hjr
              exact hji ((hnotRange_iff j).mp hjr)
            obtain ⟨e, -, he⟩ := Finset.mem_image.mp hjRange
            exact hqExtra e (by rw [← hpick e, he, hlabel])
          obtain ⟨e, -, he⟩ := Finset.mem_image.mp hiRange
          have hjRange : j ∈ used := by
            by_contra hjr
            have hjq := (hnotRange_iff j).mp hjr
            subst j
            exact hqExtra e (by rw [← hpick e, he, hlabel])
          obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hjRange
          have : e = f := entryAt_injective s (by rw [← hpick e, ← hpick f, he, hf, hlabel])
          subst f
          exact (hji (he.symm.trans hf).symm).elim
      · rintro rfl
        exact Or.inl hqExtra
  · right
    unfold IsExtra at hqExtra
    push_neg at hqExtra
    obtain ⟨e, hqe⟩ := hqExtra
    let p := pick e
    have hpq : p ≠ q := by
      intro h
      exact hqNot (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, h⟩)
    have hpqlabel : prefixLabel label s p = prefixLabel label s q := by
      rw [hpick e]
      exact hqe.symm
    refine ⟨p, q, hpq, hpqlabel, ?_, ?_⟩
    · intro i hi
      have hiRange : i ∈ used := by
        by_contra hir
        have : i = q := (hnotRange_iff i).mp hir
        exact hi e (by simpa [this] using hqe)
      obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hiRange
      exact hi f (by rw [← hpick f, hf])
    · intro i
      constructor
      · rintro (hi | ⟨j, hji, hij⟩)
        · have hiRange : i ∈ used := by
            by_contra hir
            have hiq : i = q := (hnotRange_iff i).mp hir
            exact hi e (by simpa [hiq] using hqe)
          obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hiRange
          exact (hi f (by rw [← hpick f, hf])).elim
        by_cases hiq : i = q
        · exact Or.inr hiq
        have hiRange : i ∈ used := by
          by_contra hir
          exact hiq ((hnotRange_iff i).mp hir)
        obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hiRange
        by_cases hjq : j = q
        · left
          subst j
          have hef : e = f := entryAt_injective s (by
            rw [← hpick e, ← hpick f, hpqlabel, hf, hij])
          change i = pick e
          rw [← hf, hef]
        have hjRange : j ∈ used := by
          by_contra hjr
          exact hjq ((hnotRange_iff j).mp hjr)
        obtain ⟨g, -, hg⟩ := Finset.mem_image.mp hjRange
        have hfg : f = g := by
          apply entryAt_injective s
          rw [← hpick f, ← hpick g, hf, hg, hij]
        subst g
        exact (hji (hf.symm.trans hg).symm).elim
      · rintro (rfl | rfl)
        · exact Or.inr ⟨q, hpq.symm, hpqlabel.symm⟩
        · exact Or.inr ⟨p, hpq, hpqlabel⟩

lemma extra_index_unique {N : ℕ} {label : SignVector N → Atom N}
    {s : SignedSequence N} (hs : Permissible label s)
    {i j : LabelIndex s} (hi : IsExtra label s i) (hj : IsExtra label s j) :
    i = j := by
  rcases prefixLabel_classification hs with h | h
  · obtain ⟨q, -, hextra, -⟩ := h
    exact ((hextra i).mp hi).trans ((hextra j).mp hj).symm
  · obtain ⟨-, -, -, -, hnoextra, -⟩ := h
    exact (hnoextra i hi).elim

/-! ## Elementary operations on signed sequences -/

def SignedSequence.appendAtom {N : ℕ} (s : SignedSequence N) (a : Atom N)
    (ha : a.1 ∉ s.1.map Prod.fst) : SignedSequence N :=
  ⟨s.1 ++ [a], by
    simp only [List.map_append, List.map_singleton, List.nodup_append,
      List.nodup_singleton]
    refine ⟨s.2, True.intro, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    intro hxa
    subst x
    exact ha hx⟩

@[simp] lemma SignedSequence.coe_appendAtom {N : ℕ} (s : SignedSequence N)
    (a : Atom N) (ha) : (s.appendAtom a ha).1 = s.1 ++ [a] := rfl

def SignedSequence.dropLast {N : ℕ} (s : SignedSequence N) : SignedSequence N :=
  ⟨s.1.dropLast, by
    rw [List.map_dropLast]
    exact s.2.sublist (List.dropLast_sublist _)⟩

@[simp] lemma SignedSequence.coe_dropLast {N : ℕ} (s : SignedSequence N) :
    s.dropLast.1 = s.1.dropLast := rfl

@[simp] lemma SignedSequence.length_dropLast {N : ℕ} (s : SignedSequence N) :
    s.dropLast.1.length = s.1.length - 1 := by
  simp [SignedSequence.dropLast]

/-- Exchange entries `i` and `i+1`. -/
def swapAdjacentList {N : ℕ} (l : List (Atom N)) (i : ℕ)
    (hi : i + 1 < l.length) : List (Atom N) :=
  l.take i ++ l[i + 1] :: l[i] :: l.drop (i + 2)

lemma list_eq_take_two_drop {N : ℕ} (l : List (Atom N)) (i : ℕ)
    (hi : i + 1 < l.length) :
    l = l.take i ++ l[i] :: l[i + 1] :: l.drop (i + 2) := by
  calc
    l = l.take i ++ l.drop i := (List.take_append_drop i l).symm
    _ = l.take i ++ l[i] :: l.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by omega : i < l.length)]
    _ = l.take i ++ l[i] :: l[i + 1] :: l.drop (i + 2) := by
      rw [List.drop_eq_getElem_cons hi]

lemma swapAdjacentList_perm {N : ℕ} (l : List (Atom N)) (i : ℕ)
    (hi : i + 1 < l.length) : (swapAdjacentList l i hi).Perm l := by
  have hswap :
      (l.take i ++ l[i + 1] :: l[i] :: l.drop (i + 2)).Perm
        (l.take i ++ l[i] :: l[i + 1] :: l.drop (i + 2)) :=
    List.Perm.append_left _ (List.Perm.swap _ _ _)
  have hdecomp :
      (l.take i ++ l[i] :: l[i + 1] :: l.drop (i + 2)).Perm l := by
    rw [← list_eq_take_two_drop l i hi]
  exact hswap.trans hdecomp

def SignedSequence.swapAdjacent {N : ℕ} (s : SignedSequence N) (i : ℕ)
    (hi : i + 1 < s.1.length) : SignedSequence N :=
  ⟨swapAdjacentList s.1 i hi, by
    exact ((swapAdjacentList_perm s.1 i hi).map Prod.fst).nodup_iff.mpr s.2⟩

@[simp] lemma SignedSequence.coe_swapAdjacent {N : ℕ} (s : SignedSequence N)
    (i : ℕ) (hi) : (s.swapAdjacent i hi).1 = swapAdjacentList s.1 i hi := rfl

@[simp] lemma length_swapAdjacentList {N : ℕ} (l : List (Atom N)) (i : ℕ)
    (hi : i + 1 < l.length) : (swapAdjacentList l i hi).length = l.length := by
  exact (swapAdjacentList_perm l i hi).length_eq

@[simp] lemma SignedSequence.length_swapAdjacent {N : ℕ} (s : SignedSequence N)
    (i : ℕ) (hi) : (s.swapAdjacent i hi).1.length = s.1.length := by
  simp [SignedSequence.swapAdjacent]

@[simp] lemma SignedSequence.length_appendAtom {N : ℕ} (s : SignedSequence N)
    (a : Atom N) (ha) : (s.appendAtom a ha).1.length = s.1.length + 1 := by
  simp [SignedSequence.appendAtom]

lemma prefixState_appendAtom_of_le {N : ℕ} (s : SignedSequence N) (a : Atom N)
    (ha) {j : ℕ} (hj : j ≤ s.1.length) :
    prefixState (s.appendAtom a ha) j = prefixState s j := by
  simp only [prefixState, SignedSequence.coe_appendAtom]
  rw [List.take_append_of_le_length hj]

lemma prefixState_dropLast_of_le {N : ℕ} (s : SignedSequence N) {j : ℕ}
    (hj : j ≤ s.1.length - 1) :
    prefixState s.dropLast j = prefixState s j := by
  simp only [prefixState, SignedSequence.coe_dropLast, List.dropLast_eq_take,
    List.take_take]
  rw [Nat.min_eq_left hj]

lemma prefixState_negate {N : ℕ} (s : SignedSequence N) (j : ℕ) :
    prefixState s.negate j = (prefixState s j).negate := by
  simp only [prefixState, SignedSequence.coe_negate, negateList, List.map_take]
  rw [← List.map_take]
  exact stateOfList_negateList (s.1.take j)

lemma take_swapAdjacentList_of_le {N : ℕ} (l : List (Atom N)) (i : ℕ)
    (hi : i + 1 < l.length) {j : ℕ} (hj : j ≤ i) :
    (swapAdjacentList l i hi).take j = l.take j := by
  have hil : i ≤ l.length := by omega
  have hlen : (l.take i).length = i := List.length_take_of_le hil
  have hjlen : j ≤ (l.take i).length := by simpa [hlen] using hj
  simp only [swapAdjacentList]
  rw [List.take_append_of_le_length hjlen, List.take_take,
    Nat.min_eq_left hj]

lemma drop_swapAdjacentList_of_le {N : ℕ} (l : List (Atom N)) (i : ℕ)
    (hi : i + 1 < l.length) {j : ℕ} (hj : i + 2 ≤ j) :
    (swapAdjacentList l i hi).drop j = l.drop j := by
  have hil : i ≤ l.length := by omega
  have hlen : (l.take i).length = i := List.length_take_of_le hil
  have hbase : (swapAdjacentList l i hi).drop (i + 2) = l.drop (i + 2) := by
    simp [swapAdjacentList, List.drop_append, hlen]
  calc
    (swapAdjacentList l i hi).drop j =
        ((swapAdjacentList l i hi).drop (i + 2)).drop (j - (i + 2)) := by
      rw [List.drop_drop, Nat.add_sub_of_le hj]
    _ = (l.drop (i + 2)).drop (j - (i + 2)) := by rw [hbase]
    _ = l.drop j := by rw [List.drop_drop, Nat.add_sub_of_le hj]

@[simp] lemma getElem_swapAdjacentList_left {N : ℕ} (l : List (Atom N)) (i : ℕ)
    (hi : i + 1 < l.length) :
    (swapAdjacentList l i hi)[i]'(by rw [length_swapAdjacentList]; omega) = l[i + 1] := by
  have hmin : min i l.length = i := Nat.min_eq_left (by omega)
  simp [swapAdjacentList, List.length_take, hmin]

@[simp] lemma getElem_swapAdjacentList_right {N : ℕ} (l : List (Atom N)) (i : ℕ)
    (hi : i + 1 < l.length) :
    (swapAdjacentList l i hi)[i + 1]'(by rw [length_swapAdjacentList]; omega) = l[i] := by
  have hmin : min i l.length = i := Nat.min_eq_left (by omega)
  simp [swapAdjacentList, List.length_take, hmin]

lemma swapAdjacentList_involutive {N : ℕ} (l : List (Atom N)) (i : ℕ)
    (hi : i + 1 < l.length) :
    swapAdjacentList (swapAdjacentList l i hi) i (by simpa using hi) = l := by
  let l' := swapAdjacentList l i hi
  have hi' : i + 1 < l'.length := by simpa [l'] using hi
  change swapAdjacentList l' i hi' = l
  rw [show swapAdjacentList l' i hi' =
      l'.take i ++ l'[i + 1] :: l'[i] :: l'.drop (i + 2) from rfl,
    take_swapAdjacentList_of_le l i hi le_rfl,
    getElem_swapAdjacentList_right l i hi,
    getElem_swapAdjacentList_left l i hi,
    drop_swapAdjacentList_of_le l i hi (by omega)]
  exact (list_eq_take_two_drop l i hi).symm

lemma SignedSequence.swapAdjacent_involutive {N : ℕ} (s : SignedSequence N) (i : ℕ)
    (hi : i + 1 < s.1.length) :
    (s.swapAdjacent i hi).swapAdjacent i (by simpa using hi) = s := by
  apply Subtype.ext
  exact swapAdjacentList_involutive s.1 i hi

lemma prefixState_swapAdjacent_of_ne {N : ℕ} (s : SignedSequence N) (i : ℕ)
    (hi : i + 1 < s.1.length) {j : ℕ} (hj : j ≠ i + 1) :
    prefixState (s.swapAdjacent i hi) j = prefixState s j := by
  simp only [prefixState, SignedSequence.coe_swapAdjacent]
  by_cases hji : j ≤ i
  · rw [take_swapAdjacentList_of_le _ _ _ hji]
  · have hij : i + 2 ≤ j := by omega
    apply stateOfList_perm
    exact (swapAdjacentList_perm s.1 i hi).take
      (List.Perm.of_eq (drop_swapAdjacentList_of_le s.1 i hi hij))

lemma isExtra_iff_forall_mem {N : ℕ} {label : SignVector N → Atom N}
    {s : SignedSequence N} {i : LabelIndex s} :
    IsExtra label s i ↔ ∀ a ∈ s.1, prefixLabel label s i ≠ a := by
  constructor
  · intro h a ha
    obtain ⟨e, he⟩ := List.mem_iff_get.mp ha
    exact fun hieq ↦ h e (by simpa [entryAt] using hieq.trans he.symm)
  · intro h e
    exact h _ (List.get_mem _ _)

lemma extra_fst_not_mem {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) {s : SignedSequence N} (hs : Permissible label s)
    {i : LabelIndex s} (hi : IsExtra label s i) :
    (prefixLabel label s i).1 ∉ s.1.map Prod.fst := by
  intro hmem
  simp only [List.mem_map] at hmem
  obtain ⟨a, ha, hafst⟩ := hmem
  have hla : a ∈ labelSequence label s := hs a ha
  have hli : prefixLabel label s i ∈ labelSequence label s :=
    mem_labelSequence_iff.mpr ⟨i, rfl⟩
  have heq : prefixLabel label s i = a :=
    label_eq_of_fst_eq_of_mem_labelSequence hno s hli hla hafst.symm
  exact (isExtra_iff_forall_mem.mp hi a ha) heq

lemma permissible_append_extra {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) {s : SignedSequence N} (hs : Permissible label s)
    (i : LabelIndex s) (hi : IsExtra label s i) :
    Permissible label
      (s.appendAtom (prefixLabel label s i) (extra_fst_not_mem hno hs hi)) := by
  let a := prefixLabel label s i
  let ha := extra_fst_not_mem hno hs hi
  let t := s.appendAtom a ha
  intro b hb
  have hb' : b ∈ s.1 ∨ b = a := by
    simpa [t, a] using hb
  rw [mem_labelSequence_iff]
  rcases hb' with hbs | rfl
  · obtain ⟨j, hj⟩ := mem_labelSequence_iff.mp (hs b hbs)
    let j' : LabelIndex t := ⟨j, by simp [t]⟩
    refine ⟨j', ?_⟩
    change label (prefixState t j') = b
    rw [show prefixState t j' = prefixState s j by
      apply prefixState_appendAtom_of_le
      exact Nat.le_of_lt_succ j.isLt]
    exact hj
  · let i' : LabelIndex t := ⟨i, by simp [t]⟩
    refine ⟨i', ?_⟩
    change label (prefixState t i') = a
    rw [show prefixState t i' = prefixState s i by
      apply prefixState_appendAtom_of_le
      exact Nat.le_of_lt_succ i.isLt]
    rfl

@[simp] lemma SignedSequence.dropLast_appendAtom {N : ℕ} (s : SignedSequence N)
    (a : Atom N) (ha) : (s.appendAtom a ha).dropLast = s := by
  apply Subtype.ext
  simp [SignedSequence.appendAtom, SignedSequence.dropLast]

lemma last_redundant_append_extra {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) {s : SignedSequence N} (hs : Permissible label s)
    (i : LabelIndex s) (hi : IsExtra label s i) :
    let t := s.appendAtom (prefixLabel label s i) (extra_fst_not_mem hno hs hi)
    IsRedundant label t ⟨t.1.length, by omega⟩ := by
  let a := prefixLabel label s i
  let ha := extra_fst_not_mem hno hs hi
  let t := s.appendAtom a ha
  let p : LabelIndex t := ⟨t.1.length, by omega⟩
  change IsRedundant label t p
  by_cases he : IsExtra label t p
  · exact Or.inl he
  · right
    unfold IsExtra at he
    push Not at he
    obtain ⟨e, he⟩ := he
    have het : entryAt t e ∈ t.1 := List.getElem_mem ..
    have het' : entryAt t e ∈ s.1 ∨ entryAt t e = a := by
      simpa [t, a] using het
    rcases het' with hes | hea
    · obtain ⟨u, hu⟩ := mem_labelSequence_iff.mp (hs _ hes)
      let u' : LabelIndex t := ⟨u, by simp [t]⟩
      refine ⟨u', ?_, ?_⟩
      · intro hup
        have := congrArg Fin.val hup
        change (u : ℕ) = t.1.length at this
        have htlen : t.1.length = s.1.length + 1 := by simp [t]
        rw [htlen] at this
        omega
      · change label (prefixState t u') = label (prefixState t p)
        rw [show prefixState t u' = prefixState s u by
          apply prefixState_appendAtom_of_le
          exact Nat.le_of_lt_succ u.isLt]
        exact hu.trans he.symm
    · let i' : LabelIndex t := ⟨i, by simp [t]⟩
      refine ⟨i', ?_, ?_⟩
      · intro hip
        have := congrArg Fin.val hip
        change (i : ℕ) = t.1.length at this
        have htlen : t.1.length = s.1.length + 1 := by simp [t]
        rw [htlen] at this
        omega
      · change label (prefixState t i') = label (prefixState t p)
        rw [show prefixState t i' = prefixState s i by
          apply prefixState_appendAtom_of_le
          exact Nat.le_of_lt_succ i.isLt]
        exact hea.symm.trans he.symm

lemma permissible_swap_redundant {N : ℕ} {label : SignVector N → Atom N}
    {s : SignedSequence N} (hs : Permissible label s) (q : ℕ)
    (hq : q + 1 < s.1.length)
    (hr : IsRedundant label s ⟨q + 1, by omega⟩) :
    Permissible label (s.swapAdjacent q hq) := by
  let p : LabelIndex s := ⟨q + 1, by omega⟩
  let t := s.swapAdjacent q hq
  intro a hat
  have has : a ∈ s.1 := (swapAdjacentList_perm s.1 q hq).mem_iff.mp hat
  obtain ⟨j, hj⟩ := mem_labelSequence_iff.mp (hs a has)
  rw [mem_labelSequence_iff]
  have lift_of_ne (u : LabelIndex s) (hu : (u : ℕ) ≠ q + 1)
      (hua : prefixLabel label s u = a) :
      ∃ u' : LabelIndex t, prefixLabel label t u' = a := by
    let u' : LabelIndex t := ⟨u, by simpa [t] using u.isLt⟩
    refine ⟨u', ?_⟩
    change label (prefixState t u') = a
    rw [show prefixState t u' = prefixState s u by
      apply prefixState_swapAdjacent_of_ne
      exact hu]
    exact hua
  by_cases hjp : (j : ℕ) = q + 1
  · have hjeq : j = p := Fin.ext hjp
    subst j
    rcases hr with he | ⟨u, hup, hu⟩
    · exact (isExtra_iff_forall_mem.mp he a has hj).elim
    · apply lift_of_ne u
      · intro hueq
        exact hup (Fin.ext hueq)
      · exact hu.trans hj
  · exact lift_of_ne j hjp hj

lemma redundant_swap_redundant {N : ℕ} {label : SignVector N → Atom N}
    {s : SignedSequence N} (hs : Permissible label s) (q : ℕ)
    (hq : q + 1 < s.1.length)
    (hr : IsRedundant label s ⟨q + 1, by omega⟩) :
    IsRedundant label (s.swapAdjacent q hq) ⟨q + 1, by simpa using (show q + 1 < s.1.length + 1 by omega)⟩ := by
  let p : LabelIndex s := ⟨q + 1, by omega⟩
  let t := s.swapAdjacent q hq
  let p' : LabelIndex t := ⟨q + 1, by simp [t]; omega⟩
  change IsRedundant label t p'
  by_cases he : IsExtra label t p'
  · exact Or.inl he
  · right
    unfold IsExtra at he
    push Not at he
    obtain ⟨e, he⟩ := he
    have het : entryAt t e ∈ t.1 := List.getElem_mem ..
    have hes : entryAt t e ∈ s.1 :=
      (swapAdjacentList_perm s.1 q hq).mem_iff.mp het
    obtain ⟨u, hu⟩ := mem_labelSequence_iff.mp (hs _ hes)
    have lift_outside (v : LabelIndex s) (hv : (v : ℕ) ≠ q + 1) :
        ∃ v' : LabelIndex t,
          v' ≠ p' ∧ prefixLabel label t v' = prefixLabel label s v := by
      let v' : LabelIndex t := ⟨v, by simpa [t] using v.isLt⟩
      refine ⟨v', ?_, ?_⟩
      · intro hvp
        exact hv (congrArg Fin.val hvp)
      · change label (prefixState t v') = label (prefixState s v)
        rw [show prefixState t v' = prefixState s v by
          apply prefixState_swapAdjacent_of_ne
          exact hv]
    by_cases hup : (u : ℕ) = q + 1
    · have hueq : u = p := Fin.ext hup
      subst u
      have hsp : prefixLabel label s p = prefixLabel label t p' := hu.trans he.symm
      rcases hr with hex | ⟨v, hvp, hv⟩
      · exact (isExtra_iff_forall_mem.mp hex _ hes hu).elim
      · have hvval : (v : ℕ) ≠ q + 1 := by
          intro h
          exact hvp (Fin.ext h)
        obtain ⟨v', hvp', hv'⟩ := lift_outside v hvval
        exact ⟨v', hvp', hv'.trans (hv.trans hsp)⟩
    · obtain ⟨u', hup', hu'⟩ := lift_outside u hup
      exact ⟨u', hup', hu'.trans (hu.trans he.symm)⟩

lemma permissible_dropLast_redundant {N : ℕ} {label : SignVector N → Atom N}
    {s : SignedSequence N} (hs : Permissible label s)
    (hpos : 0 < s.1.length)
    (hr : IsRedundant label s ⟨s.1.length, by omega⟩) :
    Permissible label s.dropLast := by
  let p : LabelIndex s := ⟨s.1.length, by omega⟩
  let t := s.dropLast
  intro a hat
  have has : a ∈ s.1 := (List.dropLast_sublist s.1).subset hat
  obtain ⟨j, hj⟩ := mem_labelSequence_iff.mp (hs a has)
  rw [mem_labelSequence_iff]
  have lift_of_lt (u : LabelIndex s) (hu : (u : ℕ) < s.1.length)
      (hua : prefixLabel label s u = a) :
      ∃ u' : LabelIndex t, prefixLabel label t u' = a := by
    let u' : LabelIndex t := ⟨u, by simp [t]; omega⟩
    refine ⟨u', ?_⟩
    change label (prefixState t u') = a
    rw [show prefixState t u' = prefixState s u by
      apply prefixState_dropLast_of_le
      change (u : ℕ) ≤ s.1.length - 1
      omega]
    exact hua
  by_cases hjlt : (j : ℕ) < s.1.length
  · exact lift_of_lt j hjlt hj
  · have hjeq : j = p := by
      apply Fin.ext
      change (j : ℕ) = s.1.length
      omega
    subst j
    rcases hr with he | ⟨u, hup, hu⟩
    · exact (isExtra_iff_forall_mem.mp he a has hj).elim
    · apply lift_of_lt u
      · by_contra hult
        apply hup
        apply Fin.ext
        omega
      · exact hu.trans hj

def SignedSequence.lastAtom {N : ℕ} (s : SignedSequence N) (hne : s.1 ≠ []) :
    Atom N := s.1.getLast hne

lemma SignedSequence.lastAtom_mem {N : ℕ} (s : SignedSequence N) (hne : s.1 ≠ []) :
    s.lastAtom hne ∈ s.1 := List.getLast_mem hne

lemma SignedSequence.lastAtom_not_mem_dropLast {N : ℕ} (s : SignedSequence N)
    (hne : s.1 ≠ []) : s.lastAtom hne ∉ s.dropLast.1 := by
  intro hm
  exact ((s.2.of_map Prod.fst).rel_dropLast_getLast hm) rfl

lemma exists_extra_dropLast_of_last_redundant
    {N : ℕ} {label : SignVector N → Atom N}
    {s : SignedSequence N} (hs : Permissible label s) (hne : s.1 ≠ [])
    (hr : IsRedundant label s ⟨s.1.length, by omega⟩) :
    ∃ i : LabelIndex s.dropLast,
      IsExtra label s.dropLast i ∧
      prefixLabel label s.dropLast i = s.lastAtom hne := by
  let p : LabelIndex s := ⟨s.1.length, by omega⟩
  let a := s.lastAtom hne
  let t := s.dropLast
  have ha : a ∈ s.1 := s.lastAtom_mem hne
  obtain ⟨j, hj⟩ := mem_labelSequence_iff.mp (hs a ha)
  have make (u : LabelIndex s) (hu : (u : ℕ) < s.1.length)
      (hua : prefixLabel label s u = a) :
      ∃ i : LabelIndex t, IsExtra label t i ∧ prefixLabel label t i = a := by
    let i : LabelIndex t := ⟨u, by simp [t]; omega⟩
    have hilabel : prefixLabel label t i = a := by
      change label (prefixState t i) = a
      rw [show prefixState t i = prefixState s u by
        apply prefixState_dropLast_of_le
        change (u : ℕ) ≤ s.1.length - 1
        omega]
      exact hua
    refine ⟨i, ?_, hilabel⟩
    rw [isExtra_iff_forall_mem]
    intro b hb hib
    have : a ∈ t.1 := by rw [hilabel] at hib; simpa [hib] using hb
    exact s.lastAtom_not_mem_dropLast hne this
  by_cases hjlt : (j : ℕ) < s.1.length
  · exact make j hjlt hj
  · have hjp : j = p := by
      apply Fin.ext
      change (j : ℕ) = s.1.length
      omega
    subst j
    rcases hr with he | ⟨u, hup, hu⟩
    · exact (isExtra_iff_forall_mem.mp he a ha hj).elim
    · apply make u
      · by_contra hult
        apply hup
        apply Fin.ext
        omega
      · exact hu.trans hj

lemma SignedSequence.append_lastAtom_dropLast {N : ℕ} (s : SignedSequence N)
    (hne : s.1 ≠ []) (ha : (s.lastAtom hne).1 ∉ s.dropLast.1.map Prod.fst) :
    s.dropLast.appendAtom (s.lastAtom hne) ha = s := by
  apply Subtype.ext
  exact List.dropLast_append_getLast hne

lemma stateOfList_ne_zero_of_mem {N : ℕ} {l : List (Atom N)} {a : Atom N}
    (ha : a ∈ l) : stateOfList l ≠ .zero N := by
  rcases a with ⟨x, b⟩
  cases b
  · intro hzero
    have hx : x ∈ (stateOfList l).neg := by
      simp [stateOfList, ha]
    simpa [hzero, SignVector.zero] using hx
  · intro hzero
    have hx : x ∈ (stateOfList l).pos := by
      simp [stateOfList, ha]
    simpa [hzero, SignVector.zero] using hx

lemma prefixState_ne_zero_of_pos {N : ℕ} (s : SignedSequence N) (j : ℕ)
    (hj : 0 < j) (hjl : j ≤ s.1.length) :
    prefixState s j ≠ .zero N := by
  have hlen : 0 < s.1.length := hj.trans_le hjl
  apply stateOfList_ne_zero_of_mem (a := s.1[0])
  rw [List.mem_take_iff_getElem]
  refine ⟨0, ?_, rfl⟩
  simp [hj, hlen]

lemma permissible_negate_of_extra_zero {N : ℕ} {label : SignVector N → Atom N}
    (hanti : Antipodal label) {s : SignedSequence N} (hs : Permissible label s)
    (hzero : IsExtra label s ⟨0, by simp⟩) :
    Permissible label s.negate := by
  intro b hb
  simp only [SignedSequence.coe_negate, negateList, List.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  obtain ⟨j, hj⟩ := mem_labelSequence_iff.mp (hs a ha)
  have hjpos : 0 < (j : ℕ) := by
    by_contra hjn
    have hjval : (j : ℕ) = 0 := Nat.eq_zero_of_not_pos hjn
    have hjz : j = ⟨0, by simp⟩ := Fin.ext hjval
    subst j
    exact (isExtra_iff_forall_mem.mp hzero a ha hj).elim
  let j' : LabelIndex s.negate := ⟨j, by
    change (j : ℕ) < (negateList s.1).length + 1
    simpa [negateList] using j.isLt⟩
  rw [mem_labelSequence_iff]
  refine ⟨j', ?_⟩
  change label (prefixState s.negate j') = Atom.negate a
  rw [prefixState_negate]
  rw [hanti _ (prefixState_consistent s j)
    (prefixState_ne_zero_of_pos s j hjpos (by omega))]
  exact congrArg Atom.negate hj

lemma extra_zero_of_redundant {N : ℕ} {label : SignVector N → Atom N}
    (hzeroUnique : ZeroUniqueMagnitude label) {s : SignedSequence N}
    (hr : IsRedundant label s ⟨0, by simp⟩) :
    IsExtra label s ⟨0, by simp⟩ := by
  rcases hr with he | ⟨j, hj0, hj⟩
  · exact he
  · exfalso
    have hjpos : 0 < (j : ℕ) := by
      by_contra h
      apply hj0
      apply Fin.ext
      exact Nat.eq_zero_of_not_pos h
    have hstate : prefixState s j = .zero N := by
      apply hzeroUnique
      · exact prefixState_consistent s j
      have := congrArg Prod.fst hj
      simpa [prefixLabel, prefixState_zero] using this
    exact prefixState_ne_zero_of_pos s j hjpos (by omega) hstate

lemma extra_zero_negate {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) {s : SignedSequence N} (hs : Permissible label s)
    (hzero : IsExtra label s ⟨0, by simp⟩) :
    IsExtra label s.negate ⟨0, by simp⟩ := by
  rw [isExtra_iff_forall_mem]
  intro b hb hlabel
  simp only [SignedSequence.coe_negate, negateList, List.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  obtain ⟨j, hj⟩ := mem_labelSequence_iff.mp (hs a ha)
  have hc := hno (prefixState_consistent s 0) (prefixState_consistent s j)
    (prefixState_mono s (Nat.zero_le (j : ℕ)))
  apply hc
  change label (prefixState s 0) = Atom.negate (label (prefixState s j))
  have hj' : label (prefixState s (j : ℕ)) = a := hj
  rw [hj']
  simpa [prefixLabel, prefixState_zero] using hlabel

/-! ## Ports in the finite path argument -/

/-- A `true` port expands at an extra label.  A `false` port performs the
boundary operation attached to a redundant label; such a port is suppressed
at the empty sequence, where sign change would be a loop. -/
def PortAt {N : ℕ} (label : SignVector N → Atom N)
    (s : PermissibleSequence label) :=
  {i : LabelIndex s.1 // IsExtra label s.1 i} ⊕
    {i : LabelIndex s.1 // IsRedundant label s.1 i ∧ s.1.1 ≠ []}

instance {N : ℕ} (label : SignVector N → Atom N)
    (s : PermissibleSequence label) : Fintype (PortAt label s) := by
  classical
  unfold PortAt
  infer_instance

instance {N : ℕ} (label : SignVector N → Atom N)
    (s : PermissibleSequence label) : DecidableEq (PortAt label s) :=
  Classical.decEq _

def Ports {N : ℕ} (label : SignVector N → Atom N) :=
  Σ s : PermissibleSequence label, PortAt label s

instance {N : ℕ} (label : SignVector N → Atom N) : Fintype (Ports label) :=
  by
    classical
    unfold Ports
    infer_instance

instance {N : ℕ} (label : SignVector N → Atom N) : DecidableEq (Ports label) :=
  Classical.decEq _

def ExtraPorts {N : ℕ} (label : SignVector N → Atom N) :=
  Σ s : PermissibleSequence label,
    {i : LabelIndex s.1 // IsExtra label s.1 i}

def BoundaryPorts {N : ℕ} (label : SignVector N → Atom N) :=
  Σ s : PermissibleSequence label,
    {i : LabelIndex s.1 // IsRedundant label s.1 i ∧ s.1.1 ≠ []}

instance {N : ℕ} (label : SignVector N → Atom N) : Fintype (ExtraPorts label) := by
  classical unfold ExtraPorts; infer_instance

instance {N : ℕ} (label : SignVector N → Atom N) : Fintype (BoundaryPorts label) := by
  classical unfold BoundaryPorts; infer_instance

instance {N : ℕ} (label : SignVector N → Atom N) : DecidableEq (ExtraPorts label) :=
  Classical.decEq _

instance {N : ℕ} (label : SignVector N → Atom N) : DecidableEq (BoundaryPorts label) :=
  Classical.decEq _

def ZeroBoundaryPorts {N : ℕ} (label : SignVector N → Atom N) :=
  {p : BoundaryPorts label // (p.2.1 : ℕ) = 0}

def LastBoundaryPorts {N : ℕ} (label : SignVector N → Atom N) :=
  {p : BoundaryPorts label // (p.2.1 : ℕ) = p.1.1.1.length}

def InteriorBoundaryPorts {N : ℕ} (label : SignVector N → Atom N) :=
  {p : BoundaryPorts label //
    0 < (p.2.1 : ℕ) ∧ (p.2.1 : ℕ) < p.1.1.1.length}

instance {N : ℕ} (label : SignVector N → Atom N) :
    Fintype (ZeroBoundaryPorts label) := by
  classical unfold ZeroBoundaryPorts; infer_instance

instance {N : ℕ} (label : SignVector N → Atom N) :
    Fintype (LastBoundaryPorts label) := by
  classical unfold LastBoundaryPorts; infer_instance

instance {N : ℕ} (label : SignVector N → Atom N) :
    Fintype (InteriorBoundaryPorts label) := by
  classical unfold InteriorBoundaryPorts; infer_instance

def boundaryPortsEquiv {N : ℕ} (label : SignVector N → Atom N) :
    BoundaryPorts label ≃
      ZeroBoundaryPorts label ⊕ LastBoundaryPorts label ⊕ InteriorBoundaryPorts label where
  toFun p := if h0 : (p.2.1 : ℕ) = 0 then
      Sum.inl ⟨p, h0⟩
    else if hl : (p.2.1 : ℕ) = p.1.1.1.length then
      Sum.inr (Sum.inl ⟨p, hl⟩)
    else
      Sum.inr (Sum.inr ⟨p, by
        constructor
        · omega
        · have hp := p.2.1.isLt
          omega⟩)
  invFun := fun p ↦ match p with
    | Sum.inl p => p.1
    | Sum.inr (Sum.inl p) => p.1
    | Sum.inr (Sum.inr p) => p.1
  left_inv p := by
    dsimp only
    by_cases h0 : (p.2.1 : ℕ) = 0
    · rw [dif_pos h0]
    · rw [dif_neg h0]
      by_cases hl : (p.2.1 : ℕ) = p.1.1.1.length
      · rw [dif_pos hl]
      · rw [dif_neg hl]
  right_inv p := by
    rcases p with p | p
    · dsimp only
      rw [dif_pos p.2]
      congr 1
    · rcases p with p | p
      · have h0 : (p.1.2.1 : ℕ) ≠ 0 := by
          intro hq0
          apply p.1.2.2.2
          have hlen : p.1.1.1.1.length = 0 := p.2.symm.trans hq0
          exact List.length_eq_zero_iff.mp hlen
        dsimp only
        rw [dif_neg h0, dif_pos p.2]
        congr 2
      · have h0 : (p.1.2.1 : ℕ) ≠ 0 := Nat.ne_of_gt p.2.1
        have hl : (p.1.2.1 : ℕ) ≠ p.1.1.1.1.length := Nat.ne_of_lt p.2.2
        dsimp only
        rw [dif_neg h0, dif_neg hl]
        congr 2

lemma card_ports_decomposition {N : ℕ} (label : SignVector N → Atom N) :
    Fintype.card (Ports label) =
      Fintype.card (ExtraPorts label) + Fintype.card (ZeroBoundaryPorts label) +
        Fintype.card (LastBoundaryPorts label) +
          Fintype.card (InteriorBoundaryPorts label) := by
  have hfirst : Fintype.card (Ports label) =
      Fintype.card (ExtraPorts label) + Fintype.card (BoundaryPorts label) := by
    calc
      Fintype.card (Ports label) =
          Fintype.card (ExtraPorts label ⊕ BoundaryPorts label) := by
        apply Fintype.card_congr
        simpa only [Ports, PortAt, ExtraPorts, BoundaryPorts] using
          (Equiv.sigmaSumDistrib
            (fun s : PermissibleSequence label ↦
              {i : LabelIndex s.1 // IsExtra label s.1 i})
            (fun s : PermissibleSequence label ↦
              {i : LabelIndex s.1 // IsRedundant label s.1 i ∧ s.1.1 ≠ []}))
      _ = _ := Fintype.card_sum
  rw [hfirst, Fintype.card_congr (boundaryPortsEquiv label)]
  simp only [Fintype.card_sum]
  omega

lemma card_portAt_extra_case {N : ℕ} {label : SignVector N → Atom N}
    (s : PermissibleSequence label) (q : LabelIndex s.1)
    (hq : IsExtra label s.1 q)
    (hextra : ∀ i, IsExtra label s.1 i ↔ i = q)
    (hred : ∀ i, IsRedundant label s.1 i ↔ i = q) :
    Fintype.card (PortAt label s) = if s.1.1 = [] then 1 else 2 := by
  classical
  simp only [PortAt, Fintype.card_sum, Fintype.card_subtype]
  have hExtraCard :
      (Finset.univ.filter fun i : LabelIndex s.1 ↦ IsExtra label s.1 i).card = 1 := by
    rw [show (Finset.univ.filter fun i : LabelIndex s.1 ↦ IsExtra label s.1 i) = {q} by
      ext i
      simp [hextra]]
    simp
  by_cases hnil : s.1.1 = []
  · have hRedCard :
        (Finset.univ.filter fun i : LabelIndex s.1 ↦
          IsRedundant label s.1 i ∧ s.1.1 ≠ []).card = 0 := by
      rw [show (Finset.univ.filter fun i : LabelIndex s.1 ↦
          IsRedundant label s.1 i ∧ s.1.1 ≠ []) = ∅ by
        ext i
        simp [hnil]]
      simp
    rw [hExtraCard, hRedCard]
    simp [hnil]
  · have hRedCard :
        (Finset.univ.filter fun i : LabelIndex s.1 ↦
          IsRedundant label s.1 i ∧ s.1.1 ≠ []).card = 1 := by
      rw [show (Finset.univ.filter fun i : LabelIndex s.1 ↦
          IsRedundant label s.1 i ∧ s.1.1 ≠ []) = {q} by
        ext i
        simp [hnil, hred]]
      simp
    rw [hExtraCard, hRedCard]
    simp [hnil]

lemma card_portAt_repeated_case {N : ℕ} {label : SignVector N → Atom N}
    (s : PermissibleSequence label) (hne : s.1.1 ≠ [])
    (p q : LabelIndex s.1) (hpq : p ≠ q)
    (hnoextra : ∀ i, ¬ IsExtra label s.1 i)
    (hred : ∀ i, IsRedundant label s.1 i ↔ i = p ∨ i = q) :
    Fintype.card (PortAt label s) = 2 := by
  classical
  simp only [PortAt, Fintype.card_sum, Fintype.card_subtype]
  have hExtraCard :
      (Finset.univ.filter fun i : LabelIndex s.1 ↦ IsExtra label s.1 i).card = 0 := by
    rw [show (Finset.univ.filter fun i : LabelIndex s.1 ↦ IsExtra label s.1 i) = ∅ by
      ext i
      simp [hnoextra]]
    simp
  have hRedCard :
      (Finset.univ.filter fun i : LabelIndex s.1 ↦
        IsRedundant label s.1 i ∧ s.1.1 ≠ []).card = 2 := by
    rw [show (Finset.univ.filter fun i : LabelIndex s.1 ↦
        IsRedundant label s.1 i ∧ s.1.1 ≠ []) = {p, q} by
      ext i
      simp [hne, hred]]
    simp [hpq]
  omega

lemma card_portAt {N : ℕ} {label : SignVector N → Atom N}
    (s : PermissibleSequence label) :
    Fintype.card (PortAt label s) = if s.1.1 = [] then 1 else 2 := by
  rcases prefixLabel_classification s.2 with h | h
  · obtain ⟨q, hq, hextra, hred⟩ := h
    exact card_portAt_extra_case s q hq hextra hred
  · obtain ⟨p, q, hpq, -, hnoextra, hred⟩ := h
    have hne : s.1.1 ≠ [] := by
      intro hnil
      apply hpq
      apply Fin.ext
      have hp : (p : ℕ) < 1 := by simpa [hnil] using p.isLt
      have hq : (q : ℕ) < 1 := by simpa [hnil] using q.isLt
      omega
    simpa [hne] using card_portAt_repeated_case s hne p q hpq hnoextra hred

def nilPermissible {N : ℕ} (label : SignVector N → Atom N) :
    PermissibleSequence label :=
  ⟨SignedSequence.nil N, by simp [Permissible]⟩

@[simp] lemma nilPermissible_coe {N : ℕ} (label : SignVector N → Atom N) :
    (nilPermissible label).1.1 = [] := rfl

lemma eq_nilPermissible_of_coe_eq_nil {N : ℕ} {label : SignVector N → Atom N}
    (s : PermissibleSequence label) (hs : s.1.1 = []) :
    s = nilPermissible label := by
  apply Subtype.ext
  apply Subtype.ext
  exact hs

lemma odd_card_ports {N : ℕ} (label : SignVector N → Atom N) :
    Odd (Fintype.card (Ports label)) := by
  let z := nilPermissible label
  let rest := (Finset.univ : Finset (PermissibleSequence label)).erase z
  have hzmem : z ∈ (Finset.univ : Finset (PermissibleSequence label)) := Finset.mem_univ _
  have hrest (s : PermissibleSequence label) (hs : s ∈ rest) : s.1.1 ≠ [] := by
    intro hnil
    have hsz : s = z := by
      change s = nilPermissible label
      exact eq_nilPermissible_of_coe_eq_nil s hnil
    exact (Finset.mem_erase.mp hs).1 hsz
  have hsum :
      ∑ s ∈ rest, Fintype.card (PortAt label s) = rest.card * 2 := by
    calc
      ∑ s ∈ rest, Fintype.card (PortAt label s) = ∑ _s ∈ rest, 2 := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [card_portAt]
        simp [hrest s hs]
      _ = rest.card * 2 := by simp
  refine ⟨rest.card, ?_⟩
  calc
    Fintype.card (Ports label) =
        ∑ s : PermissibleSequence label, Fintype.card (PortAt label s) :=
      Fintype.card_sigma
    _ = Fintype.card (PortAt label z) +
        ∑ s ∈ rest, Fintype.card (PortAt label s) := by
      exact (Finset.add_sum_erase Finset.univ
        (fun s ↦ Fintype.card (PortAt label s)) hzmem).symm
    _ = 1 + rest.card * 2 := by
      rw [hsum, card_portAt]
      simp [z]
    _ = 2 * rest.card + 1 := by omega

/-! ## Pairing the ports -/

/-- Expanding an extra label appends that label and makes the new terminal
index redundant. -/
def extraToLast {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) (p : ExtraPorts label) :
    LastBoundaryPorts label := by
  let s := p.1.1
  have hs : Permissible label s := p.1.2
  let i : LabelIndex s := p.2.1
  have hi : IsExtra label s i := p.2.2
  let a := prefixLabel label s i
  let ha := extra_fst_not_mem hno hs hi
  let t := s.appendAtom a ha
  have ht : Permissible label t := permissible_append_extra hno hs i hi
  let q : LabelIndex t := ⟨t.1.length, by omega⟩
  have hq : IsRedundant label t q := last_redundant_append_extra hno hs i hi
  have hne : t.1 ≠ [] := by simp [t]
  exact ⟨⟨⟨t, ht⟩, ⟨q, hq, hne⟩⟩, rfl⟩

/-- Removing a redundant terminal entry exposes the unique extra label that
reconstructs it. -/
def lastToExtra {N : ℕ} {label : SignVector N → Atom N}
    (p : LastBoundaryPorts label) : ExtraPorts label := by
  let s := p.1.1.1
  have hs : Permissible label s := p.1.1.2
  have hne : s.1 ≠ [] := p.1.2.2.2
  let q : LabelIndex s := ⟨s.1.length, by omega⟩
  have hpq : p.1.2.1 = q := by
    apply Fin.ext
    exact p.2
  have hq : IsRedundant label s q := by
    rw [← hpq]
    exact p.1.2.2.1
  have ht : Permissible label s.dropLast :=
    permissible_dropLast_redundant hs (List.length_pos_of_ne_nil hne) hq
  have hex := exists_extra_dropLast_of_last_redundant hs hne hq
  let i : LabelIndex s.dropLast := Classical.choose hex
  have hi : IsExtra label s.dropLast i := (Classical.choose_spec hex).1
  exact ⟨⟨s.dropLast, ht⟩, ⟨i, hi⟩⟩

lemma lastToExtra_prefixLabel {N : ℕ} {label : SignVector N → Atom N}
    (p : LastBoundaryPorts label) :
    prefixLabel label (lastToExtra p).1.1 (lastToExtra p).2.1 =
      p.1.1.1.lastAtom p.1.2.2.2 := by
  classical
  simp only [lastToExtra]
  exact (Classical.choose_spec
    (exists_extra_dropLast_of_last_redundant p.1.1.2 p.1.2.2.2 (by
      have hpq : p.1.2.1 =
          (⟨p.1.1.1.1.length, by omega⟩ : LabelIndex p.1.1.1) := by
        apply Fin.ext
        exact p.2
      rw [← hpq]
      exact p.1.2.2.1))).2

lemma lastToExtra_extraToLast {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) (p : ExtraPorts label) :
    lastToExtra (extraToLast hno p) = p := by
  classical
  let q := lastToExtra (extraToLast hno p)
  change q = p
  have hbase : q.1 = p.1 := by
    apply Subtype.ext
    simp [q, lastToExtra, extraToLast]
  rcases q with ⟨qs, qi⟩
  rcases p with ⟨ps, pi⟩
  change qs = ps at hbase
  subst qs
  congr 1
  apply Subtype.ext
  exact extra_index_unique ps.2 qi.2 pi.2

lemma extraToLast_lastToExtra {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) (p : LastBoundaryPorts label) :
    extraToLast hno (lastToExtra p) = p := by
  classical
  let q := extraToLast hno (lastToExtra p)
  change q = p
  have hseq : q.1.1.1 = p.1.1.1 := by
    dsimp only [q, extraToLast]
    apply Subtype.ext
    change (lastToExtra p).1.1.1 ++
      [prefixLabel label (lastToExtra p).1.1 (lastToExtra p).2.1] = p.1.1.1.1
    rw [lastToExtra_prefixLabel p]
    change p.1.1.1.1.dropLast ++ [p.1.1.1.1.getLast p.1.2.2.2] = p.1.1.1.1
    exact List.dropLast_append_getLast p.1.2.2.2
  rcases q with ⟨⟨qs, qi⟩, qlast⟩
  rcases p with ⟨⟨ps, pi⟩, plast⟩
  change qs.1 = ps.1 at hseq
  have hbase : qs = ps := Subtype.ext hseq
  subst qs
  apply Subtype.eq
  change (⟨ps, qi⟩ : BoundaryPorts label) = ⟨ps, pi⟩
  congr 1
  apply Subtype.ext
  apply Fin.ext
  exact qlast.trans plast.symm

def extraLastEquiv {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) : ExtraPorts label ≃ LastBoundaryPorts label where
  toFun := extraToLast hno
  invFun := lastToExtra
  left_inv := lastToExtra_extraToLast hno
  right_inv := extraToLast_lastToExtra hno

lemma card_extra_eq_card_last {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) :
    Fintype.card (ExtraPorts label) = Fintype.card (LastBoundaryPorts label) :=
  Fintype.card_congr (extraLastEquiv hno)

/-- A finite set admitting a fixed-point-free involution has even cardinality. -/
lemma even_card_of_fixedPointFree_involution {α : Type*} [Fintype α]
    (f : α → α) (hinv : Function.Involutive f) (hfix : ∀ x, f x ≠ x) :
    Even (Fintype.card α) := by
  classical
  let r : α → α → Prop := fun x y ↦ f x = y
  have hrsymm : Std.Symm r := ⟨by
      intro x y hxy
      rw [← hxy]
      exact hinv x⟩
  have hrirr : Std.Irrefl r := ⟨hfix⟩
  let G : SimpleGraph α := ⟨r, hrsymm, hrirr⟩
  have hdegree (x : α) : G.degree x = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    refine ⟨f x, rfl, ?_⟩
    intro y hy
    change f x = y at hy
    exact Eq.symm hy
  have hcard : Fintype.card α = 2 * G.edgeFinset.card := by
    calc
      Fintype.card α = ∑ _x : α, 1 := by simp
      _ = ∑ x : α, G.degree x := by
        apply Finset.sum_congr rfl
        intro x _
        exact (hdegree x).symm
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  exact ⟨G.edgeFinset.card, by omega⟩

lemma SignedSequence.negate_ne_self_of_nonempty {N : ℕ} (s : SignedSequence N)
    (hne : s.1 ≠ []) : s.negate ≠ s := by
  intro h
  have hl : negateList s.1 = s.1 := congrArg Subtype.val h
  obtain ⟨a, l, hslist⟩ := List.exists_cons_of_ne_nil hne
  rw [hslist] at hl
  simp only [negateList, List.map_cons, List.cons.injEq] at hl
  exact Atom.negate_ne_self a hl.1

lemma SignedSequence.swapAdjacent_ne_self {N : ℕ} (s : SignedSequence N)
    (q : ℕ) (hq : q + 1 < s.1.length) : s.swapAdjacent q hq ≠ s := by
  intro h
  have hqleft : q < (s.swapAdjacent q hq).1.length := by simp; omega
  have hqright : q < s.1.length := by omega
  have hopt := congrArg (fun l : List (Atom N) ↦ l[q]?) (congrArg Subtype.val h)
  rw [List.getElem?_eq_getElem hqleft, List.getElem?_eq_getElem hqright] at hopt
  have helem : (s.swapAdjacent q hq).1[q]'hqleft = s.1[q]'hqright :=
    Option.some.inj hopt
  have hentry : s.1[q + 1] = s.1[q] := by
    simpa only [SignedSequence.coe_swapAdjacent,
      getElem_swapAdjacentList_left] using helem
  have hmapleft : q + 1 < (s.1.map Prod.fst).length := by simp; omega
  have hmapright : q < (s.1.map Prod.fst).length := by simp; omega
  have hfst : (s.1.map Prod.fst)[q + 1]'hmapleft =
      (s.1.map Prod.fst)[q]'hmapright := by
    simpa using congrArg Prod.fst hentry
  have hindex : q + 1 = q :=
    s.2.getElem_inj_iff.mp hfst
  omega

/-- At the zero boundary, change every sign. -/
def zeroPartner {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) (hanti : Antipodal label)
    (hzeroUnique : ZeroUniqueMagnitude label) (p : ZeroBoundaryPorts label) :
    ZeroBoundaryPorts label := by
  let s := p.1.1.1
  have hs : Permissible label s := p.1.1.2
  have hne : s.1 ≠ [] := p.1.2.2.2
  let z : LabelIndex s := ⟨0, by simp⟩
  have hpz : p.1.2.1 = z := by
    apply Fin.ext
    exact p.2
  have hr : IsRedundant label s z := by
    rw [← hpz]
    exact p.1.2.2.1
  have he : IsExtra label s z := extra_zero_of_redundant hzeroUnique hr
  have ht : Permissible label s.negate :=
    permissible_negate_of_extra_zero hanti hs he
  let z' : LabelIndex s.negate := ⟨0, by simp⟩
  have he' : IsExtra label s.negate z' := extra_zero_negate hno hs he
  have hne' : s.negate.1 ≠ [] := by
    simpa [SignedSequence.coe_negate, negateList] using hne
  exact ⟨⟨⟨s.negate, ht⟩, ⟨z', Or.inl he', hne'⟩⟩, rfl⟩

lemma zeroPartner_involutive {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) (hanti : Antipodal label)
    (hzeroUnique : ZeroUniqueMagnitude label) :
    Function.Involutive (zeroPartner hno hanti hzeroUnique) := by
  classical
  intro p
  let q := zeroPartner hno hanti hzeroUnique
    (zeroPartner hno hanti hzeroUnique p)
  change q = p
  have hseq : q.1.1.1 = p.1.1.1 := by
    simp [q, zeroPartner]
  rcases q with ⟨⟨qs, qi⟩, qzero⟩
  rcases p with ⟨⟨ps, pi⟩, pzero⟩
  change qs.1 = ps.1 at hseq
  have hbase : qs = ps := Subtype.ext hseq
  subst qs
  apply Subtype.eq
  change (⟨ps, qi⟩ : BoundaryPorts label) = ⟨ps, pi⟩
  congr 1
  apply Subtype.ext
  apply Fin.ext
  exact qzero.trans pzero.symm

lemma zeroPartner_ne_self {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) (hanti : Antipodal label)
    (hzeroUnique : ZeroUniqueMagnitude label) (p : ZeroBoundaryPorts label) :
    zeroPartner hno hanti hzeroUnique p ≠ p := by
  intro hp
  have hseq := congrArg (fun q : ZeroBoundaryPorts label ↦ q.1.1.1) hp
  change p.1.1.1.negate = p.1.1.1 at hseq
  exact p.1.1.1.negate_ne_self_of_nonempty p.1.2.2.2 hseq

lemma even_card_zeroBoundaryPorts {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) (hanti : Antipodal label)
    (hzeroUnique : ZeroUniqueMagnitude label) :
    Even (Fintype.card (ZeroBoundaryPorts label)) :=
  even_card_of_fixedPointFree_involution
    (zeroPartner hno hanti hzeroUnique)
    (zeroPartner_involutive hno hanti hzeroUnique)
    (zeroPartner_ne_self hno hanti hzeroUnique)

/-- At an interior redundant index, exchange the two entries straddling that
index. -/
def interiorPartner {N : ℕ} {label : SignVector N → Atom N}
    (p : InteriorBoundaryPorts label) : InteriorBoundaryPorts label := by
  let s := p.1.1.1
  have hs : Permissible label s := p.1.1.2
  have hne : s.1 ≠ [] := p.1.2.2.2
  let q := (p.1.2.1 : ℕ) - 1
  have hqsucc : q + 1 = (p.1.2.1 : ℕ) := by
    have hjpos : 0 < (p.1.2.1 : ℕ) := p.2.1
    dsimp only [q]
    omega
  have hq : q + 1 < s.1.length := hqsucc.trans_lt p.2.2
  let j : LabelIndex s := ⟨q + 1, by omega⟩
  have hpj : p.1.2.1 = j := by
    apply Fin.ext
    exact hqsucc.symm
  have hr : IsRedundant label s j := by
    rw [← hpj]
    exact p.1.2.2.1
  let t := s.swapAdjacent q hq
  have ht : Permissible label t := permissible_swap_redundant hs q hq hr
  let j' : LabelIndex t := ⟨q + 1, by simp [t]; omega⟩
  have hr' : IsRedundant label t j' := redundant_swap_redundant hs q hq hr
  have hne' : t.1 ≠ [] := by
    intro hnil
    have hlen : t.1.length = 0 := by simp [hnil]
    have : s.1.length = 0 := by simpa [t] using hlen
    exact hne (List.length_eq_zero_iff.mp this)
  exact ⟨⟨⟨t, ht⟩, ⟨j', hr', hne'⟩⟩, by
    constructor
    · change 0 < q + 1
      omega
    · change q + 1 < t.1.length
      simpa [t] using hq⟩

lemma interiorPartner_index {N : ℕ} {label : SignVector N → Atom N}
    (p : InteriorBoundaryPorts label) :
    ((interiorPartner p).1.2.1 : ℕ) = (p.1.2.1 : ℕ) := by
  have hjpos : 0 < (p.1.2.1 : ℕ) := p.2.1
  dsimp only [interiorPartner]
  omega

lemma interiorPartner_sequence {N : ℕ} {label : SignVector N → Atom N}
    (p : InteriorBoundaryPorts label) :
    (interiorPartner p).1.1.1 =
      p.1.1.1.swapAdjacent ((p.1.2.1 : ℕ) - 1) (by
        have hjpos : 0 < (p.1.2.1 : ℕ) := p.2.1
        have hjlt : (p.1.2.1 : ℕ) < p.1.1.1.1.length := p.2.2
        omega) := by
  rfl

lemma interiorPartner_involutive {N : ℕ} {label : SignVector N → Atom N} :
    Function.Involutive (interiorPartner (label := label)) := by
  classical
  intro p
  let q := interiorPartner (interiorPartner p)
  change q = p
  have hseq : q.1.1.1 = p.1.1.1 := by
    simp [q, interiorPartner_sequence, interiorPartner_index,
      SignedSequence.swapAdjacent_involutive]
  have hindex : (q.1.2.1 : ℕ) = (p.1.2.1 : ℕ) := by
    simp [q, interiorPartner_index]
  rcases q with ⟨⟨qs, qi⟩, qinterior⟩
  rcases p with ⟨⟨ps, pi⟩, pinterior⟩
  change qs.1 = ps.1 at hseq
  change (qi.1 : ℕ) = (pi.1 : ℕ) at hindex
  have hbase : qs = ps := Subtype.ext hseq
  subst qs
  apply Subtype.eq
  change (⟨ps, qi⟩ : BoundaryPorts label) = ⟨ps, pi⟩
  congr 1
  apply Subtype.ext
  apply Fin.ext
  exact hindex

lemma interiorPartner_ne_self {N : ℕ} {label : SignVector N → Atom N}
    (p : InteriorBoundaryPorts label) : interiorPartner p ≠ p := by
  intro hp
  have hseq := congrArg (fun q : InteriorBoundaryPorts label ↦ q.1.1.1) hp
  have hswap : p.1.1.1.swapAdjacent ((p.1.2.1 : ℕ) - 1) (by
      have hjpos : 0 < (p.1.2.1 : ℕ) := p.2.1
      have hjlt : (p.1.2.1 : ℕ) < p.1.1.1.1.length := p.2.2
      omega) = p.1.1.1 := (interiorPartner_sequence p).symm.trans hseq
  exact p.1.1.1.swapAdjacent_ne_self ((p.1.2.1 : ℕ) - 1) (by
    have hjpos : 0 < (p.1.2.1 : ℕ) := p.2.1
    have hjlt : (p.1.2.1 : ℕ) < p.1.1.1.1.length := p.2.2
    omega) hswap

lemma even_card_interiorBoundaryPorts {N : ℕ} {label : SignVector N → Atom N} :
    Even (Fintype.card (InteriorBoundaryPorts label)) :=
  even_card_of_fixedPointFree_involution interiorPartner
    interiorPartner_involutive interiorPartner_ne_self

lemma even_card_ports {N : ℕ} {label : SignVector N → Atom N}
    (hno : NoComplement label) (hanti : Antipodal label)
    (hzeroUnique : ZeroUniqueMagnitude label) :
    Even (Fintype.card (Ports label)) := by
  rcases even_card_zeroBoundaryPorts hno hanti hzeroUnique with ⟨z, hz⟩
  rcases even_card_interiorBoundaryPorts (label := label) with ⟨i, hi⟩
  have hdecomp := card_ports_decomposition label
  have helast := card_extra_eq_card_last hno
  refine ⟨Fintype.card (ExtraPorts label) + z + i, ?_⟩
  omega

/-- The finite octahedral Tucker lemma.  The label at zero need not be fresh:
under the negation of the conclusion, freshness follows from antipodality and
the fact that zero is below every consistent sign vector. -/
theorem finite_tucker {N : ℕ} (label : SignVector N → Atom N)
    (hanti : Antipodal label) :
    ∃ X Y : SignVector N,
      X.Consistent ∧ Y.Consistent ∧ X ≤ Y ∧
        label X = Atom.negate (label Y) := by
  by_contra h
  have hno : NoComplement label := by
    intro X Y hX hY hXY hcomp
    exact h ⟨X, Y, hX, hY, hXY, hcomp⟩
  have hzeroUnique : ZeroUniqueMagnitude label := by
    intro X hX hmag
    by_contra hXzero
    rcases Atom.eq_or_eq_negate_of_fst_eq hmag with heq | heq
    · have hantiX := hanti X hX hXzero
      have hcomp : label (.zero N) = Atom.negate (label X.negate) := by
        rw [hantiX, Atom.negate_negate, heq]
      exact hno (SignVector.zero_consistent N) (SignVector.consistent_negate hX)
        (by constructor <;> simp [SignVector.zero]) hcomp
    · have hcomp : label (.zero N) = Atom.negate (label X) := by
        rw [heq, Atom.negate_negate]
      exact hno (SignVector.zero_consistent N) hX
        (by constructor <;> simp [SignVector.zero]) hcomp
  exact (Nat.not_even_iff_odd.mpr (odd_card_ports label))
    (even_card_ports hno hanti hzeroUnique)

/-- The usual octahedral Tucker lemma on the deleted origin.  A labeling of
the nonzero `N`-dimensional sign vectors by only `N - 1` magnitudes has a
complementary comparable pair.  The proof embeds those magnitudes into the
first `N - 1` coordinates and reserves the final coordinate as a fresh label
for the origin, reducing the statement to `finite_tucker`. -/
theorem finite_tucker_nonzero {N : ℕ} (hN : 0 < N)
    (label : SignVector N → Atom (N - 1))
    (hanti : ∀ X : SignVector N, X.Consistent → X ≠ .zero N →
      label X.negate = Atom.negate (label X)) :
    ∃ X Y : SignVector N,
      X.Consistent ∧ Y.Consistent ∧ X ≠ .zero N ∧ Y ≠ .zero N ∧
        X ≤ Y ∧ label X = Atom.negate (label Y) := by
  let embed : Atom (N - 1) → Atom N := fun a ↦
    (⟨a.1, by have := a.1.isLt; omega⟩, a.2)
  let last : Fin N := ⟨N - 1, by omega⟩
  let lifted : SignVector N → Atom N := fun X ↦
    if h : X.Consistent ∧ X ≠ .zero N then embed (label X) else (last, false)
  have hliftAnti : Antipodal lifted := by
    intro X hX hXne
    have hnegCons : X.negate.Consistent := SignVector.consistent_negate hX
    have hnegNe : X.negate ≠ .zero N := by simpa using hXne
    change (if h : X.negate.Consistent ∧ X.negate ≠ .zero N then
        embed (label X.negate) else (last, false)) =
      Atom.negate (if h : X.Consistent ∧ X ≠ .zero N then
        embed (label X) else (last, false))
    rw [dif_pos (And.intro hnegCons hnegNe), dif_pos (And.intro hX hXne),
      hanti X hX hXne]
    rfl
  have hzeroUnique : ZeroUniqueMagnitude lifted := by
    intro X hX hmag
    by_contra hXne
    have hnon : X.Consistent ∧ X ≠ .zero N := ⟨hX, hXne⟩
    have hzero : ¬((SignVector.zero N).Consistent ∧
        SignVector.zero N ≠ .zero N) := by simp
    have hval := congrArg Fin.val hmag
    simp only [lifted, dif_pos hnon, dif_neg hzero] at hval
    dsimp only [embed, last] at hval
    have hlt := (label X).1.isLt
    omega
  obtain ⟨X, Y, hX, hY, hXY, hcomp⟩ := finite_tucker lifted hliftAnti
  have hXne : X ≠ .zero N := by
    intro hXzero
    subst X
    have hmag : (lifted Y).1 = (lifted (.zero N)).1 := by
      exact (congrArg Prod.fst hcomp).symm
    have hYzero := hzeroUnique Y hY hmag
    subst Y
    exact Atom.negate_ne_self (lifted (.zero N)) hcomp.symm
  have hYne : Y ≠ .zero N := by
    intro hYzero
    subst Y
    have hmag : (lifted X).1 = (lifted (.zero N)).1 := by
      simpa using congrArg Prod.fst hcomp
    exact hXne (hzeroUnique X hX hmag)
  have hliftX : lifted X = embed (label X) := by
    simp [lifted, hX, hXne]
  have hliftY : lifted Y = embed (label Y) := by
    simp [lifted, hY, hYne]
  have hemb : embed (label X) = Atom.negate (embed (label Y)) := by
    simpa [hliftX, hliftY] using hcomp
  have hindex : (label X).1 = (label Y).1 := by
    apply Fin.ext
    have h := congrArg (fun a : Atom N ↦ (a.1 : ℕ)) hemb
    simpa [embed, Atom.negate] using h
  have hsign : (label X).2 = !(label Y).2 := by
    have h := congrArg (fun a : Atom N ↦ a.2) hemb
    simpa [embed, Atom.negate] using h
  refine ⟨X, Y, hX, hY, hXne, hYne, hXY, ?_⟩
  exact Prod.ext hindex hsign

end

end Erdos921.Tucker
