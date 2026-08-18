/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Irreducible
import ErdosProblems.Erdos186.CFP.Witness
import ErdosProblems.Erdos186.UpperPackaging

/-!
# Concrete replacement bookkeeping for the Pham--Zakharov reduction

This file supplies the set-level layer underneath
`Erdos186.Irreducible.MoveTrace`.  A `ReplacementState` contains an actual
finite lattice set, its explicitly selected structured core, and an actual
GAP containing that core.  A `ReplacementStep` contains an actual retained
subset of the old set, the exact equality of its cardinality with the new
set, and a proved transport implication for nonaveraging.  A source-specific
constructor can discharge that implication using GAP coordinates, subset
restriction, and translation without pretending that a GAP coordinate map is
globally injective on the whole lattice.

The dimension comparison, retention inequality, and GAP-volume estimate are
explicit fields of a step.  They are precisely the conclusions which the
dimension-increase and no-dimension-increase arguments (Pham--Zakharov Lemmas
6--8) must establish in each branch.  No step is asserted to exist here.
Likewise, no Conlon--Fox--Pham structure hypothesis is assumed.  A finite
`ReplacementChain` can be forgotten to the numerical `MoveTrace`, after
which all the product, dimension-jump, and termination lemmas already proved
in `Erdos186.Irreducible` apply.
-/

namespace Erdos186.PZ.Reduction

open Finset
open Erdos186.Irreducible

noncomputable section

/-- Vector nonaveraging is inherited by subsets.  This local copy keeps the
replacement layer independent of the later PZ intersection development. -/
theorem isBoxNonaveraging_mono {d : ℕ} {A C : Finset (BoxPoint d)}
    (hA : IsBoxNonaveraging A) (hCA : C ⊆ A) : IsBoxNonaveraging C := by
  intro a ha S hS hcard
  apply hA a (hCA ha) S
  · intro x hx
    have hx' := Finset.mem_erase.mp (hS hx)
    exact Finset.mem_erase.mpr ⟨hx'.1, hCA hx'.2⟩
  · exact hcard

/-- Translation of a finite lattice set. -/
def translate {d : ℕ} (v : BoxPoint d) (A : Finset (BoxPoint d)) :
    Finset (BoxPoint d) :=
  A.image fun x ↦ x + v

@[simp] theorem card_translate {d : ℕ} (v : BoxPoint d)
    (A : Finset (BoxPoint d)) : (translate v A).card = A.card := by
  classical
  exact Finset.card_image_of_injective _ (add_left_injective v)

theorem translate_nonempty {d : ℕ} (v : BoxPoint d)
    {A : Finset (BoxPoint d)} (hA : A.Nonempty) :
    (translate v A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨a + v, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩

/-- Translation preserves vector nonaveraging. -/
theorem isBoxNonaveraging_translate {d : ℕ} {A : Finset (BoxPoint d)}
    (v : BoxPoint d) (hA : IsBoxNonaveraging A) :
    IsBoxNonaveraging (translate v A) := by
  classical
  intro b hb T hT hcard
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  let e : BoxPoint d ↪ BoxPoint d :=
    ⟨fun x ↦ x + v, add_left_injective v⟩
  let S : Finset (BoxPoint d) := T.preimage e e.injective.injOn
  have hTsub : T ⊆ translate v A := hT.trans (Finset.erase_subset _ _)
  have hmap : S.map e = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_preimage.mp hy
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp (hTsub hx)
      refine Finset.mem_map.mpr ⟨y, Finset.mem_preimage.mpr ?_, hxy⟩
      rw [show e y = x by simpa [e] using hxy]
      exact hx
  have hSsub : S ⊆ A.erase a := by
    intro x hx
    have hxT : e x ∈ T := by
      rw [← hmap]
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    have hxe := Finset.mem_erase.mp (hT hxT)
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · intro hxa
      apply hxe.1
      simp [e, hxa]
    · simpa [translate, e] using hxe.2
  have hcardS : S.card = T.card := by rw [← hmap]; simp
  intro heq
  apply hA a ha S hSsub (by simpa [hcardS] using hcard)
  have hsum_map : ∑ x ∈ T, x = ∑ x ∈ S, e x := by
    rw [← hmap]
    simp [Finset.sum_map]
  rw [hsum_map] at heq
  have hcardInt : (T.card : ℤ) = S.card := by simp [hcardS]
  rw [hcardInt] at heq
  simpa [e, Finset.sum_add_distrib, smul_add] using heq

/-! ## Concrete states and individual replacement steps -/

/-- The concrete data retained at one stage of the irreducibility reduction.

The `rank` is the displayed rank of the supplied GAP.  A later theorem may
show that it equals the subset-sum dimension; this bookkeeping structure does
not manufacture such a theorem. -/
structure ReplacementState where
  ambientDimension : ℕ
  rank : ℕ
  /-- The actual set whose cardinality is the population of this state. -/
  points : Finset (BoxPoint ambientDimension)
  /-- The large CFP core which is contained in the selected progression. -/
  structuredCore : Finset (BoxPoint ambientDimension)
  progression : GAP ambientDimension rank
  structuredCore_subset_points : structuredCore ⊆ points
  structuredCore_subset_progression : structuredCore ⊆ progression.carrier
  /-- The exact number of points the structure selection is allowed to lose. -/
  loss : ℕ
  points_card_le_core_add_loss : points.card ≤ structuredCore.card + loss
  points_nonempty : points.Nonempty
  structuredCore_nonempty : structuredCore.Nonempty

namespace ReplacementState

/-- Forget a concrete state to the numerical state used by `MoveTrace`.
The lower bound on GAP volume follows from the actual nonempty contained
set. -/
def toIterationState (S : ReplacementState) : IterationState where
  population := (S.points.card : ℝ)
  dimension := S.rank
  gapSize := (S.progression.volume : ℝ)
  population_pos := by
    exact_mod_cast S.points_nonempty.card_pos
  one_le_gapSize := by
    have hcarrier : S.progression.carrier.Nonempty :=
      ⟨S.progression.coordPoint S.progression.zeroCoord,
        S.progression.coordPoint_mem_carrier S.progression.zeroCoord⟩
    have hone : 1 ≤ S.progression.carrier.card :=
      Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hcarrier)
    have hvolume : 1 ≤ S.progression.volume :=
      hone.trans S.progression.card_carrier_le_volume
    exact_mod_cast hvolume

@[simp] theorem toIterationState_population (S : ReplacementState) :
    S.toIterationState.population = (S.points.card : ℝ) := rfl

@[simp] theorem toIterationState_dimension (S : ReplacementState) :
    S.toIterationState.dimension = S.rank := rfl

@[simp] theorem toIterationState_gapSize (S : ReplacementState) :
    S.toIterationState.gapSize = (S.progression.volume : ℝ) := rfl

end ReplacementState

/-! ## An explicit structure selector and Definition 9 -/

/-- Explicit, reusable choices of the CFP conclusion for finite lattice
sets.  This is data, not an existence theorem: a caller must supply an
actual `EnhancedCFPWitness` for every input on which the selector is used.

The four numerical functions retain the parameters of that witness.  The
last field says that the selected structured core survives whenever the
input set is nonempty; in applications it follows from
`loss A < A.card` via `EnhancedCFPWitness.core_nonempty`. -/
structure StructureChoice where
  reserveBound : ∀ {d : ℕ}, Finset (BoxPoint d) → ℕ
  rankBound : ∀ {d : ℕ}, Finset (BoxPoint d) → ℕ
  dilation : ∀ {d : ℕ}, Finset (BoxPoint d) → ℕ
  loss : ∀ {d : ℕ}, Finset (BoxPoint d) → ℕ
  witness : ∀ {d : ℕ} (A : Finset (BoxPoint d)),
    CFP.EnhancedCFPWitness A (reserveBound A) (rankBound A) (dilation A) (loss A)
  core_nonempty : ∀ {d : ℕ} (A : Finset (BoxPoint d)), A.Nonempty →
    (witness A).core.Nonempty

namespace StructureChoice

variable (choice : StructureChoice)

/-- The concrete replacement state selected from an explicit CFP witness. -/
def state {d : ℕ} (A : Finset (BoxPoint d)) (hA : A.Nonempty) :
    ReplacementState where
  ambientDimension := d
  rank := (choice.witness A).rank
  points := A
  structuredCore := (choice.witness A).core
  progression := (choice.witness A).progression
  structuredCore_subset_points := (choice.witness A).core_subset
  structuredCore_subset_progression :=
    (Finset.subset_insert 0 _).trans (choice.witness A).core_zero_subset
  loss := choice.loss A
  points_card_le_core_add_loss := (choice.witness A).core_large
  points_nonempty := hA
  structuredCore_nonempty := choice.core_nonempty A hA

@[simp] theorem state_ambientDimension {d : ℕ} (A : Finset (BoxPoint d))
    (hA : A.Nonempty) : (choice.state A hA).ambientDimension = d := rfl

@[simp] theorem state_rank {d : ℕ} (A : Finset (BoxPoint d))
    (hA : A.Nonempty) : (choice.state A hA).rank = (choice.witness A).rank := rfl

@[simp] theorem state_points {d : ℕ} (A : Finset (BoxPoint d))
    (hA : A.Nonempty) : (choice.state A hA).points = A := rfl

@[simp] theorem state_structuredCore {d : ℕ} (A : Finset (BoxPoint d))
    (hA : A.Nonempty) :
    (choice.state A hA).structuredCore = (choice.witness A).core := rfl

@[simp] theorem state_progression {d : ℕ} (A : Finset (BoxPoint d))
    (hA : A.Nonempty) :
    (choice.state A hA).progression = (choice.witness A).progression := rfl

/-- The selected structured core is an actual subset of the input. -/
theorem state_core_subset {d : ℕ} (A : Finset (BoxPoint d))
    (hA : A.Nonempty) : (choice.state A hA).structuredCore ⊆ A :=
  (choice.witness A).core_subset

/-- The exact loss estimate retained from the chosen CFP witness. -/
theorem card_le_state_add_loss {d : ℕ} (A : Finset (BoxPoint d))
    (hA : A.Nonempty) :
    A.card ≤ (choice.state A hA).structuredCore.card + choice.loss A :=
  (choice.witness A).core_large

end StructureChoice

/-- Source-faithful fixed-ambient form of Pham--Zakharov Definition 9.

The paper first identifies the selected core with a subset of a coordinate
lattice.  Here that identification is deliberately left in the original
ambient lattice: `X` is a dense subset of the explicitly chosen structured
core and `translate (-x) X` plays the role of `A' - x`.  The translation
point is required to lie in the selected GAP.  The chosen structure of every
such translate must have the same rank and GAP volume at least `gamma` times
the original selected GAP volume. -/
def IsIrreducible (choice : StructureChoice) {d : ℕ}
    (A : Finset (BoxPoint d)) (hA : A.Nonempty) (δ γ : ℝ) : Prop :=
  ∀ (X : Finset (BoxPoint d))
    (_hXsub : X ⊆ (choice.state A hA).structuredCore) (hXne : X.Nonempty),
    δ * (A.card : ℝ) ≤ (X.card : ℝ) →
    ∀ x ∈ (choice.state A hA).progression.carrier,
      let shifted := translate (-x) X
      let next := choice.state shifted (translate_nonempty (-x) hXne)
      next.rank = (choice.state A hA).rank ∧
        γ * ((choice.state A hA).progression.volume : ℝ) ≤
          (next.progression.volume : ℝ)

/-- A concrete witness to the failure of fixed-ambient irreducibility. -/
structure FailingReplacementCandidate (choice : StructureChoice) {d : ℕ}
    (A : Finset (BoxPoint d)) (hA : A.Nonempty) (δ γ : ℝ) where
  retained : Finset (BoxPoint d)
  retained_subset_core : retained ⊆ (choice.state A hA).structuredCore
  retained_nonempty : retained.Nonempty
  dense : δ * (A.card : ℝ) ≤ (retained.card : ℝ)
  translationPoint : BoxPoint d
  translationPoint_mem :
    translationPoint ∈ (choice.state A hA).progression.carrier
  failure :
    let shifted := translate (-translationPoint) retained
    let next := choice.state shifted
      (translate_nonempty (-translationPoint) retained_nonempty)
    next.rank ≠ (choice.state A hA).rank ∨
      (next.progression.volume : ℝ) <
        γ * ((choice.state A hA).progression.volume : ℝ)

namespace FailingReplacementCandidate

variable {choice : StructureChoice} {d : ℕ} {A : Finset (BoxPoint d)}
  {hA : A.Nonempty} {δ γ : ℝ}

/-- The translated set whose chosen structure witnesses failure. -/
def shifted (F : FailingReplacementCandidate choice A hA δ γ) :
    Finset (BoxPoint d) := translate (-F.translationPoint) F.retained

theorem shifted_nonempty (F : FailingReplacementCandidate choice A hA δ γ) :
    F.shifted.Nonempty :=
  translate_nonempty (-F.translationPoint) F.retained_nonempty

/-- The actual next state selected from the translated dense subset. -/
def next (F : FailingReplacementCandidate choice A hA δ γ) :
    ReplacementState := choice.state F.shifted F.shifted_nonempty

/-- The retained set is genuinely contained in the current population. -/
theorem retained_subset_points
    (F : FailingReplacementCandidate choice A hA δ γ) :
    F.retained ⊆ (choice.state A hA).points :=
  F.retained_subset_core.trans (choice.state A hA).structuredCore_subset_points

/-- Retention before the explicitly recorded CFP loss. -/
theorem retained_card_le_core
    (F : FailingReplacementCandidate choice A hA δ γ) :
    F.retained.card ≤ (choice.state A hA).structuredCore.card :=
  Finset.card_le_card F.retained_subset_core

/-- Translation loses no points. -/
@[simp] theorem shifted_card
    (F : FailingReplacementCandidate choice A hA δ γ) :
    F.shifted.card = F.retained.card := by
  simp [shifted]

/-- The actual next population is exactly the translated retained set. -/
@[simp] theorem next_points
    (F : FailingReplacementCandidate choice A hA δ γ) :
    F.next.points = F.shifted := rfl

/-- The replacement itself loses no points beyond selecting `retained`:
translation preserves its exact cardinality. -/
theorem next_card_eq_retained
    (F : FailingReplacementCandidate choice A hA δ γ) :
    F.next.points.card = F.retained.card := by
  change F.shifted.card = F.retained.card
  exact F.shifted_card

/-- Dense cardinal retention for the actual next population. -/
theorem dense_le_next_card
    (F : FailingReplacementCandidate choice A hA δ γ) :
    δ * (A.card : ℝ) ≤ (F.next.points.card : ℝ) := by
  simpa only [F.next_card_eq_retained] using F.dense

/-- After applying the selected structure theorem to the translated set,
only its explicitly recorded loss can disappear from its structured core. -/
theorem card_sub_loss_le_nextCore
    (F : FailingReplacementCandidate choice A hA δ γ) :
    F.retained.card - choice.loss F.shifted ≤
      F.next.structuredCore.card := by
  rw [← F.shifted_card]
  exact (choice.witness F.shifted).card_sub_loss_le_core

/-- Combined dense-retention statement, with the selected CFP loss displayed
rather than hidden in asymptotic notation. -/
theorem dense_le_next_add_loss
    (F : FailingReplacementCandidate choice A hA δ γ) :
    δ * (A.card : ℝ) ≤
      (F.next.structuredCore.card : ℝ) + (choice.loss F.shifted : ℝ) := by
  have hlarge := choice.card_le_state_add_loss F.shifted F.shifted_nonempty
  have hcast : (F.shifted.card : ℝ) ≤
      (F.next.structuredCore.card : ℝ) + (choice.loss F.shifted : ℝ) := by
    exact_mod_cast hlarge
  rw [F.shifted_card] at hcast
  exact F.dense.trans hcast

/-- Nonaveraging passes from the original set to the actual selected next
state of a failing candidate. -/
theorem next_nonaveraging
    (F : FailingReplacementCandidate choice A hA δ γ)
    (hNA : IsBoxNonaveraging A) : IsBoxNonaveraging F.next.points := by
  have hretained : IsBoxNonaveraging F.retained :=
    isBoxNonaveraging_mono hNA
      (F.retained_subset_core.trans (choice.state_core_subset A hA))
  have hshifted : IsBoxNonaveraging F.shifted := by
    exact isBoxNonaveraging_translate (-F.translationPoint) hretained
  simpa [next, StructureChoice.state] using hshifted

end FailingReplacementCandidate

/-- Failure of Definition 9 is exactly the existence of a concrete dense
translated subset whose selected rank changes or whose GAP is too small. -/
theorem not_irreducible_iff_exists_failingCandidate
    (choice : StructureChoice) {d : ℕ} (A : Finset (BoxPoint d))
    (hA : A.Nonempty) (δ γ : ℝ) :
    ¬ IsIrreducible choice A hA δ γ ↔
      Nonempty (FailingReplacementCandidate choice A hA δ γ) := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro X hXsub hXne hdense x hx
    by_contra hgood
    apply hnone
    have hfailure :
        let next := choice.state (translate (-x) X)
          (translate_nonempty (-x) hXne)
        next.rank ≠ (choice.state A hA).rank ∨
          (next.progression.volume : ℝ) <
            γ * ((choice.state A hA).progression.volume : ℝ) := by
      dsimp only at hgood ⊢
      by_cases hdim :
          (choice.state (translate (-x) X)
              (translate_nonempty (-x) hXne)).rank =
            (choice.state A hA).rank
      · right
        exact lt_of_not_ge (fun hvolume ↦ hgood ⟨hdim, hvolume⟩)
      · exact Or.inl hdim
    exact ⟨{
      retained := X
      retained_subset_core := hXsub
      retained_nonempty := hXne
      dense := hdense
      translationPoint := x
      translationPoint_mem := hx
      failure := hfailure }⟩
  · rintro ⟨F⟩ hirr
    have hgood := hirr F.retained F.retained_subset_core
      F.retained_nonempty F.dense F.translationPoint F.translationPoint_mem
    rcases F.failure with hdim | hvolume
    · exact hdim hgood.1
    · exact (not_lt_of_ge hgood.2) hvolume

/-- One actual replacement in the irreducibility reduction.

The next set is identified with `retained`, an honest subset of the current
set at the level of cardinality.  The explicit transport implication records
the source-specific subset/coordinate/translation proof of nonaveraging.  The
numerical fields are exactly the
one-step hypotheses of `Irreducible.MoveTrace`. -/
structure ReplacementStep (p : MoveParameters)
    (current next : ReplacementState) where
  kind : MoveKind
  retained : Finset (BoxPoint current.ambientDimension)
  retained_subset : retained ⊆ current.points
  next_card_eq_retained : next.points.card = retained.card
  nonaveraging_transport :
    IsBoxNonaveraging current.points → IsBoxNonaveraging next.points
  population_retained :
    p.retention * (current.points.card : ℝ) ≤ (next.points.card : ℝ)
  upSaving : ℝ
  upSaving_nonneg : 0 ≤ upSaving
  dimension_rule :
    match kind with
    | .up => current.rank < next.rank
    | .down => next.rank < current.rank
    | .shrink => next.rank = current.rank
  gap_control :
    (next.progression.volume : ℝ) ≤
      stepMultiplier p kind upSaving * (current.progression.volume : ℝ)
  upSaving_control : kind = .up →
    upSaving ≤ p.upBase ^ (next.rank - current.rank)

namespace ReplacementStep

variable {p : MoveParameters} {current next : ReplacementState}

/-- The transport data identify the next set and retained set cardinalities. -/
theorem card_next_eq_card_retained (s : ReplacementStep p current next) :
    next.points.card = s.retained.card := s.next_card_eq_retained

/-- Every concrete replacement weakly decreases the actual set cardinality. -/
theorem card_next_le_card_current (s : ReplacementStep p current next) :
    next.points.card ≤ current.points.card := by
  rw [s.card_next_eq_card_retained]
  exact Finset.card_le_card s.retained_subset

/-- Nonaveraging passes through a concrete replacement. -/
theorem nonaveraging_next (s : ReplacementStep p current next)
    (hcurrent : IsBoxNonaveraging current.points) :
    IsBoxNonaveraging next.points :=
  s.nonaveraging_transport hcurrent

/-- The explicit GAP bound in an up move. -/
theorem gap_control_up (s : ReplacementStep p current next)
    (h : s.kind = .up) :
    (next.progression.volume : ℝ) ≤
      p.cost * s.upSaving * (current.progression.volume : ℝ) := by
  simpa [stepMultiplier, h] using s.gap_control

/-- The explicit GAP bound in a down move. -/
theorem gap_control_down (s : ReplacementStep p current next)
    (h : s.kind = .down) :
    (next.progression.volume : ℝ) ≤
      p.cost * (current.progression.volume : ℝ) := by
  simpa [stepMultiplier, h] using s.gap_control

/-- The explicit GAP bound in a same-dimensional shrink move. -/
theorem gap_control_shrink (s : ReplacementStep p current next)
    (h : s.kind = .shrink) :
    (next.progression.volume : ℝ) ≤
      p.shrinkFactor * (current.progression.volume : ℝ) := by
  simpa [stepMultiplier, h] using s.gap_control

end ReplacementStep

/-! ## Finite chains and the bridge to `MoveTrace` -/

/-- A finite chain of actual replacement steps.  As with `MoveTrace`, states
are total functions, while step data are required only before `length`. -/
structure ReplacementChain (p : MoveParameters) (length : ℕ) where
  state : ℕ → ReplacementState
  step : ∀ i, i < length → ReplacementStep p (state i) (state (i + 1))

namespace ReplacementChain

variable {p : MoveParameters} {length : ℕ}

/-- Nonaveraging is preserved at every state of a concrete chain. -/
theorem nonaveraging (C : ReplacementChain p length)
    (hzero : IsBoxNonaveraging (C.state 0).points) {m : ℕ}
    (hm : m ≤ length) : IsBoxNonaveraging (C.state m).points := by
  induction m with
  | zero => exact hzero
  | succ m ih =>
      exact (C.step m (by omega)).nonaveraging_next (ih (by omega))

/-- Cardinalities weakly decrease along a concrete replacement chain. -/
theorem card_antitone (C : ReplacementChain p length) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ length) :
    (C.state j).points.card ≤ (C.state i).points.card := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      exact (C.step j (by omega)).card_next_le_card_current.trans (ih (by omega))

/-- Forget all concrete set/GAP/transport data and retain exactly the
numerical trace used by the irreducibility termination argument. -/
noncomputable def toMoveTrace (C : ReplacementChain p length) :
    MoveTrace p length where
  state i := (C.state i).toIterationState
  kind i := if hi : i < length then (C.step i hi).kind else .shrink
  upSaving i := if hi : i < length then (C.step i hi).upSaving else 1
  upSaving_nonneg i hi := by
    simpa [hi] using (C.step i hi).upSaving_nonneg
  population_retained i hi := by
    simpa [hi] using (C.step i hi).population_retained
  dimension_rule i hi := by
    rw [show (if h : i < length then (C.step i h).kind else .shrink) =
      (C.step i hi).kind by simp [hi]]
    exact (C.step i hi).dimension_rule
  gap_control i hi := by
    simpa [hi] using (C.step i hi).gap_control
  upSaving_control i hi hkind := by
    have hk : (C.step i hi).kind = .up := by
      simpa [hi] using hkind
    simpa [hi] using (C.step i hi).upSaving_control hk

@[simp] theorem toMoveTrace_state (C : ReplacementChain p length) (i : ℕ) :
    (C.toMoveTrace.state i) = (C.state i).toIterationState := rfl

@[simp] theorem toMoveTrace_kind (C : ReplacementChain p length) {i : ℕ}
    (hi : i < length) : C.toMoveTrace.kind i = (C.step i hi).kind := by
  simp [toMoveTrace, hi]

@[simp] theorem toMoveTrace_upSaving (C : ReplacementChain p length) {i : ℕ}
    (hi : i < length) : C.toMoveTrace.upSaving i = (C.step i hi).upSaving := by
  simp [toMoveTrace, hi]

/-- Concrete-chain form of the iterated population-retention estimate. -/
theorem retention_pow_mul_card_le (C : ReplacementChain p length) {m : ℕ}
    (hm : m ≤ length) :
    p.retention ^ m * ((C.state 0).points.card : ℝ) ≤
      ((C.state m).points.card : ℝ) := by
  simpa using retention_pow_mul_le_population C.toMoveTrace hm

/-- Concrete-chain form of the collected uniform GAP-volume estimate. -/
theorem volume_le_uniform_product (C : ReplacementChain p length) {m : ℕ}
    (hm : m ≤ length) :
    ((C.state m).progression.volume : ℝ) ≤
      p.cost ^ (kindCount C.toMoveTrace .up m +
          kindCount C.toMoveTrace .down m) *
        p.shrinkFactor ^ kindCount C.toMoveTrace .shrink m *
          p.upBase ^ upwardJump C.toMoveTrace m *
            ((C.state 0).progression.volume : ℝ) := by
  simpa using gapSize_le_uniform_product C.toMoveTrace hm

/-- Concrete-chain form of the bound on dimension-changing moves. -/
theorem changingMoveCount_le_of_upwardJump_le
    (C : ReplacementChain p length) {m jumpBound : ℕ}
    (hm : m ≤ length) (hjump : upwardJump C.toMoveTrace m ≤ jumpBound) :
    kindCount C.toMoveTrace .up m + kindCount C.toMoveTrace .down m ≤
      (C.state 0).rank + 2 * jumpBound := by
  simpa using Irreducible.changingMoveCount_le_of_upwardJump_le
    C.toMoveTrace hm hjump

/-- Concrete-chain form of the explicit termination estimate. -/
theorem length_le_of_upwardJump_and_budget
    (C : ReplacementChain p length) {jumpBound shrinkBound : ℕ}
    (hjump : upwardJump C.toMoveTrace length ≤ jumpBound)
    (hbudget :
      p.cost ^ ((C.state 0).rank + 2 * jumpBound) *
          p.shrinkFactor ^ (shrinkBound + 1) *
            ((C.state 0).progression.volume : ℝ) < 1) :
    length ≤ (C.state 0).rank + 2 * jumpBound + shrinkBound := by
  simpa using Irreducible.length_le_of_upwardJump_and_budget
    C.toMoveTrace hjump hbudget

end ReplacementChain

end

end Erdos186.PZ.Reduction
