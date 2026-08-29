/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularSuccessorStage

/-!
# Limit coordinates for the regular slice recursion

At a limit recursion index, the left coordinate of the next controlled
slice is the supremum of the right coordinates used at all earlier stages.
This file isolates the order-theoretic part of that construction.

The essential points are:

* the predecessor type below a stage has cardinality strictly below the
  ambient cardinal;
* regularity therefore keeps the supremum of the earlier coordinates below
  the initial ordinal of the cardinal;
* if all earlier coordinates lie in the fixed club `Sigma`, club closure puts
  their nonempty supremum back in `Sigma`;
* the `previous_index_le` invariant makes the earlier right coordinates
  strictly increasing, hence monotone and cofinal in their supremum.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace SliceSpliceConstructor
namespace LocalConstruction

universe u

variable {V : Type u}

/-- A proper initial segment of the stage order below `kappa` has cardinality
strictly below the lift of `kappa` to the universe containing `Stage kappa`.

This is the cardinal estimate used to keep a limit-stage supremum below
`kappa.ord`. -/
theorem mk_Iio_stage_lt_lift {kappa : Cardinal.{u}}
    (i : Ladder.Stage kappa) :
    #(Set.Iio i) < Cardinal.lift.{u + 1, u} kappa := by
  let e : Set.Iio i → Set.Iio i.1 := fun j ↦ ⟨j.1.1, j.2⟩
  have he : Function.Injective e := by
    intro j l hjl
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Set.Iio i.1 ↦ z.1) hjl
  calc
    #(Set.Iio i) ≤ #(Set.Iio i.1) := Cardinal.mk_le_of_injective he
    _ = Cardinal.lift.{u + 1, u} i.1.card := by
      rw [Cardinal.mk_Iio_ordinal]
    _ < Cardinal.lift.{u + 1, u} kappa :=
      Cardinal.lift_lt.mpr (Cardinal.lt_ord.mp i.2)

/-- The supremum, still represented as a stage below `kappa`, of a family
indexed by the predecessors of one stage. -/
noncomputable def limitRangeSup {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (i : Ladder.Stage kappa)
    (f : Set.Iio i → Ladder.Stage kappa) : Ladder.Stage kappa :=
  ⟨⨆ j, (f j).1, by
    apply Stationary.lift_iSup_lt_ord_of_lt hkappa
    · rw [Cardinal.lift_id'.{u, u + 1}]
      exact mk_Iio_stage_lt_lift i
    · exact fun j ↦ (f j).2⟩

/-- `limitRangeSup` is the least upper bound of the range of the indexed
family. -/
theorem limitRangeSup_isLUB {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (i : Ladder.Stage kappa)
    (f : Set.Iio i → Ladder.Stage kappa) :
    IsLUB (Set.range f) (limitRangeSup hkappa i f) := by
  constructor
  · rintro x ⟨j, rfl⟩
    change (f j).1 ≤ ⨆ l, (f l).1
    exact Ordinal.le_iSup (fun l ↦ (f l).1) j
  · intro a ha
    change (⨆ j, (f j).1) ≤ a.1
    apply Ordinal.iSup_le
    intro j
    exact ha ⟨j, rfl⟩

/-- Every member of the indexed family is below its limit supremum. -/
theorem le_limitRangeSup {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (i : Ladder.Stage kappa)
    (f : Set.Iio i → Ladder.Stage kappa) (j : Set.Iio i) :
    f j ≤ limitRangeSup hkappa i f :=
  (limitRangeSup_isLUB hkappa i f).1 ⟨j, rfl⟩

/-- If the index is a limit and the family is strictly increasing, every
earlier value is *strictly* below the range supremum. -/
theorem lt_limitRangeSup_of_strictMono {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (i : Ladder.Stage kappa)
    (hi : Order.IsSuccLimit i.1)
    (f : Set.Iio i → Ladder.Stage kappa) (hf : StrictMono f)
    (j : Set.Iio i) :
    f j < limitRangeSup hkappa i f := by
  have hsucc : Order.succ j.1.1 < i.1 := hi.succ_lt j.2
  let lStage : Ladder.Stage kappa :=
    ⟨Order.succ j.1.1, hsucc.trans i.2⟩
  let l : Set.Iio i := ⟨lStage, hsucc⟩
  have hjl : j < l := by
    exact Order.lt_succ j.1.1
  exact (hf hjl).trans_le (le_limitRangeSup hkappa i f l)

/-- A nonempty indexed family is cofinal below its least upper bound.  This
form is convenient at limit stages: every coordinate strictly below the
chosen limit coordinate is strictly below some earlier right coordinate. -/
theorem exists_lt_of_lt_limitRangeSup {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (i : Ladder.Stage kappa)
    (f : Set.Iio i → Ladder.Stage kappa)
    (a : Ladder.Stage kappa) (ha : a < limitRangeSup hkappa i f) :
    ∃ j : Set.Iio i, a < f j := by
  by_contra h
  push_neg at h
  have haUpper : a ∈ upperBounds (Set.range f) := by
    rintro x ⟨j, rfl⟩
    exact h j
  exact (not_le_of_gt ha) ((limitRangeSup_isLUB hkappa i f).2 haUpper)

/-- The complete order-theoretic package needed at a limit stage. -/
structure LimitIndexData {kappa : Cardinal.{u}}
    (Sigma : Set (Ladder.Stage kappa)) (i : Ladder.Stage kappa)
    (f : Set.Iio i → Ladder.Stage kappa) where
  index : Ladder.Stage kappa
  index_mem : index ∈ Sigma
  range_isLUB : IsLUB (Set.range f) index
  strictMono : StrictMono f
  monotone : Monotone f
  previous_le : ∀ j, f j ≤ index
  previous_lt : ∀ j, f j < index
  index_isSuccLimit : Order.IsSuccLimit index.1
  cofinal : ∀ a, a < index → ∃ j, a < f j

/-- A strictly monotone family of club points indexed below a nonzero limit stage has
a club-valued supremum, together with its least-upper-bound and cofinality
properties. -/
theorem exists_limitIndexData {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) {Sigma : Set (Ladder.Stage kappa)}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (i : Ladder.Stage kappa) (hi : Order.IsSuccLimit i.1)
    (f : Set.Iio i → Ladder.Stage kappa)
    (hfmono : StrictMono f) (hfSigma : ∀ j, f j ∈ Sigma) :
    Nonempty (LimitIndexData Sigma i f) := by
  let alpha := limitRangeSup hkappa i f
  have hLUB : IsLUB (Set.range f) alpha :=
    limitRangeSup_isLUB hkappa i f
  have hiPos : (0 : Ordinal.{u}) < i.1 := hi.bot_lt
  have hkappaPos : (0 : Ordinal.{u}) < kappa.ord := hiPos.trans i.2
  let z : Ladder.Stage kappa := ⟨0, hkappaPos⟩
  let jz : Set.Iio i := ⟨z, hiPos⟩
  have hrange : (Set.range f).Nonempty := ⟨f jz, jz, rfl⟩
  have hRangeSigma : Set.range f ⊆ Sigma := by
    rintro x ⟨j, rfl⟩
    exact hfSigma j
  have halpha : alpha ∈ Sigma :=
    Stationary.mem_club_of_isLUB hSigma hRangeSigma hrange hLUB
  have hlt : ∀ j, f j < alpha :=
    lt_limitRangeSup_of_strictMono hkappa i hi f hfmono
  have halphaNotMem : alpha ∉ Set.range f := by
    rintro ⟨j, hj⟩
    have := hlt j
    rw [hj] at this
    exact (lt_irrefl alpha) this
  have halphaLimit : Order.IsSuccLimit alpha.1 := by
    exact (hLUB.isSuccLimit_of_notMem hrange halphaNotMem).subtypeVal
      (isLowerSet_Iio _)
  refine ⟨{
    index := alpha
    index_mem := halpha
    range_isLUB := hLUB
    strictMono := hfmono
    monotone := hfmono.monotone
    previous_le := fun j ↦ hLUB.1 ⟨j, rfl⟩
    previous_lt := hlt
    index_isSuccLimit := halphaLimit
    cofinal := ?_ }⟩
  intro a ha
  exact exists_lt_of_lt_limitRangeSup hkappa i f a ha

/-- The right-frontier coordinate supplied by an earlier recursive payload. -/
def previousNextIndex {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z : Set V}
    {i : Ladder.Stage kappa}
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      SliceSplice.StagePayload Gamma L Sigma Z) :
    Set.Iio i → Ladder.Stage kappa :=
  fun j ↦ (previous j.1 j.2).nextIndex

@[simp]
theorem previousNextIndex_apply {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z : Set V}
    {i : Ladder.Stage kappa}
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      SliceSplice.StagePayload Gamma L Sigma Z) (j : Set.Iio i) :
    previousNextIndex previous j = (previous j.1 j.2).nextIndex :=
  rfl

/-- Validity of every earlier payload makes the sequence of its right
frontier coordinates strictly increasing.  The strict step is the old
coordinate bound `previous_index_le` followed by `index_lt_next` at the
later payload. -/
theorem previousNextIndex_strictMono {kappa : Cardinal.{u}}
    {Gamma : DWeb V} {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A} {i : Ladder.Stage kappa}
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      SliceSplice.StagePayload Gamma L Sigma Z)
    (hprevious : ∀ j (hji : j < i),
      SliceSplice.IsValidStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji)) :
    StrictMono (previousNextIndex previous) := by
  intro j l hjl
  have hle := (hprevious l.1 l.2).previous_index_le j.1 hjl
  have hlt := (previous l.1 l.2).index_lt_next
  exact lt_of_le_of_lt hle hlt

/-- Every earlier right coordinate remains in the fixed club. -/
theorem previousNextIndex_mem {kappa : Cardinal.{u}}
    {Gamma : DWeb V} {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z : Set V}
    {i : Ladder.Stage kappa}
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      SliceSplice.StagePayload Gamma L Sigma Z) (j : Set.Iio i) :
    previousNextIndex previous j ∈ Sigma :=
  (previous j.1 j.2).next_mem

/-- Limit-index data specialized to a valid recursive history. -/
theorem exists_limitIndexData_of_validHistory
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    (hkappa : kappa.IsRegular)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (i : Ladder.Stage kappa) (hi : Order.IsSuccLimit i.1)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      SliceSplice.StagePayload Gamma L Sigma Z)
    (hprevious : ∀ j (hji : j < i),
      SliceSplice.IsValidStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji)) :
    Nonempty (LimitIndexData Sigma i (previousNextIndex previous)) :=
  exists_limitIndexData hkappa hSigma i hi (previousNextIndex previous)
    (previousNextIndex_strictMono previous hprevious)
    (previousNextIndex_mem previous)

end LocalConstruction
end SliceSpliceConstructor
end CardinalInduction
end Erdos599
