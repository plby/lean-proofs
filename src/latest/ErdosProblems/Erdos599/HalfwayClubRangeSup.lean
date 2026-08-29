/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClubGeometry

/-!
# Club-valued suprema of indexed half-way stages

A half-way scheduler may be indexed in a universe larger than the vertex
universe.  If its index type has cardinality at most `kappa`, the supremum
of its stages below `succ kappa` is still below `(succ kappa).ord`, because
the successor cardinal is regular.  Closure puts this supremum back in the
chosen club.

There are exactly two useful cases.  Either the supremum is attained by a
stage of the family, or every stage is strictly below it and its underlying
ordinal is a genuine nonzero limit.  This is the order package consumed by
the proper-limit compiler; no supremum field is added to scheduler states.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace HalfwayClubRangeSup

universe u v

variable {kappa : Cardinal.{u}}
variable {I : Type v} [LinearOrder I] [Nonempty I]

/-- The ordinal supremum of an indexed family of stages below
`succ kappa`, represented again as an actual ladder stage. -/
noncomputable def rangeSup
    (hkappa : Cardinal.aleph0 ≤ kappa)
    (hI : Cardinal.lift.{u} #I ≤ Cardinal.lift.{v} kappa)
    (index : I → Ladder.Stage (succ kappa)) :
    Ladder.Stage (succ kappa) :=
  ⟨⨆ i, (index i).1, by
    apply Stationary.lift_iSup_lt_ord_of_lt
      (Cardinal.isRegular_succ hkappa)
    · exact hI.trans_lt (Cardinal.lift_lt.mpr (lt_succ kappa))
    · exact fun i ↦ (index i).2⟩

/-- `rangeSup` is the least upper bound of the indexed range. -/
theorem rangeSup_isLUB
    (hkappa : Cardinal.aleph0 ≤ kappa)
    (hI : Cardinal.lift.{u} #I ≤ Cardinal.lift.{v} kappa)
    (index : I → Ladder.Stage (succ kappa)) :
    IsLUB (Set.range index) (rangeSup hkappa hI index) := by
  constructor
  · rintro _ ⟨i, rfl⟩
    change (index i).1 ≤ ⨆ j, (index j).1
    have hbdd : BddAbove (Set.range fun j : I ↦ (index j).1) := by
      refine ⟨(succ kappa).ord, ?_⟩
      rintro _ ⟨j, rfl⟩
      exact (index j).2.le
    exact le_ciSup hbdd i
  · intro b hb
    change (⨆ i, (index i).1) ≤ b.1
    apply Ordinal.iSup_le
    intro i
    exact hb ⟨i, rfl⟩

/-- Every indexed stage lies below the range supremum. -/
theorem le_rangeSup
    (hkappa : Cardinal.aleph0 ≤ kappa)
    (hI : Cardinal.lift.{u} #I ≤ Cardinal.lift.{v} kappa)
    (index : I → Ladder.Stage (succ kappa)) (i : I) :
    index i ≤ rangeSup hkappa hI index :=
  (rangeSup_isLUB hkappa hI index).1 ⟨i, rfl⟩

/-- Complete club-valued supremum data for an indexed scheduler family. -/
structure Data
    (Sigma : Set (Ladder.Stage (succ kappa)))
    (index : I → Ladder.Stage (succ kappa)) where
  supIndex : Ladder.Stage (succ kappa)
  supIndex_mem : supIndex ∈ Sigma
  range_isLUB : IsLUB (Set.range index) supIndex
  monotone : Monotone index
  previous_le : ∀ i, index i ≤ supIndex
  attained_or_genuineLimit :
    (∃ i, index i = supIndex) ∨
      ((∀ i, index i < supIndex) ∧ Order.IsSuccLimit supIndex.1)

/-- Construct the actual club member which is the indexed range supremum.
The construction is universe-polymorphic in the scheduler index type. -/
theorem exists_data
    (hkappa : Cardinal.aleph0 ≤ kappa)
    (hI : Cardinal.lift.{u} #I ≤ Cardinal.lift.{v} kappa)
    {Sigma : Set (Ladder.Stage (succ kappa))}
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (index : I → Ladder.Stage (succ kappa))
    (hmono : Monotone index)
    (hindexSigma : ∀ i, index i ∈ Sigma) :
    Nonempty (Data Sigma index) := by
  let a := rangeSup hkappa hI index
  have hLUB : IsLUB (Set.range index) a :=
    rangeSup_isLUB hkappa hI index
  have hrange : (Set.range index).Nonempty := by
    let i : I := Classical.choice inferInstance
    exact ⟨index i, i, rfl⟩
  have hrangeSigma : Set.range index ⊆ Sigma := by
    rintro _ ⟨i, rfl⟩
    exact hindexSigma i
  have haSigma : a ∈ Sigma :=
    Stationary.mem_club_of_isLUB hSigma hrangeSigma hrange hLUB
  refine ⟨{
    supIndex := a
    supIndex_mem := haSigma
    range_isLUB := hLUB
    monotone := hmono
    previous_le := fun i ↦ hLUB.1 ⟨i, rfl⟩
    attained_or_genuineLimit := ?_ }⟩
  by_cases hattained : a ∈ Set.range index
  · exact Or.inl hattained
  · apply Or.inr
    have hstrict : ∀ i, index i < a := by
      intro i
      exact lt_of_le_of_ne (hLUB.1 ⟨i, rfl⟩) (by
        intro hi
        exact hattained ⟨i, hi⟩)
    refine ⟨hstrict, ?_⟩
    exact (hLUB.isSuccLimit_of_notMem hrange hattained).subtypeVal
      (isLowerSet_Iio _)

/-- The nonattained branch exposed without unpacking `Data`. -/
theorem all_lt_and_isSuccLimit_of_not_mem_range
    (hkappa : Cardinal.aleph0 ≤ kappa)
    (hI : Cardinal.lift.{u} #I ≤ Cardinal.lift.{v} kappa)
    (index : I → Ladder.Stage (succ kappa))
    (hnot : rangeSup hkappa hI index ∉ Set.range index) :
    (∀ i, index i < rangeSup hkappa hI index) ∧
      Order.IsSuccLimit (rangeSup hkappa hI index).1 := by
  have hLUB := rangeSup_isLUB hkappa hI index
  have hrange : (Set.range index).Nonempty := by
    let i : I := Classical.choice inferInstance
    exact ⟨index i, i, rfl⟩
  constructor
  · intro i
    exact lt_of_le_of_ne (hLUB.1 ⟨i, rfl⟩) (by
      intro hi
      exact hnot ⟨i, hi⟩)
  · exact (hLUB.isSuccLimit_of_notMem hrange hnot).subtypeVal
      (isLowerSet_Iio _)

end HalfwayClubRangeSup
end Erdos599
