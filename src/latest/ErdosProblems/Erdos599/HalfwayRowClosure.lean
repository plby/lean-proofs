/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClause
import ErdosProblems.Erdos599.HalfwayStageGeometryCore

/-!
# Closing under the Section 9 row components

Assertion 9.31 closes its small set not only under the reference warp but
also under the earlier symmetric-difference/layer components of the two
slices.  This family is distinct from the later linkage which is fractured
at the closed set: the source explicitly does not claim that a path of that
later linkage meeting the closed set is contained in it.  This file adds the
former path closure to the explicit omega operator of Assertions 9.22--9.25
while preserving the same cardinal and roof bounds.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}

/-- One closing step with the additional row-component closure required by
Assertion 9.31. -/
def closingStepWithRow (Gamma : DWeb V)
    (Y row : Set Gamma.DPath) (rho : Cardinal.{u})
    (ZBefore innerRoof roof T B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧
        p.support ⊆ roof ∧ Preserves p)
    (X : Set V) : Set V :=
  closingStep Gamma Y rho ZBefore innerRoof roof T B Preserves hTarget X ∪
    meetingVertices Gamma row X

theorem subset_closingStepWithRow (Gamma : DWeb V)
    (Y row : Set Gamma.DPath) (rho : Cardinal.{u})
    (ZBefore innerRoof roof T B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧
        p.support ⊆ roof ∧ Preserves p)
    (X : Set V) :
    X ⊆ closingStepWithRow Gamma Y row rho ZBefore innerRoof roof T B
      Preserves hTarget X := by
  exact (subset_closingStep Gamma Y rho ZBefore innerRoof roof T B
    Preserves hTarget X).trans Set.subset_union_left

theorem mk_closingStepWithRow_le (Gamma : DWeb V)
    (Y row : Set Gamma.DPath) {rho kappa : Cardinal.{u}}
    (ZBefore innerRoof roof T B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧
        p.support ⊆ roof ∧ Preserves p)
    (hY : Gamma.IsWarp Y) (hrow : Gamma.IsWarp row)
    (hkappa : aleph0 ≤ kappa) (hrho : rho ≤ kappa)
    (hZBefore : #ZBefore ≤ kappa) (X : Set V) (hX : #X ≤ kappa) :
    #(closingStepWithRow Gamma Y row rho ZBefore innerRoof roof T B
      Preserves hTarget X) ≤ kappa := by
  apply (Cardinal.mk_union_le
    (closingStep Gamma Y rho ZBefore innerRoof roof T B Preserves hTarget X)
    (meetingVertices Gamma row X)).trans
  apply Cardinal.add_le_of_le hkappa
  · exact mk_closingStep_le Gamma Y ZBefore innerRoof roof T B Preserves
      hTarget hY hkappa hrho hZBefore X hX
  · exact mk_meetingVertices_le Gamma row X hrow hkappa hX

theorem closingStepWithRow_subset_roof (Gamma : DWeb V)
    (Y row : Set Gamma.DPath) (rho : Cardinal.{u})
    (ZBefore innerRoof roof T B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧
        p.support ⊆ roof ∧ Preserves p)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma Y
      ZBefore innerRoof roof)
    (hYroof : ∀ p ∈ Y, p.support ⊆ roof)
    (hrowRoof : ∀ p ∈ row, p.support ⊆ roof)
    (X : Set V) (hX : X ⊆ roof) :
    closingStepWithRow Gamma Y row rho ZBefore innerRoof roof T B
      Preserves hTarget X ⊆ roof := by
  apply Set.union_subset
  · exact closingStep_subset_roof Gamma Y rho ZBefore innerRoof roof T B
      Preserves hTarget hSafeRoof hYroof X hX
  · exact meetingVertices_subset_roof Gamma row X roof hrowRoof

/-- Assertions 9.22--9.25 with the additional earlier
symmetric-difference/layer-family closure used in Assertion 9.31.  No closure
under the later linkage to be fractured is asserted here. -/
theorem exists_assertions_9_22_to_9_25_with_rowClosure
    (Gamma : DWeb V) (Y row : Set Gamma.DPath)
    (rho kappa : Cardinal.{u})
    (ZBefore innerRoof roof T B X0 : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧
        p.support ⊆ roof ∧ Preserves p)
    (hY : Gamma.IsWarp Y) (hrow : Gamma.IsWarp row)
    (hYroof : ∀ p ∈ Y, p.support ⊆ roof)
    (hrowRoof : ∀ p ∈ row, p.support ⊆ roof)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma Y
      ZBefore innerRoof roof)
    (hkappa : aleph0 ≤ kappa) (hrho : rho ≤ kappa)
    (hZBefore : #ZBefore ≤ kappa)
    (hX0card : #X0 ≤ kappa) (hX0roof : X0 ⊆ roof) :
    ∃ Z : Set V,
      X0 ⊆ Z ∧ #Z ≤ kappa ∧
      HammockClosedUpTo Gamma Y Z ZBefore innerRoof roof rho ∧
      LargeHammockClosed Gamma Y Z ZBefore innerRoof roof rho ∧
      HasPreservingTargetPaths Gamma T Z B Preserves ∧
      ClosedUnderPaths Gamma Y Z ∧
      ClosedUnderPaths Gamma row Z ∧
      ContainedInRoof Z roof := by
  let step : Set V → Set V :=
    closingStepWithRow Gamma Y row rho ZBefore innerRoof roof T B
      Preserves hTarget
  let Z : Set V := omegaClosure step X0
  have hstageCard : ∀ n, #(closureStage step X0 n) ≤ kappa := by
    apply mk_closureStage_le hX0card
    intro X hX
    exact mk_closingStepWithRow_le Gamma Y row ZBefore innerRoof roof T B
      Preserves hTarget hY hrow hkappa hrho hZBefore X hX
  have hstageRoof : ∀ n, closureStage step X0 n ⊆ roof := by
    apply closureStage_subset_roof hX0roof
    intro X hX
    exact closingStepWithRow_subset_roof Gamma Y row rho ZBefore innerRoof
      roof T B Preserves hTarget hSafeRoof hYroof hrowRoof X hX
  have hZroof : Z ⊆ roof := by
    intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
    exact hstageRoof n hxn
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hZroof⟩
  · exact closureStage_subset_omegaClosure step X0 0
  · change #(⋃ n, closureStage step X0 n) ≤ kappa
    let stages : ULift.{u} Nat → Set V :=
      fun n => closureStage step X0 n.down
    have heq : (⋃ n, closureStage step X0 n) = ⋃ i, stages i := by
      ext x
      simp [stages]
    rw [heq]
    apply CardinalInduction.mk_iUnion_le_of_le hkappa
    · simpa [Cardinal.mk_nat] using hkappa
    · intro i
      exact hstageCard i.down
  · intro u e helig
    let q : EligiblePair ZBefore innerRoof roof := ⟨(u, e), helig⟩
    refine ⟨chosenHammock Gamma Y rho q,
      chosenHammock_spec Gamma Y rho q, ?_⟩
    apply (chosenHammock_contained_all Gamma Y rho q).trans
    apply (allHammockVertices_subset_closingStep Gamma Y rho ZBefore
      innerRoof roof T B Preserves hTarget X0).trans
    apply Set.subset_union_left.trans
    change step X0 ⊆ Z
    exact closureStage_subset_omegaClosure step X0 1
  · intro u e helig hlarge
    let q : EligiblePair ZBefore innerRoof roof := ⟨(u, e), helig⟩
    refine ⟨chosenHammock Gamma Y rho q,
      (chosenHammock_spec Gamma Y rho q).isHammock,
      chosenHammock_card_eq_of_hasHammockCard Gamma Y rho q hlarge, ?_⟩
    apply (chosenHammock_contained_all Gamma Y rho q).trans
    apply (allHammockVertices_subset_closingStep Gamma Y rho ZBefore
      innerRoof roof T B Preserves hTarget X0).trans
    apply Set.subset_union_left.trans
    change step X0 ⊆ Z
    exact closureStage_subset_omegaClosure step X0 1
  · intro v hv
    have hvRoof : v ∈ roof := hZroof hv.2
    let tv : TargetVertex T roof := ⟨v, hv.1, hvRoof⟩
    let p := targetChoice Gamma T roof B Preserves hTarget tv
    obtain ⟨n, hvn⟩ := Set.mem_iUnion.1 hv.2
    have hpSupport : p.support ⊆ Z := by
      have hpTarget : p.support ⊆
          targetVertices Gamma T roof B Preserves hTarget
            (closureStage step X0 n) := by
        intro x hx
        exact Set.mem_iUnion.2 ⟨⟨tv, hvn⟩, hx⟩
      apply hpTarget.trans
      apply (targetVertices_subset_closingStep Gamma Y rho ZBefore
        innerRoof roof T B Preserves hTarget
          (closureStage step X0 n)).trans
      apply Set.subset_union_left.trans
      change step (closureStage step X0 n) ⊆ Z
      exact closureStage_subset_omegaClosure step X0 (n + 1)
    exact ⟨p, (targetChoice_spec Gamma T roof B Preserves hTarget tv).1,
      (targetChoice_spec Gamma T roof B Preserves hTarget tv).2.1,
      hpSupport,
      (targetChoice_spec Gamma T roof B Preserves hTarget tv).2.2.2⟩
  · intro p hpY hpMeet
    obtain ⟨x, hxp, hxZ⟩ := hpMeet
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hxZ
    apply (support_subset_meetingVertices Gamma Y
      (closureStage step X0 n) hpY ⟨x, hxp, hxn⟩).trans
    apply (meetingVertices_subset_closingStep Gamma Y rho ZBefore
      innerRoof roof T B Preserves hTarget
        (closureStage step X0 n)).trans
    apply Set.subset_union_left.trans
    change step (closureStage step X0 n) ⊆ Z
    exact closureStage_subset_omegaClosure step X0 (n + 1)
  · intro p hpRow hpMeet
    obtain ⟨x, hxp, hxZ⟩ := hpMeet
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hxZ
    apply (support_subset_meetingVertices Gamma row
      (closureStage step X0 n) hpRow ⟨x, hxp, hxn⟩).trans
    apply Set.subset_union_right.trans
    change step (closureStage step X0 n) ⊆ Z
    exact closureStage_subset_omegaClosure step X0 (n + 1)

end LinkageBlueprint
end Blueprint
end Erdos599
