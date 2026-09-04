/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyClosedThreats

/-! # Exact pair-star drift under a restricted uniform selector -/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

/-- The greedy step with its uniformly chosen selector restricted to `R`.
The nonemptiness argument provides normalization, not a success estimate. -/
def restrictedGreedyKernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (R : TripleSystemOn V) (hR : R.Nonempty) : FiniteLaw (GreedyStateOn V) :=
  let : Nonempty R := ⟨⟨hR.choose, hR.choose_spec⟩⟩
  FiniteLaw.map (fun T : R ↦ greedyStep F S T.1) FiniteLaw.uniform

theorem restrictedGreedyKernel_expectationReal
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (R : TripleSystemOn V) (hR : R.Nonempty) (φ : GreedyStateOn V → ℝ) :
    (restrictedGreedyKernel F S R hR).expectationReal φ =
      (R.card : ℝ)⁻¹ * ∑ T ∈ R, φ (greedyStep F S T) := by
  let : Nonempty R := ⟨⟨hR.choose, hR.choose_spec⟩⟩
  rw [restrictedGreedyKernel, FiniteLaw.expectationReal_map,
    FiniteLaw.expectationReal_uniform, Fintype.card_coe]
  congr 1
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach R (fun T ↦ φ (greedyStep F S T))

theorem restrictedGreedyKernel_pairStar_drift
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (hS : GreedyInvariant F S) {P : Finset V} (hP : P.card = 2)
    (hR : (S.available \ availableTrianglesContainingPair S P).Nonempty) :
    let Q := availableTrianglesContainingPair S P
    (restrictedGreedyKernel F S (S.available \ Q) hR).expectationReal
      (fun S' ↦ greedyAvailableCountReal Q S' - greedyAvailableCountReal Q S) =
        -(∑ U ∈ Q, (((greedyClosedThreats F S U).card : ℝ) - Q.card)) /
          ((S.available.card : ℝ) - Q.card) := by
  dsimp only
  let Q := availableTrianglesContainingPair S P
  have hQ : Q ⊆ S.available := fun _ h ↦
    (mem_availableTrianglesContainingPair_iff.mp h).1
  have htranspose :
      (∑ T ∈ S.available \ Q, ((Q ∩ greedyClosedThreats F S T).card : ℝ)) =
        ∑ U ∈ Q, (((greedyClosedThreats F S U).card : ℝ) - Q.card) := by
    have hnat := sum_nonPair_closedThreats_eq F S hP
    have hcast := congrArg (fun k : ℕ ↦ (k : ℝ)) hnat
    push_cast at hcast
    convert hcast using 1
    change (∑ U ∈ Q, (((greedyClosedThreats F S U).card : ℝ) - Q.card)) =
      ∑ U ∈ Q, (((greedyClosedThreats F S U).card - Q.card : ℕ) : ℝ)
    apply sum_congr rfl
    intro U hU
    exact (Nat.cast_sub (card_le_card (pairStar_subset_closedThreats F S hP hU))).symm
  rw [restrictedGreedyKernel_expectationReal]
  simp_rw [greedyAvailableCountReal_step_sub]
  have hdeletions :
      (∑ T ∈ S.available \ Q, ((greedyDeletedIn F Q S T).card : ℝ)) =
        ∑ T ∈ S.available \ Q, ((Q ∩ greedyClosedThreats F S T).card : ℝ) := by
    apply sum_congr rfl
    intro T hT
    rw [greedyDeletedIn_eq_inter_closedThreats hS (mem_sdiff.mp hT).1]
  change ((S.available \ Q).card : ℝ)⁻¹ *
    (∑ T ∈ S.available \ Q, -((greedyDeletedIn F Q S T).card : ℝ)) = _
  rw [sum_neg_distrib, hdeletions, htranspose, card_sdiff_of_subset hQ,
    Nat.cast_sub (card_le_card hQ)]
  ring

/-- In the source's open-threat convention the diagonal contributes `+1`.
It must be retained until the deterministic error estimate is applied. -/
theorem restrictedGreedyKernel_pairStar_drift_open
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (hS : GreedyInvariant F S) {P : Finset V} (hP : P.card = 2)
    (hR : (S.available \ availableTrianglesContainingPair S P).Nonempty) :
    let Q := availableTrianglesContainingPair S P
    (restrictedGreedyKernel F S (S.available \ Q) hR).expectationReal
      (fun S' ↦ greedyAvailableCountReal Q S' - greedyAvailableCountReal Q S) =
        -(∑ U ∈ Q, (((greedyOpenThreats F S U).card : ℝ) - Q.card + 1)) /
          ((S.available.card : ℝ) - Q.card) := by
  dsimp only
  rw [restrictedGreedyKernel_pairStar_drift hS hP hR]
  congr 2
  apply sum_congr rfl
  intro U hU
  rw [greedyClosedThreats_card_eq_open_add_one F S
    (mem_availableTrianglesContainingPair_iff.mp hU).1]
  push_cast
  ring

end

end Erdos207
