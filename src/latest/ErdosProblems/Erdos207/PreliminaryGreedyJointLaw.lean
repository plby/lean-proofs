/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyCoveringChoiceCount
import ErdosProblems.Erdos207.PreliminaryAugmentedReserveLaw

/-!
# The stopped preliminary process supplies the augmented-reserve input

This file identifies the residual edge set in the stopped greedy process
with the crossing-edge remainder used by the master-law update.  It packages
the selected-triangle/uncovered-edge estimate in precisely the form required
by `PreliminaryAugmentedReserveLaw`.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

lemma greedyUncoveredCrossingEdges_eq_preliminaryResidual
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V) :
    greedyUncoveredEdges (crossingEdges G U) S =
      preliminaryResidualCrossingEdges G U S.chosen :=
  rfl

lemma greedyUncoveredEdges_eq_self_of_chosen_eq_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (S : GreedyStateOn V)
    (hchosen : S.chosen = ∅) :
    greedyUncoveredEdges E S = E := by
  unfold greedyUncoveredEdges
  rw [hchosen]
  ext e
  simp [greedyUncoveredEdges, mem_graphEdges_iff, coveredGraph_adj]

/-- Equation (8.7) for the concrete stopped preliminary process.  Prescribed
edges outside the crossing graph make the target event impossible; inside
the crossing graph the estimate is the product law plus the explicit
threshold-loss probability. -/
theorem stoppedGreedyProcess_probability_selected_preliminaryResidual_le_of_edgeSupply
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (D fuel : ℕ) (hD : 0 < D) (d : ℕ)
    (theta alpha eta epsilon : ℝ≥0) (S₀ : GreedyStateOn V)
    (hchosen₀ : S₀.chosen = ∅)
    (hactive₀ : D ≤ S₀.available.card)
    (hsupply : ∀ S B, D ≤ S.available.card →
      B ⊆ greedyUncoveredEdges (crossingEdges G U) S →
      ∀ e ∈ B, d ≤ (greedyChoicesCoveringEdge S e).card)
    (hscalar : ∀ S B, D ≤ S.available.card →
      B ⊆ greedyUncoveredEdges (crossingEdges G U) S →
      ((S.available.card - B.card * d / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card)
    (hselected : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      theta ^ (fuel - Q.card) ≤ eta)
    (hinactive :
      (stoppedGreedyProcessLaw F D fuel S₀).probability (fun S ↦
        ¬ D ≤ S.available.card) ≤ epsilon)
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) :
    (stoppedGreedyProcessLaw F D fuel S₀).probability (fun S ↦
        Q ⊆ S.chosen ∧
          E ⊆ preliminaryResidualCrossingEdges G U S.chosen) ≤
      alpha ^ Q.card * eta ^ E.card + epsilon := by
  let L := stoppedGreedyProcessLaw F D fuel S₀
  by_cases hE : E ⊆ crossingEdges G U
  · have hQ : Disjoint Q S₀.chosen := by
      rw [hchosen₀]
      simp
    have hB : E ⊆
        greedyUncoveredEdges (crossingEdges G U) S₀ := by
      rw [greedyUncoveredEdges_eq_self_of_chosen_eq_empty
        (crossingEdges G U) S₀ hchosen₀]
      exact hE
    simpa only [L,
      greedyUncoveredCrossingEdges_eq_preliminaryResidual] using
      (stoppedGreedyProcess_probability_selectedUncovered_le_product_add_inactive_of_edgeSupply
        F D fuel hD d theta alpha eta epsilon
          (crossingEdges G U) S₀ Q E hactive₀ hQ hB
          hsupply hscalar hselected (hsurvived Q) hinactive)
  · calc
      L.probability (fun S ↦ Q ⊆ S.chosen ∧
          E ⊆ preliminaryResidualCrossingEdges G U S.chosen) ≤
          L.probability (fun _ ↦ False) := by
        apply L.probability_mono
        intro S h
        exact hE (h.2.trans
          (preliminaryResidualCrossingEdges_subset_crossingEdges
            G U S.chosen))
      _ = 0 := L.probability_false
      _ ≤ alpha ^ Q.card * eta ^ E.card + epsilon := bot_le

end

end Erdos207
