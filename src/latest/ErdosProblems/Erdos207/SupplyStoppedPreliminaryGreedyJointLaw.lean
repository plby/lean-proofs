/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminarySurvivalScalar
import ErdosProblems.Erdos207.PreliminaryAugmentedReserveLaw

/-!
# The local-supply-stopped process supplies the preliminary joint law

This is the concrete form of the preliminary-process estimate.  It combines
the local pair-extension stopping rule, the Bernoulli survival calculation,
and the identification of uncovered crossing edges with the residual graph.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Empty initial choice leaves every crossing edge uncovered. -/
lemma supply_greedyUncoveredEdges_eq_self_of_chosen_eq_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (S : GreedyStateOn V)
    (hchosen : S.chosen = ∅) :
    greedyUncoveredEdges E S = E := by
  unfold greedyUncoveredEdges
  rw [hchosen]
  ext e
  simp [mem_graphEdges_iff, coveredGraph_adj]

/-- Equation (8.7) for the process stopped at either global supply loss or
loss of the local choice floor through an uncovered crossing edge. -/
theorem supplyStoppedGreedyProcess_probability_selected_preliminaryResidual_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (D M k fuel : ℕ) (hD : 0 < D) (hkM : k ≤ M)
    (alpha eta epsilon : ℝ≥0) (S₀ : GreedyStateOn V)
    (hchosen₀ : S₀.chosen = ∅)
    (hactive₀ : preliminarySupplyActive G U D (3 * k) S₀)
    (hupper : ∀ S, preliminarySupplyActive G U D (3 * k) S →
      S.available.card ≤ M)
    (hselected : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (fuel - Q.card)) ≤ eta)
    (hinactive :
      (supplyStoppedGreedyProcessLaw F G U D (3 * k) fuel S₀).probability
        (fun S ↦ ¬ preliminarySupplyActive G U D (3 * k) S) ≤ epsilon)
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) :
    (supplyStoppedGreedyProcessLaw F G U D (3 * k) fuel S₀).probability
        (fun S ↦ Q ⊆ S.chosen ∧
          E ⊆ preliminaryResidualCrossingEdges G U S.chosen) ≤
      alpha ^ Q.card * eta ^ E.card + epsilon := by
  let theta : ℝ≥0 :=
    ((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹
  let L := supplyStoppedGreedyProcessLaw F G U D (3 * k) fuel S₀
  have hscalar : ∀ S B, preliminarySupplyActive G U D (3 * k) S →
      B ⊆ greedyUncoveredEdges (crossingEdges G U) S →
      ((S.available.card - B.card * (3 * k) / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card := by
    intro S B hactive _hB
    have hA : 0 < S.available.card :=
      lt_of_lt_of_le hD hactive.1
    exact preliminary_survival_scalar S.available.card M k B.card
      hA (hupper S hactive) hkM
  by_cases hE : E ⊆ crossingEdges G U
  · have hQ : Disjoint Q S₀.chosen := by
      rw [hchosen₀]
      simp
    have hB : E ⊆
        greedyUncoveredEdges (crossingEdges G U) S₀ := by
      rw [supply_greedyUncoveredEdges_eq_self_of_chosen_eq_empty
        (crossingEdges G U) S₀ hchosen₀]
      exact hE
    simpa only [L, theta,
      greedyUncoveredCrossingEdges_eq_preliminaryResidual] using
      (supplyStoppedGreedyProcess_probability_selectedUncovered_le_product_add_inactive
        F G U D (3 * k) fuel hD theta alpha eta epsilon S₀ Q E
          hactive₀ hQ hB hscalar hselected (hsurvived Q) hinactive)
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
