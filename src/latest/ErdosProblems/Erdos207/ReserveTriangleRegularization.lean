/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveRegularizationInputs
import ErdosProblems.Erdos207.GraphTwoDensityRegularization
import ErdosProblems.Erdos207.PairPatternIncidence

/-! # Regularizing the actual reserve-protected preliminary triangle family -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_reserveProtected_regularized_triangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U D : Finset V) (A : TripleSystemOn V)
    (p tau xi r : ℝ≥0) (omega : Sym2 V → Bool)
    (hG : GraphSupportedOn G (D : Set V))
    (hp : 0 < p) (hp1 : p ≤ 1) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hxi : xi ≤ 1 / 1536) (hr : r ≤ 1 / 24576)
    (hdensity : 6144 ≤ p ^ 4 * tau ^ 6 * D.card)
    (hinner : (U.card : ℝ≥0) ≤ p ^ 4 * tau ^ 6 * D.card / 1536)
    (hold : ∀ S ∈ smallCliqueFamily G D,
      |((properPatternExtensions A (cliquePattern S) univ).card : ℝ) -
        (p : ℝ) ^ S.card * (tau : ℝ) ^ (S.card.choose 2) * D.card| ≤
      (xi : ℝ) * ((p : ℝ) ^ S.card * (tau : ℝ) ^ (S.card.choose 2) * D.card) + S.card)
    (hgood : ∀ S ∈ smallCliqueFamily G D, ¬ ReserveCliqueExtensionLossEvent G U A S r omega)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hfailure : 2 * (D.card : ℝ) ^ 2 *
      Real.exp (-eta ^ 2 * ((p : ℝ) ^ 2 * tau * D.card) / 16) < 1) :
    ∃ B ⊆ reserveProtectedOuterAvailable G U (reserveEdges G U omega) A,
      ∀ e ∈ graphEdges (reserveProtectedOuterGraph G U (reserveEdges G U omega)),
        |((B.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) - (p : ℝ) ^ 2 * tau * D.card / 4| ≤
          eta * ((p : ℝ) ^ 2 * tau * D.card / 4) := by
  let Gstar := reserveProtectedOuterGraph G U (reserveEdges G U omega)
  let Astar := reserveProtectedOuterAvailable G U (reserveEdges G U omega) A
  have hGstar : GraphSupportedOn Gstar (D : Set V) :=
    fun {_ _} hadj ↦ hG ((reserveProtectedOuterGraph_le G U (reserveEdges G U omega)) hadj)
  have hAstar : ∀ T ∈ Astar, tripleEdgeFinset T ⊆ graphEdges Gstar := by
    intro T hT
    rw [graphEdges_reserveProtectedOuterGraph]
    exact (mem_reserveProtectedOuterAvailable_iff.mp hT).2
  have hdensityR : (6144 : ℝ) ≤ (p : ℝ) ^ 4 * (tau : ℝ) ^ 6 * D.card := by exact_mod_cast hdensity
  have hDpos : (0 : ℝ) < D.card := by
    by_contra hn
    have hz : (D.card : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (by positivity)
    rw [hz, mul_zero] at hdensityR
    norm_num at hdensityR
  have hinputs := reserveProtected_clique_regularization_inputs G U D A p tau xi r omega
    hG hp1 htau1 hxi hr hdensity hinner hold hgood
  apply exists_graph_twoDensity_triangle_regularized Gstar Astar 2 p tau D.card eta
    (by norm_num) (by exact_mod_cast hp) (by exact_mod_cast htau) hDpos heta heta1 hAstar
  · intro e he
    have hoff := Gstar.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he)
    have hc := Sym2.card_toFinset_of_not_isDiag e hoff
    have h := (hinputs e.toFinset (by omega) (by omega) (cliquePattern_edge_le Gstar e he)).1
    simpa only [hc, show (2 : ℕ).choose 2 = 1 by decide, pow_one, Astar,
      properPatternExtensions_edge_card
        (reserveProtectedOuterAvailable G U (reserveEdges G U omega) A) e hoff] using h
  · intro S hS2 hS4 hSG
    have h := (hinputs S hS2 hS4 hSG).2
    refine ⟨h.1, ?_⟩
    calc
      _ ≤ 2 * ((p : ℝ) ^ S.card * (tau : ℝ) ^ (S.card.choose 2) * D.card) := h.2
      _ = _ := by ring
  · have hcardR : ((graphEdges Gstar).card : ℝ) ≤ (D.card : ℝ) ^ 2 := by
      exact_mod_cast graphEdges_card_le_support_sq Gstar D hGstar
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcardR (by norm_num))
      (Real.exp_pos _).le).trans_lt hfailure

end

end Erdos207
