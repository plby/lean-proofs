/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GraphTwoDensityRegularization
import ErdosProblems.Erdos207.CliqueRegularizationScalars
import ErdosProblems.Erdos207.PairPatternIncidence

/-! # Actual iteration-typical stage data supply the triangle regularizer -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsIterationTypical.exists_regularized_triangles
    {V : Type*} [Fintype V] [DecidableEq V] {ell h : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V} {A : TripleSystemOn V}
    {p tau xi : ℝ≥0} (htyp : IsIterationTypical W k G A p tau xi h)
    (i : Fin ell) (hki : k.val ≤ i.val) (hh : 4 ≤ h)
    (hp : 0 < p) (hp1 : p ≤ 1) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hxi : xi ≤ 1 / 768)
    (hG : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G)
    (hdensity : 1536 ≤ p ^ 4 * tau ^ 6 * (W.U i.castSucc).card)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hfailure : 2 * ((W.U i.castSucc).card : ℝ) ^ 2 *
      Real.exp (-eta ^ 2 * ((p : ℝ) ^ 2 * tau * (W.U i.castSucc).card) / 16) < 1) :
    ∃ B ⊆ A, ∀ e ∈ graphEdges G,
      |((B.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) -
        (p : ℝ) ^ 2 * tau * (W.U i.castSucc).card / 4| ≤
      eta * ((p : ℝ) ^ 2 * tau * (W.U i.castSucc).card / 4) := by
  let U := W.U i.castSucc
  have hvertices : ∀ T ∈ A, T.1 ⊆ U :=
    fun T hT ↦ triple_supported_of_graph_edges G U T hG (hA T hT)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpR1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp1
  have htauR : (0 : ℝ) < tau := by exact_mod_cast htau
  have htauR1 : (tau : ℝ) ≤ 1 := by exact_mod_cast htau1
  have hxiR : (xi : ℝ) ≤ 1 / 768 := by exact_mod_cast hxi
  have hdensityR : (1536 : ℝ) ≤ (p : ℝ) ^ 4 * (tau : ℝ) ^ 6 * U.card := by
    exact_mod_cast hdensity
  have hUpos : (0 : ℝ) < U.card := by
    by_contra hn
    have hz : (U.card : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (by positivity)
    rw [hz, mul_zero] at hdensityR
    norm_num at hdensityR
  have herror (S : Finset V) (hS2 : 2 ≤ S.card) (hS4 : S.card ≤ 4)
      (hSG : cliquePattern S ≤ G) :
      |((properPatternExtensions A (cliquePattern S) univ).card : ℝ) -
        (p : ℝ) ^ S.card * (tau : ℝ) ^ (S.card.choose 2) * U.card| ≤
        (xi : ℝ) * ((p : ℝ) ^ S.card * (tau : ℝ) ^ (S.card.choose 2) * U.card) + S.card := by
    rw [properPatternExtensions_univ_eq_of_supported A (cliquePattern S) U
      (cliquePattern_edges_nonempty S hS2) hvertices]
    exact htyp.clique_proper_extension_error i hki i.castSucc (Or.inl rfl) S hS2
      (hS4.trans hh) (cliquePattern_subset_supported_graph G S U hS2 hSG hG) hSG
  have htarget (S : Finset V) (hS4 : S.card ≤ 4) :
      1536 ≤ (p : ℝ) ^ S.card * (tau : ℝ) ^ (S.card.choose 2) * U.card :=
    hdensityR.trans (small_clique_target_lower p tau U.card S.card hpR.le hpR1 htauR.le htauR1
      (by positivity) hS4)
  apply exists_graph_twoDensity_triangle_regularized G A 2 p tau U.card eta
    (by norm_num) hpR htauR hUpos heta heta1 hA
  · intro e he
    have hoff := G.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he)
    have hc := Sym2.card_toFinset_of_not_isDiag e hoff
    have hErr := herror e.toFinset (by omega) (by omega) (cliquePattern_edge_le G e he)
    have hTar := htarget e.toFinset (by omega)
    simp only [hc, show (2 : ℕ).choose 2 = 1 by decide, pow_one,
      properPatternExtensions_edge_card A e hoff] at hErr hTar
    exact proper_pair_error_regularization_margin _ _ xi hTar hxiR hErr
  · intro S hS2 hS4 hSG
    have hbounds := proper_clique_error_two_sided _ _ xi S.card
      (by linarith [htarget S hS4]) (by linarith) hS4 (herror S hS2 hS4 hSG)
    refine ⟨hbounds.1, ?_⟩
    calc
      _ ≤ 2 * ((p : ℝ) ^ S.card * (tau : ℝ) ^ (S.card.choose 2) * U.card) := hbounds.2
      _ = _ := by ring
  · have hcardR : ((graphEdges G).card : ℝ) ≤ (U.card : ℝ) ^ 2 := by
      exact_mod_cast graphEdges_card_le_support_sq G U hG
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcardR (by norm_num))
      (Real.exp_pos _).le).trans_lt hfailure

end

end Erdos207
