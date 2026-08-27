/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationTriangleRegularization
import ErdosProblems.Erdos207.TwoDensityRegularizationThreshold

/-! # A uniform local-order threshold for regularizing iteration-typical stage data -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_iteration_triangle_regularization_threshold
    (tau0 : ℝ≥0) (htau0 : 0 < tau0) :
    ∃ N : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V] {ell h : ℕ},
      ∀ (W : Vortex V ell) (k : Fin (ell + 1)) (G : SimpleGraph V) (A : TripleSystemOn V),
      ∀ (p tau xi : ℝ≥0), IsIterationTypical W k G A p tau xi h →
      ∀ (i : Fin ell), k.val ≤ i.val → 4 ≤ h → N ≤ (W.U i.castSucc).card →
      ((W.U i.castSucc).card : ℝ) ^ (-1 / 6 : ℝ) ≤ p → p ≤ 1 →
      tau0 ≤ tau → tau ≤ 1 → xi ≤ 1 / 768 →
      GraphSupportedOn G (W.U i.castSucc : Set V) →
      (∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G) →
      ∃ B ⊆ A, ∀ e ∈ graphEdges G,
        |((B.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) -
          (p : ℝ) ^ 2 * tau * (W.U i.castSucc).card / 4| ≤
        ((W.U i.castSucc).card : ℝ) ^ (-1 / 4 : ℝ) *
          ((p : ℝ) ^ 2 * tau * (W.U i.castSucc).card / 4) := by
  obtain ⟨N, hN1, hN⟩ := exists_twoDensityTriangleRegularization_threshold tau0 (by exact_mod_cast htau0)
  refine ⟨N, ?_⟩
  intro V _ _ ell h W k G A p tau xi htyp i hki hh hn hp hp1 htau htau1 hxi hG hA
  have hn1 : 1 ≤ (W.U i.castSucc).card := hN1.trans hn
  have hnR : (0 : ℝ) < (W.U i.castSucc).card := by exact_mod_cast (by omega : 0 < (W.U i.castSucc).card)
  have hpR : (0 : ℝ) < p := (Real.rpow_pos_of_pos hnR _).trans_le hp
  have hp0 : 0 < p := by exact_mod_cast hpR
  have htauR : (tau0 : ℝ) ≤ tau := by exact_mod_cast htau
  obtain ⟨hdensity, hfailure⟩ := hN (W.U i.castSucc).card hn p tau hp htauR
  exact htyp.exists_regularized_triangles i hki hh hp0 hp1 (htau0.trans_le htau) htau1 hxi hG hA
    (by exact_mod_cast hdensity) (((W.U i.castSucc).card : ℝ) ^ (-1 / 4 : ℝ))
    (Real.rpow_pos_of_pos hnR _)
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1) (by norm_num)) hfailure

end

end Erdos207
