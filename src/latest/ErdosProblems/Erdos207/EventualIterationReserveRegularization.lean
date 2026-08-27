/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationReserveRegularization
import ErdosProblems.Erdos207.ReserveRegularizationPowerBudgets

/-! # Actual reserve regularization with every power-scale numerical budget discharged -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem eventually_iteration_reserve_regularization
    (b c e a L R : ℕ) (tau0 : ℝ≥0) (epsilon : ℝ)
    (hc : 1 ≤ c) (he : 1 ≤ e) (ha : 4 * b + 1 ≤ a)
    (hLreserve : 4 * b + c + 1 ≤ L) (hLsampling : 2 * b + 2 * e + 1 ≤ L)
    (htau0 : 0 < tau0) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      (1 / (t : ℝ≥0) ^ c) ≤ 1 ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] {ell h : ℕ},
      ∀ (W : Vortex V ell) (k : Fin (ell + 1)) (G : SimpleGraph V) (A : TripleSystemOn V),
      ∀ (p tau xi : ℝ≥0), IsIterationTypical W k G A p tau xi h →
      ∀ (i : Fin ell), k.val ≤ i.val → 4 ≤ h → ∀ U : Finset V,
      ∀ hr1 : (1 / (t : ℝ≥0) ^ c) ≤ 1,
      GraphSupportedOn G (W.U i.castSucc : Set V) →
      (∀ Q ∈ A, tripleEdgeFinset Q ⊆ graphEdges G) →
      t ^ L ≤ (W.U i.castSucc).card → (W.U i.castSucc).card ≤ t ^ R →
      1 / (t : ℝ≥0) ^ b ≤ p → p ≤ 1 → tau0 ≤ tau → tau ≤ 1 → xi ≤ 1 / 1536 →
      (U.card : ℝ≥0) ≤ ((W.U i.castSucc).card : ℝ≥0) / (t : ℝ≥0) ^ a →
      ((reserveEdgeLaw G U (1 / (t : ℝ≥0) ^ c) hr1).probability
        (fun omega ↦ ¬ HasReserveRegularizedTriangles G U (W.U i.castSucc) A p tau
          (1 / (t : ℝ) ^ e) omega) : ℝ) < epsilon := by
  obtain ⟨T, hT1, hT⟩ := eventually_reserveRegularization_power_budgets b c e a L R tau0 epsilon
    hc he ha hLreserve hLsampling htau0 hepsilon
  refine ⟨T, hT1, fun t ht ↦ ?_⟩
  have ht1 : (1 : ℝ≥0) ≤ t := by exact_mod_cast hT1.trans ht
  have ht0 : (0 : ℝ≥0) < t := zero_lt_one.trans_le ht1
  refine ⟨div_le_self zero_le (one_le_pow₀ ht1), ?_⟩
  intro V _ _ ell h W k G A p tau xi htyp i hki hh U hr1 hG hA hnlo hnhi hp hp1 htau htau1 hxi hinner
  obtain ⟨hdensity, hinner', hrsmall, heta0, heta1, hsample, hreserve⟩ :=
    hT t ht (W.U i.castSucc).card U.card p tau hnlo hnhi hp htau hinner
  have hp0 : 0 < p := (one_div_pos.mpr (pow_pos ht0 b)).trans_le hp
  have hprob := htyp.reserve_probability_no_regularized_triangles i hki hh U (1 / (t : ℝ≥0) ^ c)
    hr1 hG hA hp0 hp1 (htau0.trans_le htau) htau1 hxi hrsmall hdensity hinner'
    (1 / (t : ℝ) ^ e) heta0 heta1 hsample
  have hprob' : ((reserveEdgeLaw G U (1 / (t : ℝ≥0) ^ c) hr1).probability
      (fun omega ↦ ¬ HasReserveRegularizedTriangles G U (W.U i.castSucc) A p tau
        (1 / (t : ℝ) ^ e) omega) : ℝ) ≤
      12 * ((W.U i.castSucc).card + 1 : ℝ) ^ 4 * Real.exp
        (-(1 / (t : ℝ) ^ c) * ((p : ℝ) ^ 4 * (tau : ℝ) ^ 6 * (W.U i.castSucc).card) / 8) := by
    simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow, NNReal.coe_natCast] using hprob
  exact hprob'.trans_lt hreserve

end

end Erdos207
