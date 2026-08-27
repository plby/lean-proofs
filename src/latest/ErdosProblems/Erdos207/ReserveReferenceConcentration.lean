/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeBernoulliConcentration

/-! # Concentration relative to a deterministic reference, not a possibly tiny actual mean -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem reserveEdgeLaw_probability_abs_inter_count_gt_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0) (hr : r ≤ 1)
    (S : Finset (Sym2 V)) (hS : S ⊆ crossingEdges G U) (M delta : ℝ)
    (hmean : (r : ℝ)*S.card ≤ M) (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    ((reserveEdgeLaw G U r hr).probability (fun ω ↦ delta*M <
      |((S ∩ reserveEdges G U ω).card : ℝ)-(r : ℝ)*S.card|) : ℝ) ≤
        2*Real.exp (-delta^2*M/4) := by
  have hmu : (∑ e ∈ S, (reserveEdgeProbability G U r e : ℝ)) = (r : ℝ)*S.card := by
    calc
      _ = ∑ _e ∈ S, (r : ℝ) := by
        apply sum_congr rfl
        intro e he
        simp only [reserveEdgeProbability, if_pos (hS he)]
      _ = _ := by simp [mul_comm]
  have hcount (ω : Sym2 V → Bool) : (S.filter (fun e ↦ ω e = true)) = S ∩ reserveEdges G U ω := by
    ext e
    simp only [mem_filter, mem_inter, mem_reserveEdges_iff]
    exact ⟨fun h ↦ ⟨h.1, hS h.1, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
  have hb := FiniteLaw.independentBits_probability_abs_centered_gt_relative
    (reserveEdgeProbability G U r) (reserveEdgeProbability_le_one G U hr) S
    M delta (hmu.le.trans hmean) hdelta hdelta1
  simpa only [reserveEdgeLaw, centeredBernoulliSum_eq_card_sub, hmu, hcount] using hb

theorem reserveEdgeLaw_probability_abs_inter_count_gt_reference
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0) (hr : r ≤ 1)
    (S : Finset (Sym2 V)) (hS : S ⊆ crossingEdges G U) (target epsilon : ℝ)
    (hmean : (r : ℝ)*S.card ≤ 2*target) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    ((reserveEdgeLaw G U r hr).probability (fun ω ↦ epsilon*target <
      |((S ∩ reserveEdges G U ω).card : ℝ)-(r : ℝ)*S.card|) : ℝ) ≤
        2*Real.exp (-epsilon^2*target/8) := by
  have hb := reserveEdgeLaw_probability_abs_inter_count_gt_budget G U r hr S hS (2*target) (epsilon/2)
    hmean (by positivity) (by linarith only [hepsilon1])
  have heq : (epsilon/2)*(2*target) = epsilon*target := by ring
  have hexp : -(epsilon/2)^2*(2*target)/4 = -epsilon^2*target/8 := by ring
  simpa only [heq, hexp] using hb

theorem real_sampled_reference_window
    (target mu actual epsilon : ℝ)
    (hmean : (1-epsilon/2)*target ≤ mu ∧ mu ≤ (1+epsilon/2)*target)
    (hdeviation : |actual-mu| ≤ (epsilon/2)*target) :
    (1-epsilon)*target ≤ actual ∧ actual ≤ (1+epsilon)*target := by
  have hh := abs_le.mp hdeviation
  constructor <;> nlinarith only [hmean.1, hmean.2, hh.1, hh.2]

theorem real_sampled_reference_upper
    (target mu actual epsilon : ℝ)
    (hmean : mu ≤ (1+epsilon/2)*target)
    (hdeviation : |actual-mu| ≤ (epsilon/2)*target) :
    actual ≤ (1+epsilon)*target := by
  have hh := (abs_le.mp hdeviation).2
  nlinarith only [hmean, hh]

end

end Erdos207
