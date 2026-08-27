/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentBernoulliConcentration
import ErdosProblems.Erdos207.ReserveEdgeSampling

/-! # Arbitrarily small fixed relative errors for the actual independent reserve -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem FiniteLaw.independentBits_probability_abs_centered_gt_relative
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (S : Finset I) (M delta : ℝ)
    (hmu : (∑ i ∈ S, (p i : ℝ)) ≤ M) (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    ((independentBits p hp).probability (fun ω ↦ delta*M < |centeredBernoulliSum p S ω|) : ℝ) ≤
      2*Real.exp (-delta^2*M/4) := by
  let L := independentBits p hp
  let P := fun ω ↦ delta^2*M/2 ≤ (delta/2)*centeredBernoulliSum p S ω
  let N := fun ω ↦ delta^2*M/2 ≤ (-delta/2)*centeredBernoulliSum p S ω
  have hmean := mul_le_mul_of_nonneg_left hmu (sq_nonneg (delta/2))
  have hpos : (L.probability P : ℝ) ≤ Real.exp (-delta^2*M/4) := by
    apply (independentBits_probability_scaled_centered_ge p hp S (delta/2) (delta^2*M/2)
      (abs_le.mpr ⟨by linarith only [hdelta], by linarith only [hdelta1]⟩)).trans
    apply Real.exp_le_exp.mpr
    nlinarith only [hmean]
  have hneg : (L.probability N : ℝ) ≤ Real.exp (-delta^2*M/4) := by
    apply (independentBits_probability_scaled_centered_ge p hp S (-delta/2) (delta^2*M/2)
      (abs_le.mpr ⟨by linarith only [hdelta1], by linarith only [hdelta]⟩)).trans
    apply Real.exp_le_exp.mpr
    nlinarith only [hmean]
  have hcover : L.probability (fun ω ↦ delta*M < |centeredBernoulliSum p S ω|) ≤
      L.probability (fun ω ↦ P ω ∨ N ω) := by
    apply L.probability_mono
    intro ω hω
    rcases lt_abs.mp hω with h | h
    · apply Or.inl
      have hm := mul_le_mul_of_nonneg_left h.le (by positivity : 0 ≤ delta/2)
      dsimp only [P]
      nlinarith only [hm]
    · apply Or.inr
      have hm := mul_le_mul_of_nonneg_left h.le (by positivity : 0 ≤ delta/2)
      dsimp only [N]
      nlinarith only [hm]
  have hunion : (L.probability (fun ω ↦ delta*M < |centeredBernoulliSum p S ω|) : ℝ) ≤
      (L.probability P : ℝ)+(L.probability N : ℝ) := by
    exact_mod_cast hcover.trans (L.probability_or_le P N)
  change (L.probability (fun ω ↦ delta*M < |centeredBernoulliSum p S ω|) : ℝ) ≤ _
  linarith only [hunion, hpos, hneg]

theorem reserveEdgeLaw_probability_abs_inter_count_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0) (hr : r ≤ 1)
    (S : Finset (Sym2 V)) (hS : S ⊆ crossingEdges G U) (delta : ℝ) (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    ((reserveEdgeLaw G U r hr).probability (fun ω ↦ delta*((r : ℝ)*S.card) <
      |((S ∩ reserveEdges G U ω).card : ℝ)-(r : ℝ)*S.card|) : ℝ) ≤
        2*Real.exp (-delta^2*((r : ℝ)*S.card)/4) := by
  have hmean : (∑ e ∈ S, (reserveEdgeProbability G U r e : ℝ)) = (r : ℝ)*S.card := by
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
    ((r : ℝ)*S.card) delta hmean.le hdelta hdelta1
  simpa only [reserveEdgeLaw, centeredBernoulliSum_eq_card_sub, hmean, hcount] using hb

end

end Erdos207
