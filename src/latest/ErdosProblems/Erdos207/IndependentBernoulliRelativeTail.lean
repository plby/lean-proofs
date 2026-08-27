/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentBernoulliConcentration

/-! # Relative Chernoff bounds for the actual independent-bit sampler -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem FiniteLaw.independentBits_probability_relative_deviation
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (S : Finset I)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ((independentBits p hp).probability
      (fun ω ↦ eta * (∑ i ∈ S, (p i : ℝ)) < |centeredBernoulliSum p S ω|) : ℝ) ≤
      2 * Real.exp (-eta ^ 2 * (∑ i ∈ S, (p i : ℝ)) / 4) := by
  let L := independentBits p hp
  let mu : ℝ := ∑ i ∈ S, (p i : ℝ)
  let P := fun ω ↦ eta ^ 2 * mu / 2 ≤ (eta / 2) * centeredBernoulliSum p S ω
  let N := fun ω ↦ eta ^ 2 * mu / 2 ≤ (-eta / 2) * centeredBernoulliSum p S ω
  have hpos : (L.probability P : ℝ) ≤ Real.exp (-eta ^ 2 * mu / 4) := by
    have h := independentBits_probability_scaled_centered_ge p hp S (eta / 2)
      (eta ^ 2 * mu / 2) (by rw [abs_of_pos (by positivity)]; linarith)
    convert h using 1 <;> dsimp only [mu] <;> congr 1 <;> ring
  have hneg : (L.probability N : ℝ) ≤ Real.exp (-eta ^ 2 * mu / 4) := by
    have h := independentBits_probability_scaled_centered_ge p hp S (-eta / 2)
      (eta ^ 2 * mu / 2) (by rw [abs_of_neg (by linarith)]; linarith)
    convert h using 1 <;> dsimp only [mu] <;> congr 1 <;> ring
  have hcover : L.probability (fun ω ↦ eta * mu < |centeredBernoulliSum p S ω|) ≤
      L.probability (fun ω ↦ P ω ∨ N ω) := by
    apply L.probability_mono
    intro ω hω
    rcases lt_abs.mp hω with h | h
    · apply Or.inl
      dsimp only [P]
      nlinarith [mul_nonneg heta.le (sub_nonneg.mpr h.le)]
    · apply Or.inr
      dsimp only [N]
      nlinarith [mul_nonneg heta.le (sub_nonneg.mpr h.le)]
  have hunion : (L.probability
      (fun ω ↦ eta * mu < |centeredBernoulliSum p S ω|) : ℝ) ≤
      (L.probability P : ℝ) + (L.probability N : ℝ) := by
    exact_mod_cast hcover.trans (L.probability_or_le P N)
  change (L.probability (fun ω ↦ eta * mu < |centeredBernoulliSum p S ω|) : ℝ) ≤ _
  linarith

theorem FiniteLaw.independentBits_probability_any_relative_deviation
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (S : J → Finset I)
    (mu eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmu : ∀ j, (∑ i ∈ S j, (p i : ℝ)) = mu) :
    ((independentBits p hp).probability
      (fun ω ↦ ∃ j, eta * mu < |((S j).filter (fun i ↦ ω i = true)).card - mu|) : ℝ) ≤
      2 * Fintype.card J * Real.exp (-eta ^ 2 * mu / 4) := by
  classical
  let L := independentBits p hp
  have hbound : (L.probability
      (fun ω ↦ ∃ j, eta * mu < |((S j).filter (fun i ↦ ω i = true)).card - mu|) : ℝ) ≤
      ∑ j, (L.probability
        (fun ω ↦ eta * mu < |((S j).filter (fun i ↦ ω i = true)).card - mu|) : ℝ) := by
    have h := L.probability_exists_le (univ : Finset J)
      (fun j ω ↦ eta * mu < |((S j).filter (fun i ↦ ω i = true)).card - mu|)
    have hnn : L.probability
        (fun ω ↦ ∃ j, eta * mu < |((S j).filter (fun i ↦ ω i = true)).card - mu|) ≤
        ∑ j, L.probability
          (fun ω ↦ eta * mu < |((S j).filter (fun i ↦ ω i = true)).card - mu|) := by
      simpa only [mem_univ, true_and] using h
    exact_mod_cast hnn
  apply hbound.trans
  calc
    _ ≤ ∑ _j : J, 2 * Real.exp (-eta ^ 2 * mu / 4) := by
      apply sum_le_sum
      intro j hj
      simpa only [centeredBernoulliSum_eq_card_sub, hmu j] using
        independentBits_probability_relative_deviation p hp (S j) eta heta heta1
    _ = _ := by simp; ring

end

end Erdos207
