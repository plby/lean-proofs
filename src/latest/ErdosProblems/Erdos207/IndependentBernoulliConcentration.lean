/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentBernoulliMGF

/-! # Subset concentration on one nonidentical Bernoulli product law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def centeredBernoulliSum
    {I : Type*} [DecidableEq I] (p : I → ℝ≥0) (S : Finset I) (ω : I → Bool) : ℝ :=
  ∑ i ∈ S, ((if ω i then 1 else 0) - (p i : ℝ))

theorem centeredBernoulliSum_eq_card_sub
    {I : Type*} [DecidableEq I] (p : I → ℝ≥0) (S : Finset I) (ω : I → Bool) :
    centeredBernoulliSum p S ω = ((S.filter fun i ↦ ω i = true).card : ℝ) -
      ∑ i ∈ S, (p i : ℝ) := by
  unfold centeredBernoulliSum
  rw [sum_sub_distrib]
  congr 1
  simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one]

theorem FiniteLaw.independentBits_centered_subset_mgf
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (S : Finset I)
    (theta : ℝ) (htheta : |theta| ≤ 1) :
    (independentBits p hp).expectationReal
      (fun ω ↦ Real.exp (theta * centeredBernoulliSum p S ω)) ≤
      Real.exp (theta ^ 2 * ∑ i ∈ S, (p i : ℝ)) := by
  have h := independentBits_centered_exp_mgf p hp (fun i ↦ if i ∈ S then theta else 0)
    (fun i ↦ by split_ifs <;> simp_all)
  have hsum (ω : I → Bool) :
      (∑ i, (if i ∈ S then theta else 0) * ((if ω i then 1 else 0) - (p i : ℝ))) =
        theta * centeredBernoulliSum p S ω := by
    unfold centeredBernoulliSum
    rw [mul_sum]
    simp only [ite_mul, zero_mul, ← sum_filter]
    simp
  have hsq : (∑ i, (if i ∈ S then theta else 0) ^ 2 * (p i : ℝ)) =
      theta ^ 2 * ∑ i ∈ S, (p i : ℝ) := by
    simp [ite_pow, ite_mul, mul_sum]
  simpa only [hsum, hsq] using h

theorem FiniteLaw.independentBits_probability_scaled_centered_ge
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (S : Finset I)
    (theta a : ℝ) (htheta : |theta| ≤ 1) :
    ((independentBits p hp).probability
      (fun ω ↦ a ≤ theta * centeredBernoulliSum p S ω) : ℝ) ≤
      Real.exp (-a + theta ^ 2 * ∑ i ∈ S, (p i : ℝ)) := by
  let L := independentBits p hp
  have hmarkov := L.probability_coe_le_expectationReal_div
    (fun ω ↦ Real.exp (theta * centeredBernoulliSum p S ω))
    (Real.exp a) (Real.exp_pos a) (fun _ ↦ (Real.exp_pos _).le)
  have hevent : (fun ω ↦ Real.exp a ≤ Real.exp (theta * centeredBernoulliSum p S ω)) =
      (fun ω ↦ a ≤ theta * centeredBernoulliSum p S ω) := by
    funext ω
    exact propext Real.exp_le_exp
  rw [hevent] at hmarkov
  apply hmarkov.trans
  calc
    _ ≤ Real.exp (theta ^ 2 * ∑ i ∈ S, (p i : ℝ)) / Real.exp a :=
      div_le_div_of_nonneg_right (independentBits_centered_subset_mgf p hp S theta htheta)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

theorem FiniteLaw.independentBits_probability_abs_centered_gt
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (S : Finset I) (F : ℝ)
    (hmu : (∑ i ∈ S, (p i : ℝ)) ≤ 2 * F) :
    ((independentBits p hp).probability
      (fun ω ↦ F / 32 < |centeredBernoulliSum p S ω|) : ℝ) ≤
      2 * Real.exp (-F / 8192) := by
  let L := independentBits p hp
  let P := fun ω ↦ F / 4096 ≤ (1 / 128 : ℝ) * centeredBernoulliSum p S ω
  let N := fun ω ↦ F / 4096 ≤ (-1 / 128 : ℝ) * centeredBernoulliSum p S ω
  have hpos : (L.probability P : ℝ) ≤ Real.exp (-F / 8192) := by
    apply (independentBits_probability_scaled_centered_ge p hp S (1 / 128)
      (F / 4096) (by norm_num)).trans
    apply Real.exp_le_exp.mpr
    nlinarith
  have hneg : (L.probability N : ℝ) ≤ Real.exp (-F / 8192) := by
    apply (independentBits_probability_scaled_centered_ge p hp S (-1 / 128)
      (F / 4096) (by norm_num)).trans
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcover : L.probability (fun ω ↦ F / 32 < |centeredBernoulliSum p S ω|) ≤
      L.probability (fun ω ↦ P ω ∨ N ω) := by
    apply L.probability_mono
    intro ω hω
    rcases lt_abs.mp hω with h | h
    · exact Or.inl (by dsimp only [P]; linarith)
    · exact Or.inr (by dsimp only [N]; linarith)
  have hunion : (L.probability (fun ω ↦ F / 32 < |centeredBernoulliSum p S ω|) : ℝ) ≤
      (L.probability P : ℝ) + (L.probability N : ℝ) := by
    exact_mod_cast hcover.trans (L.probability_or_le P N)
  change (L.probability (fun ω ↦ F / 32 < |centeredBernoulliSum p S ω|) : ℝ) ≤ _
  linarith

theorem FiniteLaw.independentBits_probability_any_abs_centered_gt
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (S : J → Finset I) (F : ℝ)
    (hmu : ∀ j, (∑ i ∈ S j, (p i : ℝ)) ≤ 2 * F) :
    ((independentBits p hp).probability
      (fun ω ↦ ∃ j, F / 32 < |centeredBernoulliSum p (S j) ω|) : ℝ) ≤
      2 * Fintype.card J * Real.exp (-F / 8192) := by
  classical
  let L := independentBits p hp
  have hbound : (L.probability
      (fun ω ↦ ∃ j, F / 32 < |centeredBernoulliSum p (S j) ω|) : ℝ) ≤
      ∑ j, (L.probability (fun ω ↦ F / 32 < |centeredBernoulliSum p (S j) ω|) : ℝ) := by
    have hnn : L.probability
        (fun ω ↦ ∃ j, F / 32 < |centeredBernoulliSum p (S j) ω|) ≤
        ∑ j, L.probability (fun ω ↦ F / 32 < |centeredBernoulliSum p (S j) ω|) := by
      simpa using L.probability_exists_le (univ : Finset J)
        (fun j ω ↦ F / 32 < |centeredBernoulliSum p (S j) ω|)
    exact_mod_cast hnn
  apply hbound.trans
  calc
    _ ≤ ∑ _j : J, 2 * Real.exp (-F / 8192) :=
      sum_le_sum (fun j _ ↦ independentBits_probability_abs_centered_gt p hp (S j) F (hmu j))
    _ = _ := by simp; ring

end

end Erdos207
