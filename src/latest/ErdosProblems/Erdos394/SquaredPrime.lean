import ErdosProblems.Erdos394.LargePrimePart
import Mathlib.Analysis.PSeries

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The squared-medium-prime exceptional set
-/

open Nat Finset

namespace Erdos394

/-- Positive integers up to `X` divisible by the square of some prime in `P`. -/
def squaredPrimeException (P : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter
    (fun n ↦ n ≠ 0 ∧ ∃ p ∈ P, p * p ∣ n)

/-- The squared-prime exception is contained in a union of sets of multiples. -/
theorem squaredPrimeException_subset_biUnion (P : Finset ℕ) (X : ℕ) :
    squaredPrimeException P X ⊆
      P.biUnion (fun p ↦ positiveMultiplesUpTo X (p * p)) := by
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  obtain ⟨p, hp, hdiv⟩ := hn'.2.2
  apply Finset.mem_biUnion.mpr
  exact ⟨p, hp, Finset.mem_filter.mpr ⟨hn'.1, hn'.2.1, hdiv⟩⟩

/-- Reciprocal squares over any finite subset of `(z,y]` sum to at most
`1/z`. -/
theorem sum_inv_sq_le_one_div_of_mem_Ioc
    (P : Finset ℕ) {z y : ℕ} (hz : z ≠ 0) (hzy : z ≤ y)
    (hP : ∀ p ∈ P, z < p ∧ p ≤ y) :
    (∑ p ∈ P, (1 / (p : ℝ) ^ 2)) ≤ 1 / (z : ℝ) := by
  have hsub : P ⊆ Finset.Ioc z y := by
    intro p hp
    exact Finset.mem_Ioc.mpr (hP p hp)
  calc
    (∑ p ∈ P, (1 / (p : ℝ) ^ 2)) ≤
        ∑ p ∈ Finset.Ioc z y, (1 / (p : ℝ) ^ 2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp hnot
      positivity
    _ = ∑ p ∈ Finset.Ioc z y, (((p : ℝ) ^ 2)⁻¹) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [one_div]
    _ ≤ (z : ℝ)⁻¹ - (y : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hz hzy
    _ ≤ 1 / (z : ℝ) := by
      rw [one_div]
      have hyinv : 0 ≤ (y : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
      linarith

/-- Census bound for the squared-prime exceptional set. -/
theorem card_squaredPrimeException_le
    (P : Finset ℕ) {X z y : ℕ} (hz : z ≠ 0) (hzy : z ≤ y)
    (hP : ∀ p ∈ P, z < p ∧ p ≤ y) :
    ((squaredPrimeException P X).card : ℝ) ≤
      (X : ℝ) / (z : ℝ) := by
  have hcardNat : (squaredPrimeException P X).card ≤
      ∑ p ∈ P, X / (p * p) := by
    calc
      (squaredPrimeException P X).card ≤
          (P.biUnion (fun p ↦ positiveMultiplesUpTo X (p * p))).card :=
        Finset.card_le_card (squaredPrimeException_subset_biUnion P X)
      _ ≤ ∑ p ∈ P, (positiveMultiplesUpTo X (p * p)).card :=
        Finset.card_biUnion_le
      _ = ∑ p ∈ P, X / (p * p) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [card_positiveMultiplesUpTo]
  have hcast : ((squaredPrimeException P X).card : ℝ) ≤
      (X : ℝ) * ∑ p ∈ P, (1 / (p : ℝ) ^ 2) := by
    calc
      ((squaredPrimeException P X).card : ℝ) ≤
          ∑ p ∈ P, ((X / (p * p) : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      _ ≤ ∑ p ∈ P, (X : ℝ) / ((p * p : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact Nat.cast_div_le
      _ = (X : ℝ) * ∑ p ∈ P, (1 / (p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        push_cast
        ring
  apply hcast.trans
  calc
    (X : ℝ) * ∑ p ∈ P, (1 / (p : ℝ) ^ 2) ≤
        (X : ℝ) * (1 / (z : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (sum_inv_sq_le_one_div_of_mem_Ioc P hz hzy hP) (by positivity)
    _ = (X : ℝ) / (z : ℝ) := by ring

/-- The squared-prime exceptions contribute at most `X²/z` to the target
sum. -/
theorem sum_t_two_squaredPrimeException_le
    (P : Finset ℕ) {X z y : ℕ} (hz : z ≠ 0) (hzy : z ≤ y)
    (hP : ∀ p ∈ P, z < p ∧ p ≤ y) :
    (∑ n ∈ squaredPrimeException P X, (t 2 n : ℝ)) ≤
      (X : ℝ) ^ 2 / (z : ℝ) := by
  have hpoint : ∀ n ∈ squaredPrimeException P X, (t 2 n : ℝ) ≤ (X : ℝ) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn'.2.1
    have hnX : n ≤ X := by
      have := Finset.mem_range.mp hn'.1
      omega
    exact_mod_cast (t_le_self (by norm_num : 0 < 2) hnpos).trans hnX
  have hcard := card_squaredPrimeException_le P (X := X) hz hzy hP
  calc
    (∑ n ∈ squaredPrimeException P X, (t 2 n : ℝ)) ≤
        ∑ _n ∈ squaredPrimeException P X, (X : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = (X : ℝ) * (squaredPrimeException P X).card := by simp [mul_comm]
    _ ≤ (X : ℝ) * ((X : ℝ) / (z : ℝ)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = (X : ℝ) ^ 2 / (z : ℝ) := by ring

end Erdos394
