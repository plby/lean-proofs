/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An explicit bound for the difference between prime weights 1/(p-1) and 1/p.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Counting

open scoped BigOperators

/-- A telescoping majorant for the summable logarithmic correction. -/
lemma log_weight_le_telescope (x : ℝ) (hx : 1 ≤ x) :
    Real.log (x + 1) / ((x + 1) * x) ≤
      (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hlog : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx1 hx0)
    rw [Real.log_div hx1.ne' hx0.ne'] at h
    have heq : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    rwa [heq] at h
  have hratio : (x + 1) / x ≤ 2 := (div_le_iff₀ hx0).mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hlog hx1.le
  have hnum : 0 ≤ 2 - (x + 1) * (Real.log (x + 1) - Real.log x) := by
    rw [← mul_div_assoc, mul_one] at hmul
    linarith
  have heq : (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) -
      Real.log (x + 1) / ((x + 1) * x) =
      (2 - (x + 1) * (Real.log (x + 1) - Real.log x)) / (x * (x + 1)) := by
    field_simp
    ring
  apply sub_nonneg.mp
  rw [heq]
  exact div_nonneg hnum (mul_nonneg hx0.le hx1.le)

/-- Shift by two to avoid exceptional terms at zero and one. -/
noncomputable def primeWeightError (n : ℕ) : ℝ :=
  Real.log (n + 2) / (((n : ℝ) + 2) * (n + 1))

lemma primeWeightError_nonneg (n : ℕ) : 0 ≤ primeWeightError n := by
  unfold primeWeightError
  apply div_nonneg
  · apply Real.log_nonneg
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · positivity

lemma sum_primeWeightError_le (N : ℕ) :
    ∑ n ∈ Finset.range N, primeWeightError n ≤ 2 := by
  let g : ℕ → ℝ := fun n => (Real.log ((n : ℝ) + 1) + 2) / (n + 1)
  calc
    _ ≤ ∑ n ∈ Finset.range N, (g n - g (n + 1)) := by
      apply Finset.sum_le_sum
      intro n _
      have h := log_weight_le_telescope ((n : ℝ) + 1) (by
        linarith [Nat.cast_nonneg (α := ℝ) n])
      simpa only [g, primeWeightError, Nat.cast_add, Nat.cast_one,
        show (1 : ℝ) + 1 = 2 by norm_num, add_assoc] using h
    _ = g 0 - g N := Finset.sum_range_sub' g N
    _ ≤ 2 := by
      have hg : 0 ≤ g N := by
        dsimp only [g]
        apply div_nonneg
        · have hlog : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by
            linarith [Nat.cast_nonneg (α := ℝ) N])
          linarith
        · positivity
      have hg0 : g 0 = 2 := by simp [g]
      rw [hg0]
      linarith

lemma sum_prime_error_le (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * (p - 1)) ≤ 2 := by
  let S := Nat.primesLE N
  have hinj : Set.InjOn (fun p : ℕ => p - 2) S := by
    intro p hp q hq heq
    have hp2 := (Nat.mem_primesLE.mp hp).2.two_le
    have hq2 := (Nat.mem_primesLE.mp hq).2.two_le
    change p - 2 = q - 2 at heq
    omega
  have hsub : S.image (fun p => p - 2) ⊆ Finset.range N := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    have hpN := (Nat.mem_primesLE.mp hp).1
    have hp2 := (Nat.mem_primesLE.mp hp).2.two_le
    simp only [Finset.mem_range]
    omega
  have hentry (p : ℕ) (hp : p ∈ S) :
      Real.log p / ((p : ℝ) * (p - 1)) = primeWeightError (p - 2) := by
    have hp2 := (Nat.mem_primesLE.mp hp).2.two_le
    have hcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
      simp only [Nat.cast_sub hp2, Nat.cast_ofNat]
    simp only [primeWeightError, hcast]
    congr 2 <;> ring
  calc
    _ = ∑ p ∈ S, primeWeightError (p - 2) := Finset.sum_congr rfl hentry
    _ = ∑ n ∈ S.image (fun p => p - 2), primeWeightError n := (Finset.sum_image hinj).symm
    _ ≤ ∑ n ∈ Finset.range N, primeWeightError n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => primeWeightError_nonneg n)
    _ ≤ 2 := sum_primeWeightError_le N

#print axioms sum_prime_error_le
-- 'Erdos477.Counting.sum_prime_error_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
