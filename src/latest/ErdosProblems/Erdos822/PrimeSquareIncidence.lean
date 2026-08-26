/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.PrimeSquareFiber

/-!
# Summing one prime-square incidence over cofactors

This is the finite Fubini step for the repeated-root correction.  We count
only cofactors not divisible by p; on such a cofactor m=k*r*q, both fixed
factors k and r are p-free, so the inverse-square q-fiber estimate applies.
-/

namespace Erdos822

open scoped BigOperators

/-- Odd raw cofactors not divisible by p whose shifted coefficient is
divisible by p². -/
def squareDivisibleCoprimeOddCofactors (N p : ℕ) : Finset ℕ :=
  (oddRawCofactors N).filter fun m =>
    p ^ 2 ∣ shiftedTotient m ∧ ¬ p ∣ m

@[simp]
theorem mem_squareDivisibleCoprimeOddCofactors_iff
    {N p m : ℕ} :
    m ∈ squareDivisibleCoprimeOddCofactors N p ↔
      m ∈ oddRawCofactors N ∧
        p ^ 2 ∣ shiftedTotient m ∧ ¬ p ∣ m := by
  simp [squareDivisibleCoprimeOddCofactors, and_assoc]

/-- Exact expansion before the p-coprime restriction is used. -/
theorem sum_inv_squareDivisibleCoprimeOddCofactors_eq_triple
    {N p : ℕ} (hN : 2 ≤ N) :
    ∑ m ∈ squareDivisibleCoprimeOddCofactors N p, (1 : ℝ) / m =
      ∑ k ∈ oddSmallFactors N,
        ∑ r ∈ middlePrimes N,
          ∑ q ∈ largePrimes N,
            if p ^ 2 ∣ shiftedTotient (k * r * q) ∧
                ¬ p ∣ k * r * q then
              (1 : ℝ) / (k * r * q)
            else 0 := by
  unfold squareDivisibleCoprimeOddCofactors oddRawCofactors
  rw [Finset.sum_filter]
  rw [Finset.sum_image (cofactorProduct_injOn_oddCofactorTriples hN)]
  rw [oddCofactorTriples]
  change
    (∑ t ∈ oddSmallFactors N ×ˢ (middlePrimes N ×ˢ largePrimes N),
      if p ^ 2 ∣ shiftedTotient (cofactorProduct t) ∧
          ¬ p ∣ cofactorProduct t then
        (1 : ℝ) / cofactorProduct t
      else 0) = _
  rw [Finset.sum_product]
  simp_rw [Finset.sum_product]
  simp [cofactorProduct, Nat.cast_mul]

/-- A single p-square incidence has the expected inverse-square reciprocal
mass after summing over all p-free k and r. -/
theorem sum_inv_squareDivisibleCoprimeOddCofactors_le_of_fiber_bound
    {N p : ℕ} {F : ℝ} (hN : 2 ≤ N) (hF : 0 ≤ F)
    (hfiber : ∀ k ∈ oddSmallFactors N, ∀ r ∈ middlePrimes N,
      ¬ p ∣ k → ¬ p ∣ r →
      (∑ q ∈ shiftedSquareDivisibleLargePrimes N p k r, (1 : ℝ) / q) ≤ F) :
    ∑ m ∈ squareDivisibleCoprimeOddCofactors N p,
        (1 : ℝ) / m ≤
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          F := by
  classical
  rw [sum_inv_squareDivisibleCoprimeOddCofactors_eq_triple hN]
  let T : ℕ → ℕ → ℝ := fun k r =>
    if ¬ p ∣ k ∧ ¬ p ∣ r then
      ∑ q ∈ shiftedSquareDivisibleLargePrimes N p k r,
        (1 : ℝ) / (k * r * q)
    else 0
  have hpoint : ∀ k ∈ oddSmallFactors N,
      ∀ r ∈ middlePrimes N,
      (∑ q ∈ largePrimes N,
          if p ^ 2 ∣ shiftedTotient (k * r * q) ∧
              ¬ p ∣ k * r * q then
            (1 : ℝ) / (k * r * q)
          else 0) ≤ T k r := by
    intro k hk r hr
    by_cases hkr : ¬ p ∣ k ∧ ¬ p ∣ r
    · dsimp [T]
      rw [if_pos hkr]
      calc
        (∑ q ∈ largePrimes N,
            if p ^ 2 ∣ shiftedTotient (k * r * q) ∧
                ¬ p ∣ k * r * q then
              (1 : ℝ) / (k * r * q)
            else 0) ≤
            ∑ q ∈ largePrimes N,
              if p ^ 2 ∣ shiftedTotient (k * r * q) then
                (1 : ℝ) / (k * r * q)
              else 0 := by
          apply Finset.sum_le_sum
          intro q hq
          by_cases hsq : p ^ 2 ∣ shiftedTotient (k * r * q)
          · simp only [hsq, true_and, ↓reduceIte]
            split_ifs
            · positivity
            · rfl
          · simp [hsq]
        _ = ∑ q ∈ shiftedSquareDivisibleLargePrimes N p k r,
              (1 : ℝ) / (k * r * q) := by
          unfold shiftedSquareDivisibleLargePrimes
          rw [Finset.sum_filter]
    · dsimp [T]
      rw [if_neg hkr]
      have hzero : ∀ q ∈ largePrimes N,
          (if p ^ 2 ∣ shiftedTotient (k * r * q) ∧
              ¬ p ∣ k * r * q then
            (1 : ℝ) / (k * r * q)
          else 0) = 0 := by
        intro q hq
        by_cases hpk : p ∣ k
        · by_cases hcond :
              p ^ 2 ∣ shiftedTotient (k * r * q) ∧
                ¬ p ∣ k * r * q
          · exact (hcond.2 (by
              simpa [Nat.mul_assoc] using
                (dvd_mul_of_dvd_left hpk (r * q)))).elim
          · simp [hcond]
        · have hpr : p ∣ r := by
            by_contra hpr
            exact hkr ⟨hpk, hpr⟩
          by_cases hcond :
              p ^ 2 ∣ shiftedTotient (k * r * q) ∧
                ¬ p ∣ k * r * q
          · exact (hcond.2 (by
              simpa [Nat.mul_assoc] using
                (dvd_mul_of_dvd_right
                  (dvd_mul_of_dvd_left hpr q) k))).elim
          · simp [hcond]
      rw [Finset.sum_eq_zero hzero]
  calc
    (∑ k ∈ oddSmallFactors N,
        ∑ r ∈ middlePrimes N,
          ∑ q ∈ largePrimes N,
            if p ^ 2 ∣ shiftedTotient (k * r * q) ∧
                ¬ p ∣ k * r * q then
              (1 : ℝ) / (k * r * q)
            else 0) ≤
        ∑ k ∈ oddSmallFactors N,
          ∑ r ∈ middlePrimes N, T k r := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro r hr
      exact hpoint k hk r hr
    _ = ∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
          ∑ r ∈ (middlePrimes N).filter (fun r => ¬ p ∣ r),
            ∑ q ∈ shiftedSquareDivisibleLargePrimes N p k r,
              (1 : ℝ) / (k * r * q) := by
      dsimp [T]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hpk : ¬ p ∣ k
      · rw [if_pos hpk]
        rw [Finset.sum_filter]
        simp [hpk]
      · rw [if_neg hpk]
        simp [hpk]
    _ ≤ ∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
          ∑ r ∈ (middlePrimes N).filter (fun r => ¬ p ∣ r),
            ((1 : ℝ) / k * ((1 : ℝ) / r)) * F := by
      apply Finset.sum_le_sum
      intro k hk
      have hkdata := Finset.mem_filter.mp hk
      apply Finset.sum_le_sum
      intro r hr
      have hrdata := Finset.mem_filter.mp hr
      have hqsum := hfiber k hkdata.1 r hrdata.1 hkdata.2 hrdata.2
      calc
        (∑ q ∈ shiftedSquareDivisibleLargePrimes N p k r,
            (1 : ℝ) / (k * r * q)) =
            ((1 : ℝ) / k * ((1 : ℝ) / r)) *
              ∑ q ∈ shiftedSquareDivisibleLargePrimes N p k r,
                (1 : ℝ) / q := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          push_cast
          ring
        _ ≤ ((1 : ℝ) / k * ((1 : ℝ) / r)) * F := by
          exact mul_le_mul_of_nonneg_left hqsum
            (by positivity)
    _ = (∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
          (1 : ℝ) / k) *
        (∑ r ∈ (middlePrimes N).filter (fun r => ¬ p ∣ r),
          (1 : ℝ) / r) * F := by
      calc
        (∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
            ∑ r ∈ (middlePrimes N).filter (fun r => ¬ p ∣ r),
              ((1 : ℝ) / k * ((1 : ℝ) / r)) * F) =
            ∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
              ((1 : ℝ) / k *
                ∑ r ∈ (middlePrimes N).filter (fun r => ¬ p ∣ r),
                  (1 : ℝ) / r) * F := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ = (∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
              (1 : ℝ) / k) *
            (∑ r ∈ (middlePrimes N).filter (fun r => ¬ p ∣ r),
              (1 : ℝ) / r) * F := by
          rw [← Finset.sum_mul]
          congr 1
          rw [Finset.sum_mul]
    _ ≤ (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * F := by
      have hK :
          ∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
              (1 : ℝ) / k ≤
            ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
        intro k hk hnot
        positivity
      have hR :
          ∑ r ∈ (middlePrimes N).filter (fun r => ¬ p ∣ r),
              (1 : ℝ) / r ≤
            ∑ r ∈ middlePrimes N, (1 : ℝ) / r := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
        intro r hr hnot
        positivity
      gcongr

theorem sum_inv_squareDivisibleCoprimeOddCofactors_le
    {N p y : ℕ} (hN : 2 ≤ N) (hp : p.Prime) (hy : y < N ^ 21) :
    ∑ m ∈ squareDivisibleCoprimeOddCofactors N p,
        (1 : ℝ) / m ≤
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          (((1 : ℝ) / (p ^ 2 : ℕ) +
              (1 : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ)) := by
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity
  exact sum_inv_squareDivisibleCoprimeOddCofactors_le_of_fiber_bound hN (by positivity)
    (fun k hk r hr hpk hpr ↦ sum_inv_shiftedSquareDivisibleLargePrimes_le hN hp hk hr hpk hpr hy)

end Erdos822
