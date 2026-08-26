/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SlowCutoffB4Channels
import ErdosProblems.Erdos822.SlowPredecessorFibers

/-!
# Reciprocal mass of the slow-cutoff predecessor channels
-/

namespace Erdos822

open scoped BigOperators

theorem sum_inv_slowSmallMiddlePredCofactors_eq
    {N y : ℕ} (hN : 2 ≤ N) :
    ∑ m ∈ slowSmallMiddlePredCofactors N y, (1 : ℝ) / m =
      ∑ k ∈ oddSmallFactors N,
        ∑ r ∈ slowSmallMiddlePredFiber N y k,
          ∑ q ∈ largePrimes N, (1 : ℝ) / (k * r * q) := by
  classical
  unfold slowSmallMiddlePredCofactors
  rw [Finset.sum_image
    ((cofactorProduct_injOn_oddCofactorTriples hN).mono
      (Finset.filter_subset _ _))]
  rw [oddCofactorTriples]
  change
    (∑ t ∈ (oddSmallFactors N ×ˢ (middlePrimes N ×ˢ largePrimes N)).filter
        (fun t => ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ t.1 ∧ p ∣ t.2.1 - 1),
      (1 : ℝ) / cofactorProduct t) = _
  rw [Finset.sum_filter, Finset.sum_product]
  simp_rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  rw [slowSmallMiddlePredFiber]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  simp [cofactorProduct]

theorem sum_inv_slowSmallLargePredCofactors_eq
    {N y : ℕ} (hN : 2 ≤ N) :
    ∑ m ∈ slowSmallLargePredCofactors N y, (1 : ℝ) / m =
      ∑ k ∈ oddSmallFactors N,
        ∑ r ∈ middlePrimes N,
          ∑ q ∈ slowSmallLargePredFiber N y k,
            (1 : ℝ) / (k * r * q) := by
  classical
  unfold slowSmallLargePredCofactors
  rw [Finset.sum_image
    ((cofactorProduct_injOn_oddCofactorTriples hN).mono
      (Finset.filter_subset _ _))]
  rw [oddCofactorTriples]
  change
    (∑ t ∈ (oddSmallFactors N ×ˢ (middlePrimes N ×ˢ largePrimes N)).filter
        (fun t => ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ t.1 ∧ p ∣ t.2.2 - 1),
      (1 : ℝ) / cofactorProduct t) = _
  rw [Finset.sum_filter, Finset.sum_product]
  simp_rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro r hr
  rw [slowSmallLargePredFiber, Finset.sum_filter]
  simp [cofactorProduct]

theorem sum_inv_slowSmallMiddlePredCofactors_le
    {N y : ℕ} (hN : 2 ≤ N) (hy : 1 ≤ y) :
    ∑ m ∈ slowSmallMiddlePredCofactors N y, (1 : ℝ) / m ≤
      ∑ k ∈ oddSmallFactors N,
        ((1 : ℝ) / k) *
          (((((Nat.log 2 k : ℝ) / y) +
              (Nat.log 2 k : ℝ) / (N ^ 4 : ℕ)) *
              (harmonic N : ℝ)) *
            (∑ q ∈ largePrimes N, (1 : ℝ) / q)) := by
  rw [sum_inv_slowSmallMiddlePredCofactors_eq hN]
  apply Finset.sum_le_sum
  intro k hk
  have hkpos := oddSmallFactors_pos hk
  calc
    (∑ r ∈ slowSmallMiddlePredFiber N y k,
        ∑ q ∈ largePrimes N, (1 : ℝ) / (k * r * q)) =
        ∑ r ∈ slowSmallMiddlePredFiber N y k,
          (((1 : ℝ) / k) * ((1 : ℝ) / r)) *
            (∑ q ∈ largePrimes N, (1 : ℝ) / q) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      push_cast
      ring
    _ =
        ((1 : ℝ) / k) *
          ((∑ r ∈ slowSmallMiddlePredFiber N y k, (1 : ℝ) / r) *
            (∑ q ∈ largePrimes N, (1 : ℝ) / q)) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ ((1 : ℝ) / k) *
          (((((Nat.log 2 k : ℝ) / y) +
              (Nat.log 2 k : ℝ) / (N ^ 4 : ℕ)) *
              (harmonic N : ℝ)) *
            (∑ q ∈ largePrimes N, (1 : ℝ) / q)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right
        (sum_inv_slowSmallMiddlePredFiber_le_log hN hkpos hy)
      exact Finset.sum_nonneg fun q hq => by positivity

theorem sum_inv_slowSmallLargePredCofactors_le
    {N y : ℕ} (hN : 2 ≤ N) (hy : 1 ≤ y) :
    ∑ m ∈ slowSmallLargePredCofactors N y, (1 : ℝ) / m ≤
      ∑ k ∈ oddSmallFactors N,
        ((1 : ℝ) / k) *
          ((∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
            ((((Nat.log 2 k : ℝ) / y) +
              (Nat.log 2 k : ℝ) / (N ^ 21 : ℕ)) *
              (harmonic N : ℝ))) := by
  rw [sum_inv_slowSmallLargePredCofactors_eq hN]
  apply Finset.sum_le_sum
  intro k hk
  have hkpos := oddSmallFactors_pos hk
  calc
    (∑ r ∈ middlePrimes N,
        ∑ q ∈ slowSmallLargePredFiber N y k,
          (1 : ℝ) / (k * r * q)) =
        ∑ r ∈ middlePrimes N,
          (((1 : ℝ) / k) * ((1 : ℝ) / r)) *
            (∑ q ∈ slowSmallLargePredFiber N y k,
              (1 : ℝ) / q) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      push_cast
      ring
    _ =
        ((1 : ℝ) / k) *
          ((∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
            (∑ q ∈ slowSmallLargePredFiber N y k, (1 : ℝ) / q)) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ ((1 : ℝ) / k) *
          ((∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
            ((((Nat.log 2 k : ℝ) / y) +
              (Nat.log 2 k : ℝ) / (N ^ 21 : ℕ)) *
              (harmonic N : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left
        (sum_inv_slowSmallLargePredFiber_le_log hN hkpos hy)
      exact Finset.sum_nonneg fun r hr => by positivity

/-- Aggregate form of the middle-predecessor channel, replacing the
individual `log₂ k` by the uniform endpoint `log₂ N`. -/
theorem sum_inv_slowSmallMiddlePredCofactors_le_endpoint
    {N y : ℕ} (hN : 2 ≤ N) (hy : 1 ≤ y) :
    ∑ m ∈ slowSmallMiddlePredCofactors N y, (1 : ℝ) / m ≤
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (((((Nat.log 2 N : ℝ) / y) +
            (Nat.log 2 N : ℝ) / (N ^ 4 : ℕ)) *
            (harmonic N : ℝ)) *
          (∑ q ∈ largePrimes N, (1 : ℝ) / q)) := by
  calc
    (∑ m ∈ slowSmallMiddlePredCofactors N y, (1 : ℝ) / m) ≤
        ∑ k ∈ oddSmallFactors N,
          ((1 : ℝ) / k) *
            (((((Nat.log 2 k : ℝ) / y) +
                (Nat.log 2 k : ℝ) / (N ^ 4 : ℕ)) *
                (harmonic N : ℝ)) *
              (∑ q ∈ largePrimes N, (1 : ℝ) / q)) :=
      sum_inv_slowSmallMiddlePredCofactors_le hN hy
    _ ≤ ∑ k ∈ oddSmallFactors N,
          ((1 : ℝ) / k) *
            (((((Nat.log 2 N : ℝ) / y) +
                (Nat.log 2 N : ℝ) / (N ^ 4 : ℕ)) *
                (harmonic N : ℝ)) *
              (∑ q ∈ largePrimes N, (1 : ℝ) / q)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN : k ≤ N := oddSmallFactors_le hk
      have hlogNat : Nat.log 2 k ≤ Nat.log 2 N := Nat.log_mono_right hkN
      have hlog : (Nat.log 2 k : ℝ) ≤ Nat.log 2 N := by exact_mod_cast hlogNat
      have hH0 : 0 ≤ (harmonic N : ℝ) := by
        rw [harmonic_eq_sum_Icc, Rat.cast_sum]
        exact Finset.sum_nonneg fun j hj => by positivity
      gcongr
    _ = _ := by rw [Finset.sum_mul]

/-- Aggregate form of the large-predecessor channel. -/
theorem sum_inv_slowSmallLargePredCofactors_le_endpoint
    {N y : ℕ} (hN : 2 ≤ N) (hy : 1 ≤ y) :
    ∑ m ∈ slowSmallLargePredCofactors N y, (1 : ℝ) / m ≤
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        ((∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          ((((Nat.log 2 N : ℝ) / y) +
            (Nat.log 2 N : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ))) := by
  calc
    (∑ m ∈ slowSmallLargePredCofactors N y, (1 : ℝ) / m) ≤
        ∑ k ∈ oddSmallFactors N,
          ((1 : ℝ) / k) *
            ((∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
              ((((Nat.log 2 k : ℝ) / y) +
                (Nat.log 2 k : ℝ) / (N ^ 21 : ℕ)) *
                (harmonic N : ℝ))) :=
      sum_inv_slowSmallLargePredCofactors_le hN hy
    _ ≤ ∑ k ∈ oddSmallFactors N,
          ((1 : ℝ) / k) *
            ((∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
              ((((Nat.log 2 N : ℝ) / y) +
                (Nat.log 2 N : ℝ) / (N ^ 21 : ℕ)) *
                (harmonic N : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN : k ≤ N := oddSmallFactors_le hk
      have hlogNat : Nat.log 2 k ≤ Nat.log 2 N := Nat.log_mono_right hkN
      have hlog : (Nat.log 2 k : ℝ) ≤ Nat.log 2 N := by exact_mod_cast hlogNat
      have hH0 : 0 ≤ (harmonic N : ℝ) := by
        rw [harmonic_eq_sum_Icc, Rat.cast_sum]
        exact Finset.sum_nonneg fun j hj => by positivity
      gcongr
    _ = _ := by
      let A : ℝ := ∑ r ∈ middlePrimes N, (1 : ℝ) / r
      let X : ℝ := (((Nat.log 2 N : ℝ) / y) +
        (Nat.log 2 N : ℝ) / (N ^ 21 : ℕ)) * (harmonic N : ℝ)
      have hfactor :
          (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) * (A * X) =
            ∑ k ∈ oddSmallFactors N, ((1 : ℝ) / k) * (A * X) := by
        rw [Finset.sum_mul]
      change (∑ k ∈ oddSmallFactors N, ((1 : ℝ) / k) * (A * X)) =
        (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) * (A * X)
      exact hfactor.symm

end Erdos822
