import Util.Linnik.FiniteMoment

/-!
# Arbitrarily small exponential moments

A fixed zero-free gap supplies an arbitrarily small absolute factor.
Combining it with repulsion makes the total moment proportional to the
exceptional gap, including when that gap is arbitrarily small.
-/

namespace Linnik

open scoped BigOperators

theorem exists_nat_mul_exp_neg_le
    {C kappa epsilon : ℝ} (hC : 0 ≤ C) (hkappa : 0 < kappa) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, C * Real.exp (-(N : ℝ) * kappa) ≤ epsilon := by
  have ha : Real.exp (-kappa) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (div_pos hepsilon (show 0 < C + 1 by linarith)) ha
  refine ⟨N, ?_⟩
  have hpow : Real.exp (-kappa) ^ N = Real.exp (-(N : ℝ) * kappa) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpow] at hN
  have hsmall := (lt_div_iff₀ (show 0 < C + 1 by linarith)).mp hN
  nlinarith [Real.exp_pos (-(N : ℝ) * kappa)]

theorem exp_moment_le_extra_gap
    {ι : Type*} (S : Finset ι) (u a : ι → ℝ)
    {c E kappa C : ℝ} (hE : 0 ≤ E)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hgap : ∀ i ∈ S, kappa ≤ u i)
    (hmoment : (∑ i ∈ S, a i * Real.exp (-c * u i)) ≤ C) :
    (∑ i ∈ S, a i * Real.exp (-(c + E) * u i)) ≤
      C * Real.exp (-E * kappa) := by
  calc
    (∑ i ∈ S, a i * Real.exp (-(c + E) * u i)) ≤
        ∑ i ∈ S, (a i * Real.exp (-c * u i)) * Real.exp (-E * kappa) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [show -(c + E) * u i = -c * u i + -E * u i by ring, Real.exp_add, ← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (ha i hi) (Real.exp_pos _).le)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hgap i hi) (neg_nonpos.mpr hE)
    _ = (∑ i ∈ S, a i * Real.exp (-c * u i)) * Real.exp (-E * kappa) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ C * Real.exp (-E * kappa) := mul_le_mul_of_nonneg_right hmoment (Real.exp_pos _).le

theorem exists_small_exp_moment_parameter
    {C c kappa epsilon : ℝ} (hC : 0 ≤ C) (hkappa : 0 < kappa) (hepsilon : 0 < epsilon) :
    ∃ D : ℝ, c ≤ D ∧ ∀ (ι : Type*) (S : Finset ι) (u a : ι → ℝ),
      (∀ i ∈ S, 0 ≤ a i) → (∀ i ∈ S, kappa ≤ u i) →
      (∑ i ∈ S, a i * Real.exp (-c * u i)) ≤ C →
      (∑ i ∈ S, a i * Real.exp (-D * u i)) ≤ epsilon := by
  obtain ⟨N, hN⟩ := exists_nat_mul_exp_neg_le hC hkappa hepsilon
  refine ⟨c + N, by linarith [Nat.cast_nonneg (α := ℝ) N], ?_⟩
  intro ι S u a ha hgap hmoment
  exact (exp_moment_le_extra_gap S u a (Nat.cast_nonneg N) ha hgap hmoment).trans hN

theorem exists_small_repelled_moment_parameter
    {C c R b kappa epsilon : ℝ} (hC : 0 ≤ C) (hkappa : 0 < kappa) (hepsilon : 0 < epsilon) :
    ∃ D : ℝ, c + 2 * R ≤ D ∧
      ∀ (ι : Type*) (S : Finset ι) (u a : ι → ℝ) (lambda : ℝ),
        0 ≤ lambda → lambda ≤ 1 →
        (∀ i ∈ S, 0 ≤ a i) → (∀ i ∈ S, kappa ≤ u i) →
        (∀ i ∈ S, Real.exp (-R * u i) ≤ b * lambda) →
        (∑ i ∈ S, a i * Real.exp (-c * u i)) ≤ C →
        (∑ i ∈ S, a i * Real.exp (-D * u i)) ≤ epsilon * lambda := by
  obtain ⟨N, hN⟩ := exists_nat_mul_exp_neg_le
    (mul_nonneg hC (sq_nonneg b)) hkappa hepsilon
  refine ⟨c + 2 * R + N, by linarith [Nat.cast_nonneg (α := ℝ) N], ?_⟩
  intro ι S u a lambda hlambda₀ hlambda₁ ha hgap hrepulsion hmoment
  have hamp := exp_moment_amplification S u a ha hrepulsion hmoment
  have hextra := exp_moment_le_extra_gap S u a (Nat.cast_nonneg N) ha hgap hamp
  calc
    (∑ i ∈ S, a i * Real.exp (-(c + 2 * R + (N : ℝ)) * u i)) ≤
        (C * (b * lambda) ^ 2) * Real.exp (-(N : ℝ) * kappa) := hextra
    _ = (C * b ^ 2 * Real.exp (-(N : ℝ) * kappa)) * lambda ^ 2 := by ring
    _ ≤ epsilon * lambda ^ 2 := mul_le_mul_of_nonneg_right hN (sq_nonneg lambda)
    _ ≤ epsilon * lambda := mul_le_mul_of_nonneg_left (by nlinarith) hepsilon.le

end Linnik
