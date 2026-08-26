import ErdosProblems.Erdos421.PrimeLogHarmonicBound
import ErdosProblems.Erdos421.SelbergEulerProducts

/-! # A uniform exponential error for the Selberg normalizer -/

namespace Erdos421

theorem exp_sub_one_le_exp_one_mul {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp t - 1 ≤ Real.exp 1 * t := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-t)) (Real.exp_pos t).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht1) ht
  nlinarith

theorem prime_rankin_power_bound {z : ℝ} (hz : 2 ≤ z) {p : ℕ}
    (hp : p.Prime) (hpz : (p : ℝ) ≤ z) :
    (p : ℝ) ^ (1 / Real.log z) - 1 ≤ Real.exp 1 * Real.log p / Real.log z := by
  have hL : 0 < Real.log z := Real.log_pos (by linarith)
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hLp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hlog := Real.log_le_log hpp hpz
  have ht0 : 0 ≤ Real.log p / Real.log z := div_nonneg hLp hL.le
  have ht1 : Real.log p / Real.log z ≤ 1 := (div_le_one hL).mpr hlog
  have hb := exp_sub_one_le_exp_one_mul ht0 ht1
  rw [Real.rpow_def_of_pos hpp]
  rw [show Real.log (p : ℝ) * (1 / Real.log z) = Real.log p / Real.log z by ring]
  simpa only [mul_div_assoc] using hb

theorem prime_rankin_exponent_le (S : Finset ℕ) {z : ℝ} (hz : 2 ≤ z)
    (hS : ∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ z) :
    (∑ p ∈ S, ((p : ℝ) ^ (1 / Real.log z) - 1) / p) ≤ 16 * Real.exp 1 := by
  have hL : 0 < Real.log z := Real.log_pos (by linarith)
  calc
    _ ≤ ∑ p ∈ S, (Real.exp 1 * Real.log p / Real.log z) / p := by
      apply Finset.sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_right (prime_rankin_power_bound hz (hS p hp).1 (hS p hp).2)
        (Nat.cast_nonneg p)
    _ = (Real.exp 1 / Real.log z) * ∑ p ∈ S, Real.log (p : ℝ) / p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (Real.exp 1 / Real.log z) * (16 * Real.log z) :=
      mul_le_mul_of_nonneg_left (finite_prime_log_harmonic_le S hz hS) (by positivity)
    _ = _ := by field_simp

theorem selbergNormalizer_reciprocal_lower (s : BoundingSieve) {z : ℝ} (hz : 2 ≤ z)
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hν : ∀ p ∈ s.prodPrimes.primeFactors, s.nu p = (p : ℝ)⁻¹)
    {D : ℕ} (hD : 0 < D) :
    (sieveEulerProduct s)⁻¹ *
      (1 - Real.exp (16 * Real.exp 1 - Real.log D / Real.log z)) ≤ selbergNormalizer s D := by
  have hL : 0 < Real.log z := Real.log_pos (by linarith)
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have hV := (sieveEulerProduct_pos s).le
  have hsum : (∑ p ∈ s.prodPrimes.primeFactors,
      s.nu p * ((p : ℝ) ^ (1 / Real.log z) - 1)) ≤ 16 * Real.exp 1 := by
    have hb := prime_rankin_exponent_le s.prodPrimes.primeFactors hz
      (fun p hp ↦ ⟨Nat.prime_of_mem_primeFactors hp, hprimes p hp⟩)
    have he : (∑ p ∈ s.prodPrimes.primeFactors,
        s.nu p * ((p : ℝ) ^ (1 / Real.log z) - 1)) =
        ∑ p ∈ s.prodPrimes.primeFactors, ((p : ℝ) ^ (1 / Real.log z) - 1) / p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hν p hp]
      ring
    rwa [he]
  have hb := selbergNormalizer_exp_rankin s hD (le_of_lt (one_div_pos.mpr hL))
  have he : ((D : ℝ) ^ (1 / Real.log z))⁻¹ * Real.exp (16 * Real.exp 1) =
      Real.exp (16 * Real.exp 1 - Real.log D / Real.log z) := by
    rw [Real.rpow_def_of_pos hDp, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have hc := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum)
    (by positivity : 0 ≤ ((D : ℝ) ^ (1 / Real.log z))⁻¹)
  rw [he] at hc
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hc 1) (by positivity)).trans hb

end Erdos421
