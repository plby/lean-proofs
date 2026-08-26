import ErdosProblems.Erdos520.HarperTiltedMoments

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Uniform bounds for Harper's tilted prime increments

The exact identities in `HarperTiltedMoments` become useful in a
Berry--Esseen or barrier argument only after their sizes are controlled
uniformly.  This file records those elementary estimates with explicit
constants.  In particular, primes at least `16` retain at least three
quarters of their fair-sign variance under the tilted law.
-/

/-- Harper's one-coordinate sign bias is at most twice the critical
prime scale. -/
theorem abs_harperTiltBias_le
    {p : ℕ} (hp : 0 < p) (t : ℝ) :
    |harperTiltBias p t| ≤ 2 * (Real.sqrt (p : ℝ))⁻¹ := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hsqrt : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hpR
  have hnormalizer : 1 ≤ 1 + (p : ℝ)⁻¹ := by
    exact le_add_of_nonneg_right (inv_nonneg.mpr hpR.le)
  rw [harperTiltBias, abs_div, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos hsqrt, abs_of_pos (by positivity : (0 : ℝ) < 1 + (p : ℝ)⁻¹)]
  have hcos : |Real.cos (t * Real.log (p : ℝ))| ≤ 1 :=
    Real.abs_cos_le_one _
  apply (div_le_div₀ (by positivity) ?_ (by positivity) ?_)
  · nlinarith
  · simpa only [mul_one] using!
      mul_le_mul_of_nonneg_left hnormalizer hsqrt.le

/-- Squaring the preceding estimate puts the bias loss on the `1/p` scale. -/
theorem harperTiltBias_sq_le_four_div
    {p : ℕ} (hp : 0 < p) (t : ℝ) :
    harperTiltBias p t ^ 2 ≤ 4 / (p : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) :=
    Real.sq_sqrt hpR.le
  have h := sq_le_sq₀ (abs_nonneg (harperTiltBias p t))
    (by positivity : 0 ≤ 2 * (Real.sqrt (p : ℝ))⁻¹)
  have hsq := h.mpr (abs_harperTiltBias_le hp t)
  rw [sq_abs] at hsq
  calc
    harperTiltBias p t ^ 2 ≤
        (2 * (Real.sqrt (p : ℝ))⁻¹) ^ 2 := hsq
    _ = 4 / (p : ℝ) := by
      rw [mul_pow, inv_pow, hsqrtSq]
      ring

/-- On the prime blocks used in the Gaussian comparison, tilting cannot
remove more than one quarter of the fair-sign variance. -/
theorem three_fourths_le_one_sub_harperTiltBias_sq
    {p : ℕ} (hp : 16 ≤ p) (t : ℝ) :
    (3 / 4 : ℝ) ≤ 1 - harperTiltBias p t ^ 2 := by
  have hp0 : 0 < p := by omega
  have hpR : (16 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hdiv : 4 / (p : ℝ) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (p : ℝ))).2
    nlinarith
  have hb := harperTiltBias_sq_le_four_div hp0 t
  linarith

theorem one_sub_harperTiltBias_sq_le_one (p : ℕ) (t : ℝ) :
    1 - harperTiltBias p t ^ 2 ≤ 1 := by
  exact sub_le_self _ (sq_nonneg _)

/-- A centered tilted sign is uniformly bounded by two. -/
theorem abs_cubeSign_sub_harperTiltBias_le_two
    {p : ℕ} (hp : 4 ≤ p) (t : ℝ) (b : Bool) :
    |cubeSign b - harperTiltBias p t| ≤ 2 := by
  have hbias : |harperTiltBias p t| ≤ 1 := by
    have hsqrt : (2 : ℝ) ≤ Real.sqrt (p : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      exact_mod_cast hp
    have h := abs_harperTiltBias_le (by omega : 0 < p) t
    have hinv : 2 * (Real.sqrt (p : ℝ))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]
      exact (div_le_iff₀ (Real.sqrt_pos.2 (by positivity))).2
        (by simpa using! hsqrt)
    exact h.trans hinv
  calc
    |cubeSign b - harperTiltBias p t| ≤
        |cubeSign b| + |harperTiltBias p t| := abs_sub _ _
    _ ≤ 2 := by
      cases b <;> norm_num [cubeSign] <;> linarith

/-- The centered linearized logarithmic increment is bounded at the
critical prime scale. -/
theorem abs_harperLinearPrimeIncrement_sub_mean_le
    {p : ℕ} (hp : 4 ≤ p) (t u : ℝ) (b : Bool) :
    |harperLinearPrimeIncrement p u b -
        harperTiltBias p t *
          (Real.cos (u * Real.log (p : ℝ)) / Real.sqrt (p : ℝ))| ≤
      2 * (Real.sqrt (p : ℝ))⁻¹ := by
  have hpoint :
      harperLinearPrimeIncrement p u b -
          harperTiltBias p t *
            (Real.cos (u * Real.log (p : ℝ)) / Real.sqrt (p : ℝ)) =
        (cubeSign b - harperTiltBias p t) *
          Real.cos (u * Real.log (p : ℝ)) *
            (Real.sqrt (p : ℝ))⁻¹ := by
    unfold harperLinearPrimeIncrement
    ring
  rw [hpoint, abs_mul, abs_mul]
  have hsign := abs_cubeSign_sub_harperTiltBias_le_two hp t b
  have hcos : |Real.cos (u * Real.log (p : ℝ))| ≤ 1 :=
    Real.abs_cos_le_one _
  have hinv : 0 ≤ |(Real.sqrt (p : ℝ))⁻¹| := abs_nonneg _
  calc
    |cubeSign b - harperTiltBias p t| *
          |Real.cos (u * Real.log (p : ℝ))| *
        |(Real.sqrt (p : ℝ))⁻¹| ≤
      2 * 1 * |(Real.sqrt (p : ℝ))⁻¹| := by gcongr
    _ = 2 * (Real.sqrt (p : ℝ))⁻¹ := by
      rw [abs_of_nonneg (by positivity)]
      ring

/-- A convenient cubic absolute-moment envelope for one centered
linearized coordinate. -/
theorem abs_harperLinearPrimeIncrement_sub_mean_pow_three_le
    {p : ℕ} (hp : 4 ≤ p) (t u : ℝ) (b : Bool) :
    |harperLinearPrimeIncrement p u b -
        harperTiltBias p t *
          (Real.cos (u * Real.log (p : ℝ)) / Real.sqrt (p : ℝ))| ^ 3 ≤
      8 * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
  have h := abs_harperLinearPrimeIncrement_sub_mean_le hp t u b
  have hpow := pow_le_pow_left₀ (abs_nonneg _) h 3
  calc
    |harperLinearPrimeIncrement p u b -
          harperTiltBias p t *
            (Real.cos (u * Real.log (p : ℝ)) /
              Real.sqrt (p : ℝ))| ^ 3 ≤
        (2 * (Real.sqrt (p : ℝ))⁻¹) ^ 3 := hpow
    _ = 8 * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by ring

/-- Integrating the pointwise cubic envelope gives the same explicit
one-coordinate Berry--Esseen budget. -/
theorem integral_abs_harperLinearPrimeIncrement_sub_mean_pow_three_le
    {p : ℕ} (hp : 4 ≤ p) (t u : ℝ) :
    (∫ b,
        |harperLinearPrimeIncrement p u b -
          harperTiltBias p t *
            (Real.cos (u * Real.log (p : ℝ)) /
              Real.sqrt (p : ℝ))| ^ 3
        ∂harperTiltedCoin p t) ≤
      8 * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
  rw [integral_harperTiltedCoin]
  let R : ℝ := 8 * (Real.sqrt (p : ℝ))⁻¹ ^ 3
  have hwf := harperTiltedCoinWeight_nonneg p t false
  have hwt := harperTiltedCoinWeight_nonneg p t true
  have hf :=
    abs_harperLinearPrimeIncrement_sub_mean_pow_three_le hp t u false
  have ht :=
    abs_harperLinearPrimeIncrement_sub_mean_pow_three_le hp t u true
  have hsum := harperTiltedCoinWeight_false_add_true p t
  change harperTiltedCoinWeight p t false * _ +
      harperTiltedCoinWeight p t true * _ ≤ R
  calc
    harperTiltedCoinWeight p t false *
          |harperLinearPrimeIncrement p u false -
            harperTiltBias p t *
              (Real.cos (u * Real.log (p : ℝ)) /
                Real.sqrt (p : ℝ))| ^ 3 +
        harperTiltedCoinWeight p t true *
          |harperLinearPrimeIncrement p u true -
            harperTiltBias p t *
              (Real.cos (u * Real.log (p : ℝ)) /
                Real.sqrt (p : ℝ))| ^ 3 ≤
        harperTiltedCoinWeight p t false * R +
          harperTiltedCoinWeight p t true * R :=
      add_le_add (mul_le_mul_of_nonneg_left hf hwf)
        (mul_le_mul_of_nonneg_left ht hwt)
    _ = R := by rw [← add_mul, hsum, one_mul]

/-- The square of the deterministic prime coefficient is exactly the
familiar cosine-square over `p`. -/
theorem harperPrimeCoefficient_sq
    {p : ℕ} (hp : 0 < p) (u : ℝ) :
    (Real.cos (u * Real.log (p : ℝ)) / Real.sqrt (p : ℝ)) ^ 2 =
      Real.cos (u * Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [div_pow, Real.sq_sqrt hpR.le]

/-- Upper variance comparison for a tilted linearized prime coordinate. -/
theorem integral_harperLinearPrimeIncrement_sub_mean_sq_le
    {p : ℕ} (hp : 4 ≤ p) (t u : ℝ) :
    (∫ b,
        (harperLinearPrimeIncrement p u b -
          harperTiltBias p t *
            (Real.cos (u * Real.log (p : ℝ)) /
              Real.sqrt (p : ℝ))) ^ 2
        ∂harperTiltedCoin p t) ≤
      Real.cos (u * Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by
  rw [integral_harperLinearPrimeIncrement_sub_mean_sq,
    harperPrimeCoefficient_sq (by omega : 0 < p)]
  have hcoeff :
      0 ≤ Real.cos (u * Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by positivity
  exact mul_le_of_le_one_right hcoeff
    (one_sub_harperTiltBias_sq_le_one p t)

/-- Lower variance comparison: from `p ≥ 16` onward at least three quarters
of the cosine-square variance survives the tilt. -/
theorem three_fourths_mul_primeCoefficient_sq_le_integral_variance
    {p : ℕ} (hp : 16 ≤ p) (t u : ℝ) :
    (3 / 4 : ℝ) *
        (Real.cos (u * Real.log (p : ℝ)) ^ 2 / (p : ℝ)) ≤
      ∫ b,
        (harperLinearPrimeIncrement p u b -
          harperTiltBias p t *
            (Real.cos (u * Real.log (p : ℝ)) /
              Real.sqrt (p : ℝ))) ^ 2
        ∂harperTiltedCoin p t := by
  rw [integral_harperLinearPrimeIncrement_sub_mean_sq,
    harperPrimeCoefficient_sq (by omega : 0 < p)]
  have h := mul_le_mul_of_nonneg_left
    (three_fourths_le_one_sub_harperTiltBias_sq hp t)
    (div_nonneg
      (sq_nonneg (Real.cos (u * Real.log (p : ℝ))))
      (Nat.cast_nonneg p))
  simpa only [mul_comm] using! h

end Problem520
end Erdos
