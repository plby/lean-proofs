import ErdosProblems.Erdos520.HarperBlockLaw

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Explicit decay of the quartic Gaussian budget

The fourth-order term in the Fejér/Esseen comparison is summable over all
prime coordinates above the lower endpoint of a scheduled block.  A coarse
inverse-square-root bound is enough and lets us reuse the cubic tail estimate.
-/

theorem harperCenteredLinearPrimeVariance_le_inv
    {p : ℕ} (hp : 0 < p) (t u : ℝ) :
    harperCenteredLinearPrimeVariance p t u ≤ (p : ℝ)⁻¹ := by
  unfold harperCenteredLinearPrimeVariance
  rw [harperPrimeCoefficient_sq hp]
  have hcos : Real.cos (u * Real.log (p : ℝ)) ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_cos (u * Real.log (p : ℝ)),
      Real.cos_le_one (u * Real.log (p : ℝ))]
  have hcoeff :
      Real.cos (u * Real.log (p : ℝ)) ^ 2 / (p : ℝ) ≤ (p : ℝ)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) hcos
  exact (mul_le_of_le_one_right (by positivity)
    (one_sub_harperTiltBias_sq_le_one p t)).trans hcoeff

theorem harperCenteredLinearPrimeVariance_div_two_sq_le_cubicScale
    {p : ℕ} (hp : 1 ≤ p) (t u : ℝ) :
    (harperCenteredLinearPrimeVariance p t u / 2) ^ 2 ≤
      (1 / 4 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
  have hp0 : 0 < p := Nat.zero_lt_of_lt hp
  have hvar0 : 0 ≤ harperCenteredLinearPrimeVariance p t u :=
    harperCenteredLinearPrimeVariance_nonneg p t u
  have hvar := harperCenteredLinearPrimeVariance_le_inv hp0 t u
  have hsquare := pow_le_pow_left₀ hvar0 hvar 2
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hsqrtPos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hpR
  have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) :=
    Real.sq_sqrt hpR.le
  have hinv : (p : ℝ)⁻¹ ^ 2 ≤
      (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
    rw [show (p : ℝ)⁻¹ ^ 2 = (Real.sqrt (p : ℝ))⁻¹ ^ 4 by
      rw [← hsqrtSq, inv_pow, ← pow_mul]
      norm_num]
    have hsqrtInvLe : (Real.sqrt (p : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hsqrtPos]
      exact Real.one_le_sqrt.mpr (by exact_mod_cast hp)
    calc
      (Real.sqrt (p : ℝ))⁻¹ ^ 4 =
          (Real.sqrt (p : ℝ))⁻¹ ^ 3 *
            (Real.sqrt (p : ℝ))⁻¹ := by ring
      _ ≤ (Real.sqrt (p : ℝ))⁻¹ ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left hsqrtInvLe (by positivity)
      _ = (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by ring
  calc
    (harperCenteredLinearPrimeVariance p t u / 2) ^ 2 =
        (1 / 4 : ℝ) * harperCenteredLinearPrimeVariance p t u ^ 2 := by ring
    _ ≤ (1 / 4 : ℝ) * (p : ℝ)⁻¹ ^ 2 := by gcongr
    _ ≤ (1 / 4 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by gcongr

/-- The scheduled quartic coefficient decays at least as fast as the
inverse square root of the lower endpoint. -/
theorem harperBlockGaussianQuarticBudget_scheduled_le
    (y j : ℕ) (t u : ℝ) :
    harperBlockGaussianQuarticBudget y
        (harperScheduledPrimeBlock y j) t u ≤
      (1 / 2 : ℝ) *
        (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ := by
  let S := harperScheduledPrimeBlock y j
  unfold harperBlockGaussianQuarticBudget
  calc
    (∑ p ∈ S, (harperCenteredLinearPrimeVariance p.1 t u / 2) ^ 2) ≤
        ∑ p ∈ S, (1 / 4 : ℝ) *
          (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3 := by
      apply Finset.sum_le_sum
      intro p hp
      exact harperCenteredLinearPrimeVariance_div_two_sq_le_cubicScale
        (by have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp; omega)
        t u
    _ = (3 / 8 : ℝ) * harperBlockCubicRemainder y S := by
      unfold harperBlockCubicRemainder
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (3 / 8 : ℝ) *
        ((4 / 3 : ℝ) *
          (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹) := by
      gcongr
      exact harperBlockCubicRemainder_scheduled_le y j
    _ = (1 / 2 : ℝ) *
        (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ := by ring

/-- A completely explicit low-frequency discrepancy integral.  The sole
frequency restriction says that twice the cutoff lies below the square root
of the block's lower endpoint. -/
theorem harperScheduledBlockEsseenIntegral_le_explicit
    (y j : ℕ) (t u T : ℝ) (hT : 0 ≤ T)
    (hfrequency : 2 * T ≤ Real.sqrt (harperBlockEndpoint j : ℝ)) :
    harperEsseenIntegral
        (fun v ↦ harperTiltedLinearPrimeBlockCharacteristic y
          (harperScheduledPrimeBlock y j) t u v)
        (fun v ↦ Complex.exp
          (-((v ^ 2 * harperLinearBlockVariance y
            (harperScheduledPrimeBlock y j) t u / 2 : ℝ) : ℂ))) T ≤
      (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
        (32 * T ^ 3 + T ^ 4) := by
  have hbase := harperScheduledBlockEsseenIntegral_le y j t u T hT
    (fun v hv p hp ↦ by
      have hpA := (mem_harperScheduledPrimeBlock p).mp hp |>.1
      have hp0 : 0 < p.1 := by
        have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
        omega
      have hpR : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hp0
      have hsqrtp : 0 < Real.sqrt (p.1 : ℝ) := Real.sqrt_pos.2 hpR
      have hsqrtMono : Real.sqrt (harperBlockEndpoint j : ℝ) ≤
          Real.sqrt (p.1 : ℝ) := by
        exact Real.sqrt_le_sqrt (by exact_mod_cast hpA.le)
      have htwo : 2 * |v| ≤ Real.sqrt (p.1 : ℝ) := by
        calc
          2 * |v| ≤ 2 * T := mul_le_mul_of_nonneg_left hv (by norm_num)
          _ ≤ Real.sqrt (harperBlockEndpoint j : ℝ) := hfrequency
          _ ≤ Real.sqrt (p.1 : ℝ) := hsqrtMono
      rw [show |v| * (2 * (Real.sqrt (p.1 : ℝ))⁻¹) =
          (2 * |v|) / Real.sqrt (p.1 : ℝ) by ring]
      exact (div_le_one hsqrtp).2 htwo)
    (fun v hv p hp ↦ by
      have hpA := (mem_harperScheduledPrimeBlock p).mp hp |>.1
      have hp0 : 0 < p.1 := by
        have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
        omega
      have hpR : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hp0
      have hsqrtp : 0 < Real.sqrt (p.1 : ℝ) := Real.sqrt_pos.2 hpR
      have hsqrtMono : Real.sqrt (harperBlockEndpoint j : ℝ) ≤
          Real.sqrt (p.1 : ℝ) := by
        exact Real.sqrt_le_sqrt (by exact_mod_cast hpA.le)
      have hvroot : |v| ≤ Real.sqrt (p.1 : ℝ) := by
        calc
          |v| ≤ T := hv
          _ ≤ 2 * T := by linarith
          _ ≤ Real.sqrt (harperBlockEndpoint j : ℝ) := hfrequency
          _ ≤ Real.sqrt (p.1 : ℝ) := hsqrtMono
      have hvSq : v ^ 2 ≤ (p.1 : ℝ) := by
        rw [← Real.sq_sqrt hpR.le, ← sq_abs v]
        exact pow_le_pow_left₀ (abs_nonneg v) hvroot 2
      have hvar := harperCenteredLinearPrimeVariance_le_inv hp0 t u
      unfold harperPrimeGaussianQuadratic
      calc
        v ^ 2 * harperCenteredLinearPrimeVariance p.1 t u / 2 ≤
            v ^ 2 * (p.1 : ℝ)⁻¹ / 2 := by gcongr
        _ ≤ 1 / 2 := by
          rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
          rw [mul_inv_le_iff₀ hpR]
          simpa using! hvSq)
  calc
    harperEsseenIntegral
        (fun v ↦ harperTiltedLinearPrimeBlockCharacteristic y
          (harperScheduledPrimeBlock y j) t u v)
        (fun v ↦ Complex.exp
          (-((v ^ 2 * harperLinearBlockVariance y
            (harperScheduledPrimeBlock y j) t u / 2 : ℝ) : ℂ))) T ≤
        2 * T *
          ((16 * (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹) * T ^ 2 +
            harperBlockGaussianQuarticBudget y
              (harperScheduledPrimeBlock y j) t u * T ^ 3) := hbase
    _ ≤ 2 * T *
          ((16 * (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹) * T ^ 2 +
            ((1 / 2 : ℝ) *
              (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹) * T ^ 3) := by
      gcongr
      exact harperBlockGaussianQuarticBudget_scheduled_le y j t u
    _ = (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
        (32 * T ^ 3 + T ^ 4) := by ring

end Problem520
end Erdos
