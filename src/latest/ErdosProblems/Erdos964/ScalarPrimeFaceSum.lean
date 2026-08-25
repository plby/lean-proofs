import ErdosProblems.Erdos964.ScalarPrimeQuadratureActual
import ErdosProblems.Erdos964.PrimeLogWeightCancellation

/-!
# The prime-face sum in the normalization of the affine prime counts
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

noncomputable def scalarPrimeIntegral (η β : ℝ) : ℝ :=
  (∫ z in (η / β)..1, scalarSmallPrimeIntegrand (β / 2) z) +
    Real.log ((1 - β / 2) / (β / 2)) * truncatedSieveFace 1

noncomputable def scalarPrimeFaceSum (η β : ℝ) (K t : ℕ) : ℝ :=
  ∑ p ∈ scalarSmallPrimeSupport η K t,
    scalarSieveFace (Real.log p / Real.log (modulusCutoff β t)) /
      ((p : ℝ) * Real.log (((t ^ 2 : ℕ) : ℝ) / p))

theorem tendsto_scalarPrimeFaceSum (K : ℕ) (hK : 0 < K)
    (η β : ℝ) (hη : 0 < η) (hηβ : η < β) (hβ1 : β < 1) :
    Tendsto (fun t : ℕ => Real.log (t ^ 2 : ℕ) * scalarPrimeFaceSum η β K t)
      atTop (𝓝 (scalarPrimeIntegral η β)) := by
  have hβ : 0 < β := hη.trans hηβ
  have h := tendsto_scalar_prime_support_integral_actual_radius K hK η β hη hηβ hβ1
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_log_scalar_power_radius β hβ).eventually (eventually_gt_atTop 0)] with t ht hR
  have hNpos : (0 : ℝ) < (t ^ 2 : ℕ) := by
    exact_mod_cast (show 0 < t ^ 2 by positivity)
  have hNlog : 0 < Real.log (t ^ 2 : ℕ) := Real.log_pos
    (by exact_mod_cast (show 1 < t ^ 2 by nlinarith))
  rw [scalarPrimeFaceSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := (scalarSmallPrimeSupport_spec η K t p hp).1
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  rw [primeLogWeight_scalarPrimeIntegrand_eq _ _ p hR.ne' hprime,
    reference_log_weight_cancel _ _ _ _ _ hR.ne' hNlog.ne',
    Real.log_div hNpos.ne' hp0]

theorem scalarPrimeIntegral_positive_margin :
    (19 / 15 : ℝ) + 1 / 10000 < 3 * sieveRadiusExponent *
      scalarPrimeIntegral ((2 * sieveRadiusExponent) / 100) (2 * sieveRadiusExponent) := by
  have hparam : 2 * sieveRadiusExponent / 2 = sieveRadiusExponent := by ring
  have hcut : ((2 * sieveRadiusExponent) / 100) / (2 * sieveRadiusExponent) =
      (1 / 100 : ℝ) := by norm_num [sieveRadiusExponent]
  have hJ : scalarPrimeIntegral ((2 * sieveRadiusExponent) / 100) (2 * sieveRadiusExponent) =
      (∫ z in (1 / 100 : ℝ)..1,
        truncatedSieveFace z / (z * (1 - sieveRadiusExponent * z))) +
      Real.log ((1 - sieveRadiusExponent) / sieveRadiusExponent) * truncatedSieveFace 1 := by
    unfold scalarPrimeIntegral
    rw [hparam, hcut]
    congr 1
    apply intervalIntegral.integral_congr
    intro z hz
    exact (ggpy_face_integrand_eq sieveRadiusExponent z).symm
  have h := ggpy_integral_positive_margin
  rw [ggpy_first_moment_eq, ← hJ] at h
  linarith

end Erdos964
