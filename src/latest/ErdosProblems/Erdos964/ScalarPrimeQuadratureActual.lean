import ErdosProblems.Erdos964.ScalarPrimeQuadrature
import ErdosProblems.Erdos964.ScalarPrimeParameterUniform
import ErdosProblems.Erdos964.ScalarPrimeLogMass

/-!
# Prime quadrature with the actual floored-radius parameter
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

theorem tendsto_scalar_prime_support_integral_actual_radius (K : ℕ) (hK : 0 < K)
    (η β : ℝ) (hη : 0 < η) (hηβ : η < β) (hβ1 : β < 1) :
    Tendsto (fun t : ℕ => ∑ p ∈ scalarSmallPrimeSupport η K t,
        (Real.log p / (p : ℝ)) *
          scalarPrimeIntegrand (Real.log (modulusCutoff β t) / Real.log (t ^ 2 : ℕ))
            (Real.log p / Real.log (modulusCutoff β t)) / Real.log (modulusCutoff β t)) atTop
      (𝓝 ((∫ z in (η / β)..1, scalarSmallPrimeIntegrand (β / 2) z) +
        Real.log ((1 - β / 2) / (β / 2)) * truncatedSieveFace 1)) := by
  have hβ : 0 < β := hη.trans hηβ
  let L : ℕ → ℝ := fun t => Real.log (modulusCutoff β t)
  let a : ℕ → ℝ := fun t => L t / Real.log (t ^ 2 : ℕ)
  let A : ℕ → ℝ := fun t => ∑ p ∈ scalarSmallPrimeSupport η K t,
    (Real.log p / (p : ℝ)) * scalarPrimeIntegrand (a t) (Real.log p / L t) / L t
  let F : ℕ → ℝ := fun t => ∑ p ∈ scalarSmallPrimeSupport η K t,
    (Real.log p / (p : ℝ)) * scalarPrimeIntegrand (β / 2) (Real.log p / L t) / L t
  have hF := tendsto_scalar_prime_support_integral K hK η β hη hηβ hβ1
  change Tendsto F atTop _ at hF
  obtain ⟨C, hC, herror⟩ :=
    exists_scalar_prime_integrand_uniform_parameter_error K hK η β hη hηβ hβ1
  obtain ⟨T₀, hT₀, hmass⟩ := exists_scalar_prime_log_mass_bound β hβ
  have ha : Tendsto (fun t : ℕ => a t - β / 2) atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_log_scalar_power_radius_div_log_square β hβ).sub_const (β / 2)
  have htail : Tendsto (fun t : ℕ => (2 / β) * (C * |a t - β / 2|)) atTop (𝓝 0) := by
    simpa only [abs_zero, mul_zero] using (ha.abs.const_mul C).const_mul (2 / β)
  have hdiff : Tendsto (fun t => A t - F t) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) _ htail
    filter_upwards [herror, eventually_ge_atTop T₀,
      (tendsto_log_scalar_power_radius β hβ).eventually (eventually_gt_atTop 0)] with t he ht hL
    simp only [sub_zero, Real.norm_eq_abs]
    let w : ℕ → ℝ := fun p => (Real.log p / (p : ℝ)) / L t
    have hw (p : ℕ) : 0 ≤ w p := div_nonneg
      (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) hL.le
    have hid : A t - F t = ∑ p ∈ scalarSmallPrimeSupport η K t,
        w p * (scalarPrimeIntegrand (a t) (Real.log p / L t) -
          scalarPrimeIntegrand (β / 2) (Real.log p / L t)) := by
      dsimp only [A, F]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp only [w]
      ring
    rw [hid]
    calc
      _ ≤ ∑ p ∈ scalarSmallPrimeSupport η K t,
          |w p * (scalarPrimeIntegrand (a t) (Real.log p / L t) -
            scalarPrimeIntegrand (β / 2) (Real.log p / L t))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ scalarSmallPrimeSupport η K t, w p * (C * |a t - β / 2|) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul, abs_of_nonneg (hw p)]
        exact mul_le_mul_of_nonneg_left (he p hp) (hw p)
      _ = (∑ p ∈ scalarSmallPrimeSupport η K t, w p) * (C * |a t - β / 2|) := by
        rw [Finset.sum_mul]
      _ ≤ (2 / β) * (C * |a t - β / 2|) :=
        mul_le_mul_of_nonneg_right (hmass t K η ht) (by positivity)
  have h := hdiff.add hF
  simp only [zero_add] at h
  apply h.congr'
  exact Eventually.of_forall (fun t => by change (A t - F t) + F t = A t; ring)

end Erdos964
