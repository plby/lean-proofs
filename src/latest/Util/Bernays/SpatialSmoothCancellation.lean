import Util.Bernays.SpatialUntwisting
import Util.Bernays.GenusSmoothedCancellation

/-!
# Cancellation against arbitrary smooth compact spatial tests
-/

open Set Filter Topology
open scoped ContDiff

namespace Bernays

theorem spatial_smooth_cancellation_of_smoothed {a : ℕ → ℂ}
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    (hsm : ∀ φ : W21,
      Tendsto (fun δ : ℝ => ‖smoothedSeries a φ δ‖ / Real.sqrt δ) (𝓝[>] 0) (𝓝 0))
    {Ψ : ℝ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : tsupport Ψ ⊆ Ioi 0) :
    Tendsto (fun δ : ℝ =>
      ‖∑' n : ℕ, a n * Ψ ((n : ℝ) / Real.exp (1 / δ))‖ /
        (Real.exp (1 / δ) * Real.sqrt δ)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨b, L, Q, hb, hL, hQ, hΨ₀, hΨQ, hΨsupp⟩ :=
    compact_positive_test_bounds hΨ.continuous hsupp hplus
  let U (δ : ℝ) : ℂ := ∑' n : ℕ, a n * Ψ ((n : ℝ) / Real.exp (1 / δ))
  let T (δ : ℝ) : ℂ := ∑' n : ℕ, dirichletTwist a δ n * Ψ ((n : ℝ) / Real.exp (1 / δ))
  let D (δ : ℝ) : ℝ := Real.exp (1 / δ) * Real.sqrt δ
  let e : ℝ := Real.exp (-1)
  have he : 0 < e := Real.exp_pos _
  have hT : Tendsto (fun δ => ‖T δ‖ / D δ) (𝓝[>] 0) (𝓝 0) :=
    spatial_twisted_cancellation_of_smoothed hsm hΨ hsupp hplus
  have hE : Tendsto (fun δ => ‖T δ - (e : ℂ) * U δ‖ / D δ) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun δ : ℝ =>
        (Real.exp (-1) * (Real.exp (δ * L) - 1) * Q) * (1 + 2 * C * (b + 2)))
        (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun δ : ℝ =>
          (Real.exp (-1) * (Real.exp (δ * L) - 1) * Q) * (1 + 2 * C * (b + 2))) := by fun_prop
      simpa only [zero_mul, Real.exp_zero, sub_self, mul_zero] using
        (hc.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    apply squeeze_zero' (Eventually.of_forall (fun δ =>
      div_nonneg (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)))) _ hlim
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact spatial_untwist_error_le ha hC hcount hb hL hQ hΨ₀ hΨQ hΨsupp hδ
  have hlim := (hT.add hE).div_const e
  simp only [add_zero, zero_div] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun δ =>
    div_nonneg (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)))) _ hlim
  filter_upwards [] with δ
  have hnorm : e * ‖U δ‖ ≤ ‖T δ‖ + ‖T δ - (e : ℂ) * U δ‖ := by
    have h := norm_sub_le (T δ) (T δ - (e : ℂ) * U δ)
    rw [sub_sub_cancel, norm_mul, Complex.norm_real, Real.norm_of_nonneg he.le] at h
    exact h
  have hnorm' : ‖U δ‖ ≤ (‖T δ‖ + ‖T δ - (e : ℂ) * U δ‖) / e := by
    apply (le_div_iff₀ he).mpr
    simpa only [mul_comm e] using hnorm
  have hdiv := div_le_div_of_nonneg_right hnorm'
    (show 0 ≤ D δ from mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
  change ‖U δ‖ / D δ ≤ (‖T δ‖ / D δ + ‖T δ - (e : ℂ) * U δ‖ / D δ) / e
  exact hdiv.trans_eq (by ring)

theorem genusLocal_spatial_smooth_cancellation {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
    ∀ Ψ : ℝ → ℂ, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Ioi 0 →
      Tendsto (fun δ : ℝ =>
        ‖∑' n : ℕ, genusLocalAF hD ψ n * Ψ ((n : ℝ) / Real.exp (1 / δ))‖ /
          (Real.exp (1 / δ) * Real.sqrt δ)) (𝓝[>] 0) (𝓝 0) := by
  let := quadraticOrderIsDomain hD
  intro ψ hψ Ψ hΨ hsupp hplus
  obtain ⟨C, hC, hcount⟩ := genusLocalAF_logCountBound hD
  exact spatial_smooth_cancellation_of_smoothed (genusLocalAF_norm_le_one hD ψ) hC.le (hcount ψ)
    (genusLocal_smoothed_cancellation hD ψ hψ) hΨ hsupp hplus

end Bernays
