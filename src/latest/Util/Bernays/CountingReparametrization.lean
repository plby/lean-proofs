import Util.Bernays.LocalDilation
import Util.Bernays.SpatialSmoothCancellation

/-!
# Real endpoints and exponential reparametrization of counting limits
-/

open Filter Topology Asymptotics
open scoped ContDiff

namespace Bernays

theorem scale_mul_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => scale (c * x) / scale x) atTop (𝓝 c) := by
  simpa only [div_inv_eq_mul, inv_inv, mul_comm] using scale_dilation_limit (inv_pos.mpr hc)

theorem count_floor_scale_limit {A : ℕ → ℝ} {C : ℝ}
    (hA : Tendsto (fun N : ℕ => A N / scale N) atTop (𝓝 C)) :
    Tendsto (fun x : ℝ => A ⌊x⌋₊ / scale x) atTop (𝓝 C) := by
  have hscale : ∀ᶠ x : ℝ in atTop, scale x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (scale_pos hx).ne'
  have hratio := (isEquivalent_iff_tendsto_one hscale).mp scale_natFloor_isEquivalent
  have h := (hA.comp (tendsto_nat_floor_atTop (α := ℝ))).mul hratio
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [(tendsto_nat_floor_atTop (α := ℝ)).eventually (eventually_ge_atTop 2)] with x hx
  have hs : scale (⌊x⌋₊ : ℝ) ≠ 0 := (scale_pos (by exact_mod_cast hx)).ne'
  change (A ⌊x⌋₊ / scale (⌊x⌋₊ : ℝ)) * (scale (⌊x⌋₊ : ℝ) / scale x) = _
  field_simp

theorem count_floor_dilation_limit {A : ℕ → ℝ} {C c : ℝ}
    (hA : Tendsto (fun N : ℕ => A N / scale N) atTop (𝓝 C)) (hc : 0 < c) :
    Tendsto (fun x : ℝ => A ⌊c * x⌋₊ / scale x) atTop (𝓝 (C * c)) := by
  have hcx : Tendsto (fun x : ℝ => c * x) atTop atTop := tendsto_id.const_mul_atTop hc
  have h := ((count_floor_scale_limit hA).comp hcx).mul (scale_mul_limit hc)
  apply h.congr'
  filter_upwards [hcx.eventually (eventually_gt_atTop (1 : ℝ))] with x hx
  have hs : scale (c * x) ≠ 0 := (scale_pos hx).ne'
  change (A ⌊c * x⌋₊ / scale (c * x)) * (scale (c * x) / scale x) = _
  field_simp

theorem inverse_log_tendsto :
    Tendsto (fun x : ℝ => 1 / Real.log x) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact one_div_pos.mpr (Real.log_pos hx)

theorem spatial_smooth_cancellation_atTop {a : ℕ → ℂ} {Ψ : ℝ → ℂ}
    (h : Tendsto (fun δ : ℝ =>
      ‖∑' n : ℕ, a n * Ψ ((n : ℝ) / Real.exp (1 / δ))‖ /
        (Real.exp (1 / δ) * Real.sqrt δ)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun x : ℝ => ‖∑' n : ℕ, a n * Ψ ((n : ℝ) / x)‖ / scale x)
      atTop (𝓝 0) := by
  apply (h.comp inverse_log_tendsto).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx₀ : 0 < x := zero_lt_one.trans hx
  change ‖∑' n : ℕ, a n * Ψ ((n : ℝ) / Real.exp (1 / (1 / Real.log x)))‖ /
    (Real.exp (1 / (1 / Real.log x)) * Real.sqrt (1 / Real.log x)) = _
  rw [one_div_one_div, Real.exp_log hx₀, one_div, Real.sqrt_inv]
  rfl

end Bernays
