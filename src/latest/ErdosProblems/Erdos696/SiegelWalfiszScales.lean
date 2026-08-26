import Mathlib

/-! # Elementary scales for the Siegel–Walfisz estimate -/

namespace Erdos696

open Filter

noncomputable def swError (c x : ℝ) : ℝ :=
  x * Real.exp (-c * Real.sqrt (Real.log x))

lemma swError_nonneg {x : ℝ} (hx : 0 ≤ x) (c : ℝ) : 0 ≤ swError c x :=
  mul_nonneg hx (Real.exp_pos _).le

lemma swError_antitone {c d x : ℝ} (hx : 0 ≤ x) (hcd : c ≤ d) :
    swError d x ≤ swError c x := by
  unfold swError
  gcongr

lemma sqrt_le_swError {c x : ℝ} (hc : c ≤ 1) (hx : 0 < x)
    (hlog : 4 ≤ Real.log x) : Real.sqrt x ≤ swError c x := by
  have hL : 0 ≤ Real.log x := by linarith only [hlog]
  have hu : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hu2 : Real.sqrt (Real.log x) ^ 2 = Real.log x := Real.sq_sqrt hL
  have huge : 2 ≤ Real.sqrt (Real.log x) := by
    nlinarith only [hu, hu2, hlog]
  have hscale : c * Real.sqrt (Real.log x) ≤ Real.log x / 2 := by
    have h := mul_le_mul_of_nonneg_right hc hu
    nlinarith only [h, hu2, mul_nonneg hu (sub_nonneg.mpr huge)]
  calc
    Real.sqrt x = Real.exp (Real.log x / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
      congr 1
      ring
    _ ≤ Real.exp (Real.log x - c * Real.sqrt (Real.log x)) :=
      Real.exp_monotone (by linarith only [hscale])
    _ = swError c x := by
      rw [swError, sub_eq_add_neg, Real.exp_add, Real.exp_log hx]
      congr 2
      ring

lemma eventually_log_rpow_le_sqrt (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ A ≤ Real.sqrt x := by
  have h := (isLittleO_log_rpow_rpow_atTop A
    (by norm_num : (0 : ℝ) < 1 / 2)).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog A),
    abs_of_nonneg (Real.rpow_nonneg hx0 (1 / 2)), one_mul,
    ← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg x)] using hx

/-- A pointwise exponential error remains of the same shape after taking
the maximum over all smaller endpoints. -/
lemma swError_le_of_sqrt_le {x y c d : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hlog : 0 ≤ Real.log x)
    (hys : Real.sqrt x ≤ y) (hyx : y ≤ x) (hd : 0 ≤ d) (hcd : c ≤ d / 2) :
    swError d y ≤ swError c x := by
  have hlogxy : Real.log x / 2 ≤ Real.log y := by
    rw [← Real.log_sqrt hx.le]
    exact Real.log_le_log (Real.sqrt_pos.mpr hx) hys
  have hlogy : 0 ≤ Real.log y := (by positivity : 0 ≤ Real.log x / 2).trans hlogxy
  have hsqrt : Real.sqrt (Real.log x) / 2 ≤ Real.sqrt (Real.log y) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [div_pow, Real.sq_sqrt hlog, Real.sq_sqrt hlogy]
    nlinarith only [hlogxy, hlog]
  have hscale : c * Real.sqrt (Real.log x) ≤ d * Real.sqrt (Real.log y) := by
    calc
      _ ≤ (d / 2) * Real.sqrt (Real.log x) :=
        mul_le_mul_of_nonneg_right hcd (Real.sqrt_nonneg _)
      _ = d * (Real.sqrt (Real.log x) / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt hd
  exact mul_le_mul hyx (Real.exp_monotone (by linarith only [hscale]))
    (Real.exp_pos _).le hx.le

/-- Passing from pointwise estimates to a maximum over initial segments. -/
lemma exists_eventually_uniform_sw {f : ℕ → ℝ}
    (hlinear : ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, |f n| ≤ K * n)
    (hpoint : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |f n| ≤ C * swError c n) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ᶠ x : ℕ in atTop, ∀ n : ℕ, n ≤ x → |f n| ≤ C * swError c x := by
  obtain ⟨K, hK, hlinear⟩ := hlinear
  obtain ⟨C₀, c₀, hC₀, hc₀, N, hpoint⟩ := hpoint
  let c := min (c₀ / 2) 1
  have hc : 0 < c := lt_min (by positivity) zero_lt_one
  have hc1 : c ≤ 1 := min_le_right _ _
  have hcc₀ : c ≤ c₀ / 2 := min_le_left _ _
  refine ⟨C₀ + K, c, by positivity, hc, hc1, ?_⟩
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (max 4 (N ^ 2)),
    hlogTop.eventually_ge_atTop 4] with x hx hlog
  intro n hn
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hxN : N ^ 2 ≤ x := (le_max_right _ _).trans hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hE : 0 ≤ swError c x := swError_nonneg hx0.le c
  have hs : Real.sqrt (x : ℝ) ≤ swError c x := sqrt_le_swError hc1 hx0 hlog
  by_cases hsmall : (n : ℝ) ≤ Real.sqrt (x : ℝ)
  · calc
      _ ≤ K * (n : ℝ) := hlinear n
      _ ≤ K * swError c x := mul_le_mul_of_nonneg_left (hsmall.trans hs) hK.le
      _ ≤ (C₀ + K) * swError c x :=
        mul_le_mul_of_nonneg_right (by linarith only [hC₀]) hE
  · have hlarge : Real.sqrt (x : ℝ) < n := lt_of_not_ge hsmall
    have hn0 : (0 : ℝ) < n := (Real.sqrt_nonneg _).trans_lt hlarge
    have hNs : (N : ℝ) ≤ Real.sqrt (x : ℝ) := by
      apply (Real.le_sqrt (by positivity) hx0.le).mpr
      exact_mod_cast hxN
    have hNn : N ≤ n := by exact_mod_cast (hNs.trans_lt hlarge).le
    calc
      _ ≤ C₀ * swError c₀ n := hpoint n hNn
      _ ≤ C₀ * swError c x := by
        apply mul_le_mul_of_nonneg_left _ hC₀.le
        exact swError_le_of_sqrt_le hx0 hn0 (by linarith only [hlog])
          hlarge.le (by exact_mod_cast hn) hc₀.le hcc₀
      _ ≤ (C₀ + K) * swError c x :=
        mul_le_mul_of_nonneg_right (by linarith only [hK]) hE

end Erdos696
