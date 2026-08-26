import ErdosProblems.Erdos1002.GaussRareDigitWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Quantitative Gauss rare-digit windows

This file upgrades the exact one-digit block formula to an explicit quadratic
remainder.  Both sources of error are visible: the logarithmic remainder and
the ceiling/floor displacement of the two digit endpoints.  A separate upper
bound also covers windows so narrow that their integer digit block is empty;
this is the form needed for shrinking endpoint strips.
-/

open MeasureTheory Set

namespace Erdos1002

noncomputable section

/-- Elementary logarithmic remainder, proved without a Taylor-series
placeholder. -/
theorem abs_log_one_add_sub_self_le_sq {x : ℝ} (hx : 0 ≤ x) :
    |Real.log (1 + x) - x| ≤ x ^ 2 := by
  have hpos : 0 < 1 + x := by linarith
  have hupper : Real.log (1 + x) ≤ x := by
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlower : x / (1 + x) ≤ Real.log (1 + x) := by
    calc
      x / (1 + x) = 1 - (1 + x)⁻¹ := by
        field_simp
        ring
      _ ≤ Real.log (1 + x) := Real.one_sub_inv_le_log_of_pos hpos
  rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
  calc
    -(Real.log (1 + x) - x) = x - Real.log (1 + x) := by ring
    _ ≤ x - x / (1 + x) := sub_le_sub_left hlower x
    _ = x ^ 2 / (1 + x) := by
      field_simp
      ring
    _ ≤ x ^ 2 := by
      apply (div_le_iff₀ hpos).2
      nlinarith [mul_nonneg (sq_nonneg x) hx]

private theorem abs_one_div_sub_one_div_le_inv_sq
    {x q : ℝ} (hx : 0 < x) (hxq : x ≤ q) (hqx : q ≤ x + 1) :
    |1 / q - 1 / x| ≤ 1 / x ^ 2 := by
  have hq : 0 < q := hx.trans_le hxq
  have hinv : 1 / q ≤ 1 / x := one_div_le_one_div_of_le hx hxq
  rw [abs_of_nonpos (sub_nonpos.mpr hinv)]
  have hidentity : -(1 / q - 1 / x) = (q - x) / (x * q) := by
    field_simp
    ring
  rw [hidentity]
  apply (div_le_iff₀ (mul_pos hx hq)).2
  have hdiff : q - x ≤ 1 := by linarith
  have hone : 1 ≤ q / x := (le_div_iff₀ hx).2 (by simpa using! hxq)
  calc
    q - x ≤ 1 := hdiff
    _ ≤ (1 / x ^ 2) * (x * q) := by
      have heq : (1 / x ^ 2) * (x * q) = q / x := by
        field_simp
      rw [heq]
      exact hone

private theorem abs_log_one_add_one_div_sub_one_div_le
    {x q : ℝ} (hx : 0 < x) (hxq : x ≤ q) (hqx : q ≤ x + 1) :
    |Real.log (1 + 1 / q) - 1 / x| ≤ 2 * (1 / x ^ 2) := by
  have hq : 0 < q := hx.trans_le hxq
  have hlog := abs_log_one_add_sub_self_le_sq (one_div_nonneg.mpr hq.le)
  have hround := abs_one_div_sub_one_div_le_inv_sq hx hxq hqx
  have hinv : 1 / q ≤ 1 / x := one_div_le_one_div_of_le hx hxq
  have hinv0 : 0 ≤ 1 / q := one_div_nonneg.mpr hq.le
  have hsquare : (1 / q) ^ 2 ≤ (1 / x) ^ 2 :=
    by simpa only [pow_two] using! mul_self_le_mul_self hinv0 hinv
  have hsquare' : (1 / q) ^ 2 ≤ 1 / x ^ 2 := by
    simpa only [one_div_pow] using! hsquare
  calc
    |Real.log (1 + 1 / q) - 1 / x| =
        |(Real.log (1 + 1 / q) - 1 / q) + (1 / q - 1 / x)| := by
          congr 1
          ring
    _ ≤ |Real.log (1 + 1 / q) - 1 / q| + |1 / q - 1 / x| :=
      abs_add_le _ _
    _ ≤ (1 / q) ^ 2 + 1 / x ^ 2 := add_le_add hlog hround
    _ ≤ 1 / x ^ 2 + 1 / x ^ 2 := add_le_add hsquare' le_rfl
    _ = 2 * (1 / x ^ 2) := by ring

/-- The two rounded logarithmic endpoints approximate their unrounded
values with a completely explicit quadratic error.  No nonemptiness of the
integer digit block is needed for this analytic estimate. -/
theorem abs_gaussRareDigit_logNumerator_sub_le
    {scale lower upper : ℝ}
    (hscale : 0 < scale) (hlower : 0 < lower) (hupper : lower < upper) :
    |(Real.log (1 + 1 / (⌈scale / upper⌉₊ : ℝ)) -
          Real.log (1 + 1 / (((⌊scale / lower⌋₊ + 1 : ℕ) : ℝ)))) -
        (upper - lower) / scale| ≤
      2 * (upper ^ 2 + lower ^ 2) / scale ^ 2 := by
  have hupper0 : 0 < upper := hlower.trans hupper
  have hxUpper : 0 < scale / upper := div_pos hscale hupper0
  have hxLower : 0 < scale / lower := div_pos hscale hlower
  have hceilLow : scale / upper ≤ (⌈scale / upper⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hceilHigh : (⌈scale / upper⌉₊ : ℝ) ≤ scale / upper + 1 :=
    (Nat.ceil_lt_add_one hxUpper.le).le
  have hfloorLow : scale / lower ≤ (((⌊scale / lower⌋₊ + 1 : ℕ) : ℝ)) := by
    have h := (Nat.lt_floor_add_one (scale / lower)).le
    norm_num only [Nat.cast_add, Nat.cast_one] at h ⊢
    exact h
  have hfloorHigh : (((⌊scale / lower⌋₊ + 1 : ℕ) : ℝ)) ≤
      scale / lower + 1 := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    exact add_le_add (Nat.floor_le hxLower.le) le_rfl
  have hupperRaw := abs_log_one_add_one_div_sub_one_div_le
    hxUpper hceilLow hceilHigh
  have hlowerRaw := abs_log_one_add_one_div_sub_one_div_le
    hxLower hfloorLow hfloorHigh
  have hupperApprox :
      |Real.log (1 + 1 / (⌈scale / upper⌉₊ : ℝ)) - upper / scale| ≤
        2 * upper ^ 2 / scale ^ 2 := by
    convert! hupperRaw using 1 <;> field_simp
  have hlowerApprox :
      |Real.log (1 + 1 / (((⌊scale / lower⌋₊ + 1 : ℕ) : ℝ))) -
          lower / scale| ≤ 2 * lower ^ 2 / scale ^ 2 := by
    convert! hlowerRaw using 1 <;> field_simp
  calc
    |(Real.log (1 + 1 / (⌈scale / upper⌉₊ : ℝ)) -
          Real.log (1 + 1 / (((⌊scale / lower⌋₊ + 1 : ℕ) : ℝ)))) -
        (upper - lower) / scale| =
        |(Real.log (1 + 1 / (⌈scale / upper⌉₊ : ℝ)) - upper / scale) -
          (Real.log (1 + 1 / (((⌊scale / lower⌋₊ + 1 : ℕ) : ℝ))) -
            lower / scale)| := by
              congr 1
              field_simp
              ring
    _ ≤ |Real.log (1 + 1 / (⌈scale / upper⌉₊ : ℝ)) - upper / scale| +
          |Real.log (1 + 1 / (((⌊scale / lower⌋₊ + 1 : ℕ) : ℝ))) -
            lower / scale| := abs_sub _ _
    _ ≤ 2 * upper ^ 2 / scale ^ 2 + 2 * lower ^ 2 / scale ^ 2 :=
      add_le_add hupperApprox hlowerApprox
    _ = 2 * (upper ^ 2 + lower ^ 2) / scale ^ 2 := by ring

/-- Quantitative one-event Gauss rare-window estimate.  The size assumption
is exactly the convenient sufficient condition ensuring that the rounded
digit block is nonempty. -/
theorem gaussMeasure_real_scaledGaussFirstDigitWindow_quantitative
    {scale lower upper : ℝ}
    (hscale : 0 < scale) (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : lower * upper ≤ scale * (upper - lower)) :
    |gaussMeasure.real (scaledGaussFirstDigitWindow scale lower upper) -
        (upper - lower) / (scale * Real.log 2)| ≤
      (2 * (upper ^ 2 + lower ^ 2) / scale ^ 2) / Real.log 2 := by
  have hupper0 : 0 < upper := hlower.trans hupper
  have hlo : 0 < ⌈scale / upper⌉₊ :=
    Nat.ceil_pos.mpr (div_pos hscale hupper0)
  have hsep : scale / upper + 1 ≤ scale / lower := by
    have hrewrite : scale / upper + 1 = (scale + upper) / upper := by
      field_simp
    rw [hrewrite, div_le_div_iff₀ hupper0 hlower]
    nlinarith
  have hlohi : ⌈scale / upper⌉₊ ≤ ⌊scale / lower⌋₊ := by
    rw [Nat.le_floor_iff (div_pos hscale hlower).le]
    exact (Nat.ceil_lt_add_one (div_pos hscale hupper0).le).le.trans hsep
  rw [← gaussFirstDigitBlock_floorCeil_eq_scaledWindow hscale hlower hupper,
    gaussMeasure_real_gaussFirstDigitBlock hlo hlohi]
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hnum := abs_gaussRareDigit_logNumerator_sub_le hscale hlower hupper
  have hrewrite :
      (Real.log (1 + 1 / (⌈scale / upper⌉₊ : ℝ)) -
          Real.log (1 + 1 / (((⌊scale / lower⌋₊ + 1 : ℕ) : ℝ)))) /
          Real.log 2 -
        (upper - lower) / (scale * Real.log 2) =
      ((Real.log (1 + 1 / (⌈scale / upper⌉₊ : ℝ)) -
          Real.log (1 + 1 / (((⌊scale / lower⌋₊ + 1 : ℕ) : ℝ)))) -
        (upper - lower) / scale) / Real.log 2 := by
    field_simp
  rw [hrewrite, abs_div, abs_of_pos hlog]
  exact (div_le_div_iff_of_pos_right hlog).2 hnum

/-- Natural-scale specialization of the quantitative rare-window estimate. -/
theorem gaussMeasure_real_scaledGaussFirstDigitWindow_nat_quantitative
    (L : ℕ) (hL : 0 < L) {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : lower * upper ≤ (L : ℝ) * (upper - lower)) :
    |gaussMeasure.real (scaledGaussFirstDigitWindow (L : ℝ) lower upper) -
        (upper - lower) / ((L : ℝ) * Real.log 2)| ≤
      (2 * (upper ^ 2 + lower ^ 2) / (L : ℝ) ^ 2) / Real.log 2 := by
  exact gaussMeasure_real_scaledGaussFirstDigitWindow_quantitative
    (by exact_mod_cast hL) hlower hupper hlarge

/-- Uniform upper estimate which remains valid when rounding makes the digit
block empty.  This is the correct form for shrinking windows. -/
theorem gaussMeasure_real_scaledGaussFirstDigitWindow_le
    {scale lower upper : ℝ}
    (hscale : 0 < scale) (hlower : 0 < lower) (hupper : lower < upper) :
    gaussMeasure.real (scaledGaussFirstDigitWindow scale lower upper) ≤
      (((upper - lower) / scale +
        2 * (upper ^ 2 + lower ^ 2) / scale ^ 2) / Real.log 2) := by
  have hupper0 : 0 < upper := hlower.trans hupper
  have hlo : 0 < ⌈scale / upper⌉₊ :=
    Nat.ceil_pos.mpr (div_pos hscale hupper0)
  by_cases hlohi : ⌈scale / upper⌉₊ ≤ ⌊scale / lower⌋₊
  · rw [← gaussFirstDigitBlock_floorCeil_eq_scaledWindow hscale hlower hupper,
      gaussMeasure_real_gaussFirstDigitBlock hlo hlohi]
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    apply (div_le_div_iff_of_pos_right hlog).2
    have hnum := abs_gaussRareDigit_logNumerator_sub_le hscale hlower hupper
    let logUpper : ℝ := Real.log (1 + 1 / (⌈scale / upper⌉₊ : ℝ))
    let logLower : ℝ :=
      Real.log (1 + 1 / ((⌊scale / lower⌋₊ + 1 : ℕ) : ℝ))
    let target : ℝ := (upper - lower) / scale
    let remainder : ℝ := 2 * (upper ^ 2 + lower ^ 2) / scale ^ 2
    have hnum' : |logUpper - logLower - target| ≤ remainder := by
      simpa only [logUpper, logLower, target, remainder] using! hnum
    change logUpper - logLower ≤ target + remainder
    calc
      logUpper - logLower = (logUpper - logLower - target) + target := by ring
      _ ≤ remainder + target :=
        add_le_add ((le_abs_self _).trans hnum') le_rfl
      _ = target + remainder := by ring
  · have hsucc : ⌊scale / lower⌋₊ + 1 ≤ ⌈scale / upper⌉₊ := by omega
    have hcast : (((⌊scale / lower⌋₊ + 1 : ℕ) : ℝ)) ≤
        (⌈scale / upper⌉₊ : ℝ) := by exact_mod_cast hsucc
    have hinv : 1 / (⌈scale / upper⌉₊ : ℝ) ≤
        1 / (((⌊scale / lower⌋₊ + 1 : ℕ) : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hcast
    have hempty : gaussFirstDigitBlock ⌈scale / upper⌉₊ ⌊scale / lower⌋₊ = ∅ := by
      unfold gaussFirstDigitBlock
      exact Ioc_eq_empty_of_le hinv
    rw [← gaussFirstDigitBlock_floorCeil_eq_scaledWindow hscale hlower hupper,
      hempty]
    simp only [measureReal_empty]
    apply div_nonneg
    · exact add_nonneg
        (div_nonneg (sub_nonneg.mpr hupper.le) hscale.le)
        (div_nonneg
          (mul_nonneg (by norm_num)
            (add_nonneg (sq_nonneg upper) (sq_nonneg lower)))
          (sq_nonneg scale))
    · exact (Real.log_pos one_lt_two).le

/-- The shrinking strip around one value-coordinate endpoint. -/
def scaledGaussFirstDigitBoundaryStrip
    (scale center width : ℝ) : Set ℝ :=
  {x | x ∈ Ioc (0 : ℝ) 1 ∧
    |scale / (gaussFirstDigitNat x : ℝ) - center| ≤ width / scale}

theorem scaledGaussFirstDigitBoundaryStrip_eq_window
    (scale center width : ℝ) :
    scaledGaussFirstDigitBoundaryStrip scale center width =
      scaledGaussFirstDigitWindow scale
        (center - width / scale) (center + width / scale) := by
  ext x
  simp only [scaledGaussFirstDigitBoundaryStrip, scaledGaussFirstDigitWindow,
    mem_setOf_eq]
  rw [and_congr_right_iff]
  intro hx
  rw [abs_sub_le_iff]
  constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> linarith

/-- Quantitative endpoint-strip estimate.  Its right side is an explicit
constant times `scale⁻²`; no relation between the strip width and the digit
lattice spacing is assumed, so the proof also covers an empty rounded block. -/
theorem gaussMeasure_real_scaledGaussFirstDigitBoundaryStrip_le
    {scale center width : ℝ}
    (hscale : 0 < scale) (hcenter : 0 < center) (hwidth : 0 < width)
    (hsize : 2 * width ≤ center * scale) :
    gaussMeasure.real (scaledGaussFirstDigitBoundaryStrip scale center width) ≤
      (((2 * width + 10 * center ^ 2) / scale ^ 2) / Real.log 2) := by
  have hradiusPos : 0 < width / scale := div_pos hwidth hscale
  have hradius : width / scale ≤ center / 2 := by
    apply (div_le_iff₀ hscale).2
    nlinarith
  have hlower : 0 < center - width / scale := by linarith
  have hupper : center - width / scale < center + width / scale := by linarith
  rw [scaledGaussFirstDigitBoundaryStrip_eq_window]
  have hmass := gaussMeasure_real_scaledGaussFirstDigitWindow_le
    hscale hlower hupper
  have hlower0 : 0 ≤ center - width / scale := hlower.le
  have hlowerLe : center - width / scale ≤ center := by linarith
  have hupper0 : 0 ≤ center + width / scale := by positivity
  have hupperLe : center + width / scale ≤ 2 * center := by linarith
  have hlowerSq : (center - width / scale) ^ 2 ≤ center ^ 2 :=
    by simpa only [pow_two] using! mul_self_le_mul_self hlower0 hlowerLe
  have hupperSq : (center + width / scale) ^ 2 ≤ (2 * center) ^ 2 :=
    by simpa only [pow_two] using! mul_self_le_mul_self hupper0 hupperLe
  have hsquares :
      (center + width / scale) ^ 2 + (center - width / scale) ^ 2 ≤
        5 * center ^ 2 := by nlinarith
  have hscaleSq : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hinside :
      ((center + width / scale) - (center - width / scale)) / scale +
          2 * ((center + width / scale) ^ 2 +
            (center - width / scale) ^ 2) / scale ^ 2 ≤
        (2 * width + 10 * center ^ 2) / scale ^ 2 := by
    have heq :
        ((center + width / scale) - (center - width / scale)) / scale +
            2 * ((center + width / scale) ^ 2 +
              (center - width / scale) ^ 2) / scale ^ 2 =
          (2 * width + 2 * ((center + width / scale) ^ 2 +
            (center - width / scale) ^ 2)) / scale ^ 2 := by
      field_simp
      ring
    rw [heq, div_le_div_iff_of_pos_right hscaleSq]
    nlinarith
  exact hmass.trans <| (div_le_div_iff_of_pos_right
    (Real.log_pos one_lt_two)).2 hinside

end

end Erdos1002
