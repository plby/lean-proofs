import ErdosProblems.Erdos520.HarperEsseen
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.IntegralCharFun

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory Set
open scoped FourierTransform Interval Real

namespace Erdos
namespace Problem520

/-!
# The Fejér smoothing probability law

We use the continuous squared-sinc form of the Fejér density.  With the
characteristic-function convention `exp (t * x * I)`, its transform is the
triangular cutoff `max (1 - |t|) 0`.
-/

/-- The triangular characteristic cutoff. -/
noncomputable def harperFejerTriangle (t : ℝ) : ℝ :=
  max (1 - |t|) 0

/-- The same triangle in Mathlib's `exp (-2π i x ξ)` Fourier convention. -/
noncomputable def harperFejerFourierProfile (ξ : ℝ) : ℂ :=
  (harperFejerTriangle (2 * Real.pi * ξ) : ℝ)

/-- Fejér's probability density, with its removable value filled at zero. -/
noncomputable def harperFejerDensity (x : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * Real.sinc (x / 2) ^ 2

theorem continuous_harperFejerTriangle : Continuous harperFejerTriangle := by
  unfold harperFejerTriangle
  fun_prop

@[simp] theorem harperFejerTriangle_neg (t : ℝ) :
    harperFejerTriangle (-t) = harperFejerTriangle t := by
  simp [harperFejerTriangle]

theorem harperFejerTriangle_nonneg (t : ℝ) :
    0 ≤ harperFejerTriangle t := by
  unfold harperFejerTriangle
  exact le_max_right _ _

theorem harperFejerTriangle_le_one (t : ℝ) :
    harperFejerTriangle t ≤ 1 := by
  unfold harperFejerTriangle
  exact max_le (by linarith [abs_nonneg t]) zero_le_one

theorem continuous_harperFejerFourierProfile :
    Continuous harperFejerFourierProfile := by
  unfold harperFejerFourierProfile
  exact Complex.continuous_ofReal.comp
    (continuous_harperFejerTriangle.comp (by fun_prop))

theorem continuous_harperFejerDensity : Continuous harperFejerDensity := by
  unfold harperFejerDensity
  fun_prop

theorem harperFejerDensity_nonneg (x : ℝ) :
    0 ≤ harperFejerDensity x := by
  unfold harperFejerDensity
  positivity

@[simp] theorem harperFejerDensity_zero :
    harperFejerDensity 0 = (2 * Real.pi)⁻¹ := by
  simp [harperFejerDensity]

theorem harperFejerDensity_eq_one_sub_cos
    {x : ℝ} (hx : x ≠ 0) :
    harperFejerDensity x = (1 - Real.cos x) / (Real.pi * x ^ 2) := by
  rw [harperFejerDensity, Real.sinc_of_ne_zero (div_ne_zero hx (by norm_num))]
  have hcos := Real.cos_two_mul_eq_one_sub (x / 2)
  have htwo : 2 * (x / 2) = x := by ring
  rw [htwo] at hcos
  have hsin : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    linarith
  rw [hsin]
  field_simp

theorem abs_sinc_half_le_two_div_abs
    {x : ℝ} (hx : x ≠ 0) :
    |Real.sinc (x / 2)| ≤ 2 / |x| := by
  rw [Real.sinc_of_ne_zero (div_ne_zero hx (by norm_num)), abs_div,
    abs_div]
  norm_num
  have hsin : |Real.sin (x / 2)| ≤ 1 := Real.abs_sin_le_one _
  have hxabs : 0 < |x| := abs_pos.mpr hx
  calc
    |Real.sin (x / 2)| / (|x| / 2) ≤ 1 / (|x| / 2) := by
      gcongr
    _ = 2 / |x| := by field_simp

/-- A convenient global integrable envelope. -/
theorem harperFejerDensity_le_cauchy (x : ℝ) :
    harperFejerDensity x ≤ 8 * (1 + x ^ 2)⁻¹ := by
  by_cases hx : |x| ≤ 1
  · have hsinc := Real.abs_sinc_le_one (x / 2)
    have hsincSq : Real.sinc (x / 2) ^ 2 ≤ 1 := by
      rw [← sq_abs]
      simpa using! (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 hsinc
    have hcoef : (2 * Real.pi)⁻¹ ≤ 1 := by
      rw [inv_le_one₀]
      · nlinarith [Real.pi_gt_three]
      · positivity
    have hdens : harperFejerDensity x ≤ 1 := by
      unfold harperFejerDensity
      calc
        (2 * Real.pi)⁻¹ * Real.sinc (x / 2) ^ 2 ≤ 1 * 1 := by
          gcongr
        _ = 1 := by ring
    have hxSq : x ^ 2 ≤ 1 := by
      rw [← sq_abs]
      simpa using! (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 hx
    have hden : 0 < 1 + x ^ 2 := by positivity
    rw [le_mul_inv_iff₀ hden]
    nlinarith
  · have hx0 : x ≠ 0 := by
      intro h
      subst x
      simp at hx
    have hxabs : 1 < |x| := lt_of_not_ge hx
    have hsinc := abs_sinc_half_le_two_div_abs hx0
    have hsincSq : Real.sinc (x / 2) ^ 2 ≤ (2 / |x|) ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _)
        (div_nonneg (by norm_num) (abs_nonneg x))).2 hsinc
    have hcoef : (2 * Real.pi)⁻¹ ≤ 1 := by
      rw [inv_le_one₀]
      · nlinarith [Real.pi_gt_three]
      · positivity
    have hxSq : 1 < x ^ 2 := by nlinarith [sq_abs x]
    have hxSqPos : 0 < x ^ 2 := by positivity
    have hden : 0 < 1 + x ^ 2 := by positivity
    have hdens : harperFejerDensity x ≤ 4 / x ^ 2 := by
      unfold harperFejerDensity
      calc
        (2 * Real.pi)⁻¹ * Real.sinc (x / 2) ^ 2 ≤
            1 * (2 / |x|) ^ 2 := by gcongr
        _ = 4 / x ^ 2 := by
          rw [div_pow, sq_abs]
          norm_num
    rw [le_mul_inv_iff₀ hden]
    calc
      harperFejerDensity x * (1 + x ^ 2) ≤
          (4 / x ^ 2) * (1 + x ^ 2) := by gcongr
      _ ≤ 8 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hxSqPos]
        nlinarith

theorem integrable_harperFejerDensity : Integrable harperFejerDensity := by
  refine (integrable_inv_one_add_sq.const_mul 8).mono'
    continuous_harperFejerDensity.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (harperFejerDensity_nonneg x)]
  exact harperFejerDensity_le_cauchy x

theorem support_harperFejerFourierProfile_subset :
    Function.support harperFejerFourierProfile ⊆
      Icc (-(2 * Real.pi)⁻¹) ((2 * Real.pi)⁻¹) := by
  let a : ℝ := (2 * Real.pi)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hpa : (2 * Real.pi) * a = 1 := by
    dsimp [a]
    exact mul_inv_cancel₀ hp.ne'
  intro x hx
  by_contra hmem
  simp only [mem_Icc, not_and_or, not_le] at hmem
  have habsx : a < |x| := by
    rcases hmem with hleft | hright
    · have hxneg : x < 0 := hleft.trans (neg_lt_zero.mpr ha)
      rw [abs_of_neg hxneg]
      linarith
    · have hxpos : 0 < x := ha.trans hright
      rw [abs_of_pos hxpos]
      exact hright
  have hmul : 1 < |2 * Real.pi * x| := by
    have h := mul_lt_mul_of_pos_left habsx hp
    rw [hpa] at h
    simpa [abs_mul, abs_of_pos hp] using! h
  unfold harperFejerFourierProfile harperFejerTriangle at hx
  norm_cast at hx
  have : max (1 - |2 * Real.pi * x|) 0 = 0 :=
    max_eq_right (by linarith)
  exact hx (by simpa [this])

theorem integrable_harperFejerFourierProfile :
    Integrable harperFejerFourierProfile := by
  let a : ℝ := (2 * Real.pi)⁻¹
  have hsupp : Function.support harperFejerFourierProfile ⊆
      Icc (-a) a := by
    simpa [a] using! support_harperFejerFourierProfile_subset
  have hOn := continuous_harperFejerFourierProfile.continuousOn.integrableOn_compact
    (μ := volume)
    (isCompact_Icc : IsCompact (Icc (-a) a))
  have hInd := hOn.integrable_indicator measurableSet_Icc
  have heq : (Icc (-a) a).indicator harperFejerFourierProfile =
      harperFejerFourierProfile := by
    funext x
    by_cases hx : x ∈ Icc (-a) a
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      by_contra hne
      exact hx (hsupp (fun h ↦ hne h.symm))
  rw [heq] at hInd
  exact hInd

/-! ## Explicit inverse transform of the triangle -/

theorem harperFejerFourierProfile_eq_left
    {x : ℝ} (hx : x ∈ Icc (-(2 * Real.pi)⁻¹) 0) :
    harperFejerFourierProfile x =
      ((1 + (2 * Real.pi) * x : ℝ) : ℂ) := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hpa : (2 * Real.pi) * (2 * Real.pi)⁻¹ = 1 :=
    mul_inv_cancel₀ hp.ne'
  have hnonpos : (2 * Real.pi) * x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hp.le hx.2
  have hlower : -1 ≤ (2 * Real.pi) * x := by
    have h := mul_le_mul_of_nonneg_left hx.1 hp.le
    rw [mul_neg, hpa] at h
    exact h
  unfold harperFejerFourierProfile harperFejerTriangle
  rw [abs_of_nonpos hnonpos, max_eq_left (by linarith)]
  norm_num

theorem harperFejerFourierProfile_eq_right
    {x : ℝ} (hx : x ∈ Icc 0 ((2 * Real.pi)⁻¹)) :
    harperFejerFourierProfile x =
      ((1 - (2 * Real.pi) * x : ℝ) : ℂ) := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hpa : (2 * Real.pi) * (2 * Real.pi)⁻¹ = 1 :=
    mul_inv_cancel₀ hp.ne'
  have hnonneg : 0 ≤ (2 * Real.pi) * x :=
    mul_nonneg hp.le hx.1
  have hupper : (2 * Real.pi) * x ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hx.2 hp.le
    rw [hpa] at h
    exact h
  unfold harperFejerFourierProfile harperFejerTriangle
  rw [abs_of_nonneg hnonneg, max_eq_left (by linarith)]

private theorem hasDerivAt_cexp_mul_affine_primitive
    (A B C : ℂ) (hC : C ≠ 0) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ ↦
        Complex.exp (C * (y : ℂ)) *
          ((A + B * (y : ℂ)) / C - B / C ^ 2))
      (Complex.exp (C * (x : ℂ)) * (A + B * (x : ℂ))) x := by
  have hlin : HasDerivAt (fun y : ℝ ↦ C * (y : ℂ)) C x := by
    simpa only [mul_one] using!
      (((hasDerivAt_id (x : ℂ)).const_mul C).comp_ofReal)
  have hexp : HasDerivAt
      (fun y : ℝ ↦ Complex.exp (C * (y : ℂ)))
      (Complex.exp (C * (x : ℂ)) * C) x :=
    (Complex.hasDerivAt_exp _).comp x hlin
  have hBy : HasDerivAt (fun y : ℝ ↦ B * (y : ℂ)) B x := by
    simpa only [mul_one] using!
      (((hasDerivAt_id (x : ℂ)).const_mul B).comp_ofReal)
  have hq : HasDerivAt
      (fun y : ℝ ↦ (A + B * (y : ℂ)) / C - B / C ^ 2)
      (B / C) x := by
    exact ((hBy.const_add A).div_const C).sub_const (B / C ^ 2)
  convert! hexp.mul hq using 1
  field_simp
  ring

private theorem intervalIntegral_affine_mul_cexp
    (A B C : ℂ) (hC : C ≠ 0) (l u : ℝ) :
    (∫ x in l..u,
        (A + B * (x : ℂ)) * Complex.exp (C * (x : ℂ))) =
      Complex.exp (C * (u : ℂ)) *
          ((A + B * (u : ℂ)) / C - B / C ^ 2) -
        Complex.exp (C * (l : ℂ)) *
          ((A + B * (l : ℂ)) / C - B / C ^ 2) := by
  let P : ℝ → ℂ := fun y ↦
    Complex.exp (C * (y : ℂ)) *
      ((A + B * (y : ℂ)) / C - B / C ^ 2)
  have hP (x : ℝ) : HasDerivAt P
      (Complex.exp (C * (x : ℂ)) * (A + B * (x : ℂ))) x := by
    exact hasDerivAt_cexp_mul_affine_primitive A B C hC x
  have hderiv : deriv P =
      fun x : ℝ ↦ Complex.exp (C * (x : ℂ)) * (A + B * (x : ℂ)) :=
    funext fun x ↦ (hP x).deriv
  calc
    (∫ x in l..u,
        (A + B * (x : ℂ)) * Complex.exp (C * (x : ℂ))) =
        ∫ x in l..u,
          Complex.exp (C * (x : ℂ)) * (A + B * (x : ℂ)) := by
      congr 1 with x
      ring
    _ = P u - P l := by
      exact intervalIntegral.integral_deriv_eq_sub' P hderiv
        (fun x _ ↦ (hP x).differentiableAt) (by fun_prop)
    _ = _ := rfl

private theorem intervalIntegral_affine
    (A B : ℂ) (l u : ℝ) :
    (∫ x in l..u, A + B * (x : ℂ)) =
      (A * (u : ℂ) + B * (u : ℂ) ^ 2 / 2) -
        (A * (l : ℂ) + B * (l : ℂ) ^ 2 / 2) := by
  let P : ℝ → ℂ := fun y ↦
    A * (y : ℂ) + B * (y : ℂ) ^ 2 / 2
  have hP (x : ℝ) : HasDerivAt P (A + B * (x : ℂ)) x := by
    have hid : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) 1 x :=
      (hasDerivAt_id (x : ℂ)).comp_ofReal
    convert! (hid.const_mul A).add ((hid.pow 2).const_mul (B / 2)) using 1
    · funext y
      simp [P]
      ring
    · ring
  have hderiv : deriv P = fun x : ℝ ↦ A + B * (x : ℂ) :=
    funext fun x ↦ (hP x).deriv
  calc
    (∫ x in l..u, A + B * (x : ℂ)) = P u - P l := by
      exact intervalIntegral.integral_deriv_eq_sub' P hderiv
        (fun x _ ↦ (hP x).differentiableAt) (by fun_prop)
    _ = _ := rfl

private theorem intervalIntegral_harperFejerFourierProfile_eq_inv_two_pi :
    (∫ ξ in (-(2 * Real.pi)⁻¹)..((2 * Real.pi)⁻¹),
      harperFejerFourierProfile ξ) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by
  let p : ℝ := 2 * Real.pi
  let a : ℝ := p⁻¹
  have hp : 0 < p := by dsimp [p]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hsplit :
      (∫ ξ in (-a)..0, harperFejerFourierProfile ξ) +
          ∫ ξ in 0..a, harperFejerFourierProfile ξ =
        ∫ ξ in (-a)..a, harperFejerFourierProfile ξ := by
    exact intervalIntegral.integral_add_adjacent_intervals
      (continuous_harperFejerFourierProfile.intervalIntegrable _ _)
      (continuous_harperFejerFourierProfile.intervalIntegrable _ _)
  rw [← hsplit]
  have hleft :
      (∫ ξ in (-a)..0, harperFejerFourierProfile ξ) =
        ∫ ξ in (-a)..0, ((1 + p * ξ : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro ξ hξ
    have hξa : ξ ∈ Icc (-a) 0 := by
      simpa [uIcc_of_le (neg_nonpos.mpr ha.le)] using! hξ
    simpa [p, a] using! harperFejerFourierProfile_eq_left hξa
  have hright :
      (∫ ξ in 0..a, harperFejerFourierProfile ξ) =
        ∫ ξ in 0..a, ((1 - p * ξ : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro ξ hξ
    have hξa : ξ ∈ Icc 0 a := by
      simpa [uIcc_of_le ha.le] using! hξ
    simpa [p, a] using! harperFejerFourierProfile_eq_right hξa
  rw [hleft, hright]
  simp_rw [show ∀ ξ : ℝ, ((1 + p * ξ : ℝ) : ℂ) =
      1 + (p : ℂ) * (ξ : ℂ) by intro ξ; norm_cast,
    show ∀ ξ : ℝ, ((1 - p * ξ : ℝ) : ℂ) =
      1 + (-(p : ℂ)) * (ξ : ℂ) by intro ξ; push_cast; ring]
  rw [intervalIntegral_affine, intervalIntegral_affine]
  dsimp [a]
  push_cast
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hp.ne', hp0]
  dsimp [p]
  push_cast
  ring

private theorem harperFejerFourierInv_eq_interval (x : ℝ) :
    FourierTransformInv.fourierInv harperFejerFourierProfile x =
      ∫ ξ in (-(2 * Real.pi)⁻¹)..((2 * Real.pi)⁻¹),
        Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
          harperFejerFourierProfile ξ := by
  rw [Real.fourierInv_eq']
  simp only [smul_eq_mul]
  let a : ℝ := (2 * Real.pi)⁻¹
  have ha : 0 ≤ a := by dsimp [a]; positivity
  let f : ℝ → ℂ := fun ξ ↦
    Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
      harperFejerFourierProfile ξ
  change (∫ ξ, f ξ) = ∫ ξ in (-a)..a, f ξ
  have hind : (Icc (-a) a).indicator f = f := by
    funext ξ
    by_cases hξ : ξ ∈ Icc (-a) a
    · rw [Set.indicator_of_mem hξ]
    · rw [Set.indicator_of_notMem hξ]
      have hprof : harperFejerFourierProfile ξ = 0 := by
        by_contra hne
        have hs : ξ ∈ Function.support harperFejerFourierProfile := by
          exact hne
        exact hξ (by
          simpa [a] using! support_harperFejerFourierProfile_subset hs)
      simp [f, hprof]
  calc
    (∫ ξ, f ξ) = ∫ ξ in Icc (-a) a, f ξ := by
      rw [← integral_indicator measurableSet_Icc, hind]
    _ = ∫ ξ in (-a)..a, f ξ := by
      rw [intervalIntegral.integral_of_le (by linarith : -a ≤ a),
        ← integral_Icc_eq_integral_Ioc]

theorem harperFejerFourierInv_eq_density (x : ℝ) :
    FourierTransformInv.fourierInv harperFejerFourierProfile x =
      (harperFejerDensity x : ℂ) := by
  by_cases hx : x = 0
  · subst x
    rw [harperFejerFourierInv_eq_interval]
    simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_mul]
    rw [intervalIntegral_harperFejerFourierProfile_eq_inv_two_pi]
    simp [harperFejerDensity_zero]
  · rw [harperFejerFourierInv_eq_interval]
    let p : ℝ := 2 * Real.pi
    let a : ℝ := p⁻¹
    let C : ℂ := ((p * x : ℝ) : ℂ) * Complex.I
    let f : ℝ → ℂ := fun ξ ↦
      Complex.exp (((p * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
        harperFejerFourierProfile ξ
    have hp : 0 < p := by dsimp [p]; positivity
    have ha : 0 < a := by dsimp [a]; positivity
    have hinner (y : ℝ) : inner ℝ y x = y * x := by
      change x * y = y * x
      ring
    have hC : C ≠ 0 := by
      dsimp [C]
      apply mul_ne_zero
      · exact_mod_cast (mul_ne_zero hp.ne' hx)
      · exact Complex.I_ne_zero
    change (∫ ξ in (-a)..a, f ξ) = (harperFejerDensity x : ℂ)
    have hfcont : Continuous f := by
      change Continuous (fun ξ : ℝ ↦
        Complex.exp (((p * (x * ξ) : ℝ) : ℂ) * Complex.I) *
          harperFejerFourierProfile ξ)
      apply Continuous.mul
      · fun_prop
      · exact continuous_harperFejerFourierProfile
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hfcont.intervalIntegrable (-a) 0)
      (hfcont.intervalIntegrable 0 a)]
    have hleft :
        (∫ ξ in (-a)..0, f ξ) =
          ∫ ξ in (-a)..0,
            (1 + (p : ℂ) * (ξ : ℂ)) *
              Complex.exp (C * (ξ : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro ξ hξ
      have hξa : ξ ∈ Icc (-a) 0 := by
        simpa [uIcc_of_le (neg_nonpos.mpr ha.le)] using! hξ
      have hprof : harperFejerFourierProfile ξ =
          ((1 + p * ξ : ℝ) : ℂ) := by
        simpa [p, a] using! harperFejerFourierProfile_eq_left (by
          simpa [p, a] using! hξa)
      have harg : (((p * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) =
          C * (ξ : ℂ) := by
        rw [hinner]
        dsimp [C]
        push_cast
        ring
      change Complex.exp (((p * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
        harperFejerFourierProfile ξ = _
      rw [hprof, harg]
      push_cast
      ring
    have hright :
        (∫ ξ in 0..a, f ξ) =
          ∫ ξ in 0..a,
            (1 + (-(p : ℂ)) * (ξ : ℂ)) *
              Complex.exp (C * (ξ : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro ξ hξ
      have hξa : ξ ∈ Icc 0 a := by
        simpa [uIcc_of_le ha.le] using! hξ
      have hprof : harperFejerFourierProfile ξ =
          ((1 - p * ξ : ℝ) : ℂ) := by
        simpa [p, a] using! harperFejerFourierProfile_eq_right (by
          simpa [p, a] using! hξa)
      have harg : (((p * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) =
          C * (ξ : ℂ) := by
        rw [hinner]
        dsimp [C]
        push_cast
        ring
      change Complex.exp (((p * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
        harperFejerFourierProfile ξ = _
      rw [hprof, harg]
      push_cast
      ring
    have hpa : p * a = 1 := by
      dsimp [a]
      exact mul_inv_cancel₀ hp.ne'
    have hpaC : (p : ℂ) * (a : ℂ) = 1 := by
      exact_mod_cast hpa
    have hCa : C * (a : ℂ) = (x : ℂ) * Complex.I := by
      dsimp [C]
      push_cast
      calc
        ((p : ℂ) * (x : ℂ)) * Complex.I * (a : ℂ) =
            ((p : ℂ) * (a : ℂ)) * (x : ℂ) * Complex.I := by ring
        _ = (x : ℂ) * Complex.I := by rw [hpaC]; ring
    have hCnegA' : C * -(a : ℂ) = -((x : ℂ) * Complex.I) := by
      rw [mul_neg, hCa]
    rw [hleft, hright,
      intervalIntegral_affine_mul_cexp 1 (p : ℂ) C hC,
      intervalIntegral_affine_mul_cexp 1 (-(p : ℂ)) C hC,
      harperFejerDensity_eq_one_sub_cos hx]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    push_cast
    rw [hCa, hCnegA']
    simp only [hpaC, neg_mul, mul_neg, add_neg_cancel, zero_div,
      Complex.exp_neg]
    have hsum :
        (Complex.exp ((x : ℂ) * Complex.I))⁻¹ +
            Complex.exp ((x : ℂ) * Complex.I) =
          2 * Complex.cos (x : ℂ) := by
      rw [← Complex.exp_neg]
      have hneg : -((x : ℂ) * Complex.I) = (-(x : ℂ)) * Complex.I := by ring
      rw [hneg, Complex.exp_mul_I, Complex.exp_mul_I,
        Complex.cos_neg, Complex.sin_neg]
      ring
    field_simp [hC, hx, Real.pi_ne_zero]
    simp only [zero_mul, add_zero, one_mul]
    dsimp [C, p]
    push_cast
    have hE : Complex.exp ((x : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have hsumE :
        1 + Complex.exp ((x : ℂ) * Complex.I) ^ 2 =
          2 * Complex.cos (x : ℂ) *
            Complex.exp ((x : ℂ) * Complex.I) := by
      calc
        1 + Complex.exp ((x : ℂ) * Complex.I) ^ 2 =
            ((Complex.exp ((x : ℂ) * Complex.I))⁻¹ +
              Complex.exp ((x : ℂ) * Complex.I)) *
                Complex.exp ((x : ℂ) * Complex.I) := by
          field_simp [hE]
        _ = _ := by rw [hsum]
    ring_nf
    rw [Complex.I_sq]
    linear_combination
      2 * ((x : ℂ) ^ 2 * (Real.pi : ℂ) ^ 2) * hsumE

@[simp] theorem harperFejerDensity_neg (x : ℝ) :
    harperFejerDensity (-x) = harperFejerDensity x := by
  unfold harperFejerDensity
  have h : -x / 2 = -(x / 2) := by ring
  rw [h, Real.sinc_neg]

theorem harperFejerFourierProfile_fourier_eq_density (x : ℝ) :
    FourierTransform.fourier harperFejerFourierProfile x =
      (harperFejerDensity x : ℂ) := by
  have h := Real.fourierInv_eq_fourier_neg harperFejerFourierProfile (-x)
  rw [harperFejerFourierInv_eq_density] at h
  simpa using! h.symm

theorem integrable_fourier_harperFejerFourierProfile :
    Integrable (FourierTransform.fourier harperFejerFourierProfile) := by
  have heq : FourierTransform.fourier harperFejerFourierProfile =
      fun x : ℝ ↦ (harperFejerDensity x : ℂ) := by
    funext x
    exact harperFejerFourierProfile_fourier_eq_density x
  rw [heq]
  exact integrable_harperFejerDensity.ofReal

/-- The Fejér density has the compact triangular Fourier transform. -/
theorem harperFejerDensity_fourier_eq_profile (x : ℝ) :
    FourierTransform.fourier (fun y : ℝ ↦ (harperFejerDensity y : ℂ)) x =
      harperFejerFourierProfile x := by
  have hinv : FourierTransformInv.fourierInv harperFejerFourierProfile =
      fun y : ℝ ↦ (harperFejerDensity y : ℂ) := by
    funext y
    exact harperFejerFourierInv_eq_density y
  have h := continuous_harperFejerFourierProfile.fourier_fourierInv_eq
    integrable_harperFejerFourierProfile
    integrable_fourier_harperFejerFourierProfile
  rw [hinv] at h
  exact congrFun h x

theorem integral_harperFejerDensity_eq_one :
    (∫ x : ℝ, harperFejerDensity x) = 1 := by
  have h := harperFejerDensity_fourier_eq_profile 0
  rw [Real.fourier_eq'] at h
  simp only [neg_mul, inner_zero_right, mul_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, smul_eq_mul, one_mul,
    harperFejerFourierProfile, harperFejerTriangle, abs_zero, sub_zero,
    zero_le_one, sup_of_le_left, Complex.ofReal_one] at h
  exact_mod_cast h

noncomputable def harperFejerDensityNNReal (x : ℝ) : NNReal :=
  Real.toNNReal (harperFejerDensity x)

@[simp] theorem coe_harperFejerDensityNNReal (x : ℝ) :
    (harperFejerDensityNNReal x : ℝ) = harperFejerDensity x := by
  simp [harperFejerDensityNNReal, harperFejerDensity_nonneg]

theorem continuous_harperFejerDensityNNReal :
    Continuous harperFejerDensityNNReal := by
  exact continuous_real_toNNReal.comp continuous_harperFejerDensity

/-- The probability measure associated to the Fejér density. -/
noncomputable def harperFejerMeasure : Measure ℝ :=
  volume.withDensity (fun x ↦ (harperFejerDensityNNReal x : ENNReal))

noncomputable instance harperFejerMeasure_isProbabilityMeasure :
    IsProbabilityMeasure harperFejerMeasure := by
  refine ⟨?_⟩
  rw [harperFejerMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [lintegral_coe_eq_integral harperFejerDensityNNReal]
  · simp [integral_harperFejerDensity_eq_one]
  · simpa only [coe_harperFejerDensityNNReal] using!
      integrable_harperFejerDensity

/-- The characteristic function of the Fejér probability law is the compact
triangular cutoff. -/
theorem charFun_harperFejerMeasure (t : ℝ) :
    charFun harperFejerMeasure t = (harperFejerTriangle t : ℂ) := by
  let p : ℝ := 2 * Real.pi
  have hp : p ≠ 0 := by dsimp [p]; positivity
  have hphase (x : ℝ) :
      -2 * Real.pi * inner ℝ x (-(t / p)) = t * x := by
    have hinner : inner ℝ x (-(t / p)) = -(t / p) * x := by
      change (-(t / p)) * x = -(t / p) * x
      rfl
    rw [hinner]
    dsimp [p] at hp ⊢
    field_simp [hp]
  calc
    charFun harperFejerMeasure t =
        ∫ x, harperFejerDensityNNReal x •
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) := by
      rw [charFun_apply_real, harperFejerMeasure,
        integral_withDensity_eq_integral_smul
          continuous_harperFejerDensityNNReal.measurable]
    _ = ∫ x : ℝ, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
          (harperFejerDensity x : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [NNReal.smul_def, coe_harperFejerDensityNNReal,
        Complex.real_smul]
      ring
    _ = FourierTransform.fourier
          (fun x : ℝ ↦ (harperFejerDensity x : ℂ)) (-(t / p)) := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards with x
      rw [hphase]
      simp only [smul_eq_mul]
      push_cast
      rfl
    _ = harperFejerFourierProfile (-(t / p)) :=
      harperFejerDensity_fourier_eq_profile _
    _ = (harperFejerTriangle t : ℂ) := by
      unfold harperFejerFourierProfile
      have harg : 2 * Real.pi * (-(t / p)) = -t := by
        dsimp [p]
        field_simp
      rw [harg, harperFejerTriangle_neg]

private theorem intervalIntegral_one_sub_harperFejerTriangle
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ t in (-s)..s, (1 : ℂ) - (harperFejerTriangle t : ℂ)) =
      ((s ^ 2 : ℝ) : ℂ) := by
  let g : ℝ → ℂ := fun t ↦ (1 : ℂ) - (harperFejerTriangle t : ℂ)
  have hgcont : Continuous g := by
    dsimp [g]
    exact continuous_const.sub
      (Complex.continuous_ofReal.comp continuous_harperFejerTriangle)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hgcont.intervalIntegrable (-s) 0)
    (hgcont.intervalIntegrable 0 s)]
  have hleft :
      (∫ t in (-s)..0, g t) =
        ∫ t in (-s)..0, (0 : ℂ) + (-1 : ℂ) * (t : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc (-s) 0 := by
      simpa [uIcc_of_le (neg_nonpos.mpr hs0)] using! ht
    have hnonneg : 0 ≤ 1 + t := by linarith [htI.1]
    dsimp [g, harperFejerTriangle]
    rw [abs_of_nonpos htI.2, max_eq_left (by linarith)]
    push_cast
    ring
  have hright :
      (∫ t in 0..s, g t) =
        ∫ t in 0..s, (0 : ℂ) + (1 : ℂ) * (t : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc 0 s := by
      simpa [uIcc_of_le hs0] using! ht
    have hnonneg : 0 ≤ 1 - t := by linarith [htI.2]
    dsimp [g, harperFejerTriangle]
    rw [abs_of_nonneg htI.1, max_eq_left hnonneg]
    push_cast
    ring
  rw [hleft, hright, intervalIntegral_affine, intervalIntegral_affine]
  push_cast
  ring

/-- Explicit tail bound for the unscaled Fejér law. -/
theorem harperFejerMeasure_tail_le_two_div
    {r : ℝ} (hr : 2 ≤ r) :
    harperFejerMeasure.real {x | r < |x|} ≤ 2 / r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hs0 : 0 ≤ 2 * r⁻¹ := by positivity
  have hs1 : 2 * r⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one₀ hr0]
    exact hr
  have htail := measureReal_abs_gt_le_integral_charFun
    (μ := harperFejerMeasure) hr0
  rw [show (-2 * r⁻¹ : ℝ) = -(2 * r⁻¹) by ring] at htail
  simp_rw [charFun_harperFejerMeasure] at htail
  rw [intervalIntegral_one_sub_harperFejerTriangle hs0 hs1] at htail
  norm_cast at htail
  have hrne : r ≠ 0 := hr0.ne'
  have habs : |(2 * r⁻¹) ^ 2| = (2 * r⁻¹) ^ 2 :=
    abs_of_nonneg (sq_nonneg _)
  rw [Real.norm_eq_abs, habs] at htail
  calc
    harperFejerMeasure.real {x | r < |x|} ≤
        2⁻¹ * r * (2 * r⁻¹) ^ 2 := htail
    _ = 2 / r := by field_simp

/-- The Fejér law scaled to Fourier bandwidth `T`. -/
noncomputable def harperFejerMeasureScaled (T : ℝ) : Measure ℝ :=
  harperFejerMeasure.map (T⁻¹ * ·)

noncomputable instance harperFejerMeasureScaled_isProbabilityMeasure (T : ℝ) :
    IsProbabilityMeasure (harperFejerMeasureScaled T) := by
  unfold harperFejerMeasureScaled
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem charFun_harperFejerMeasureScaled (T t : ℝ) :
    charFun (harperFejerMeasureScaled T) t =
      (harperFejerTriangle (T⁻¹ * t) : ℂ) := by
  rw [harperFejerMeasureScaled, charFun_map_mul,
    charFun_harperFejerMeasure]

/-- At spatial scale `8 / T`, the bandwidth-`T` Fejér law loses at most
one quarter of its mass. -/
theorem harperFejerMeasureScaled_tail_le_quarter
    {T : ℝ} (hT : 0 < T) :
    (harperFejerMeasureScaled T).real {x | 8 / T < |x|} ≤ 1 / 4 := by
  have hset : (T⁻¹ * ·) ⁻¹' {x : ℝ | 8 / T < |x|} =
      {x : ℝ | 8 < |x|} := by
    ext x
    simp only [preimage_setOf_eq, mem_setOf_eq]
    rw [show T⁻¹ * x = x / T by field_simp, abs_div, abs_of_pos hT,
      div_lt_div_iff_of_pos_right hT]
  rw [harperFejerMeasureScaled,
    map_measureReal_apply (by fun_prop)
      (measurableSet_lt measurable_const measurable_abs), hset]
  calc
    harperFejerMeasure.real {x : ℝ | 8 < |x|} ≤ 2 / 8 :=
      harperFejerMeasure_tail_le_two_div (r := (8 : ℝ)) (by norm_num)
    _ = 1 / 4 := by norm_num

end Problem520
end Erdos
