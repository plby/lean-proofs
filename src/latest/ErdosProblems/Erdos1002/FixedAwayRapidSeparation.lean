import ErdosProblems.Erdos1002.FixedAwaySamplingBV

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Rapid separated envelopes for the fixed-away multiplier

This file upgrades the quadratic summability envelope to arbitrary fixed
order.  Constants are explicit in the derivative order, so later uses may
specialize the order before any asymptotic parameters vary.
-/

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate Real Topology

namespace Erdos1002

noncomputable section

def fixedAwayPVRapidDecayConstant (t δ : ℝ) (J : ℕ) : ℝ :=
  (2 : ℝ) ^ J *
    (fixedAwayPVLocalBound t +
      fixedAwayDerivativeBound t δ (J + 1) /
        ((J : ℝ) * (2 * Real.pi) ^ (J + 1)))

theorem fixedAwayPVRapidDecayConstant_nonneg
    (t δ : ℝ) {J : ℕ} (hJ : 0 < J) :
    0 ≤ fixedAwayPVRapidDecayConstant t δ J := by
  unfold fixedAwayPVRapidDecayConstant
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hden : 0 < (J : ℝ) * (2 * Real.pi) ^ (J + 1) := by positivity
  exact mul_nonneg (by positivity) (add_nonneg
    (fixedAwayPVLocalBound_nonneg t)
    (div_nonneg (fixedAwayDerivativeBound_nonneg t δ (J + 1)) hden.le))

theorem norm_fixedAwayPVTransform_smooth_le_rapidDecay
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    {J : ℕ} (hJ : 0 < J) (y : ℝ) :
    ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t y‖ ≤
      fixedAwayPVRapidDecayConstant t δ J * (1 + |y|)⁻¹ ^ J := by
  let D : ℝ := ‖fixedAwayPVTransform
    (fixedAwaySmoothCorrection t δ) t y‖
  let B : ℝ := fixedAwayPVLocalBound t
  let C : ℝ := fixedAwayDerivativeBound t δ (J + 1) /
    ((J : ℝ) * (2 * Real.pi) ^ (J + 1))
  have hD : 0 ≤ D := norm_nonneg _
  have hB : 0 ≤ B := fixedAwayPVLocalBound_nonneg t
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hdenC : 0 < (J : ℝ) * (2 * Real.pi) ^ (J + 1) := by positivity
    exact div_nonneg
      (fixedAwayDerivativeBound_nonneg t δ (J + 1)) hdenC.le
  change D ≤ 2 ^ J * (B + C) * (1 + |y|)⁻¹ ^ J
  have hden : 0 < 1 + |y| := by positivity
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hden J)]
  by_cases hySmall : |y| ≤ 1
  · have hlocal : D ≤ B := by
      simpa only [D, B] using!
        norm_fixedAwayPVTransform_smooth_le_local hδ hδt.le hySmall
    have hpow : (1 + |y|) ^ J ≤ (2 : ℝ) ^ J := by
      gcongr
      linarith [abs_nonneg y]
    have hpowNonneg : 0 ≤ (1 + |y|) ^ J := by positivity
    nlinarith [mul_le_mul hlocal hpow hpowNonneg hB]
  · have hyLarge : 1 < |y| := lt_of_not_ge hySmall
    have hy0 : y ≠ 0 := abs_pos.mp (zero_lt_one.trans hyLarge)
    have hn : 1 < J + 1 := by omega
    have htail := norm_fixedAwayPVTransform_smooth_le_rpow_tail_abs
      hδ hδt (J + 1) hn hy0
    have hexp : -((J + 1 : ℕ) : ℝ) + 1 = -(J : ℝ) := by
      push_cast
      ring
    have hrpow : |y| ^ (-(J : ℝ)) = (|y| ^ J)⁻¹ := by
      have hneg := Real.rpow_neg (abs_nonneg y) (J : ℝ)
      rw [Real.rpow_natCast] at hneg
      exact hneg
    have htailC : D ≤ C / |y| ^ J := by
      dsimp only [D, C]
      calc
        ‖fixedAwayPVTransform
            (fixedAwaySmoothCorrection t δ) t y‖ ≤
          (fixedAwayDerivativeBound t δ (J + 1) /
            (2 * Real.pi) ^ (J + 1)) *
            (-|y| ^ (-((J + 1 : ℕ) : ℝ) + 1) /
              (-((J + 1 : ℕ) : ℝ) + 1)) := htail
        _ = (fixedAwayDerivativeBound t δ (J + 1) /
              ((J : ℝ) * (2 * Real.pi) ^ (J + 1))) /
              |y| ^ J := by
          rw [hexp, hrpow]
          field_simp [hJR.ne', hy0, Real.pi_ne_zero]
    have hyPowPos : 0 < |y| ^ J := pow_pos (abs_pos.mpr hy0) J
    have htailMul : D * |y| ^ J ≤ C :=
      (le_div_iff₀ hyPowPos).mp htailC
    have hbase : 1 + |y| ≤ 2 * |y| := by linarith
    have hpow : (1 + |y|) ^ J ≤ (2 * |y|) ^ J := by gcongr
    have hscaled : D * (1 + |y|) ^ J ≤ 2 ^ J * C := by
      calc
        D * (1 + |y|) ^ J ≤ D * (2 * |y|) ^ J :=
          mul_le_mul_of_nonneg_left hpow hD
        _ = 2 ^ J * (D * |y| ^ J) := by rw [mul_pow]; ring
        _ ≤ 2 ^ J * C := mul_le_mul_of_nonneg_left htailMul (by positivity)
    nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ) ^ J by positivity) hB]

def fixedAwayDerivativeRapidDecayConstant (t δ : ℝ) (J : ℕ) : ℝ :=
  (2 : ℝ) ^ J *
    (fixedAwayDerivativeBound0 t δ +
      fixedAwayDerivativeBound t δ J / (2 * Real.pi) ^ J)

theorem fixedAwayDerivativeRapidDecayConstant_nonneg
    (t δ : ℝ) (J : ℕ) :
    0 ≤ fixedAwayDerivativeRapidDecayConstant t δ J := by
  unfold fixedAwayDerivativeRapidDecayConstant
  exact mul_nonneg (by positivity) (add_nonneg
    (fixedAwayDerivativeBound0_nonneg t δ)
    (div_nonneg (fixedAwayDerivativeBound_nonneg t δ J) (by positivity)))

theorem norm_deriv_fixedAwayPVTransform_smooth_le_rapidDecay
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (J : ℕ) {y : ℝ} (hy0 : y ≠ 0) :
    ‖deriv (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t) y‖ ≤
      fixedAwayDerivativeRapidDecayConstant t δ J *
        (1 + |y|)⁻¹ ^ J := by
  let D : ℝ := ‖deriv
    (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t) y‖
  let B : ℝ := fixedAwayDerivativeBound0 t δ
  let C : ℝ := fixedAwayDerivativeBound t δ J / (2 * Real.pi) ^ J
  have hD : 0 ≤ D := norm_nonneg _
  have hB : 0 ≤ B := fixedAwayDerivativeBound0_nonneg t δ
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact div_nonneg (fixedAwayDerivativeBound_nonneg t δ J) (by positivity)
  change D ≤ 2 ^ J * (B + C) * (1 + |y|)⁻¹ ^ J
  have hden : 0 < 1 + |y| := by positivity
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hden J)]
  by_cases hySmall : |y| ≤ 1
  · have hpoly := fixedAwayPVTransform_smooth_deriv_polynomial
      hδ hδt 0 y hy0
    have hlocal : D ≤ B := by
      simpa only [pow_zero, one_mul, D, B,
        fixedAwayDerivativeBound0] using! hpoly
    have hpow : (1 + |y|) ^ J ≤ (2 : ℝ) ^ J := by
      gcongr
      linarith [abs_nonneg y]
    have hpowNonneg : 0 ≤ (1 + |y|) ^ J := by positivity
    nlinarith [mul_le_mul hlocal hpow hpowNonneg hB]
  · have hyLarge : 1 < |y| := lt_of_not_ge hySmall
    have hpoly := fixedAwayPVTransform_smooth_deriv_polynomial
      hδ hδt J y hy0
    have hfreq : 0 < (2 * Real.pi * |y|) ^ J := by positivity
    have htail : D ≤ C / |y| ^ J := by
      have hfirst : D ≤ fixedAwayDerivativeBound t δ J /
          (2 * Real.pi * |y|) ^ J := by
        apply (le_div_iff₀ hfreq).2
        simpa only [D, fixedAwayDerivativeBound, mul_comm] using! hpoly
      dsimp only [C]
      calc
        D ≤ fixedAwayDerivativeBound t δ J /
            (2 * Real.pi * |y|) ^ J := hfirst
        _ = (fixedAwayDerivativeBound t δ J /
            (2 * Real.pi) ^ J) / |y| ^ J := by
          rw [mul_pow]
          field_simp [Real.pi_ne_zero, hy0]
    have hyPowPos : 0 < |y| ^ J := pow_pos (abs_pos.mpr hy0) J
    have htailMul : D * |y| ^ J ≤ C :=
      (le_div_iff₀ hyPowPos).mp htail
    have hbase : 1 + |y| ≤ 2 * |y| := by linarith
    have hpow : (1 + |y|) ^ J ≤ (2 * |y|) ^ J := by gcongr
    have hscaled : D * (1 + |y|) ^ J ≤ 2 ^ J * C := by
      calc
        D * (1 + |y|) ^ J ≤ D * (2 * |y|) ^ J :=
          mul_le_mul_of_nonneg_left hpow hD
        _ = 2 ^ J * (D * |y| ^ J) := by rw [mul_pow]; ring
        _ ≤ 2 ^ J * C := mul_le_mul_of_nonneg_left htailMul (by positivity)
    nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ) ^ J by positivity) hB]

def fixedAwayRapidEnvelope (J : ℕ) (x : ℝ) : ℝ :=
  (1 + |x|)⁻¹ ^ J

theorem fixedAwayRapidEnvelope_nonneg (J : ℕ) (x : ℝ) :
    0 ≤ fixedAwayRapidEnvelope J x := by
  unfold fixedAwayRapidEnvelope
  positivity

theorem fixedAwayRapidEnvelope_le_one (J : ℕ) (x : ℝ) :
    fixedAwayRapidEnvelope J x ≤ 1 := by
  unfold fixedAwayRapidEnvelope
  have h := inv_le_one_of_one_le₀
    (le_add_of_nonneg_right (abs_nonneg x))
  have hnonneg : 0 ≤ (1 + |x|)⁻¹ := by positivity
  exact pow_le_one₀ hnonneg h

theorem fixedAwayRapidEnvelope_add_two (J : ℕ) (x : ℝ) :
    fixedAwayRapidEnvelope (J + 2) x =
      fixedAwayRapidEnvelope J x * fixedAwayRapidEnvelope 2 x := by
  unfold fixedAwayRapidEnvelope
  rw [pow_add]

theorem fixedAwayRapidEnvelope_le_eight_separated_of_far
    (J : ℕ) {x d : ℝ} (hfar : |d| / 8 ≤ |x|) :
    fixedAwayRapidEnvelope J x ≤
      8 ^ J * fixedAwayRapidEnvelope J d := by
  have hsmallDen : (1 + |d|) / 8 ≤ 1 + |x| := by
    nlinarith [abs_nonneg d, abs_nonneg x]
  have hsmallPos : 0 < (1 + |d|) / 8 := by positivity
  have hlargePos : 0 < 1 + |x| := by positivity
  have hinv : (1 + |x|)⁻¹ ≤ ((1 + |d|) / 8)⁻¹ :=
    (inv_le_inv₀ hlargePos hsmallPos).2 hsmallDen
  have hinvNonneg : 0 ≤ (1 + |x|)⁻¹ := by positivity
  have hpow := pow_le_pow_left₀ hinvNonneg hinv J
  unfold fixedAwayRapidEnvelope
  calc
    (1 + |x|)⁻¹ ^ J ≤ ((1 + |d|) / 8)⁻¹ ^ J := hpow
    _ = 8 ^ J * (1 + |d|)⁻¹ ^ J := by
      rw [inv_div, div_pow, div_eq_mul_inv, inv_pow]

theorem fixedAwayRapidEnvelope_product_separated
    (J : ℕ) {lam d x : ℝ} (hlam : 0 < lam) (hlam4 : lam ≤ 4) :
    fixedAwayRapidEnvelope (J + 2) x *
        fixedAwayRapidEnvelope (J + 2) (lam * x - d) ≤
      8 ^ J * fixedAwayRapidEnvelope J d *
        (fixedAwayRapidEnvelope 2 x +
          fixedAwayRapidEnvelope 2 (lam * x - d)) := by
  by_cases hfar : |d| / 8 ≤ |x|
  · let y : ℝ := lam * x - d
    have hJ := fixedAwayRapidEnvelope_le_eight_separated_of_far J hfar
    have hone := fixedAwayRapidEnvelope_le_one (J + 2) y
    have hnonneg := fixedAwayRapidEnvelope_nonneg 2 x
    calc
      fixedAwayRapidEnvelope (J + 2) x *
          fixedAwayRapidEnvelope (J + 2) (lam * x - d) ≤
        fixedAwayRapidEnvelope (J + 2) x := by
          simpa only [y] using! mul_le_of_le_one_right
            (fixedAwayRapidEnvelope_nonneg (J + 2) x) hone
      _ = fixedAwayRapidEnvelope J x * fixedAwayRapidEnvelope 2 x :=
        fixedAwayRapidEnvelope_add_two J x
      _ ≤ (8 ^ J * fixedAwayRapidEnvelope J d) *
          fixedAwayRapidEnvelope 2 x :=
        mul_le_mul_of_nonneg_right hJ hnonneg
      _ ≤ 8 ^ J * fixedAwayRapidEnvelope J d *
          (fixedAwayRapidEnvelope 2 x +
            fixedAwayRapidEnvelope 2 (lam * x - d)) := by
        apply mul_le_mul_of_nonneg_left
        · exact le_add_of_nonneg_right
            (fixedAwayRapidEnvelope_nonneg 2 (lam * x - d))
        · exact mul_nonneg (by positivity)
            (fixedAwayRapidEnvelope_nonneg J d)
  · have hxsmall : |x| < |d| / 8 := lt_of_not_ge hfar
    have hlamabs : |lam * x| = lam * |x| := by
      rw [abs_mul, abs_of_pos hlam]
    have hdTriangle : |d| ≤ |lam * x - d| + |lam * x| := by
      calc
        |d| = |(d - lam * x) + lam * x| := by ring_nf
        _ ≤ |d - lam * x| + |lam * x| := abs_add_le _ _
        _ = |lam * x - d| + |lam * x| := by rw [abs_sub_comm]
    have hother : |d| / 2 ≤ |lam * x - d| := by
      rw [hlamabs] at hdTriangle
      have : lam * |x| < |d| / 2 := by
        calc
          lam * |x| ≤ 4 * |x| :=
            mul_le_mul_of_nonneg_right hlam4 (abs_nonneg x)
          _ < |d| / 2 := by linarith
      linarith
    have hJtwo := fixedAwayRapidEnvelope_le_eight_separated_of_far
      J (show |d| / 8 ≤ |lam * x - d| by
        nlinarith [abs_nonneg d])
    have hone := fixedAwayRapidEnvelope_le_one (J + 2) x
    have hnonneg := fixedAwayRapidEnvelope_nonneg 2 (lam * x - d)
    calc
      fixedAwayRapidEnvelope (J + 2) x *
          fixedAwayRapidEnvelope (J + 2) (lam * x - d) ≤
        fixedAwayRapidEnvelope (J + 2) (lam * x - d) :=
          mul_le_of_le_one_left
            (fixedAwayRapidEnvelope_nonneg (J + 2) (lam * x - d)) hone
      _ = fixedAwayRapidEnvelope J (lam * x - d) *
          fixedAwayRapidEnvelope 2 (lam * x - d) :=
        fixedAwayRapidEnvelope_add_two J (lam * x - d)
      _ ≤ (8 ^ J * fixedAwayRapidEnvelope J d) *
          fixedAwayRapidEnvelope 2 (lam * x - d) :=
        mul_le_mul_of_nonneg_right hJtwo hnonneg
      _ ≤ 8 ^ J * fixedAwayRapidEnvelope J d *
          (fixedAwayRapidEnvelope 2 x +
            fixedAwayRapidEnvelope 2 (lam * x - d)) := by
        apply mul_le_mul_of_nonneg_left
        · exact le_add_of_nonneg_left
            (fixedAwayRapidEnvelope_nonneg 2 x)
        · exact mul_nonneg (by positivity)
            (fixedAwayRapidEnvelope_nonneg J d)

theorem continuous_fixedAwayRapidEnvelope (J : ℕ) :
    Continuous (fixedAwayRapidEnvelope J) := by
  unfold fixedAwayRapidEnvelope
  exact ((continuous_const.add continuous_abs).inv₀
    (fun x ↦ by change (1 : ℝ) + |x| ≠ 0; positivity)).pow J

theorem integrable_fixedAwayRapidEnvelope_two :
    Integrable (fixedAwayRapidEnvelope 2) := by
  have hmajor : Integrable (fun x : ℝ ↦ (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq
  have hmeas : AEStronglyMeasurable (fixedAwayRapidEnvelope 2) := by
    exact (continuous_fixedAwayRapidEnvelope 2).aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards with x
  have hden : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by
    nlinarith [sq_abs x, abs_nonneg x]
  unfold fixedAwayRapidEnvelope
  rw [inv_pow]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (inv_le_inv₀ (by positivity) (by positivity)).2 hden

def fixedAwayRapidEnvelopeTwoMass : ℝ :=
  ∫ x : ℝ, fixedAwayRapidEnvelope 2 x

theorem fixedAwayRapidEnvelopeTwoMass_nonneg :
    0 ≤ fixedAwayRapidEnvelopeTwoMass := by
  unfold fixedAwayRapidEnvelopeTwoMass
  exact integral_nonneg fun x ↦ fixedAwayRapidEnvelope_nonneg 2 x

theorem integrable_fixedAwayRapidEnvelope_two_affine
    {lam d : ℝ} (hlam : lam ≠ 0) :
    Integrable fun x : ℝ ↦ fixedAwayRapidEnvelope 2 (lam * x - d) := by
  have hshift := integrable_fixedAwayRapidEnvelope_two.comp_sub_right d
  have hscale := hshift.comp_mul_left' hlam
  simpa only [Function.comp_apply] using! hscale

theorem integral_fixedAwayRapidEnvelope_two_affine
    (lam d : ℝ) :
    (∫ x : ℝ, fixedAwayRapidEnvelope 2 (lam * x - d)) =
      |lam⁻¹| * fixedAwayRapidEnvelopeTwoMass := by
  let g : ℝ → ℝ := fun z ↦ fixedAwayRapidEnvelope 2 (z - d)
  have hscale := Measure.integral_comp_mul_left g lam
  have hshift : (∫ z : ℝ, g z) = fixedAwayRapidEnvelopeTwoMass := by
    have htranslation := integral_add_right_eq_self (μ := volume)
      (fixedAwayRapidEnvelope 2) (-d)
    simpa only [g, sub_eq_add_neg, fixedAwayRapidEnvelopeTwoMass] using!
      htranslation
  simpa only [g, hshift] using! hscale

theorem integral_fixedAwayRapidEnvelope_product_separated_le
    (J : ℕ) {lam d : ℝ} (hlam : 0 < lam)
    (hlamQuarter : (1 : ℝ) / 4 ≤ lam) (hlam4 : lam ≤ 4) :
    (∫ x : ℝ,
      fixedAwayRapidEnvelope (J + 2) x *
        fixedAwayRapidEnvelope (J + 2) (lam * x - d)) ≤
      5 * 8 ^ J * fixedAwayRapidEnvelope J d *
        fixedAwayRapidEnvelopeTwoMass := by
  let K : ℝ := 8 ^ J * fixedAwayRapidEnvelope J d
  let F : ℝ → ℝ := fun x ↦
    fixedAwayRapidEnvelope (J + 2) x *
      fixedAwayRapidEnvelope (J + 2) (lam * x - d)
  let G : ℝ → ℝ := fun x ↦ K *
    (fixedAwayRapidEnvelope 2 x +
      fixedAwayRapidEnvelope 2 (lam * x - d))
  have hlam0 : lam ≠ 0 := hlam.ne'
  have hGint : Integrable G := by
    exact (integrable_fixedAwayRapidEnvelope_two.add
      (integrable_fixedAwayRapidEnvelope_two_affine hlam0)).const_mul K
  have hFmeas : AEStronglyMeasurable F := by
    apply Continuous.aestronglyMeasurable
    dsimp only [F]
    exact (continuous_fixedAwayRapidEnvelope (J + 2)).mul
      ((continuous_fixedAwayRapidEnvelope (J + 2)).comp
        ((continuous_const.mul continuous_id).sub continuous_const))
  have hFG : ∀ x, F x ≤ G x := by
    intro x
    exact fixedAwayRapidEnvelope_product_separated J hlam hlam4
  have hFint : Integrable F := by
    apply hGint.mono' hFmeas
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp only [F]
      exact mul_nonneg
        (fixedAwayRapidEnvelope_nonneg (J + 2) x)
        (fixedAwayRapidEnvelope_nonneg (J + 2) (lam * x - d)))]
    exact hFG x
  have hintegral : (∫ x : ℝ, F x) ≤ ∫ x : ℝ, G x :=
    integral_mono hFint hGint hFG
  have hinv : |lam⁻¹| ≤ 4 := by
    rw [abs_inv, abs_of_pos hlam]
    exact (inv_le_comm₀ hlam (by norm_num : (0 : ℝ) < 4)).2 (by
      norm_num
      exact hlamQuarter)
  have hmass := fixedAwayRapidEnvelopeTwoMass_nonneg
  calc
    (∫ x : ℝ,
        fixedAwayRapidEnvelope (J + 2) x *
          fixedAwayRapidEnvelope (J + 2) (lam * x - d)) =
        ∫ x : ℝ, F x := rfl
    _ ≤ ∫ x : ℝ, G x := hintegral
    _ = K * (fixedAwayRapidEnvelopeTwoMass +
          |lam⁻¹| * fixedAwayRapidEnvelopeTwoMass) := by
      dsimp only [G]
      rw [integral_const_mul, integral_add
          integrable_fixedAwayRapidEnvelope_two
          (integrable_fixedAwayRapidEnvelope_two_affine hlam0),
        integral_fixedAwayRapidEnvelope_two_affine lam d]
      rfl
    _ ≤ K * (fixedAwayRapidEnvelopeTwoMass +
          4 * fixedAwayRapidEnvelopeTwoMass) := by
      apply mul_le_mul_of_nonneg_left
      · gcongr
      · dsimp only [K]
        exact mul_nonneg (by positivity)
          (fixedAwayRapidEnvelope_nonneg J d)
    _ = 5 * 8 ^ J * fixedAwayRapidEnvelope J d *
        fixedAwayRapidEnvelopeTwoMass := by
      dsimp only [K]
      ring

/-- Scale-and-translate form of the two-envelope convolution.  The factor
`s⁻¹` is deliberately kept on the left: it is exactly the chain-rule
factor occurring in the first term of the differentiated Hermitian
product. -/
theorem inv_mul_integral_fixedAwayRapidEnvelope_scaled_product_le
    (J : ℕ) {s a s' a' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (hss' : s ≤ 4 * s') (hs's : s' ≤ 4 * s) :
    s⁻¹ * (∫ x : ℝ,
      fixedAwayRapidEnvelope (J + 2) ((x - a) / s) *
        fixedAwayRapidEnvelope (J + 2) ((x - a') / s')) ≤
      5 * 8 ^ J *
        fixedAwayRapidEnvelope J ((a' - a) / s') *
        fixedAwayRapidEnvelopeTwoMass := by
  let F : ℝ → ℝ := fun x ↦
    fixedAwayRapidEnvelope (J + 2) ((x - a) / s) *
      fixedAwayRapidEnvelope (J + 2) ((x - a') / s')
  let lam : ℝ := s / s'
  let d : ℝ := (a' - a) / s'
  have hlam : 0 < lam := div_pos hs hs'
  have hlamQuarter : (1 : ℝ) / 4 ≤ lam := by
    dsimp only [lam]
    rw [le_div_iff₀ hs']
    nlinarith
  have hlam4 : lam ≤ 4 := by
    dsimp only [lam]
    rw [div_le_iff₀ hs']
    exact hss'
  have htranslation := integral_add_right_eq_self (μ := volume) F a
  have hscale := Measure.integral_comp_mul_left (fun z ↦ F (z + a)) s
  have hchange :
      s⁻¹ * (∫ x : ℝ, F x) =
        ∫ x : ℝ,
          fixedAwayRapidEnvelope (J + 2) x *
            fixedAwayRapidEnvelope (J + 2) (lam * x - d) := by
    calc
      s⁻¹ * (∫ x : ℝ, F x) =
          |s⁻¹| * (∫ z : ℝ, F (z + a)) := by
            rw [abs_of_pos (inv_pos.mpr hs), htranslation]
      _ = ∫ x : ℝ, F (s * x + a) := hscale.symm
      _ = ∫ x : ℝ,
          fixedAwayRapidEnvelope (J + 2) x *
            fixedAwayRapidEnvelope (J + 2) (lam * x - d) := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [F, lam, d]
        congr 2 <;> field_simp [hs.ne', hs'.ne'] <;> ring
  change s⁻¹ * (∫ x : ℝ, F x) ≤ _
  rw [hchange]
  exact integral_fixedAwayRapidEnvelope_product_separated_le
    J hlam hlamQuarter hlam4

/-- Pointwise rapid separation of two carriers at comparable positive
scales.  This is the sup-norm part of the scaled multiplier estimate; the
conjugate in the second factor is retained throughout. -/
theorem norm_fixedAwayScaledHermitianProduct_le_rapidSeparatedEnvelope
    {t δ s a s' a' : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (hs : 0 < s) (hs' : 0 < s')
    (hss' : s ≤ 4 * s')
    (J : ℕ) (x : ℝ) :
    ‖fixedAwayScaledHermitianProduct t δ s a s' a' x‖ ≤
      fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2 * 8 ^ J *
        fixedAwayRapidEnvelope J ((a' - a) / s') *
        (fixedAwayRapidEnvelope 2 ((x - a) / s) +
          fixedAwayRapidEnvelope 2 ((x - a') / s')) := by
  let C : ℝ := fixedAwayPVRapidDecayConstant t δ (J + 2)
  let u : ℝ := (x - a) / s
  let v : ℝ := (x - a') / s'
  let lam : ℝ := s / s'
  let d : ℝ := (a' - a) / s'
  have hM : 0 < J + 2 := by omega
  have hC : 0 ≤ C :=
    fixedAwayPVRapidDecayConstant_nonneg t δ hM
  have hu := norm_fixedAwayPVTransform_smooth_le_rapidDecay
    hδ hδt hM u
  have hv := norm_fixedAwayPVTransform_smooth_le_rapidDecay
    hδ hδt hM v
  have hlam : 0 < lam := div_pos hs hs'
  have hlam4 : lam ≤ 4 := by
    dsimp only [lam]
    rw [div_le_iff₀ hs']
    exact hss'
  have huv : v = lam * u - d := by
    dsimp only [u, v, lam, d]
    field_simp [hs.ne', hs'.ne']
    ring
  have henv := fixedAwayRapidEnvelope_product_separated
    J (x := u) (d := d) hlam hlam4
  rw [← huv] at henv
  unfold fixedAwayScaledHermitianProduct fixedAwayScaledPV
  rw [norm_mul, Complex.norm_conj]
  change ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t u‖ *
      ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t v‖ ≤ _
  change _ ≤ C ^ 2 * 8 ^ J * fixedAwayRapidEnvelope J d *
    (fixedAwayRapidEnvelope 2 u + fixedAwayRapidEnvelope 2 v)
  calc
    ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t u‖ *
        ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t v‖ ≤
      (C * fixedAwayRapidEnvelope (J + 2) u) *
        (C * fixedAwayRapidEnvelope (J + 2) v) := by
          exact mul_le_mul hu hv (norm_nonneg _)
            (mul_nonneg hC
              (fixedAwayRapidEnvelope_nonneg (J + 2) u))
    _ = C ^ 2 *
        (fixedAwayRapidEnvelope (J + 2) u *
          fixedAwayRapidEnvelope (J + 2) v) := by ring
    _ ≤ C ^ 2 * (8 ^ J * fixedAwayRapidEnvelope J d *
          (fixedAwayRapidEnvelope 2 u + fixedAwayRapidEnvelope 2 v)) :=
      mul_le_mul_of_nonneg_left henv (sq_nonneg C)
    _ = C ^ 2 * 8 ^ J * fixedAwayRapidEnvelope J d *
        (fixedAwayRapidEnvelope 2 u + fixedAwayRapidEnvelope 2 v) := by ring

theorem norm_fixedAwayScaledHermitianProduct_le_rapidSeparation
    {t δ s a s' a' : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (hs : 0 < s) (hs' : 0 < s')
    (hss' : s ≤ 4 * s')
    (J : ℕ) (x : ℝ) :
    ‖fixedAwayScaledHermitianProduct t δ s a s' a' x‖ ≤
      2 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2 * 8 ^ J *
        fixedAwayRapidEnvelope J ((a' - a) / s') := by
  have hraw := norm_fixedAwayScaledHermitianProduct_le_rapidSeparatedEnvelope
    (a := a) (a' := a') hδ hδt hs hs' hss' J x
  have hleft := fixedAwayRapidEnvelope_le_one 2 ((x - a) / s)
  have hright := fixedAwayRapidEnvelope_le_one 2 ((x - a') / s')
  have hconstant : 0 ≤
      fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2 * 8 ^ J *
        fixedAwayRapidEnvelope J ((a' - a) / s') := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (by positivity))
      (fixedAwayRapidEnvelope_nonneg J ((a' - a) / s'))
  exact hraw.trans (by nlinarith)

/-- Exact carrier-charge formula plus rapid decay of the nonvanishing
factor at each distinct carrier. -/
theorem fixedAwayHermitianCarrierJumpCost_le_rapid_of_ne
    {t δ s a s' a' : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (haa' : a ≠ a') {J : ℕ} (hJ : 0 < J) :
    fixedAwayHermitianCarrierJumpCost t δ s a s' a' ≤
      2 * Real.pi * fixedAwayPVRapidDecayConstant t δ J *
        (fixedAwayRapidEnvelope J ((a - a') / s') +
          fixedAwayRapidEnvelope J ((a' - a) / s)) := by
  rw [fixedAwayHermitianCarrierJumpCost, if_neg haa']
  have hfirst := norm_fixedAwayPVTransform_smooth_le_rapidDecay
    hδ hδt hJ ((a - a') / s')
  have hsecond := norm_fixedAwayPVTransform_smooth_le_rapidDecay
    hδ hδt hJ ((a' - a) / s)
  change _ ≤ fixedAwayPVRapidDecayConstant t δ J *
      fixedAwayRapidEnvelope J ((a - a') / s') at hfirst
  change _ ≤ fixedAwayPVRapidDecayConstant t δ J *
      fixedAwayRapidEnvelope J ((a' - a) / s) at hsecond
  unfold fixedAwayScaledPV
  calc
    2 * Real.pi *
        (‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
            ((a - a') / s')‖ +
          ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
            ((a' - a) / s)‖) ≤
      2 * Real.pi *
        (fixedAwayPVRapidDecayConstant t δ J *
            fixedAwayRapidEnvelope J ((a - a') / s') +
          fixedAwayPVRapidDecayConstant t δ J *
            fixedAwayRapidEnvelope J ((a' - a) / s)) := by
        gcongr
    _ = 2 * Real.pi * fixedAwayPVRapidDecayConstant t δ J *
        (fixedAwayRapidEnvelope J ((a - a') / s') +
          fixedAwayRapidEnvelope J ((a' - a) / s)) := by ring

/-- Rapid pointwise envelope for the ordinary derivative away from the two
carrier points.  The excluded points are exactly the regulated jumps counted
separately by `fixedAwayHermitianCarrierJumpCost`. -/
theorem norm_deriv_fixedAwayScaledHermitianProduct_le_rapidEnvelope
    {t δ s a s' a' x : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (hs : 0 < s) (hs' : 0 < s') (hxa : x ≠ a) (hxa' : x ≠ a')
    (J : ℕ) :
    ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖ ≤
      s⁻¹ *
          (fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
            fixedAwayRapidEnvelope (J + 2) ((x - a) / s)) *
          (fixedAwayPVRapidDecayConstant t δ (J + 2) *
            fixedAwayRapidEnvelope (J + 2) ((x - a') / s')) +
        (fixedAwayPVRapidDecayConstant t δ (J + 2) *
            fixedAwayRapidEnvelope (J + 2) ((x - a) / s)) *
          (s'⁻¹ *
            (fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
              fixedAwayRapidEnvelope (J + 2) ((x - a') / s'))) := by
  let R : ℝ → ℂ :=
    fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
  let u : ℝ := (x - a) / s
  let v : ℝ := (x - a') / s'
  let D : ℝ := fixedAwayDerivativeRapidDecayConstant t δ (J + 2)
  let C : ℝ := fixedAwayPVRapidDecayConstant t δ (J + 2)
  have hM : 0 < J + 2 := by omega
  have hu0 : u ≠ 0 := div_ne_zero (sub_ne_zero.mpr hxa) hs.ne'
  have hv0 : v ≠ 0 := div_ne_zero (sub_ne_zero.mpr hxa') hs'.ne'
  have hDu := norm_deriv_fixedAwayPVTransform_smooth_le_rapidDecay
    hδ hδt.le (J + 2) hu0
  have hDv := norm_deriv_fixedAwayPVTransform_smooth_le_rapidDecay
    hδ hδt.le (J + 2) hv0
  have hRu := norm_fixedAwayPVTransform_smooth_le_rapidDecay
    hδ hδt hM u
  have hRv := norm_fixedAwayPVTransform_smooth_le_rapidDecay
    hδ hδt hM v
  change ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖ ≤
    s⁻¹ * (D * fixedAwayRapidEnvelope (J + 2) u) *
        (C * fixedAwayRapidEnvelope (J + 2) v) +
      (C * fixedAwayRapidEnvelope (J + 2) u) *
        (s'⁻¹ * (D * fixedAwayRapidEnvelope (J + 2) v))
  rw [(hasDerivAt_fixedAwayScaledHermitianProduct
    hδ hδt.le hs.ne' hs'.ne' hxa hxa').deriv]
  calc
    ‖((s⁻¹ : ℝ) • deriv R u) * conj (R v) +
        R u * conj ((s'⁻¹ : ℝ) • deriv R v)‖ ≤
      ‖((s⁻¹ : ℝ) • deriv R u) * conj (R v)‖ +
        ‖R u * conj ((s'⁻¹ : ℝ) • deriv R v)‖ := norm_add_le _ _
    _ = s⁻¹ * ‖deriv R u‖ * ‖R v‖ +
        ‖R u‖ * (s'⁻¹ * ‖deriv R v‖) := by
      simp only [norm_mul, Complex.norm_conj, norm_smul, Real.norm_eq_abs]
      rw [abs_of_pos (inv_pos.mpr hs), abs_of_pos (inv_pos.mpr hs')]
    _ ≤ s⁻¹ * (D * fixedAwayRapidEnvelope (J + 2) u) *
          (C * fixedAwayRapidEnvelope (J + 2) v) +
        (C * fixedAwayRapidEnvelope (J + 2) u) *
          (s'⁻¹ * (D * fixedAwayRapidEnvelope (J + 2) v)) := by
      apply add_le_add
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_left hDu (inv_nonneg.mpr hs.le)) hRv
          (norm_nonneg _)
          (mul_nonneg (inv_nonneg.mpr hs.le)
            (mul_nonneg
              (fixedAwayDerivativeRapidDecayConstant_nonneg t δ (J + 2))
              (fixedAwayRapidEnvelope_nonneg (J + 2) u)))
      · exact mul_le_mul hRu
          (mul_le_mul_of_nonneg_left hDv (inv_nonneg.mpr hs'.le))
          (mul_nonneg (inv_nonneg.mpr hs'.le) (norm_nonneg _))
          (mul_nonneg
            (fixedAwayPVRapidDecayConstant_nonneg t δ hM)
            (fixedAwayRapidEnvelope_nonneg (J + 2) u))

theorem integrable_fixedAwayRapidEnvelope_scaled_product
    (J : ℕ) {s a s' a' : ℝ} (hs : s ≠ 0) :
    Integrable fun x : ℝ ↦
      fixedAwayRapidEnvelope (J + 2) ((x - a) / s) *
        fixedAwayRapidEnvelope (J + 2) ((x - a') / s') := by
  have hbase := integrable_fixedAwayRapidEnvelope_two.comp_div hs
  have hmajor := hbase.comp_sub_right a
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦
      fixedAwayRapidEnvelope (J + 2) ((x - a) / s) *
        fixedAwayRapidEnvelope (J + 2) ((x - a') / s')) := by
    apply Continuous.aestronglyMeasurable
    exact ((continuous_fixedAwayRapidEnvelope (J + 2)).comp
        ((continuous_id.sub continuous_const).div_const s)).mul
      ((continuous_fixedAwayRapidEnvelope (J + 2)).comp
        ((continuous_id.sub continuous_const).div_const s'))
  apply hmajor.mono' hmeas
  filter_upwards with x
  have hfirstNonneg :=
    fixedAwayRapidEnvelope_nonneg (J + 2) ((x - a) / s)
  have hsecondOne :=
    fixedAwayRapidEnvelope_le_one (J + 2) ((x - a') / s')
  have hJone := fixedAwayRapidEnvelope_le_one J ((x - a) / s)
  have htwoNonneg := fixedAwayRapidEnvelope_nonneg 2 ((x - a) / s)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hfirstNonneg
    (fixedAwayRapidEnvelope_nonneg (J + 2) ((x - a') / s')))]
  calc
    fixedAwayRapidEnvelope (J + 2) ((x - a) / s) *
        fixedAwayRapidEnvelope (J + 2) ((x - a') / s') ≤
      fixedAwayRapidEnvelope (J + 2) ((x - a) / s) :=
        mul_le_of_le_one_right hfirstNonneg hsecondOne
    _ = fixedAwayRapidEnvelope J ((x - a) / s) *
        fixedAwayRapidEnvelope 2 ((x - a) / s) :=
      fixedAwayRapidEnvelope_add_two J ((x - a) / s)
    _ ≤ fixedAwayRapidEnvelope 2 ((x - a) / s) := by
      nlinarith

/-- The continuous-variation contribution has arbitrary fixed-order
separation decay.  The two displayed envelopes correspond to the two
possible choices of carrier-centered change of variables. -/
theorem integral_norm_deriv_fixedAwayScaledHermitianProduct_le_rapidSeparation
    {t δ s a s' a' : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (hs : 0 < s) (hs' : 0 < s')
    (hss' : s ≤ 4 * s') (hs's : s' ≤ 4 * s)
    (J : ℕ) :
    (∫ x : ℝ,
      ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖) ≤
      5 * 8 ^ J *
        fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
        fixedAwayPVRapidDecayConstant t δ (J + 2) *
        fixedAwayRapidEnvelopeTwoMass *
        (fixedAwayRapidEnvelope J ((a' - a) / s') +
          fixedAwayRapidEnvelope J ((a - a') / s)) := by
  let P : ℝ → ℝ := fun x ↦
    fixedAwayRapidEnvelope (J + 2) ((x - a) / s) *
      fixedAwayRapidEnvelope (J + 2) ((x - a') / s')
  let A : ℝ :=
    fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
      fixedAwayPVRapidDecayConstant t δ (J + 2)
  let H : ℝ → ℝ := fun x ↦
    A * (s⁻¹ * P x + s'⁻¹ * P x)
  have hP : Integrable P := by
    simpa only [P] using!
      integrable_fixedAwayRapidEnvelope_scaled_product
        J hs.ne'
  have hH : Integrable H := by
    exact ((hP.const_mul s⁻¹).add (hP.const_mul s'⁻¹)).const_mul A
  have hactual : Integrable (fun x : ℝ ↦
      ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖) :=
    (integrable_deriv_fixedAwayScaledHermitianProduct
      hδ hδt hs.ne' hs'.ne').norm
  have hpoint : ∀ᵐ x ∂(volume : Measure ℝ),
      ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖ ≤ H x := by
    filter_upwards [(volume : Measure ℝ).ae_ne a,
      (volume : Measure ℝ).ae_ne a'] with x hxa hxa'
    have hraw := norm_deriv_fixedAwayScaledHermitianProduct_le_rapidEnvelope
      hδ hδt hs hs' hxa hxa' J
    dsimp only [H, A, P]
    convert! hraw using 1
    all_goals ring
  have hintegral : (∫ x : ℝ,
      ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖) ≤
      ∫ x : ℝ, H x := integral_mono_ae hactual hH hpoint
  have hfirst :=
    inv_mul_integral_fixedAwayRapidEnvelope_scaled_product_le
      (a := a) (a' := a') J hs hs' hss' hs's
  have hsecondRaw :=
    inv_mul_integral_fixedAwayRapidEnvelope_scaled_product_le
      (s := s') (a := a') (s' := s) (a' := a)
      J hs' hs hs's hss'
  have hsecond : s'⁻¹ * (∫ x : ℝ, P x) ≤
      5 * 8 ^ J * fixedAwayRapidEnvelope J ((a - a') / s) *
        fixedAwayRapidEnvelopeTwoMass := by
    have hint : (∫ x : ℝ, P x) =
        ∫ x : ℝ,
          fixedAwayRapidEnvelope (J + 2) ((x - a') / s') *
            fixedAwayRapidEnvelope (J + 2) ((x - a) / s) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [P]
      ring
    rw [hint]
    exact hsecondRaw
  have hA : 0 ≤ A := by
    exact mul_nonneg
      (fixedAwayDerivativeRapidDecayConstant_nonneg t δ (J + 2))
      (fixedAwayPVRapidDecayConstant_nonneg t δ (by omega))
  calc
    (∫ x : ℝ,
        ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖) ≤
      ∫ x : ℝ, H x := hintegral
    _ = A * (s⁻¹ * (∫ x : ℝ, P x) +
          s'⁻¹ * (∫ x : ℝ, P x)) := by
      dsimp only [H]
      rw [integral_const_mul,
        integral_add (hP.const_mul s⁻¹) (hP.const_mul s'⁻¹),
        integral_const_mul, integral_const_mul]
    _ ≤ A *
        (5 * 8 ^ J * fixedAwayRapidEnvelope J ((a' - a) / s') *
            fixedAwayRapidEnvelopeTwoMass +
          5 * 8 ^ J * fixedAwayRapidEnvelope J ((a - a') / s) *
            fixedAwayRapidEnvelopeTwoMass) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hA
    _ = 5 * 8 ^ J *
        fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
        fixedAwayPVRapidDecayConstant t δ (J + 2) *
        fixedAwayRapidEnvelopeTwoMass *
        (fixedAwayRapidEnvelope J ((a' - a) / s') +
          fixedAwayRapidEnvelope J ((a - a') / s)) := by
      dsimp only [A]
      ring

/-- At comparable positive scales, the two carrier-normalized separation
parameters are interchangeable at the cost of a fixed dyadic factor. -/
theorem fixedAwayRapidEnvelope_normalized_swap_le
    (J : ℕ) {s a s' a' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (hss' : s ≤ 4 * s') :
  fixedAwayRapidEnvelope J ((a - a') / s) ≤
      8 ^ J * fixedAwayRapidEnvelope J ((a' - a) / s') := by
  apply fixedAwayRapidEnvelope_le_eight_separated_of_far
  rw [abs_div, abs_div, abs_of_pos hs, abs_of_pos hs']
  rw [show |a' - a| = |a - a'| by exact abs_sub_comm a' a]
  have hD : 0 ≤ |a - a'| := abs_nonneg _
  have hinv : (4 * s')⁻¹ ≤ s⁻¹ := by
    exact (inv_le_inv₀ (by positivity : (0 : ℝ) < 4 * s') hs).2 hss'
  have hmul := mul_le_mul_of_nonneg_left hinv hD
  rw [mul_inv_rev] at hmul
  norm_num at hmul
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hn : 0 ≤ |a - a'| * s'⁻¹ :=
    mul_nonneg hD (inv_nonneg.mpr hs'.le)
  calc
    |a - a'| * s'⁻¹ * 8⁻¹ ≤
        |a - a'| * (s'⁻¹ * (1 / 4)) := by nlinarith
    _ ≤ |a - a'| * s⁻¹ := hmul

def fixedAwayHermitianRapidVariationConstant
    (t δ : ℝ) (J : ℕ) : ℝ :=
  5 * 8 ^ J *
      fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
      fixedAwayPVRapidDecayConstant t δ (J + 2) *
      fixedAwayRapidEnvelopeTwoMass * (1 + 8 ^ J) +
    4 * Real.pi * fixedAwayPVRapidDecayConstant t δ J * (1 + 8 ^ J) +
    4 * Real.pi ^ 2

theorem fixedAwayHermitianRapidVariationConstant_nonneg
    (t δ : ℝ) (J : ℕ) :
    0 ≤ fixedAwayHermitianRapidVariationConstant t δ J := by
  unfold fixedAwayHermitianRapidVariationConstant
  have hD := fixedAwayDerivativeRapidDecayConstant_nonneg t δ (J + 2)
  have hC2 := fixedAwayPVRapidDecayConstant_nonneg t δ (by omega : 0 < J + 2)
  have hmass := fixedAwayRapidEnvelopeTwoMass_nonneg
  have hC : 0 ≤ fixedAwayPVRapidDecayConstant t δ J := by
    unfold fixedAwayPVRapidDecayConstant
    exact mul_nonneg (by positivity) (add_nonneg
      (fixedAwayPVLocalBound_nonneg t)
      (div_nonneg (fixedAwayDerivativeBound_nonneg t δ (J + 1))
        (mul_nonneg (Nat.cast_nonneg J) (by positivity))))
  positivity

/-- Sampled total variation of the unprojected Hermitian weight, with all
ordinary derivative and regulated carrier-point contributions absorbed into
one arbitrary-order separation envelope. -/
theorem tsum_variation_fixedAwayHermitianIntegerWeight_le_rapidSeparation
    {t δ s a s' a' : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (hs : 0 < s) (hs' : 0 < s')
    (hss' : s ≤ 4 * s') (hs's : s' ≤ 4 * s)
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖fixedAwayHermitianIntegerWeight t δ s a s' a' n -
        fixedAwayHermitianIntegerWeight t δ s a s' a' (n + 1)‖) ≤
      fixedAwayHermitianRapidVariationConstant t δ J *
        fixedAwayRapidEnvelope J ((a' - a) / s') := by
  have hraw := tsum_variation_fixedAwayHermitianIntegerWeight_le
    (t := t) (δ := δ) (s := s) (a := a) (s' := s') (a' := a')
    hδ hδt hs hs'
  have hderiv :=
    integral_norm_deriv_fixedAwayScaledHermitianProduct_le_rapidSeparation
      (a := a) (a' := a') hδ hδt hs hs' hss' hs's J
  have hswap := fixedAwayRapidEnvelope_normalized_swap_le
    (a := a) (a' := a') J hs hs' hss'
  let E : ℝ := fixedAwayRapidEnvelope J ((a' - a) / s')
  have hE : 0 ≤ E := fixedAwayRapidEnvelope_nonneg J _
  have hderiv' : (∫ x : ℝ,
      ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖) ≤
      (5 * 8 ^ J *
        fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
        fixedAwayPVRapidDecayConstant t δ (J + 2) *
        fixedAwayRapidEnvelopeTwoMass * (1 + 8 ^ J)) * E := by
    exact hderiv.trans (by
      dsimp only [E]
      have hcoef : 0 ≤ 5 * 8 ^ J *
          fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
          fixedAwayPVRapidDecayConstant t δ (J + 2) *
          fixedAwayRapidEnvelopeTwoMass := by
        have hD := fixedAwayDerivativeRapidDecayConstant_nonneg t δ (J + 2)
        have hC := fixedAwayPVRapidDecayConstant_nonneg t δ (by omega : 0 < J + 2)
        have hmass := fixedAwayRapidEnvelopeTwoMass_nonneg
        positivity
      nlinarith)
  have hjump : 2 * fixedAwayHermitianCarrierJumpCost t δ s a s' a' ≤
      (4 * Real.pi * fixedAwayPVRapidDecayConstant t δ J *
          (1 + 8 ^ J) + 4 * Real.pi ^ 2) * E := by
    by_cases haa' : a = a'
    · subst a'
      rw [fixedAwayHermitianCarrierJumpCost_eq_diagonal]
      have hEeq : E = 1 := by simp [E, fixedAwayRapidEnvelope]
      rw [hEeq]
      have hnonneg : 0 ≤ 4 * Real.pi *
          fixedAwayPVRapidDecayConstant t δ J * (1 + 8 ^ J) := by
        have hC := fixedAwayPVRapidDecayConstant_nonneg t δ hJ
        positivity
      nlinarith [sq_nonneg Real.pi]
    · have hcost := fixedAwayHermitianCarrierJumpCost_le_rapid_of_ne
        (s := s) (s' := s') hδ hδt haa' hJ
      have hpi : 0 ≤ 2 * Real.pi *
          fixedAwayPVRapidDecayConstant t δ J := by
        have hC := fixedAwayPVRapidDecayConstant_nonneg t δ hJ
        positivity
      have hfirstEq :
          fixedAwayRapidEnvelope J ((a - a') / s') = E := by
        dsimp only [E]
        simp only [fixedAwayRapidEnvelope, abs_div, abs_sub_comm]
      have hswap' : fixedAwayRapidEnvelope J ((a' - a) / s) ≤
          8 ^ J * E := by
        dsimp only [E]
        simpa only [fixedAwayRapidEnvelope, abs_div, abs_sub_comm] using! hswap
      rw [hfirstEq] at hcost
      dsimp only [E] at hswap ⊢
      have hcost' : 2 * fixedAwayHermitianCarrierJumpCost
          t δ s a s' a' ≤
          (4 * Real.pi * fixedAwayPVRapidDecayConstant t δ J *
            (1 + 8 ^ J)) *
              fixedAwayRapidEnvelope J ((a' - a) / s') := by
        have hsum : E + fixedAwayRapidEnvelope J ((a' - a) / s) ≤
            (1 + 8 ^ J) * E := by nlinarith
        calc
          2 * fixedAwayHermitianCarrierJumpCost t δ s a s' a' ≤
              2 * ((2 * Real.pi * fixedAwayPVRapidDecayConstant t δ J) *
                (E + fixedAwayRapidEnvelope J ((a' - a) / s))) :=
            mul_le_mul_of_nonneg_left hcost (by norm_num)
          _ ≤ 2 * ((2 * Real.pi * fixedAwayPVRapidDecayConstant t δ J) *
                ((1 + 8 ^ J) * E)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsum hpi) (by norm_num)
          _ = (4 * Real.pi * fixedAwayPVRapidDecayConstant t δ J *
                (1 + 8 ^ J)) * E := by ring
      calc
        2 * fixedAwayHermitianCarrierJumpCost t δ s a s' a' ≤
            (4 * Real.pi * fixedAwayPVRapidDecayConstant t δ J *
              (1 + 8 ^ J)) * E := hcost'
        _ ≤ (4 * Real.pi * fixedAwayPVRapidDecayConstant t δ J *
              (1 + 8 ^ J)) * E + 4 * Real.pi ^ 2 * E :=
          le_add_of_nonneg_right (mul_nonneg (by positivity) hE)
        _ = (4 * Real.pi * fixedAwayPVRapidDecayConstant t δ J *
              (1 + 8 ^ J) + 4 * Real.pi ^ 2) * E := by ring
  exact hraw.trans (by
    unfold fixedAwayHermitianRapidVariationConstant
    dsimp only [E] at hderiv' hjump ⊢
    nlinarith)

def fixedAwayHermitianRapidBVConstant
    (t δ : ℝ) (J : ℕ) : ℝ :=
  2 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2 * 8 ^ J +
    fixedAwayHermitianRapidVariationConstant t δ J

theorem fixedAwayHermitianRapidBVConstant_nonneg
    (t δ : ℝ) (J : ℕ) :
    0 ≤ fixedAwayHermitianRapidBVConstant t δ J := by
  unfold fixedAwayHermitianRapidBVConstant
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (by positivity) (sq_nonneg _)) (by positivity))
    (fixedAwayHermitianRapidVariationConstant_nonneg t δ J)

/-- Fully instantiated all-integer Hermitian Abel estimate.  This is the
formal counterpart of the off-diagonal estimate obtained from the incomplete
Ramanujan bound and the separated BV multiplier. -/
theorem norm_tsum_fixedAwayHermitianRamanujanMultiplier_le_rapidSeparation
    {t δ s a s' a' : ℝ} {p p' : ℕ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hs : 0 < s) (hs' : 0 < s')
    (hss' : s ≤ 4 * s') (hs's : s' ≤ 4 * s)
    {J : ℕ} (hJ : 0 < J)
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ‖∑' n : ℤ,
        hermitianRamanujanMultiplierTerm
          (fixedAwayHermitianIntegerWeight t δ s a s' a') p p' n‖ ≤
      (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ))) *
        (fixedAwayHermitianRapidBVConstant t δ J *
          fixedAwayRapidEnvelope J ((a' - a) / s')) := by
  let w : ℤ → ℂ :=
    fixedAwayHermitianIntegerWeight t δ s a s' a'
  let B : ℝ :=
    2 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2 * 8 ^ J *
      fixedAwayRapidEnvelope J ((a' - a) / s')
  let V : ℝ := fixedAwayHermitianRapidVariationConstant t δ J *
    fixedAwayRapidEnvelope J ((a' - a) / s')
  have hw : Summable fun n : ℤ ↦ ‖w n‖ := by
    simpa only [w] using! summable_norm_fixedAwayHermitianIntegerWeight
      (t := t) (δ := δ) (s := s) (a := a) (s' := s') (a' := a')
      hδ hδt hs hs'
  have hvariation : Summable fun n : ℤ ↦ ‖w n - w (n + 1)‖ := by
    simpa only [w] using!
      summable_variation_fixedAwayHermitianIntegerWeight
        (t := t) (δ := δ) (s := s) (a := a) (s' := s') (a' := a')
        hδ hδt hs hs'
  have hsup : ∀ n : ℤ, ‖w n‖ ≤ B := by
    intro n
    dsimp only [w, B, fixedAwayHermitianIntegerWeight]
    exact norm_fixedAwayScaledHermitianProduct_le_rapidSeparation
      hδ hδt hs hs' hss' J (n : ℝ)
  have hvar : (∑' n : ℤ, ‖w n - w (n + 1)‖) ≤ V := by
    dsimp only [w, V]
    exact tsum_variation_fixedAwayHermitianIntegerWeight_le_rapidSeparation
      hδ hδt hs hs' hss' hs's hJ
  have hraw := norm_tsum_hermitianRamanujanMultiplierTerm_le
    w hp hp' hpp' hw hvariation hsup hvar
  simpa only [w, B, V, fixedAwayHermitianRapidBVConstant,
    add_mul] using! hraw

end

end Erdos1002
