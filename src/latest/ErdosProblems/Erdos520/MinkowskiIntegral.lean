import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory
open scoped ENNReal

namespace Erdos
namespace Problem520

/-!
# Integral Minkowski inequality

This file records the nonnegative integral form of Minkowski's inequality
used when the `z`-integral in the thin-prime-block argument is moved outside
an `L^p` norm in the probability variable.
-/

namespace IntegralMinkowski

variable {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
  {ν : Measure Z} {μ : Measure Ω} [SFinite ν] [SFinite μ]

/-- The integral form of Minkowski's inequality for nonnegative extended-real
functions.  The explicit finiteness assumption on the left-hand `p`-moment
is harmless in the thin-block application (where a finite moment bound is
already available) and avoids imposing any finiteness hypothesis on the two
underlying measures.

In formulas,
`‖∫ F(z, ·) dν(z)‖_{L^p(μ)} ≤ ∫ ‖F(z, ·)‖_{L^p(μ)} dν(z)`.
-/
theorem lintegral_Lp_lintegral_le
    {F : Z → Ω → ℝ≥0∞}
    (hF : Measurable (fun x : Z × Ω => F x.1 x.2))
    {p : ℝ} (hp : 1 ≤ p)
    (hfinite : (∫⁻ ω, (∫⁻ z, F z ω ∂ν) ^ p ∂μ) ≠ ⊤) :
    (∫⁻ ω, (∫⁻ z, F z ω ∂ν) ^ p ∂μ) ^ (1 / p) ≤
      ∫⁻ z, (∫⁻ ω, F z ω ^ p ∂μ) ^ (1 / p) ∂ν := by
  let H : Ω → ℝ≥0∞ := fun ω => ∫⁻ z, F z ω ∂ν
  let I : ℝ≥0∞ := ∫⁻ ω, H ω ^ p ∂μ
  let B : ℝ≥0∞ := ∫⁻ z, (∫⁻ ω, F z ω ^ p ∂μ) ^ (1 / p) ∂ν
  have hH : Measurable H := hF.lintegral_prod_left
  have hFswap : Measurable (Function.uncurry (fun ω z => F z ω)) := by
    simpa [Function.uncurry, Function.comp_def] using! hF.comp measurable_swap
  change I ^ (1 / p) ≤ B
  rcases hp.eq_or_lt with rfl | hp
  · simpa only [I, B, H, one_div, inv_one, ENNReal.rpow_one] using!
      (lintegral_lintegral_swap (μ := μ) (ν := ν) hFswap.aemeasurable).le
  have hpq : p.HolderConjugate p.conjExponent :=
    Real.HolderConjugate.conjExponent hp
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  by_cases hI0 : I = 0
  · simp [hI0, hp_pos]
  have hpow : ∀ ω, H ω ^ p = H ω * H ω ^ (p - 1) := by
    intro ω
    by_cases h0 : H ω = 0
    · simp [h0, hp_pos, sub_pos.mpr hp]
    by_cases htop : H ω = ⊤
    · simp [htop, hp_pos, sub_pos.mpr hp]
    calc
      H ω ^ p = H ω ^ (1 + (p - 1)) := by ring_nf
      _ = H ω ^ 1 * H ω ^ (p - 1) := ENNReal.rpow_add _ _ h0 htop
      _ = H ω * H ω ^ (p - 1) := by rw [ENNReal.rpow_one]
  have hmain : I ≤ B * I ^ (1 / p.conjExponent) := by
    calc
      I = ∫⁻ ω, ∫⁻ z, F z ω * H ω ^ (p - 1) ∂ν ∂μ := by
        simp_rw [I, hpow]
        congr 1
        funext ω
        exact (lintegral_mul_const (H ω ^ (p - 1))
          (hF.comp measurable_prodMk_right)).symm
      _ = ∫⁻ z, ∫⁻ ω, F z ω * H ω ^ (p - 1) ∂μ ∂ν := by
        rw [lintegral_lintegral_swap]
        exact hFswap.mul
          ((hH.comp measurable_fst).pow_const (p - 1)) |>.aemeasurable
      _ ≤ ∫⁻ z, (∫⁻ ω, F z ω ^ p ∂μ) ^ (1 / p) *
          I ^ (1 / p.conjExponent) ∂ν := by
        refine lintegral_mono fun z => ?_
        have hzF : AEMeasurable (F z) μ :=
          (hF.comp measurable_prodMk_left).aemeasurable
        have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hzF
          (hH.pow_const (p - 1)).aemeasurable
        simpa only [← ENNReal.rpow_mul, hpq.sub_one_mul_conj, I] using! hholder
      _ = B * I ^ (1 / p.conjExponent) := by
        have hFp : Measurable
            (Function.uncurry (fun z ω => F z ω ^ p)) := by
          simpa [Function.uncurry] using! hF.pow_const p
        have hAz : Measurable fun z =>
            (∫⁻ ω, F z ω ^ p ∂μ) ^ (1 / p) :=
          hFp.lintegral_prod_right.pow_const (1 / p)
        simpa only [B] using!
          (lintegral_mul_const (μ := ν) (I ^ (1 / p.conjExponent)) hAz)
  have hI_top : I ≠ ⊤ := by
    simpa only [I, H] using! hfinite
  have hIroot0 : I ^ (1 / p) ≠ 0 := by
    simp [hI0, hI_top, hp_pos]
  have h_inv_conj : 1 / p.conjExponent = 1 - 1 / p := by
    nth_rw 2 [← hpq.inv_add_inv_eq_one]
    ring
  have hnormalized : 1 ≤ I ^ (-(1 / p)) * B := by
    rw [h_inv_conj, sub_eq_add_neg, ENNReal.rpow_add _ _ hI0 hI_top,
      ENNReal.rpow_one] at hmain
    conv_rhs at hmain => enter [2]; rw [mul_comm]
    conv_lhs at hmain => rw [← one_mul I]
    rwa [← mul_assoc, ENNReal.mul_le_mul_iff_left hI0 hI_top, mul_comm] at hmain
  rwa [← ENNReal.mul_le_mul_iff_right hIroot0
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hI_top), ← mul_assoc,
    ← ENNReal.rpow_add _ _ hI0 hI_top, ← sub_eq_add_neg, sub_self,
    ENNReal.rpow_zero, one_mul, mul_one] at hnormalized

/-- Real-valued integral Minkowski for a nonnegative jointly measurable
kernel.  The hypotheses state exactly the integrability needed to identify
each of the four Bochner integrals below with its nonnegative `lintegral`;
in particular, no nonintegrable-default value of the Bochner integral enters
the conclusion.

In formulas,
`(∫ ω, (∫ z, F z ω) ^ r) ^ (1/r)
  ≤ ∫ z, (∫ ω, F z ω ^ r) ^ (1/r)`.
-/
theorem integral_Lp_integral_le
    {F : Z → Ω → ℝ}
    (hF : Measurable (fun x : Z × Ω ↦ F x.1 x.2))
    (hF_nonneg : ∀ z ω, 0 ≤ F z ω)
    {r : ℕ} (hr : 1 ≤ r)
    (hinner_integrable : ∀ ω, Integrable (fun z ↦ F z ω) ν)
    (hmoment_integrable :
      Integrable (fun ω ↦ (∫ z, F z ω ∂ν) ^ r) μ)
    (hsection_integrable : ∀ z,
      Integrable (fun ω ↦ F z ω ^ r) μ)
    (hroot_integrable : Integrable
      (fun z ↦ (∫ ω, F z ω ^ r ∂μ) ^ (1 / (r : ℝ))) ν) :
    (∫ ω, (∫ z, F z ω ∂ν) ^ r ∂μ) ^ (1 / (r : ℝ)) ≤
      ∫ z, (∫ ω, F z ω ^ r ∂μ) ^ (1 / (r : ℝ)) ∂ν := by
  let G : Z → Ω → ℝ≥0∞ := fun z ω ↦ ENNReal.ofReal (F z ω)
  let A : Ω → ℝ := fun ω ↦ ∫ z, F z ω ∂ν
  let B : Z → ℝ := fun z ↦ ∫ ω, F z ω ^ r ∂μ
  let L : ℝ := ∫ ω, A ω ^ r ∂μ
  let R : ℝ := ∫ z, B z ^ (1 / (r : ℝ)) ∂ν
  have hr_pos : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hr
  have hrR_pos : (0 : ℝ) < r := by exact_mod_cast hr_pos
  have hexp_nonneg : 0 ≤ 1 / (r : ℝ) := by positivity
  have hA_nonneg : ∀ ω, 0 ≤ A ω := fun ω ↦
    integral_nonneg (fun z ↦ hF_nonneg z ω)
  have hB_nonneg : ∀ z, 0 ≤ B z := fun z ↦
    integral_nonneg (fun ω ↦ pow_nonneg (hF_nonneg z ω) r)
  have hL_nonneg : 0 ≤ L :=
    integral_nonneg (fun ω ↦ pow_nonneg (hA_nonneg ω) r)
  have hR_nonneg : 0 ≤ R :=
    integral_nonneg (fun z ↦ Real.rpow_nonneg (hB_nonneg z) _)
  have hG : Measurable (fun x : Z × Ω ↦ G x.1 x.2) := by
    exact ENNReal.measurable_ofReal.comp hF
  have hinner : ∀ ω, (∫⁻ z, G z ω ∂ν) = ENNReal.ofReal (A ω) := by
    intro ω
    exact (ofReal_integral_eq_lintegral_ofReal
      (hinner_integrable ω) (ae_of_all ν fun z ↦ hF_nonneg z ω)).symm
  have hsection : ∀ z, (∫⁻ ω, G z ω ^ (r : ℝ) ∂μ) =
      ENNReal.ofReal (B z) := by
    intro z
    rw [show (fun ω ↦ G z ω ^ (r : ℝ)) =
        fun ω ↦ ENNReal.ofReal (F z ω ^ r) by
      funext ω
      simp only [G]
      rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow (hF_nonneg z ω)]]
    exact (ofReal_integral_eq_lintegral_ofReal
      (hsection_integrable z)
      (ae_of_all μ fun ω ↦ pow_nonneg (hF_nonneg z ω) r)).symm
  have hleft :
      (∫⁻ ω, (∫⁻ z, G z ω ∂ν) ^ (r : ℝ) ∂μ) =
        ENNReal.ofReal L := by
    simp_rw [hinner]
    rw [show (fun ω ↦ ENNReal.ofReal (A ω) ^ (r : ℝ)) =
        fun ω ↦ ENNReal.ofReal (A ω ^ r) by
      funext ω
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (hA_nonneg ω)]]
    exact (ofReal_integral_eq_lintegral_ofReal
      hmoment_integrable
      (ae_of_all μ fun ω ↦ pow_nonneg (hA_nonneg ω) r)).symm
  have hright :
      (∫⁻ z, (∫⁻ ω, G z ω ^ (r : ℝ) ∂μ) ^
          (1 / (r : ℝ)) ∂ν) = ENNReal.ofReal R := by
    simp_rw [hsection, ENNReal.ofReal_rpow_of_nonneg
      (hB_nonneg _) hexp_nonneg]
    exact (ofReal_integral_eq_lintegral_ofReal
      hroot_integrable
      (ae_of_all ν fun z ↦ Real.rpow_nonneg (hB_nonneg z) _)).symm
  have hfinite :
      (∫⁻ ω, (∫⁻ z, G z ω ∂ν) ^ (r : ℝ) ∂μ) ≠ ⊤ := by
    rw [hleft]
    exact ENNReal.ofReal_ne_top
  have hmain := lintegral_Lp_lintegral_le hG
    (p := (r : ℝ)) (by exact_mod_cast hr) hfinite
  rw [hleft, hright, ENNReal.ofReal_rpow_of_nonneg hL_nonneg hexp_nonneg]
    at hmain
  exact (ENNReal.ofReal_le_ofReal_iff hR_nonneg).mp hmain

/-- Natural-exponent spelling of `integral_Lp_integral_le`, with the second
measure named explicitly for convenient use at concrete finite probability
fibers. -/
theorem integral_natLp_integral_le
    {F : Z → Ω → ℝ} {μ' : Measure Ω} [SFinite μ']
    (hF : Measurable (fun x : Z × Ω ↦ F x.1 x.2))
    (hF_nonneg : ∀ z ω, 0 ≤ F z ω)
    (r : ℕ) (hr : 1 ≤ r)
    (hinner_integrable : ∀ ω, Integrable (fun z ↦ F z ω) ν)
    (hmoment_integrable :
      Integrable (fun ω ↦ (∫ z, F z ω ∂ν) ^ r) μ')
    (hsection_integrable : ∀ z,
      Integrable (fun ω ↦ F z ω ^ r) μ')
    (hroot_integrable : Integrable
      (fun z ↦ (∫ ω, F z ω ^ r ∂μ') ^ (1 / (r : ℝ))) ν) :
    (∫ ω, (∫ z, F z ω ∂ν) ^ r ∂μ') ^ (1 / (r : ℝ)) ≤
      ∫ z, (∫ ω, F z ω ^ r ∂μ') ^ (1 / (r : ℝ)) ∂ν := by
  exact integral_Lp_integral_le (μ := μ') hF hF_nonneg hr
    hinner_integrable hmoment_integrable hsection_integrable hroot_integrable

/-- Scalar form of `integral_Lp_integral_le`.  This is convenient when an
energy is normalized by a nonnegative constant outside its inner integral,
as in the factor `1 / log b` in the thin-prime-block energy. -/
theorem integral_Lp_const_mul_integral_le
    {F : Z → Ω → ℝ}
    (hF : Measurable (fun x : Z × Ω ↦ F x.1 x.2))
    (hF_nonneg : ∀ z ω, 0 ≤ F z ω)
    {r : ℕ} (hr : 1 ≤ r)
    {c : ℝ} (hc : 0 ≤ c)
    (hinner_integrable : ∀ ω, Integrable (fun z ↦ F z ω) ν)
    (hmoment_integrable :
      Integrable (fun ω ↦ (∫ z, F z ω ∂ν) ^ r) μ)
    (hsection_integrable : ∀ z,
      Integrable (fun ω ↦ F z ω ^ r) μ)
    (hroot_integrable : Integrable
      (fun z ↦ (∫ ω, F z ω ^ r ∂μ) ^ (1 / (r : ℝ))) ν) :
    (∫ ω, (c * ∫ z, F z ω ∂ν) ^ r ∂μ) ^ (1 / (r : ℝ)) ≤
      c * ∫ z, (∫ ω, F z ω ^ r ∂μ) ^ (1 / (r : ℝ)) ∂ν := by
  let A : Ω → ℝ := fun ω ↦ ∫ z, F z ω ∂ν
  let L : ℝ := ∫ ω, A ω ^ r ∂μ
  let R : ℝ := ∫ z,
    (∫ ω, F z ω ^ r ∂μ) ^ (1 / (r : ℝ)) ∂ν
  have hr_pos : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hr
  have hr_ne : r ≠ 0 := Nat.ne_of_gt hr_pos
  have hA_nonneg : ∀ ω, 0 ≤ A ω := fun ω ↦
    integral_nonneg (fun z ↦ hF_nonneg z ω)
  have hL_nonneg : 0 ≤ L :=
    integral_nonneg (fun ω ↦ pow_nonneg (hA_nonneg ω) r)
  have hbase : L ^ (1 / (r : ℝ)) ≤ R := by
    simpa only [A, L, R] using! integral_Lp_integral_le
      hF hF_nonneg hr hinner_integrable hmoment_integrable
        hsection_integrable hroot_integrable
  have hscaled :
      (∫ ω, (c * A ω) ^ r ∂μ) ^ (1 / (r : ℝ)) =
        c * L ^ (1 / (r : ℝ)) := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    rw [Real.mul_rpow (pow_nonneg hc r) hL_nonneg]
    rw [show 1 / (r : ℝ) = ((r : ℝ))⁻¹ by rw [one_div]]
    rw [Real.pow_rpow_inv_natCast hc hr_ne]
  change (∫ ω, (c * A ω) ^ r ∂μ) ^ (1 / (r : ℝ)) ≤ c * R
  rw [hscaled]
  exact mul_le_mul_of_nonneg_left hbase hc

/-- Weighted and normalized real-valued integral Minkowski.  Keeping the
weight outside the pointwise `L^r` root makes this form directly applicable
to inverse-square energies: take `w z = z⁻²` and
`c = (log b)⁻¹`.

The section hypothesis concerns `F ^ r`, rather than `(w * F) ^ r`; the
latter is derived internally by pulling the nonnegative scalar weight through
the finite moment and its root. -/
theorem integral_Lp_const_mul_weighted_integral_le
    {F : Z → Ω → ℝ} {w : Z → ℝ}
    (hF : Measurable (fun x : Z × Ω ↦ F x.1 x.2))
    (hw : Measurable w)
    (hF_nonneg : ∀ z ω, 0 ≤ F z ω)
    (hw_nonneg : ∀ z, 0 ≤ w z)
    {r : ℕ} (hr : 1 ≤ r)
    {c : ℝ} (hc : 0 ≤ c)
    (hinner_integrable : ∀ ω,
      Integrable (fun z ↦ w z * F z ω) ν)
    (hmoment_integrable : Integrable
      (fun ω ↦ (∫ z, w z * F z ω ∂ν) ^ r) μ)
    (hsection_integrable : ∀ z,
      Integrable (fun ω ↦ F z ω ^ r) μ)
    (hroot_integrable : Integrable
      (fun z ↦ w z *
        (∫ ω, F z ω ^ r ∂μ) ^ (1 / (r : ℝ))) ν) :
    (∫ ω, (c * ∫ z, w z * F z ω ∂ν) ^ r ∂μ) ^
        (1 / (r : ℝ)) ≤
      c * ∫ z, w z *
        (∫ ω, F z ω ^ r ∂μ) ^ (1 / (r : ℝ)) ∂ν := by
  let G : Z → Ω → ℝ := fun z ω ↦ w z * F z ω
  let B : Z → ℝ := fun z ↦ ∫ ω, F z ω ^ r ∂μ
  have hr_pos : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hr
  have hr_ne : r ≠ 0 := Nat.ne_of_gt hr_pos
  have hB_nonneg : ∀ z, 0 ≤ B z := fun z ↦
    integral_nonneg (fun ω ↦ pow_nonneg (hF_nonneg z ω) r)
  have hG_meas : Measurable (fun x : Z × Ω ↦ G x.1 x.2) := by
    exact (hw.comp measurable_fst).mul hF
  have hG_nonneg : ∀ z ω, 0 ≤ G z ω := fun z ω ↦
    mul_nonneg (hw_nonneg z) (hF_nonneg z ω)
  have hG_section_integrable : ∀ z,
      Integrable (fun ω ↦ G z ω ^ r) μ := by
    intro z
    rw [show (fun ω ↦ G z ω ^ r) =
        fun ω ↦ (w z) ^ r * F z ω ^ r by
      funext ω
      simp only [G, mul_pow]]
    exact (hsection_integrable z).const_mul ((w z) ^ r)
  have hroot_eq : ∀ z,
      (∫ ω, G z ω ^ r ∂μ) ^ (1 / (r : ℝ)) =
        w z * B z ^ (1 / (r : ℝ)) := by
    intro z
    have hmoment_eq :
        (∫ ω, G z ω ^ r ∂μ) = (w z) ^ r * B z := by
      simp_rw [G, mul_pow]
      rw [integral_const_mul]
    rw [hmoment_eq, Real.mul_rpow
      (pow_nonneg (hw_nonneg z) r) (hB_nonneg z)]
    rw [show 1 / (r : ℝ) = ((r : ℝ))⁻¹ by rw [one_div]]
    rw [Real.pow_rpow_inv_natCast (hw_nonneg z) hr_ne]
  have hG_root_integrable : Integrable
      (fun z ↦ (∫ ω, G z ω ^ r ∂μ) ^ (1 / (r : ℝ))) ν := by
    rw [show (fun z ↦ (∫ ω, G z ω ^ r ∂μ) ^ (1 / (r : ℝ))) =
        fun z ↦ w z * B z ^ (1 / (r : ℝ)) by
      funext z
      exact hroot_eq z]
    exact hroot_integrable
  have hmain := integral_Lp_const_mul_integral_le
    hG_meas hG_nonneg hr hc hinner_integrable hmoment_integrable
      hG_section_integrable hG_root_integrable
  simpa only [G, B, hroot_eq] using! hmain

end IntegralMinkowski

end Problem520
end Erdos
