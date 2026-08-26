import ErdosProblems.Erdos1002.PrincipalValueTransform

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The fixed-away principal-value transform

The cutoff quotient `χ(v)/v` is not Lebesgue integrable at infinity, so
its transform cannot be represented by the ordinary `L¹` Fourier integral.
This file instead subtracts the compactly supported correction
`κ = 1 - χ` from the already proved symmetric transform of `1/v`.
The correction is paired across the two half-lines and written using `sinc`,
which removes the apparent singularity at zero.

This construction proves the zero convention, both one-sided jump values,
oddness, and Hermitian symmetry without a distributional Fourier transform.
-/

open Filter Set
open scoped ComplexConjugate Real Topology

namespace Erdos1002

noncomputable section

/-- The paired integral
`\int_0^C κ(v) sin(2πtv)/v dv`, with the removable value at `v = 0`
written through `sinc`. -/
def compactCutoffPairedSine (κ : ℝ → ℝ) (C t : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..C,
    κ v * ((2 * Real.pi * t) * Real.sinc ((2 * Real.pi * t) * v))

/-- The symmetric principal-value transform of `κ(v)/v` when `κ` is
even and supported in `[-C,C]`, expressed by pairing the two half-lines. -/
def compactCutoffPVCorrection (κ : ℝ → ℝ) (C t : ℝ) : ℂ :=
  (-2 * Complex.I) * (compactCutoffPairedSine κ C t : ℂ)

/-- Rigorous paired realization of the manuscript's `R_χ`, with
`κ = 1 - χ` on its compact support. -/
def fixedAwayPVTransform (κ : ℝ → ℝ) (C t : ℝ) : ℂ :=
  signedExponentialPV t - compactCutoffPVCorrection κ C t

/-- Symmetric truncation after subtracting the compact paired correction.
Once `κ` is supported in `[-C,C]`, this is exactly the paired truncation
of `(1 - κ(v))/v` for every radius beyond `C`. -/
def fixedAwayPVTruncation (κ : ℝ → ℝ) (C t R : ℝ) : ℂ :=
  symmetricExponentialTruncation t R - compactCutoffPVCorrection κ C t

/-- The paired symmetric truncations converge to `fixedAwayPVTransform`.
This is the principal-value construction; no ordinary `L¹` Fourier
integral of the nonintegrable quotient is invoked. -/
theorem tendsto_fixedAwayPVTruncation_atTop (κ : ℝ → ℝ) (C t : ℝ) :
    Tendsto (fixedAwayPVTruncation κ C t) atTop
      (nhds (fixedAwayPVTransform κ C t)) := by
  exact (tendsto_symmetricExponentialTruncation_atTop t).sub
    tendsto_const_nhds

/-- The literal paired cutoff quotient on the finite symmetric interval.
The factor `-2i` is the result of pairing `v` with `-v`. -/
def pairedCutoffQuotientTruncation
    (χ : ℝ → ℝ) (t R : ℝ) : ℂ :=
  (-2 * Complex.I) *
    (((∫ v in (0 : ℝ)..R,
      χ v * sineKernel (2 * Real.pi * t) v) : ℝ) : ℂ)

/-- If `κ` is continuous and vanishes from `C` onward, then subtracting
its compact correction is exactly the finite paired transform of
`χ = 1 - κ`, for every `R ≥ C`. -/
theorem pairedCutoffQuotientTruncation_one_sub_eq
    (κ : ℝ → ℝ) (C t R : ℝ)
    (hκcont : Continuous κ) (_hC : 0 ≤ C) (hCR : C ≤ R)
    (hκzeroright : ∀ v, C ≤ v → κ v = 0) :
    pairedCutoffQuotientTruncation (fun v ↦ 1 - κ v) t R =
      fixedAwayPVTruncation κ C t R := by
  let a : ℝ := 2 * Real.pi * t
  have hsineCont : Continuous (sineKernel a) := by
    unfold sineKernel
    fun_prop
  have hprodCont : Continuous (fun v ↦ κ v * sineKernel a v) :=
    hκcont.mul hsineCont
  have htail : (∫ v in C..R, κ v * sineKernel a v) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _v : ℝ ↦ 0) (by
      intro v hv
      rw [uIcc_of_le hCR] at hv
      change κ v * sineKernel a v = 0
      rw [hκzeroright v hv.1, zero_mul])]
    simp
  have hcompact :
      (∫ v in (0 : ℝ)..R, κ v * sineKernel a v) =
        ∫ v in (0 : ℝ)..C, κ v * sineKernel a v := by
    have hzeroC : IntervalIntegrable
        (fun v ↦ κ v * sineKernel a v) MeasureTheory.volume 0 C :=
      hprodCont.intervalIntegrable 0 C
    have hCRint : IntervalIntegrable
        (fun v ↦ κ v * sineKernel a v) MeasureTheory.volume C R :=
      hprodCont.intervalIntegrable C R
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      hzeroC hCRint
    rw [htail, add_zero] at hadd
    exact hadd.symm
  have hbase : IntervalIntegrable (sineKernel a) MeasureTheory.volume 0 R :=
    hsineCont.intervalIntegrable 0 R
  have hprod : IntervalIntegrable
      (fun v ↦ κ v * sineKernel a v) MeasureTheory.volume 0 R :=
    hprodCont.intervalIntegrable 0 R
  have hreal :
      (∫ v in (0 : ℝ)..R, (1 - κ v) * sineKernel a v) =
        sineIntegralTruncation a R - compactCutoffPairedSine κ C t := by
    calc
      (∫ v in (0 : ℝ)..R, (1 - κ v) * sineKernel a v) =
          ∫ v in (0 : ℝ)..R,
            sineKernel a v - κ v * sineKernel a v := by
        apply intervalIntegral.integral_congr
        intro v _hv
        ring
      _ = (∫ v in (0 : ℝ)..R, sineKernel a v) -
          ∫ v in (0 : ℝ)..R, κ v * sineKernel a v :=
        intervalIntegral.integral_sub hbase hprod
      _ = sineIntegralTruncation a R -
          compactCutoffPairedSine κ C t := by
        rw [hcompact]
        rfl
  unfold pairedCutoffQuotientTruncation fixedAwayPVTruncation
  rw [hreal, symmetricExponentialTruncation_eq]
  unfold compactCutoffPVCorrection
  dsimp [a]
  push_cast
  ring

theorem compactCutoffPairedSine_zero (κ : ℝ → ℝ) (C : ℝ) :
    compactCutoffPairedSine κ C 0 = 0 := by
  simp [compactCutoffPairedSine]

theorem compactCutoffPVCorrection_zero (κ : ℝ → ℝ) (C : ℝ) :
    compactCutoffPVCorrection κ C 0 = 0 := by
  simp [compactCutoffPVCorrection, compactCutoffPairedSine_zero]

theorem fixedAwayPVTransform_zero (κ : ℝ → ℝ) (C : ℝ) :
    fixedAwayPVTransform κ C 0 = 0 := by
  simp [fixedAwayPVTransform, signedExponentialPV,
    compactCutoffPVCorrection_zero]

theorem compactCutoffPairedSine_neg (κ : ℝ → ℝ) (C t : ℝ) :
    compactCutoffPairedSine κ C (-t) =
      -compactCutoffPairedSine κ C t := by
  unfold compactCutoffPairedSine
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro v _hv
  change κ v * ((2 * Real.pi * -t) *
      Real.sinc ((2 * Real.pi * -t) * v)) =
    -(κ v * ((2 * Real.pi * t) *
      Real.sinc ((2 * Real.pi * t) * v)))
  rw [show 2 * Real.pi * -t = -(2 * Real.pi * t) by ring,
    show -(2 * Real.pi * t) * v = -(2 * Real.pi * t * v) by ring,
    Real.sinc_neg]
  ring

theorem compactCutoffPVCorrection_neg (κ : ℝ → ℝ) (C t : ℝ) :
    compactCutoffPVCorrection κ C (-t) =
      -compactCutoffPVCorrection κ C t := by
  simp only [compactCutoffPVCorrection, compactCutoffPairedSine_neg,
    Complex.ofReal_neg]
  ring

theorem signedExponentialPV_neg (t : ℝ) :
    signedExponentialPV (-t) = -signedExponentialPV t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hnt : 0 < -t := neg_pos.mpr ht
    simp [signedExponentialPV, ht, hnt, not_lt.mpr ht.le]
  · simp [signedExponentialPV]
  · have hnt : -t < 0 := neg_lt_zero.mpr ht
    simp [signedExponentialPV, ht, hnt, not_lt.mpr ht.le]

theorem fixedAwayPVTransform_neg (κ : ℝ → ℝ) (C t : ℝ) :
    fixedAwayPVTransform κ C (-t) = -fixedAwayPVTransform κ C t := by
  rw [fixedAwayPVTransform, fixedAwayPVTransform,
    signedExponentialPV_neg, compactCutoffPVCorrection_neg]
  ring

theorem conj_signedExponentialPV (t : ℝ) :
    conj (signedExponentialPV t) = -signedExponentialPV t := by
  unfold signedExponentialPV
  split_ifs <;> simp

theorem conj_compactCutoffPVCorrection (κ : ℝ → ℝ) (C t : ℝ) :
    conj (compactCutoffPVCorrection κ C t) =
      -compactCutoffPVCorrection κ C t := by
  unfold compactCutoffPVCorrection
  simp only [map_mul, map_neg, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal]
  ring

theorem conj_fixedAwayPVTransform (κ : ℝ → ℝ) (C t : ℝ) :
    conj (fixedAwayPVTransform κ C t) =
      -fixedAwayPVTransform κ C t := by
  simp only [fixedAwayPVTransform, map_sub, conj_signedExponentialPV,
    conj_compactCutoffPVCorrection]
  ring

theorem fixedAwayPVTransform_neg_eq_conj
    (κ : ℝ → ℝ) (C t : ℝ) :
    fixedAwayPVTransform κ C (-t) =
      conj (fixedAwayPVTransform κ C t) := by
  rw [fixedAwayPVTransform_neg, conj_fixedAwayPVTransform]

theorem abs_compactCutoffPairedSine_le
    (κ : ℝ → ℝ) {M : ℝ} (C t : ℝ)
    (hκ : ∀ v ∈ uIoc (0 : ℝ) C, |κ v| ≤ M) :
    |compactCutoffPairedSine κ C t| ≤
      (M * |2 * Real.pi * t|) * |C| := by
  unfold compactCutoffPairedSine
  have hpoint : ∀ v ∈ uIoc (0 : ℝ) C,
      ‖κ v * ((2 * Real.pi * t) *
        Real.sinc ((2 * Real.pi * t) * v))‖ ≤
          M * |2 * Real.pi * t| := by
    intro v hv
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hsinc : |Real.sinc ((2 * Real.pi * t) * v)| ≤ 1 :=
      Real.abs_sinc_le_one _
    have hfreq : 0 ≤ |2 * Real.pi * t| := abs_nonneg _
    have hkernel : 0 ≤ |2 * Real.pi * t| * 1 :=
      mul_nonneg hfreq zero_le_one
    calc
      |κ v| * (|2 * Real.pi * t| *
          |Real.sinc ((2 * Real.pi * t) * v)|) ≤
        |κ v| * (|2 * Real.pi * t| * 1) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsinc hfreq) (abs_nonneg _)
      _ ≤ M * (|2 * Real.pi * t| * 1) := by
          exact mul_le_mul_of_nonneg_right (hκ v hv) hkernel
      _ = M * |2 * Real.pi * t| := by ring
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simpa only [Real.norm_eq_abs, sub_zero] using! h

theorem norm_compactCutoffPVCorrection_le
    (κ : ℝ → ℝ) {M : ℝ} (C t : ℝ)
    (hκ : ∀ v ∈ uIoc (0 : ℝ) C, |κ v| ≤ M) :
    ‖compactCutoffPVCorrection κ C t‖ ≤
      2 * ((M * |2 * Real.pi * t|) * |C|) := by
  unfold compactCutoffPVCorrection
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hconst : ‖(-2 : ℂ) * Complex.I‖ = 2 := by norm_num
  rw [hconst]
  gcongr
  exact abs_compactCutoffPairedSine_le κ C t hκ

theorem tendsto_compactCutoffPVCorrection_zero
    (κ : ℝ → ℝ) {M : ℝ} (C : ℝ)
    (hκ : ∀ v ∈ uIoc (0 : ℝ) C, |κ v| ≤ M) :
    Tendsto (compactCutoffPVCorrection κ C) (nhds 0) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun t ↦ norm_nonneg _)
    (fun t ↦ norm_compactCutoffPVCorrection_le κ C t hκ)
  have hcont : ContinuousAt
      (fun t : ℝ ↦ 2 * ((M * |2 * Real.pi * t|) * |C|)) 0 := by
    fun_prop
  simpa using! hcont.tendsto

theorem tendsto_fixedAwayPVTransform_nhdsGT_zero
    (κ : ℝ → ℝ) {M : ℝ} (C : ℝ)
    (hκ : ∀ v ∈ uIoc (0 : ℝ) C, |κ v| ≤ M) :
    Tendsto (fixedAwayPVTransform κ C) (𝓝[>] 0)
      (nhds (-Complex.I * Real.pi)) := by
  have hsigned : Tendsto signedExponentialPV (𝓝[>] 0)
      (nhds (-Complex.I * Real.pi)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    simp [signedExponentialPV, htpos]
  have hcorr : Tendsto (compactCutoffPVCorrection κ C) (𝓝[>] 0)
      (nhds 0) := tendsto_nhdsWithin_of_tendsto_nhds
        (tendsto_compactCutoffPVCorrection_zero κ C hκ)
  simpa only [fixedAwayPVTransform, sub_zero] using! hsigned.sub hcorr

theorem tendsto_fixedAwayPVTransform_nhdsLT_zero
    (κ : ℝ → ℝ) {M : ℝ} (C : ℝ)
    (hκ : ∀ v ∈ uIoc (0 : ℝ) C, |κ v| ≤ M) :
    Tendsto (fixedAwayPVTransform κ C) (𝓝[<] 0)
      (nhds (Complex.I * Real.pi)) := by
  have hsigned : Tendsto signedExponentialPV (𝓝[<] 0)
      (nhds (Complex.I * Real.pi)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htneg : t < 0 := ht
    simp [signedExponentialPV, htneg, not_lt.mpr htneg.le]
  have hcorr : Tendsto (compactCutoffPVCorrection κ C) (𝓝[<] 0)
      (nhds 0) := tendsto_nhdsWithin_of_tendsto_nhds
        (tendsto_compactCutoffPVCorrection_zero κ C hκ)
  simpa only [fixedAwayPVTransform, sub_zero] using! hsigned.sub hcorr

end

end Erdos1002
