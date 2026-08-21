import ErdosProblems.Erdos228.Kernel
import ErdosProblems.Erdos228.KernelClaims

/-!
# The removable denominator-replacement amplitude

This file supplies the analytic ingredient in Claim 2 of the odd-kernel
argument.  The function `1 / sin u - 1 / u` is extended continuously at the
origin by writing it as the divided slope of the inverse sinc function.  On
`[-pi / 2, pi / 2]` the resulting function has nonnegative derivative, and
its total endpoint variation is exactly `2 - 4 / pi`.
-/

namespace Erdos228.KernelReplacementMonotone

open Real Set

noncomputable section

/-- The analytic extension at zero of `1 / sin u - 1 / u`. -/
def replacementAmplitude : ℝ → ℝ :=
  dslope (fun u : ℝ ↦ (Real.sinc u)⁻¹) 0

@[simp] theorem replacementAmplitude_zero : replacementAmplitude 0 = 0 := by
  rw [replacementAmplitude, dslope_same]
  have hsinc : AnalyticAt ℝ Real.sinc 0 := by
    rw [Real.sinc_eq_dslope]
    exact Real.analyticAt_sin.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt
  have hinv : DifferentiableAt ℝ (fun u : ℝ ↦ (Real.sinc u)⁻¹) 0 :=
    (hsinc.inv (by simp)).differentiableAt
  let d := deriv (fun u : ℝ ↦ (Real.sinc u)⁻¹) 0
  have hd : HasDerivAt (fun u : ℝ ↦ (Real.sinc u)⁻¹) d 0 := hinv.hasDerivAt
  have hdneg : HasDerivAt (fun u : ℝ ↦ (Real.sinc (-u))⁻¹) (-d) 0 := by
    have hcomp := HasDerivAt.comp_of_eq (x := (0 : ℝ)) hd
      (hasDerivAt_neg 0) (by simp)
    simpa [d, Function.comp_def] using hcomp
  have hdneg' : HasDerivAt (fun u : ℝ ↦ (Real.sinc u)⁻¹) (-d) 0 := by
    simpa only [Real.sinc_neg] using hdneg
  have := hd.unique hdneg'
  dsimp [d] at this ⊢
  linarith

/-- Away from the removable singularity, the extension is the original
denominator-replacement amplitude. -/
theorem replacementAmplitude_eq {u : ℝ} (hu : u ≠ 0)
    (hsu : Real.sin u ≠ 0) :
    replacementAmplitude u = 1 / Real.sin u - 1 / u := by
  have hmul : u * replacementAmplitude u = (Real.sinc u)⁻¹ - 1 := by
    simpa [replacementAmplitude] using
      (sub_smul_dslope (fun x : ℝ ↦ (Real.sinc x)⁻¹) 0 u)
  apply (mul_left_cancel₀ hu)
  rw [hmul, Real.sinc_of_ne_zero hu]
  field_simp [hu, hsu]

private lemma analyticAt_sinc_zero : AnalyticAt ℝ Real.sinc 0 := by
  rw [Real.sinc_eq_dslope]
  exact Real.analyticAt_sin.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt

theorem analyticAt_replacementAmplitude_zero :
    AnalyticAt ℝ replacementAmplitude 0 := by
  have hinv : AnalyticAt ℝ (fun u : ℝ ↦ (Real.sinc u)⁻¹) 0 :=
    analyticAt_sinc_zero.inv (by simp)
  exact hinv.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt

theorem sin_ne_zero_of_mem_half {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hu0 : u ≠ 0) : Real.sin u ≠ 0 := by
  intro hsu
  apply hu0
  exact (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [hu.1, Real.pi_pos])
    (by linarith [hu.2, Real.pi_pos])).mp hsu

theorem analyticAt_replacementAmplitude {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    AnalyticAt ℝ replacementAmplitude u := by
  by_cases hu0 : u = 0
  · simpa [hu0] using analyticAt_replacementAmplitude_zero
  have hsu := sin_ne_zero_of_mem_half hu hu0
  have hrhs : AnalyticAt ℝ (fun x : ℝ ↦ 1 / Real.sin x - 1 / x) u := by
    fun_prop
  apply hrhs.congr
  filter_upwards [eventually_ne_nhds hu0,
      (Real.continuous_sin.tendsto u) (isOpen_ne.mem_nhds hsu)] with x hx0 hsx
  exact (replacementAmplitude_eq hx0 hsx).symm

theorem differentiableAt_replacementAmplitude {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    DifferentiableAt ℝ replacementAmplitude u :=
  (analyticAt_replacementAmplitude hu).differentiableAt

theorem hasDerivAt_replacementAmplitude {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt replacementAmplitude (deriv replacementAmplitude u) u :=
  (differentiableAt_replacementAmplitude hu).hasDerivAt

theorem replacementAmplitude_mul_self_nonneg {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    0 ≤ replacementAmplitude u * u := by
  rcases lt_trichotomy u 0 with hu0 | rfl | hu0
  · have hsu : Real.sin u < 0 := by
      rw [← neg_pos, ← Real.sin_neg]
      exact Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hu0)
        (by linarith [hu.1, Real.pi_pos])
    rw [replacementAmplitude_eq hu0.ne (ne_of_lt hsu)]
    have hsle : u ≤ Real.sin u := by
      have := Real.sin_le (show 0 ≤ -u by linarith)
      rw [Real.sin_neg] at this
      linarith
    rw [show (1 / Real.sin u - 1 / u) * u =
        (u - Real.sin u) / Real.sin u by
      field_simp [hu0.ne, ne_of_lt hsu]
      ]
    exact div_nonneg_of_nonpos (sub_nonpos.mpr hsle) hsu.le
  · simp
  · have hsu : 0 < Real.sin u :=
      Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [hu.2, Real.pi_pos])
    rw [replacementAmplitude_eq hu0.ne' (ne_of_gt hsu)]
    have hsle := Real.sin_le hu0.le
    rw [show (1 / Real.sin u - 1 / u) * u =
        (u - Real.sin u) / Real.sin u by
      field_simp [hu0.ne', ne_of_gt hsu]
      ]
    exact div_nonneg (sub_nonneg.mpr hsle) hsu.le

/-- The derivative is nonnegative throughout the closed half-period.  At
zero this follows from the divided-slope limit; away from zero it reduces to
`u² cos u ≤ sin² u`. -/
theorem deriv_replacementAmplitude_nonneg {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    0 ≤ deriv replacementAmplitude u := by
  by_cases hu0 : u = 0
  · subst u
    have hd := analyticAt_replacementAmplitude_zero.differentiableAt.hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope] at hd
    apply ge_of_tendsto hd
    have hIcc : Icc (-(Real.pi / 2)) (Real.pi / 2) ∈ nhds (0 : ℝ) :=
      Icc_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have hIcc' : Icc (-(Real.pi / 2)) (Real.pi / 2) ∈
        nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ :=
      mem_nhdsWithin_of_mem_nhds hIcc
    filter_upwards [self_mem_nhdsWithin, hIcc'] with x hx hxmem
    have hx0 : x ≠ 0 := by simpa using hx
    simp only [slope, replacementAmplitude_zero, sub_zero, vsub_eq_sub,
      smul_eq_mul]
    rw [show x⁻¹ * replacementAmplitude x =
        (replacementAmplitude x * x) / x ^ 2 by
      field_simp [hx0]
      ]
    exact div_nonneg (replacementAmplitude_mul_self_nonneg hxmem) (sq_nonneg x)
  · have hsu := sin_ne_zero_of_mem_half hu hu0
    have heq : replacementAmplitude =ᶠ[nhds u]
        (fun x : ℝ ↦ 1 / Real.sin x - 1 / x) := by
      filter_upwards [eventually_ne_nhds hu0,
        (Real.continuous_sin.tendsto u) (isOpen_ne.mem_nhds hsu)] with x hx0 hsx
      exact replacementAmplitude_eq hx0 hsx
    have hbase := ((Real.hasDerivAt_sin u).inv hsu).sub
      ((hasDerivAt_id u).inv hu0)
    have hbase' : HasDerivAt (fun x : ℝ ↦ 1 / Real.sin x - 1 / x)
        (1 / u ^ 2 - Real.cos u / Real.sin u ^ 2) u := by
      have hfun : (fun x : ℝ ↦ 1 / Real.sin x - 1 / x) =
          Real.sin⁻¹ - id⁻¹ := by
        funext x
        simp only [one_div, Pi.sub_apply, Pi.inv_apply, id_eq]
      have hcoef : 1 / u ^ 2 - Real.cos u / Real.sin u ^ 2 =
          -Real.cos u / Real.sin u ^ 2 - -1 / id u ^ 2 := by
        simp only [id_eq]
        ring
      rw [hfun, hcoef]
      exact hbase
    have hderiv : HasDerivAt replacementAmplitude
        (1 / u ^ 2 - Real.cos u / Real.sin u ^ 2) u := by
      exact heq.hasDerivAt_iff.mpr hbase'
    rw [hderiv.deriv]
    have habs : |u| ≤ Real.pi / 2 := (abs_le).2 hu
    have hcos0 : 0 ≤ Real.cos u := Real.cos_nonneg_of_mem_Icc hu
    have hsin_sq : u ^ 2 * Real.cos u ≤ Real.sin u ^ 2 := by
      have ht0 : 0 ≤ |u| := abs_nonneg u
      have ht2 : |u| < 2 := by
        exact lt_of_le_of_lt habs (by linarith [Real.pi_lt_four])
      have htsq : |u| ^ 2 < (2 : ℝ) ^ 2 :=
        (sq_lt_sq₀ ht0 (by norm_num)).2 ht2
      have hsmall : |u| ^ 2 ≤ 12 := by norm_num at htsq ⊢; linarith
      have hslo := Real.sin_ge_sub_cube (abs_nonneg u)
      have hcosup := Erdos228.Kernel.cos_le_taylor_four (abs_nonneg u)
      rw [Real.cos_abs] at hcosup
      have hbase : 0 ≤ |u| - |u| ^ 3 / 6 := by
        rw [show |u| - |u| ^ 3 / 6 = |u| * (1 - |u| ^ 2 / 6) by ring]
        exact mul_nonneg ht0 (by nlinarith [htsq])
      have habspi : |u| ≤ Real.pi := by linarith [habs, Real.pi_pos]
      have hsine0 : 0 ≤ Real.sin |u| :=
        Real.sin_nonneg_of_nonneg_of_le_pi ht0 habspi
      have hsloSq : (|u| - |u| ^ 3 / 6) ^ 2 ≤ Real.sin |u| ^ 2 :=
        (sq_le_sq₀ hbase hsine0).2 hslo
      have habssin := Real.abs_sin_eq_sin_abs_of_abs_le_pi habspi
      have hsinSqEq : Real.sin |u| ^ 2 = Real.sin u ^ 2 := by
        rw [← habssin, sq_abs]
      have hcosmult : |u| ^ 2 * Real.cos u ≤
          |u| ^ 2 * (1 - |u| ^ 2 / 2 + |u| ^ 4 / 24) :=
        mul_le_mul_of_nonneg_left hcosup (sq_nonneg |u|)
      have hprod : 0 ≤ |u| ^ 4 * (12 - |u| ^ 2) :=
        mul_nonneg (pow_nonneg ht0 4) (sub_nonneg.mpr hsmall)
      have hpoly : |u| ^ 2 * (1 - |u| ^ 2 / 2 + |u| ^ 4 / 24) ≤
          (|u| - |u| ^ 3 / 6) ^ 2 := by
        nlinarith
      rw [← sq_abs u, ← hsinSqEq]
      exact hcosmult.trans (hpoly.trans hsloSq)
    have hden : 0 < u ^ 2 * Real.sin u ^ 2 :=
      mul_pos (sq_pos_of_ne_zero hu0) (sq_pos_of_ne_zero hsu)
    rw [show 1 / u ^ 2 - Real.cos u / Real.sin u ^ 2 =
        (Real.sin u ^ 2 - u ^ 2 * Real.cos u) /
          (u ^ 2 * Real.sin u ^ 2) by
      field_simp [hu0, hsu]
      ]
    exact div_nonneg (sub_nonneg.mpr hsin_sq) hden.le

/-- The derivative data in precisely the form used by the smooth grid
oscillation estimate. -/
theorem replacementAmplitude_derivative_data :
    (∀ u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivAt replacementAmplitude (deriv replacementAmplitude u) u) ∧
    ContinuousOn (deriv replacementAmplitude)
      (Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
    (∀ u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2),
      0 ≤ deriv replacementAmplitude u) := by
  refine ⟨fun u hu ↦ hasDerivAt_replacementAmplitude hu, ?_,
    fun u hu ↦ deriv_replacementAmplitude_nonneg hu⟩
  intro u hu
  exact (analyticAt_replacementAmplitude hu).deriv.continuousAt.continuousWithinAt

theorem monotoneOn_replacementAmplitude :
    MonotoneOn replacementAmplitude
      (Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun u hu ↦
      (analyticAt_replacementAmplitude hu).continuousAt.continuousWithinAt
  · exact fun u hu ↦
      (differentiableAt_replacementAmplitude (interior_subset hu)).differentiableWithinAt
  · intro u hu
    exact deriv_replacementAmplitude_nonneg (interior_subset hu)

@[simp] theorem replacementAmplitude_pi_div_two :
    replacementAmplitude (Real.pi / 2) = 1 - 2 / Real.pi := by
  rw [replacementAmplitude_eq (by positivity) (by simp), Real.sin_pi_div_two]
  field_simp [Real.pi_ne_zero]

@[simp] theorem replacementAmplitude_neg_pi_div_two :
    replacementAmplitude (-(Real.pi / 2)) = -(1 - 2 / Real.pi) := by
  rw [replacementAmplitude_eq
      (neg_ne_zero.mpr (div_ne_zero Real.pi_ne_zero (by norm_num))) (by simp), Real.sin_neg,
    Real.sin_pi_div_two]
  field_simp [Real.pi_ne_zero]
  ring

/-- The total variation used after telescoping all Claim-2 intervals. -/
theorem replacementAmplitude_endpoint_variation :
    replacementAmplitude (Real.pi / 2) -
      replacementAmplitude (-(Real.pi / 2)) = 2 - 4 / Real.pi := by
  rw [replacementAmplitude_pi_div_two, replacementAmplitude_neg_pi_div_two]
  ring

end

end Erdos228.KernelReplacementMonotone
