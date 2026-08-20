/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos783.GSConvolution
import ErdosProblems.Erdos783.GSMoments

/-! # Local convolution calculus for the GS moments -/

open MeasureTheory Set
open scoped Convolution

namespace Erdos783

noncomputable section

def gsStepLocal (K : ℝ) : ℝ → ℝ :=
  gsLocalize K (fun _t : ℝ ↦ 1)

def gsDefectLocal (chi : ℝ → ℝ) (K : ℝ) : ℝ → ℝ :=
  gsLocalize K (gsDefectWeight chi)

def gsWeightedDefectLocal (chi : ℝ → ℝ) (K : ℝ) : ℝ → ℝ :=
  gsLocalize K (fun t ↦ t * gsDefectWeight chi t)

def gsKernelLocal (chi : ℝ → ℝ) (K : ℝ) : ℝ → ℝ :=
  gsLocalize K chi

def gsMomentLocal (chi : ℝ → ℝ) (K : ℝ) (n : ℕ) : ℝ → ℝ :=
  gsLocalize K (gsMoment chi n)

def gsCoordMomentLocal (chi : ℝ → ℝ) (K : ℝ) (n : ℕ) : ℝ → ℝ :=
  gsLocalize K (fun t ↦ t * gsMoment chi n t)

lemma gsLocalize_eq_zero_of_nonpos (K : ℝ) (f : ℝ → ℝ)
    {t : ℝ} (ht : t ≤ 0) : gsLocalize K f t = 0 := by
  simp [gsLocalize, not_lt_of_ge ht]

lemma gsStepLocal_nonpos (K : ℝ) {t : ℝ} (ht : t ≤ 0) :
    gsStepLocal K t = 0 := gsLocalize_eq_zero_of_nonpos K _ ht

lemma gsDefectLocal_nonpos (chi : ℝ → ℝ) (K : ℝ) {t : ℝ} (ht : t ≤ 0) :
    gsDefectLocal chi K t = 0 := gsLocalize_eq_zero_of_nonpos K _ ht

lemma gsWeightedDefectLocal_nonpos (chi : ℝ → ℝ) (K : ℝ)
    {t : ℝ} (ht : t ≤ 0) :
    gsWeightedDefectLocal chi K t = 0 :=
  gsLocalize_eq_zero_of_nonpos K _ ht

lemma gsKernelLocal_nonpos (chi : ℝ → ℝ) (K : ℝ)
    {t : ℝ} (ht : t ≤ 0) : gsKernelLocal chi K t = 0 :=
  gsLocalize_eq_zero_of_nonpos K _ ht

lemma gsMomentLocal_nonpos (chi : ℝ → ℝ) (K : ℝ) (n : ℕ)
    {t : ℝ} (ht : t ≤ 0) : gsMomentLocal chi K n t = 0 :=
  gsLocalize_eq_zero_of_nonpos K _ ht

lemma gsCoordMomentLocal_nonpos (chi : ℝ → ℝ) (K : ℝ) (n : ℕ)
    {t : ℝ} (ht : t ≤ 0) : gsCoordMomentLocal chi K n t = 0 :=
  gsLocalize_eq_zero_of_nonpos K _ ht

lemma intervalIntegrable_gsMoment
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {K : ℝ} (hK : 0 ≤ K) :
    IntervalIntegrable (gsMoment chi n) volume 0 K := by
  apply MonotoneOn.intervalIntegrable
  rw [uIcc_of_le hK]
  exact (gsMoment_mono_Ici_zero hchi n).mono Icc_subset_Ici_self

lemma integrable_gsLocalize_moment
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {K : ℝ} (hK : 0 ≤ K) :
    Integrable (gsLocalize K (gsMoment chi n)) :=
  integrable_gsLocalize hK (intervalIntegrable_gsMoment hchi n hK)

lemma integrable_gsMomentLocal
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {K : ℝ} (hK : 0 ≤ K) : Integrable (gsMomentLocal chi K n) := by
  exact integrable_gsLocalize_moment hchi n hK

lemma integrable_gsStepLocal {K : ℝ} (hK : 0 ≤ K) :
    Integrable (gsStepLocal K) := by
  exact integrable_gsLocalize hK intervalIntegrable_const

lemma measurable_gsLocalize_moment
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ) (K : ℝ) :
    Measurable (gsLocalize K (gsMoment chi n)) := by
  let mext : ℝ → ℝ := fun x ↦ gsMoment chi n (max 0 x)
  have hmextMono : Monotone mext := by
    intro a b hab
    apply gsMoment_mono_Ici_zero hchi n
    · exact mem_Ici.mpr (le_max_left _ _)
    · exact mem_Ici.mpr (le_max_left _ _)
    · exact max_le_max le_rfl hab
  have hmext : Measurable mext := hmextMono.measurable
  have heq : gsLocalize K (gsMoment chi n) =
      (Ioo (0 : ℝ) K).indicator mext := by
    funext x
    by_cases hx : x ∈ Ioo (0 : ℝ) K
    · simp [gsLocalize, mext, hx, max_eq_right hx.1.le]
    · simp [gsLocalize, hx]
  rw [heq]
  exact hmext.indicator measurableSet_Ioo

lemma gsLocalize_moment_bound
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {K : ℝ} (hK : 1 ≤ K) (x : ℝ) :
    ‖gsLocalize K (gsMoment chi n) x‖ ≤ gsLogScale chi K ^ n := by
  by_cases hx : x ∈ Ioo (0 : ℝ) K
  · rw [gsLocalize, indicator_of_mem hx, Real.norm_eq_abs,
      abs_of_nonneg (gsMoment_nonneg hchi n hx.1.le)]
    exact (gsMoment_mono_Ici_zero hchi n
        (mem_Ici.mpr hx.1.le) (mem_Ici.mpr (zero_le_one.trans hK)) hx.2.le).trans
      (gsMoment_le_logScale_pow hchi n hK)
  · simp [gsLocalize, hx, pow_nonneg (gsLogScale_nonneg hchi hK)]

lemma intervalIntegrable_gsDefectWeight_zero
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) :
    IntervalIntegrable (gsDefectWeight chi) volume 0 1 := by
  have hz : IntervalIntegrable (fun _t : ℝ ↦ (0 : ℝ)) volume 0 1 :=
    intervalIntegrable_const
  apply hz.congr
  intro t ht
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  simp [gsDefectWeight, hchi.2.2.2 t ht.1.le ht.2]

lemma intervalIntegrable_gsDefectWeight_zero_to
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {K : ℝ} (hK : 1 ≤ K) :
    IntervalIntegrable (gsDefectWeight chi) volume 0 K := by
  rw [intervalIntegrable_iff]
  rw [uIoc_of_le (zero_le_one.trans hK)]
  have hleft := (intervalIntegrable_gsDefectWeight_zero hchi).1
  have hright := (intervalIntegrable_gsDefectKernel hchi zero_lt_one hK).1
  convert IntegrableOn.union hleft hright using 1
  rw [Ioc_union_Ioc_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1) hK]

lemma integrable_gsLocalize_defectWeight
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {K : ℝ} (hK : 1 ≤ K) :
    Integrable (gsLocalize K (gsDefectWeight chi)) :=
  integrable_gsLocalize (zero_le_one.trans hK)
    (intervalIntegrable_gsDefectWeight_zero_to hchi hK)

lemma integrable_gsDefectLocal
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {K : ℝ} (hK : 1 ≤ K) : Integrable (gsDefectLocal chi K) := by
  exact integrable_gsLocalize_defectWeight hchi hK

lemma intervalIntegrable_gsWeightedDefect
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {K : ℝ} (hK : 1 ≤ K) :
    IntervalIntegrable (fun t ↦ t * gsDefectWeight chi t) volume 0 K := by
  have h := (intervalIntegrable_gsDefectWeight_zero_to hchi hK).mul_continuousOn
    continuousOn_id
  convert h using 1
  ext t
  simp [id, mul_comm]

lemma integrable_gsWeightedDefectLocal
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {K : ℝ} (hK : 1 ≤ K) :
    Integrable (gsWeightedDefectLocal chi K) := by
  exact integrable_gsLocalize (zero_le_one.trans hK)
    (intervalIntegrable_gsWeightedDefect hchi hK)

lemma integrable_gsKernelLocal
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {K : ℝ} (hK : 0 ≤ K) : Integrable (gsKernelLocal chi K) := by
  exact integrable_gsLocalize hK (hchi.1 0 K)

lemma intervalIntegrable_gsCoordMoment
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {K : ℝ} (hK : 0 ≤ K) :
    IntervalIntegrable (fun t ↦ t * gsMoment chi n t) volume 0 K := by
  have h := (intervalIntegrable_gsMoment hchi n hK).mul_continuousOn
    continuousOn_id
  convert h using 1
  ext t
  simp [id, mul_comm]

lemma integrable_gsCoordMomentLocal
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {K : ℝ} (hK : 0 ≤ K) :
    Integrable (gsCoordMomentLocal chi K n) := by
  exact integrable_gsLocalize hK
    (intervalIntegrable_gsCoordMoment hchi n hK)

lemma gsStepLocal_bound (K x : ℝ) : ‖gsStepLocal K x‖ ≤ 1 := by
  by_cases hx : x ∈ Ioo (0 : ℝ) K <;> simp [gsStepLocal, gsLocalize, hx]

lemma gsDefectLocal_bound
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (K x : ℝ) :
    ‖gsDefectLocal chi K x‖ ≤ 1 := by
  by_cases hx : x ∈ Ioo (0 : ℝ) K
  · rw [gsDefectLocal, gsLocalize, indicator_of_mem hx, Real.norm_eq_abs]
    by_cases hx1 : x ≤ 1
    · rw [show gsDefectWeight chi x = 0 by
        simp [gsDefectWeight, hchi.2.2.2 x hx.1.le hx1]]
      simp
    · have hxone : 1 ≤ x := (lt_of_not_ge hx1).le
      have hnonneg : 0 ≤ gsDefectWeight chi x :=
        gsDefectWeight_nonneg hchi hxone
      rw [abs_of_nonneg hnonneg]
      apply (div_le_one (zero_lt_one.trans_le hxone)).mpr
      have hchi0 := hchi.2.1 x hx.1.le
      linarith
  · simp [gsDefectLocal, gsLocalize, hx]

lemma gsWeightedDefectLocal_bound
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (K x : ℝ) :
    ‖gsWeightedDefectLocal chi K x‖ ≤ 1 := by
  by_cases hx : x ∈ Ioo (0 : ℝ) K
  · rw [gsWeightedDefectLocal, gsLocalize, indicator_of_mem hx,
      Real.norm_eq_abs]
    have hxne : x ≠ 0 := hx.1.ne'
    have heq : x * gsDefectWeight chi x = 1 - chi x := by
      unfold gsDefectWeight
      field_simp
    rw [heq, abs_of_nonneg (sub_nonneg.mpr (hchi.2.2.1 x hx.1.le))]
    linarith [hchi.2.1 x hx.1.le]
  · simp [gsWeightedDefectLocal, gsLocalize, hx]

lemma gsKernelLocal_bound
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (K x : ℝ) :
    ‖gsKernelLocal chi K x‖ ≤ 1 := by
  by_cases hx : x ∈ Ioo (0 : ℝ) K
  · rw [gsKernelLocal, gsLocalize, indicator_of_mem hx,
      Real.norm_eq_abs, abs_of_nonneg (hchi.2.1 x hx.1.le)]
    exact hchi.2.2.1 x hx.1.le
  · simp [gsKernelLocal, gsLocalize, hx]

lemma gsKernelLocal_eq_step_sub_weighted
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (K : ℝ) :
    gsKernelLocal chi K = gsStepLocal K - gsWeightedDefectLocal chi K := by
  funext t
  by_cases ht : t ∈ Ioo (0 : ℝ) K
  · have htne : t ≠ 0 := ht.1.ne'
    simp only [gsKernelLocal, gsStepLocal, gsWeightedDefectLocal,
      gsLocalize, indicator_of_mem ht, Pi.sub_apply]
    unfold gsDefectWeight
    field_simp
    ring
  · simp [gsKernelLocal, gsStepLocal, gsWeightedDefectLocal,
      gsLocalize, ht]

lemma gsMomentLocal_bound
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {K : ℝ} (hK : 1 ≤ K) (x : ℝ) :
    ‖gsMomentLocal chi K n x‖ ≤ gsLogScale chi K ^ n := by
  exact gsLocalize_moment_bound hchi n hK x

lemma intervalIntegrable_gsDefect_mul_moment_zero_to
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {x : ℝ} (hx0 : 0 ≤ x) :
    IntervalIntegrable
      (fun t : ℝ ↦ gsDefectWeight chi t * gsMoment chi n (x - t))
      volume 0 x := by
  by_cases hx1 : 1 ≤ x
  · have hleft : IntervalIntegrable
        (fun t : ℝ ↦ gsDefectWeight chi t * gsMoment chi n (x - t))
        volume 0 1 := by
      have hz : IntervalIntegrable (fun _t : ℝ ↦ (0 : ℝ)) volume 0 1 :=
        intervalIntegrable_const
      apply hz.congr
      intro t ht
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      simp [gsDefectWeight, hchi.2.2.2 t ht.1.le ht.2]
    have hright := intervalIntegrable_gsDefect_mul_moment hchi n hx1
    rw [intervalIntegrable_iff, uIoc_of_le hx0]
    have hleft' := hleft.1
    have hright' := hright.1
    convert IntegrableOn.union hleft' hright' using 1
    rw [Ioc_union_Ioc_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1) hx1]
  · have hz : IntervalIntegrable (fun _t : ℝ ↦ (0 : ℝ)) volume 0 x :=
      intervalIntegrable_const
    apply hz.congr
    intro t ht
    rw [uIoc_of_le hx0] at ht
    have ht1 : t ≤ 1 := ht.2.trans (le_of_not_ge hx1)
    simp [gsDefectWeight, hchi.2.2.2 t ht.1.le ht1]

/-- The recursive GS moment is convolution by the defect density, after
compact localization. -/
lemma gsLocalize_defect_convolution_moment
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {K x : ℝ} (hx0 : 0 ≤ x) (hxK : x < K) :
    ((gsLocalize K (gsDefectWeight chi)) ⋆[ContinuousLinearMap.mul ℝ ℝ]
        (gsLocalize K (gsMoment chi n))) x =
      gsMoment chi (n + 1) x := by
  rw [gsLocalize_convolution_apply hx0 hxK]
  by_cases hx1 : 1 ≤ x
  · rw [gsMoment, if_pos hx1]
    have hleft : IntervalIntegrable
        (fun t : ℝ ↦ gsDefectWeight chi t * gsMoment chi n (x - t))
        volume 0 1 := by
      have hz : IntervalIntegrable (fun _t : ℝ ↦ (0 : ℝ)) volume 0 1 :=
        intervalIntegrable_const
      apply hz.congr
      intro t ht
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      simp [gsDefectWeight, hchi.2.2.2 t ht.1.le ht.2]
    have hright := intervalIntegrable_gsDefect_mul_moment hchi n hx1
    have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
    rw [show (∫ t : ℝ in 0..1,
        gsDefectWeight chi t * gsMoment chi n (x - t)) = 0 by
      rw [show (∫ t : ℝ in 0..1,
          gsDefectWeight chi t * gsMoment chi n (x - t)) =
          ∫ _t : ℝ in 0..1, (0 : ℝ) by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        simp [gsDefectWeight, hchi.2.2.2 t ht.1 ht.2]]
      simp] at hadd
    linarith
  · rw [gsMoment, if_neg hx1]
    rw [show (∫ t : ℝ in 0..x,
        gsDefectWeight chi t * gsMoment chi n (x - t)) = 0 by
      rw [show (∫ t : ℝ in 0..x,
          gsDefectWeight chi t * gsMoment chi n (x - t)) =
          ∫ _t : ℝ in 0..x, (0 : ℝ) by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hx0] at ht
        have ht1 : t ≤ 1 := ht.2.trans (le_of_not_ge hx1)
        simp [gsDefectWeight, hchi.2.2.2 t ht.1 ht1]]
      simp]

lemma gsDefectLocal_convolution_momentLocal
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {K x : ℝ} (hx0 : 0 ≤ x) (hxK : x < K) :
    (gsDefectLocal chi K ⋆[ContinuousLinearMap.mul ℝ ℝ]
        gsMomentLocal chi K n) x = gsMoment chi (n + 1) x := by
  exact gsLocalize_defect_convolution_moment hchi n hx0 hxK

lemma gsMomentLocal_succ_eq_defect_convolution_on_Icc
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {K x : ℝ} (hx0 : 0 ≤ x) (hxK : x < K) :
    ∀ y ∈ Icc (0 : ℝ) x,
      gsMomentLocal chi K (n + 1) y =
        (gsDefectLocal chi K ⋆[ContinuousLinearMap.mul ℝ ℝ]
          gsMomentLocal chi K n) y := by
  intro y hy
  have hyK : y < K := hy.2.trans_lt hxK
  have hrec := gsDefectLocal_convolution_momentLocal hchi n hy.1 hyK
  by_cases hyzero : y = 0
  · subst y
    have hmzero : gsMoment chi (n + 1) 0 = 0 := by
      rw [gsMoment]
      norm_num
    rw [hmzero] at hrec
    simpa [gsMomentLocal, gsLocalize] using hrec.symm
  · have hypos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hyzero)
    rw [gsMomentLocal, gsLocalize,
      indicator_of_mem (show y ∈ Ioo (0 : ℝ) K from ⟨hypos, hyK⟩)]
    exact hrec.symm

lemma gs_outer_convolution_momentLocal_succ
    {chi outer : ℝ → ℝ} (hchi : IsGSKernel chi)
    (houter : ∀ t : ℝ, t ≤ 0 → outer t = 0) (n : ℕ)
    {K x : ℝ} (hx0 : 0 ≤ x) (hxK : x < K) :
    (outer ⋆[ContinuousLinearMap.mul ℝ ℝ]
        gsMomentLocal chi K (n + 1)) x =
      (outer ⋆[ContinuousLinearMap.mul ℝ ℝ]
        (gsDefectLocal chi K ⋆[ContinuousLinearMap.mul ℝ ℝ]
          gsMomentLocal chi K n)) x := by
  apply gs_convolution_congr_Icc houter
    (fun _t ht ↦ gsMomentLocal_nonpos chi K (n + 1) ht)
    (fun _t ht ↦ gs_convolution_eq_zero_of_nonpos
      (fun _s hs ↦ gsDefectLocal_nonpos chi K hs)
      (fun _s hs ↦ gsMomentLocal_nonpos chi K n hs) ht)
    hx0
  exact gsMomentLocal_succ_eq_defect_convolution_on_Icc hchi n hx0 hxK

/-- Multiplication by the endpoint coordinate splits between the newly
inserted defect variable and the residual moment. -/
lemma gs_moment_coordinate_identity
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {K x : ℝ} (hx0 : 0 ≤ x) (hxK : x < K) :
    x * gsMoment chi (n + 1) x =
      (gsWeightedDefectLocal chi K ⋆[ContinuousLinearMap.mul ℝ ℝ]
          gsMomentLocal chi K n) x +
        (gsDefectLocal chi K ⋆[ContinuousLinearMap.mul ℝ ℝ]
          gsCoordMomentLocal chi K n) x := by
  have hbase := intervalIntegrable_gsDefect_mul_moment_zero_to hchi n hx0
  have hleftRaw := hbase.mul_continuousOn continuousOn_id
  have hleft : IntervalIntegrable
      (fun t : ℝ ↦ (t * gsDefectWeight chi t) *
        gsMoment chi n (x - t)) volume 0 x := by
    convert hleftRaw using 1
    ext t
    simp [id]
    ring
  have hsubcont : ContinuousOn (fun t : ℝ ↦ x - t) (uIcc 0 x) :=
    continuousOn_const.sub continuousOn_id
  have hrightRaw := hbase.mul_continuousOn hsubcont
  have hright : IntervalIntegrable
      (fun t : ℝ ↦ gsDefectWeight chi t *
        ((x - t) * gsMoment chi n (x - t))) volume 0 x := by
    convert hrightRaw using 1
    ext t
    ring
  rw [← gsDefectLocal_convolution_momentLocal hchi n hx0 hxK]
  rw [gsDefectLocal, gsMomentLocal, gsWeightedDefectLocal,
    gsCoordMomentLocal,
    gsLocalize_convolution_apply hx0 hxK,
    gsLocalize_convolution_apply hx0 hxK,
    gsLocalize_convolution_apply hx0 hxK]
  exact gs_interval_convolution_coordinate
    (gsDefectWeight chi) (gsMoment chi n) hleft hright

/-- The coordinate-sum identity for the symmetric simplex moments.  In
convolution notation it says
`H * I_n + n (t w) * I_{n-1} = t I_n`. -/
theorem gs_step_convolution_moment_identity
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) :
    ∀ n : ℕ, ∀ {K x : ℝ}, 1 ≤ K → 0 ≤ x → x < K →
      (gsStepLocal K ⋆[ContinuousLinearMap.mul ℝ ℝ]
          gsMomentLocal chi K n) x +
        (n : ℝ) *
          (gsWeightedDefectLocal chi K ⋆[ContinuousLinearMap.mul ℝ ℝ]
            gsMomentLocal chi K n.pred) x =
        x * gsMoment chi n x := by
  intro n
  induction n with
  | zero =>
      intro K x hK hx0 hxK
      rw [Nat.cast_zero, zero_mul, add_zero, gsMoment_zero]
      change ((gsLocalize K (fun _t : ℝ ↦ 1)) ⋆[
        ContinuousLinearMap.mul ℝ ℝ]
        (gsLocalize K (fun _t : ℝ ↦ 1))) x = x * 1
      rw [gsLocalize_convolution_apply hx0 hxK]
      simp
  | succ n ih =>
      intro K x hK hx0 hxK
      let H : ℝ → ℝ := gsStepLocal K
      let W : ℝ → ℝ := gsDefectLocal chi K
      let D : ℝ → ℝ := gsWeightedDefectLocal chi K
      let Mn : ℝ → ℝ := gsMomentLocal chi K n
      let Mp : ℝ → ℝ := gsMomentLocal chi K n.pred
      let Ms : ℝ → ℝ := gsMomentLocal chi K (n + 1)
      let Cn : ℝ → ℝ := gsCoordMomentLocal chi K n
      let A : ℝ → ℝ := H ⋆[ContinuousLinearMap.mul ℝ ℝ] Mn
      let B : ℝ → ℝ := D ⋆[ContinuousLinearMap.mul ℝ ℝ] Mp
      let G : ℝ → ℝ := A + (n : ℝ) • B
      have hH : Integrable H := integrable_gsStepLocal (zero_le_one.trans hK)
      have hW : Integrable W := integrable_gsDefectLocal hchi hK
      have hD : Integrable D := integrable_gsWeightedDefectLocal hchi hK
      have hMn : Integrable Mn :=
        integrable_gsMomentLocal hchi n (zero_le_one.trans hK)
      have hMp : Integrable Mp :=
        integrable_gsMomentLocal hchi n.pred (zero_le_one.trans hK)
      have hMs : Integrable Ms :=
        integrable_gsMomentLocal hchi (n + 1) (zero_le_one.trans hK)
      have hCn : Integrable Cn :=
        integrable_gsCoordMomentLocal hchi n (zero_le_one.trans hK)
      have hMnbound : ∀ y : ℝ, ‖Mn y‖ ≤ gsLogScale chi K ^ n :=
        gsMomentLocal_bound hchi n hK
      have hMpbound : ∀ y : ℝ, ‖Mp y‖ ≤ gsLogScale chi K ^ n.pred :=
        gsMomentLocal_bound hchi n.pred hK
      have hreplaceH :
          (H ⋆[ContinuousLinearMap.mul ℝ ℝ] Ms) x =
            (H ⋆[ContinuousLinearMap.mul ℝ ℝ]
              (W ⋆[ContinuousLinearMap.mul ℝ ℝ] Mn)) x := by
        exact gs_outer_convolution_momentLocal_succ hchi
          (fun _t ht ↦ gsStepLocal_nonpos K ht) n hx0 hxK
      have hreplaceD :
          (n : ℝ) * (D ⋆[ContinuousLinearMap.mul ℝ ℝ] Mn) x =
            (n : ℝ) *
              (D ⋆[ContinuousLinearMap.mul ℝ ℝ]
                (W ⋆[ContinuousLinearMap.mul ℝ ℝ] Mp)) x := by
        cases n with
        | zero => simp
        | succ m =>
            congr 1
            exact gs_outer_convolution_momentLocal_succ hchi
              (fun _t ht ↦ gsWeightedDefectLocal_nonpos chi K ht)
              m hx0 hxK
      have hassocHW :
          (H ⋆[ContinuousLinearMap.mul ℝ ℝ]
              (W ⋆[ContinuousLinearMap.mul ℝ ℝ] Mn)) x =
            (W ⋆[ContinuousLinearMap.mul ℝ ℝ]
              (H ⋆[ContinuousLinearMap.mul ℝ ℝ] Mn)) x := by
        calc
          _ = ((H ⋆[ContinuousLinearMap.mul ℝ ℝ] W) ⋆[
                ContinuousLinearMap.mul ℝ ℝ] Mn) x :=
            (gs_convolution_assoc_of_integrable_bounded hH hW hMn
              hMnbound).symm
          _ = ((W ⋆[ContinuousLinearMap.mul ℝ ℝ] H) ⋆[
                ContinuousLinearMap.mul ℝ ℝ] Mn) x := by
            rw [gs_convolution_comm H W]
          _ = _ :=
            gs_convolution_assoc_of_integrable_bounded hW hH hMn hMnbound
      have hassocDW :
          (D ⋆[ContinuousLinearMap.mul ℝ ℝ]
              (W ⋆[ContinuousLinearMap.mul ℝ ℝ] Mp)) x =
            (W ⋆[ContinuousLinearMap.mul ℝ ℝ]
              (D ⋆[ContinuousLinearMap.mul ℝ ℝ] Mp)) x := by
        calc
          _ = ((D ⋆[ContinuousLinearMap.mul ℝ ℝ] W) ⋆[
                ContinuousLinearMap.mul ℝ ℝ] Mp) x :=
            (gs_convolution_assoc_of_integrable_bounded hD hW hMp
              hMpbound).symm
          _ = ((W ⋆[ContinuousLinearMap.mul ℝ ℝ] D) ⋆[
                ContinuousLinearMap.mul ℝ ℝ] Mp) x := by
            rw [gs_convolution_comm D W]
          _ = _ :=
            gs_convolution_assoc_of_integrable_bounded hW hD hMp hMpbound
      have hAint : Integrable A := hH.integrable_convolution
        (ContinuousLinearMap.mul ℝ ℝ) hMn
      have hBint : Integrable B := hD.integrable_convolution
        (ContinuousLinearMap.mul ℝ ℝ) hMp
      let CA : ℝ := (∫ t : ℝ, ‖H t‖) * gsLogScale chi K ^ n
      let CB : ℝ := (∫ t : ℝ, ‖D t‖) * gsLogScale chi K ^ n.pred
      have hCA0 : 0 ≤ CA := mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)
        (pow_nonneg (gsLogScale_nonneg hchi hK) _)
      have hCB0 : 0 ≤ CB := mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)
        (pow_nonneg (gsLogScale_nonneg hchi hK) _)
      have hAbound : ∀ y : ℝ, ‖A y‖ ≤ CA := by
        intro y
        exact gs_norm_convolution_le_integral_norm_mul hH
          (pow_nonneg (gsLogScale_nonneg hchi hK) _) hMnbound
      have hBbound : ∀ y : ℝ, ‖B y‖ ≤ CB := by
        intro y
        exact gs_norm_convolution_le_integral_norm_mul hD
          (pow_nonneg (gsLogScale_nonneg hchi hK) _) hMpbound
      have hWA : ConvolutionExistsAt W A x (ContinuousLinearMap.mul ℝ ℝ) :=
        gs_convolutionExistsAt_of_integrable_bounded hW hAint hAbound
      have hWB : ConvolutionExistsAt W B x (ContinuousLinearMap.mul ℝ ℝ) :=
        gs_convolutionExistsAt_of_integrable_bounded hW hBint hBbound
      have hWnB : ConvolutionExistsAt W ((n : ℝ) • B) x
          (ContinuousLinearMap.mul ℝ ℝ) := by
        rw [ConvolutionExistsAt] at hWB ⊢
        convert hWB.const_mul (n : ℝ) using 1
        ext t
        simp [smul_eq_mul, ContinuousLinearMap.mul_apply']
        ring
      have hdistrib :
          (W ⋆[ContinuousLinearMap.mul ℝ ℝ] G) x =
            (W ⋆[ContinuousLinearMap.mul ℝ ℝ] A) x +
              (n : ℝ) * (W ⋆[ContinuousLinearMap.mul ℝ ℝ] B) x := by
        have hd := hWA.distrib_add hWnB
        change (W ⋆[ContinuousLinearMap.mul ℝ ℝ]
            (A + (n : ℝ) • B)) x = _ at hd
        rw [convolution_smul] at hd
        simpa [G, Pi.smul_apply, smul_eq_mul] using hd
      have hCG :
          (W ⋆[ContinuousLinearMap.mul ℝ ℝ] Cn) x =
            (W ⋆[ContinuousLinearMap.mul ℝ ℝ] G) x := by
        apply gs_convolution_congr_Icc
          (fun _t ht ↦ gsDefectLocal_nonpos chi K ht)
          (fun _t ht ↦ gsCoordMomentLocal_nonpos chi K n ht)
          (fun t ht ↦ by
            dsimp only [G, A, B]
            rw [Pi.add_apply, Pi.smul_apply]
            simp only [smul_eq_mul]
            rw [gs_convolution_eq_zero_of_nonpos
              (fun _s hs ↦ gsStepLocal_nonpos K hs)
              (fun _s hs ↦ gsMomentLocal_nonpos chi K n hs) ht,
              gs_convolution_eq_zero_of_nonpos
                (fun _s hs ↦ gsWeightedDefectLocal_nonpos chi K hs)
                (fun _s hs ↦ gsMomentLocal_nonpos chi K n.pred hs) ht]
            ring)
          hx0
        intro y hy
        have hyK : y < K := hy.2.trans_lt hxK
        have hiy := ih (K := K) (x := y) hK hy.1 hyK
        dsimp only [Cn, G, A, B, gsCoordMomentLocal]
        rw [Pi.add_apply, Pi.smul_apply]
        simp only [smul_eq_mul]
        by_cases hyzero : y = 0
        · subst y
          have hz := hiy.symm
          simpa [H, D, Mn, Mp, gsLocalize] using hz
        · have hypos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hyzero)
          rw [gsLocalize, indicator_of_mem
            (show y ∈ Ioo (0 : ℝ) K from ⟨hypos, hyK⟩)]
          exact hiy.symm
      have hmiddle :
          (H ⋆[ContinuousLinearMap.mul ℝ ℝ] Ms) x +
              (n : ℝ) * (D ⋆[ContinuousLinearMap.mul ℝ ℝ] Mn) x =
            (W ⋆[ContinuousLinearMap.mul ℝ ℝ] Cn) x := by
        rw [hreplaceH, hreplaceD, hassocHW, hassocDW, hCG, hdistrib]
      have hcoord := gs_moment_coordinate_identity hchi n hx0 hxK
      change x * gsMoment chi (n + 1) x =
        (D ⋆[ContinuousLinearMap.mul ℝ ℝ] Mn) x +
          (W ⋆[ContinuousLinearMap.mul ℝ ℝ] Cn) x at hcoord
      change (H ⋆[ContinuousLinearMap.mul ℝ ℝ] Ms) x +
          ((n + 1 : ℕ) : ℝ) *
            (D ⋆[ContinuousLinearMap.mul ℝ ℝ] Mn) x =
        x * gsMoment chi (n + 1) x
      rw [hcoord, ← hmiddle]
      push_cast
      ring

/-- Convolving the `n`-th simplex moment with the original kernel leaves
two adjacent defect terms; these telescope in the alternating series. -/
lemma gs_kernel_convolution_moment_identity
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {K u : ℝ} (hK : 1 ≤ K) (hu0 : 0 ≤ u) (huK : u < K) :
    (∫ t : ℝ in 0..u, chi t * gsMoment chi n (u - t)) =
      u * gsMoment chi n u -
        (n : ℝ) *
          (gsWeightedDefectLocal chi K ⋆[ContinuousLinearMap.mul ℝ ℝ]
            gsMomentLocal chi K n.pred) u -
        (gsWeightedDefectLocal chi K ⋆[ContinuousLinearMap.mul ℝ ℝ]
          gsMomentLocal chi K n) u := by
  let H : ℝ → ℝ := gsStepLocal K
  let D : ℝ → ℝ := gsWeightedDefectLocal chi K
  let Q : ℝ → ℝ := gsKernelLocal chi K
  let Mn : ℝ → ℝ := gsMomentLocal chi K n
  let Mp : ℝ → ℝ := gsMomentLocal chi K n.pred
  have hH : Integrable H := integrable_gsStepLocal (zero_le_one.trans hK)
  have hD : Integrable D := integrable_gsWeightedDefectLocal hchi hK
  have hMn : Integrable Mn :=
    integrable_gsMomentLocal hchi n (zero_le_one.trans hK)
  have hMnbound : ∀ y : ℝ, ‖Mn y‖ ≤ gsLogScale chi K ^ n :=
    gsMomentLocal_bound hchi n hK
  have hHM : ConvolutionExistsAt H Mn u (ContinuousLinearMap.mul ℝ ℝ) :=
    gs_convolutionExistsAt_of_integrable_bounded hH hMn hMnbound
  have hDM : ConvolutionExistsAt D Mn u (ContinuousLinearMap.mul ℝ ℝ) :=
    gs_convolutionExistsAt_of_integrable_bounded hD hMn hMnbound
  have hsplit :
      (Q ⋆[ContinuousLinearMap.mul ℝ ℝ] Mn) u =
        (H ⋆[ContinuousLinearMap.mul ℝ ℝ] Mn) u -
          (D ⋆[ContinuousLinearMap.mul ℝ ℝ] Mn) u := by
    have hQ : Q = H - D := by
      exact gsKernelLocal_eq_step_sub_weighted hchi K
    rw [hQ, convolution_def, convolution_def, convolution_def]
    rw [show (fun t : ℝ ↦
        (ContinuousLinearMap.mul ℝ ℝ ((H - D) t)) (Mn (u - t))) =
        (fun t ↦ (ContinuousLinearMap.mul ℝ ℝ (H t)) (Mn (u - t)) -
          (ContinuousLinearMap.mul ℝ ℝ (D t)) (Mn (u - t))) by
      funext t
      simp [ContinuousLinearMap.mul_apply']]
    exact integral_sub hHM hDM
  have hstep := gs_step_convolution_moment_identity hchi n hK hu0 huK
  change (H ⋆[ContinuousLinearMap.mul ℝ ℝ] Mn) u +
      (n : ℝ) * (D ⋆[ContinuousLinearMap.mul ℝ ℝ] Mp) u =
    u * gsMoment chi n u at hstep
  rw [← gsLocalize_convolution_apply (f := chi) (g := gsMoment chi n)
      hu0 huK]
  change (Q ⋆[ContinuousLinearMap.mul ℝ ℝ] Mn) u = _
  rw [hsplit]
  linarith

lemma intervalIntegrable_gsKernel_mul_moment_zero_to
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {u : ℝ} (hu0 : 0 ≤ u) :
    IntervalIntegrable
      (fun t : ℝ ↦ chi t * gsMoment chi n (u - t)) volume 0 u := by
  let K : ℝ := max 1 u + 1
  have hK1 : 1 ≤ K := by dsimp only [K]; linarith [le_max_left (1 : ℝ) u]
  have huK : u < K := by dsimp only [K]; linarith [le_max_right (1 : ℝ) u]
  let Q : ℝ → ℝ := gsKernelLocal chi K
  let Mn : ℝ → ℝ := gsMomentLocal chi K n
  have hQ : Integrable Q := integrable_gsKernelLocal hchi (zero_le_one.trans hK1)
  have hMn : Integrable Mn :=
    integrable_gsMomentLocal hchi n (zero_le_one.trans hK1)
  have hMnbound : ∀ y : ℝ, ‖Mn y‖ ≤ gsLogScale chi K ^ n :=
    gsMomentLocal_bound hchi n hK1
  have hconv : ConvolutionExistsAt Q Mn u (ContinuousLinearMap.mul ℝ ℝ) :=
    gs_convolutionExistsAt_of_integrable_bounded hQ hMn hMnbound
  have hint : Integrable (fun t : ℝ ↦ Q t * Mn (u - t)) := by
    simpa [ConvolutionExistsAt, ContinuousLinearMap.mul_apply'] using hconv
  apply hint.intervalIntegrable.congr_uIoo
  intro t ht
  rw [uIoo_of_le hu0] at ht
  have htK : t ∈ Ioo (0 : ℝ) K := ⟨ht.1, ht.2.trans huK⟩
  have hsubK : u - t ∈ Ioo (0 : ℝ) K := by
    constructor
    · linarith [ht.2]
    · linarith [ht.1, huK]
  simp [Q, Mn, gsKernelLocal, gsMomentLocal, gsLocalize, htK, hsubK]

lemma intervalIntegrable_gsKernel_mul_alternating
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (N : ℕ)
    {u : ℝ} (hu0 : 0 ≤ u) :
    IntervalIntegrable
      (fun t : ℝ ↦ chi t * gsAlternatingMomentSum chi N (u - t))
      volume 0 u := by
  rw [show (fun t : ℝ ↦
      chi t * gsAlternatingMomentSum chi N (u - t)) =
      ∑ j ∈ Finset.range (N + 1),
        (fun t ↦ ((-1 : ℝ) ^ j / j.factorial) *
          (chi t * gsMoment chi j (u - t))) by
    funext t
    simp only [gsAlternatingMomentSum]
    rw [Finset.mul_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j hj
    ring]
  apply IntervalIntegrable.sum
  intro j hj
  exact (intervalIntegrable_gsKernel_mul_moment_zero_to hchi j hu0).const_mul _

lemma gsAlternatingMomentSum_succ (chi : ℝ → ℝ) (N : ℕ) (u : ℝ) :
    gsAlternatingMomentSum chi (N + 1) u =
      gsAlternatingMomentSum chi N u +
        (-1 : ℝ) ^ (N + 1) * gsMoment chi (N + 1) u /
          (N + 1).factorial := by
  simp only [gsAlternatingMomentSum]
  rw [show N + 1 + 1 = (N + 1) + 1 by omega,
    Finset.sum_range_succ]

/-- The exact residual after inserting a finite alternating moment sum in
the GS Volterra equation. -/
lemma gs_kernel_convolution_alternating_identity
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) :
    ∀ N : ℕ, ∀ {K u : ℝ}, 1 ≤ K → 0 ≤ u → u < K →
      (∫ t : ℝ in 0..u,
        chi t * gsAlternatingMomentSum chi N (u - t)) =
        u * gsAlternatingMomentSum chi N u +
          ((-1 : ℝ) ^ (N + 1) / N.factorial) *
            (gsWeightedDefectLocal chi K ⋆[ContinuousLinearMap.mul ℝ ℝ]
              gsMomentLocal chi K N) u := by
  intro N
  induction N with
  | zero =>
      intro K u hK hu0 huK
      have h := gs_kernel_convolution_moment_identity hchi 0 hK hu0 huK
      simp only [gsAlternatingMomentSum, Finset.sum_range_succ,
        Finset.sum_range_zero, Finset.sum_empty, zero_add, gsMoment_zero,
        pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
        Nat.cast_zero, zero_mul, sub_zero] at h ⊢
      linarith
  | succ N ih =>
      intro K u hK hu0 huK
      let D : ℝ → ℝ := gsWeightedDefectLocal chi K
      let MN : ℝ → ℝ := gsMomentLocal chi K N
      let MS : ℝ → ℝ := gsMomentLocal chi K (N + 1)
      let a : ℝ := (-1 : ℝ) ^ (N + 1) / (N + 1).factorial
      have hAlt := intervalIntegrable_gsKernel_mul_alternating hchi N hu0
      have hMom := intervalIntegrable_gsKernel_mul_moment_zero_to
        hchi (N + 1) hu0
      have hTerm : IntervalIntegrable
          (fun t : ℝ ↦ a * (chi t * gsMoment chi (N + 1) (u - t)))
          volume 0 u := hMom.const_mul a
      have hsplit :
          (∫ t : ℝ in 0..u,
            chi t * gsAlternatingMomentSum chi (N + 1) (u - t)) =
            (∫ t : ℝ in 0..u,
              chi t * gsAlternatingMomentSum chi N (u - t)) +
              a * (∫ t : ℝ in 0..u,
                chi t * gsMoment chi (N + 1) (u - t)) := by
        rw [show (fun t : ℝ ↦
            chi t * gsAlternatingMomentSum chi (N + 1) (u - t)) =
            (fun t ↦ chi t * gsAlternatingMomentSum chi N (u - t) +
              a * (chi t * gsMoment chi (N + 1) (u - t))) by
          funext t
          rw [gsAlternatingMomentSum_succ]
          dsimp only [a]
          ring]
        rw [intervalIntegral.integral_add hAlt hTerm,
          intervalIntegral.integral_const_mul]
      have hih := ih (K := K) (u := u) hK hu0 huK
      have hmom := gs_kernel_convolution_moment_identity
        hchi (N + 1) hK hu0 huK
      change (∫ t : ℝ in 0..u,
          chi t * gsMoment chi (N + 1) (u - t)) =
        u * gsMoment chi (N + 1) u -
          ((N + 1 : ℕ) : ℝ) *
            (D ⋆[ContinuousLinearMap.mul ℝ ℝ] MN) u -
          (D ⋆[ContinuousLinearMap.mul ℝ ℝ] MS) u at hmom
      change (∫ t : ℝ in 0..u,
          chi t * gsAlternatingMomentSum chi N (u - t)) =
        u * gsAlternatingMomentSum chi N u +
          ((-1 : ℝ) ^ (N + 1) / N.factorial) *
            (D ⋆[ContinuousLinearMap.mul ℝ ℝ] MN) u at hih
      have hfact : (((N + 1).factorial : ℕ) : ℝ) =
          ((N + 1 : ℕ) : ℝ) * (N.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        norm_cast
      have hfacN : (N.factorial : ℝ) ≠ 0 := by positivity
      have hfacS : ((N + 1).factorial : ℝ) ≠ 0 := by positivity
      have hcoef : a * ((N + 1 : ℕ) : ℝ) =
          (-1 : ℝ) ^ (N + 1) / N.factorial := by
        dsimp only [a]
        rw [hfact]
        field_simp
      have hnext : (-1 : ℝ) ^ (N + 1 + 1) / (N + 1).factorial = -a := by
        dsimp only [a]
        rw [pow_succ]
        ring
      have haterm :
          (-1 : ℝ) ^ (N + 1) * gsMoment chi (N + 1) u /
              (N + 1).factorial =
            a * gsMoment chi (N + 1) u := by
        dsimp only [a]
        ring
      rw [hsplit, hih, hmom, gsAlternatingMomentSum_succ]
      change _ = u *
          (gsAlternatingMomentSum chi N u +
            (-1 : ℝ) ^ (N + 1) * gsMoment chi (N + 1) u /
              (N + 1).factorial) +
        ((-1 : ℝ) ^ (N + 1 + 1) / (N + 1).factorial) *
          (D ⋆[ContinuousLinearMap.mul ℝ ℝ] MS) u
      rw [haterm, ← hcoef, hnext]
      ring

/-- The residual convolution in the finite alternating expansion vanishes
strictly before the next possible simplex dimension.  Indeed the weighted
defect is zero on `[0,1]`, while for `t > 1` the remaining `N`-simplex has
endpoint below `N`. -/
lemma gs_weightedDefect_convolution_moment_eq_zero_of_lt
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (N : ℕ)
    {K u : ℝ} (hu0 : 0 ≤ u) (huK : u < K)
    (huN : u < (N : ℝ) + 1) :
    (gsWeightedDefectLocal chi K ⋆[ContinuousLinearMap.mul ℝ ℝ]
      gsMomentLocal chi K N) u = 0 := by
  rw [gsWeightedDefectLocal, gsMomentLocal,
    gsLocalize_convolution_apply hu0 huK]
  rw [show (∫ t : ℝ in 0..u,
      (t * gsDefectWeight chi t) * gsMoment chi N (u - t)) =
      ∫ _t : ℝ in 0..u, (0 : ℝ) by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hu0] at ht
    by_cases ht1 : t ≤ 1
    · have hchiOne : chi t = 1 := hchi.2.2.2 t ht.1 ht1
      simp [gsDefectWeight, hchiOne]
    · have htOne : 1 < t := lt_of_not_ge ht1
      have harg0 : 0 ≤ u - t := sub_nonneg.mpr ht.2
      have hargN : u - t < N := by
        push_cast at huN ⊢
        linarith
      change (t * gsDefectWeight chi t) * gsMoment chi N (u - t) = 0
      rw [gsMoment_eq_zero_of_lt harg0 hargN, mul_zero]]
  simp

/-- On a compact interval lying below dimension `N+1`, the finite
alternating moment sum satisfies the GS Volterra equation exactly. -/
lemma gs_alternatingMomentSum_equation_of_lt
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (N : ℕ)
    {u : ℝ} (hu0 : 0 ≤ u) (huN : u < (N : ℝ) + 1) :
    (∫ t : ℝ in 0..u,
      chi t * gsAlternatingMomentSum chi N (u - t)) =
      u * gsAlternatingMomentSum chi N u := by
  let K : ℝ := max 1 u + 1
  have hK : 1 ≤ K := by
    dsimp only [K]
    linarith [le_max_left (1 : ℝ) u]
  have huK : u < K := by
    dsimp only [K]
    linarith [le_max_right (1 : ℝ) u]
  have hid := gs_kernel_convolution_alternating_identity hchi N hK hu0 huK
  have hz := gs_weightedDefect_convolution_moment_eq_zero_of_lt
    hchi N hu0 huK huN
  rw [hz, mul_zero, add_zero] at hid
  exact hid

end

end Erdos783
