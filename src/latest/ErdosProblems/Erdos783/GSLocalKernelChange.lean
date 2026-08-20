/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos783.GSKernelChange

/-! # Kernel change from a compactly constructed base solution -/

open MeasureTheory Set Finset
open scoped BigOperators Convolution

namespace Erdos783

noncomputable section

/-- Exactly the local data used by the first kernel-change truncation. -/
structure GSCompactSolution
    (chi sigma : ℝ → ℝ) (K : ℝ) : Prop where
  one : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → sigma u = 1
  equation : ∀ u : ℝ, 1 ≤ u → u < K →
    u * sigma u = ∫ t : ℝ in 0..u, chi t * sigma (u - t)
  integral : ∀ u : ℝ, 1 ≤ u → u < K →
    IntervalIntegrable (fun t : ℝ ↦ chi t * sigma (u - t)) volume 0 u
  localIntegral : IntervalIntegrable sigma volume 0 K
  range : ∀ u ∈ Icc (0 : ℝ) K, sigma u ∈ Icc (0 : ℝ) 1

lemma gsCompactSolution_alternating
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (N : ℕ)
    {K : ℝ} (hK : 1 ≤ K) (hKN : K < (N : ℝ) + 1) :
    GSCompactSolution chi (gsAlternatingMomentSum chi N) K := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u hu0 hu1
    exact gsAlternatingMomentSum_eq_one_of_le_one chi N hu0 hu1
  · intro u hu1 huK
    exact (gs_alternatingMomentSum_equation_of_lt hchi N
      (zero_le_one.trans hu1) (huK.trans hKN)).symm
  · intro u hu1 huK
    exact intervalIntegrable_gsKernel_mul_alternating hchi N
      (zero_le_one.trans hu1)
  · rw [show gsAlternatingMomentSum chi N =
        ∑ j ∈ Finset.range (N + 1),
          ((-1 : ℝ) ^ j / j.factorial) • gsMoment chi j by
      funext u
      simp only [gsAlternatingMomentSum, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring]
    apply IntervalIntegrable.sum
    intro j hj
    exact (intervalIntegrable_gsMoment hchi j (zero_le_one.trans hK)).const_mul _
  · exact gs_alternatingMomentSum_mem_Icc_of_lt hchi N hK hKN

lemma integrable_gsLocalize_compactSolution
    {psi base : ℝ → ℝ} {K : ℝ}
    (hbase : GSCompactSolution psi base K) (hK0 : 0 ≤ K) :
    Integrable (gsLocalize K base) := by
  exact integrable_gsLocalize hK0 hbase.localIntegral

lemma gsLocalize_compactSolution_bound
    {psi base : ℝ → ℝ} {K : ℝ}
    (hbase : GSCompactSolution psi base K) (x : ℝ) :
    ‖gsLocalize K base x‖ ≤ 1 := by
  by_cases hx : x ∈ Ioo (0 : ℝ) K
  · rw [gsLocalize, indicator_of_mem hx, Real.norm_eq_abs]
    have hr := hbase.range x ⟨hx.1.le, hx.2.le⟩
    rw [abs_of_nonneg hr.1]
    exact hr.2
  · simp [gsLocalize, hx]

lemma gsCompact_base_convolution
    {psi base : ℝ → ℝ} (hpsi : IsGSKernel psi)
    {K x : ℝ} (hbase : GSCompactSolution psi base K)
    (hx0 : 0 ≤ x) (hxK : x < K) :
    (gsKernelLocal psi K ⋆[ContinuousLinearMap.mul ℝ ℝ]
      gsPerturbIterate (fun _ ↦ 1) base K 0) x =
      x * gsPerturbIterate (fun _ ↦ 1) base K 0 x := by
  change ((gsLocalize K psi) ⋆[ContinuousLinearMap.mul ℝ ℝ]
      (gsLocalize K base)) x = x * gsLocalize K base x
  rw [gsLocalize_convolution_apply hx0 hxK]
  by_cases hx : x = 0
  · subst x
    simp [gsLocalize]
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  rw [gsLocalize, indicator_of_mem
    (show x ∈ Ioo (0 : ℝ) K from ⟨hxpos, hxK⟩)]
  by_cases hx1 : 1 ≤ x
  · exact (hbase.equation x hx1 hxK).symm
  · have hxle : x ≤ 1 := le_of_not_ge hx1
    rw [show (∫ t : ℝ in 0..x, psi t * base (x - t)) =
        ∫ _t : ℝ in 0..x, (1 : ℝ) by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hx0] at ht
      change psi t * base (x - t) = 1
      rw [hpsi.2.2.2 t ht.1 (ht.2.trans hxle),
        hbase.one (x - t) (sub_nonneg.mpr ht.2)
          ((sub_le_self _ ht.1).trans hxle)]
      norm_num,
      hbase.one x hx0 hxle]
    simp

lemma integrable_gsCompactPerturbCoord_zero
    {theta psi base : ℝ → ℝ} {K : ℝ}
    (hbase : GSCompactSolution psi base K) (hK0 : 0 ≤ K) :
    Integrable (gsPerturbCoord theta base K 0) := by
  apply integrable_gsLocalize hK0
  have hT := integrable_gsLocalize_compactSolution hbase hK0
  have hTint : IntervalIntegrable (gsLocalize K base) volume 0 K :=
    hT.intervalIntegrable
  have hmul := hTint.mul_continuousOn continuousOn_id
  convert hmul using 1
  ext t
  simp [gsPerturbIterate, id, mul_comm]

lemma gsCompactPerturbCoord_zero_bound
    {theta psi base : ℝ → ℝ} {K : ℝ}
    (hbase : GSCompactSolution psi base K) (hK0 : 0 ≤ K) (x : ℝ) :
    ‖gsPerturbCoord theta base K 0 x‖ ≤ K := by
  by_cases hx : x ∈ Ioo (0 : ℝ) K
  · rw [gsPerturbCoord, gsLocalize, indicator_of_mem hx, norm_mul,
      Real.norm_eq_abs, abs_of_nonneg hx.1.le]
    simpa [gsPerturbIterate] using mul_le_mul (le_of_lt hx.2)
      (gsLocalize_compactSolution_bound hbase x)
      (norm_nonneg _) hK0
  · have hz : gsPerturbCoord theta base K 0 x = 0 := by
      simp [gsPerturbCoord, gsLocalize, hx]
    rw [hz, norm_zero]
    exact hK0

/-- Endpoint multiplication for the first perturbation iterate, under only
compact base-solution hypotheses. -/
lemma gsCompact_perturb_coordinate_zero
    {theta psi base : ℝ → ℝ} (htheta : IsGSKernel theta)
    {K x : ℝ} (hK : 1 ≤ K) (hbase : GSCompactSolution psi base K)
    (hx0 : 0 ≤ x) (hxK : x < K) :
    x * gsPerturbIterate theta base K 1 x =
      (gsWeightedDefectLocal theta K ⋆[ContinuousLinearMap.mul ℝ ℝ]
        gsPerturbIterate theta base K 0) x +
      (gsDefectLocal theta K ⋆[ContinuousLinearMap.mul ℝ ℝ]
        gsPerturbCoord theta base K 0) x := by
  let P : ℝ → ℝ := gsDefectLocal theta K
  let D : ℝ → ℝ := gsWeightedDefectLocal theta K
  let T : ℝ → ℝ := gsPerturbIterate theta base K 0
  let C : ℝ → ℝ := gsPerturbCoord theta base K 0
  have hPnonpos : ∀ t : ℝ, t ≤ 0 → P t = 0 :=
    fun _t ht ↦ gsDefectLocal_nonpos theta K ht
  have hDnonpos : ∀ t : ℝ, t ≤ 0 → D t = 0 :=
    fun _t ht ↦ gsWeightedDefectLocal_nonpos theta K ht
  have hTnonpos : ∀ t : ℝ, t ≤ 0 → T t = 0 :=
    fun _t ht ↦ gsPerturbIterate_nonpos theta base K 0 ht
  have hCnonpos : ∀ t : ℝ, t ≤ 0 → C t = 0 :=
    fun _t ht ↦ gsPerturbCoord_nonpos theta base K 0 ht
  have hP := integrable_gsDefectLocal htheta hK
  have hD := integrable_gsWeightedDefectLocal htheta hK
  have hT := integrable_gsLocalize_compactSolution hbase (zero_le_one.trans hK)
  have hC := integrable_gsCompactPerturbCoord_zero (theta := theta)
    hbase (zero_le_one.trans hK)
  have hTbound : ∀ y : ℝ, ‖T y‖ ≤ 1 :=
    gsLocalize_compactSolution_bound hbase
  have hCbound : ∀ y : ℝ, ‖C y‖ ≤ K :=
    gsCompactPerturbCoord_zero_bound hbase (zero_le_one.trans hK)
  have hDT : ConvolutionExistsAt D T x (ContinuousLinearMap.mul ℝ ℝ) :=
    gs_convolutionExistsAt_of_integrable_bounded hD hT hTbound
  have hPC : ConvolutionExistsAt P C x (ContinuousLinearMap.mul ℝ ℝ) :=
    gs_convolutionExistsAt_of_integrable_bounded hP hC hCbound
  have hleft : IntervalIntegrable
      (fun t : ℝ ↦ (t * P t) * T (x - t)) volume 0 x := by
    have hi : Integrable (fun t : ℝ ↦ D t * T (x - t)) := by
      simpa [ConvolutionExistsAt, ContinuousLinearMap.mul_apply'] using hDT
    apply hi.intervalIntegrable.congr
    intro t ht
    rw [uIoc_of_le hx0] at ht
    have htK : t ∈ Ioo (0 : ℝ) K := ⟨ht.1, ht.2.trans_lt hxK⟩
    change D t * T (x - t) = (t * P t) * T (x - t)
    simp [P, D, gsDefectLocal, gsWeightedDefectLocal, gsLocalize, htK]
  have hright : IntervalIntegrable
      (fun t : ℝ ↦ P t * ((x - t) * T (x - t))) volume 0 x := by
    have hi : Integrable (fun t : ℝ ↦ P t * C (x - t)) := by
      simpa [ConvolutionExistsAt, ContinuousLinearMap.mul_apply'] using hPC
    apply hi.intervalIntegrable.congr
    intro t ht
    rw [uIoc_of_le hx0] at ht
    have hsub0 : 0 ≤ x - t := sub_nonneg.mpr ht.2
    by_cases hsub : x - t = 0
    · have htEq : t = x := (sub_eq_zero.mp hsub).symm
      subst t
      simp [C, gsPerturbCoord, gsLocalize]
    · have hsubK : x - t ∈ Ioo (0 : ℝ) K :=
        ⟨lt_of_le_of_ne hsub0 (Ne.symm hsub),
          (sub_le_self _ ht.1.le).trans_lt hxK⟩
      change P t * C (x - t) = P t * ((x - t) * T (x - t))
      congr 1
      dsimp only [C, gsPerturbCoord]
      rw [gsLocalize, indicator_of_mem hsubK]
  have hcoord := gs_interval_convolution_coordinate P T hleft hright
  have hDP : D = fun t : ℝ ↦ t * P t := by
    funext t
    by_cases ht : t ∈ Ioo (0 : ℝ) K
    · simp [P, D, gsDefectLocal, gsWeightedDefectLocal, gsLocalize, ht]
    · simp [P, D, gsDefectLocal, gsWeightedDefectLocal, gsLocalize, ht]
  have hDconv :
      (D ⋆[ContinuousLinearMap.mul ℝ ℝ] T) x =
        ∫ t : ℝ in 0..x, (t * P t) * T (x - t) := by
    rw [gs_convolution_apply_of_nonpos_eq_zero hDnonpos hTnonpos hx0, hDP]
  have hPCconv :
      (P ⋆[ContinuousLinearMap.mul ℝ ℝ] C) x =
        ∫ t : ℝ in 0..x, P t * ((x - t) * T (x - t)) := by
    rw [gs_convolution_apply_of_nonpos_eq_zero hPnonpos hCnonpos hx0]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx0] at ht
    have hsub0 : 0 ≤ x - t := sub_nonneg.mpr ht.2
    by_cases hsub : x - t = 0
    · change P t * C (x - t) = P t * ((x - t) * T (x - t))
      rw [hsub]
      simp [C, gsPerturbCoord, gsLocalize]
    · have hsubK : x - t ∈ Ioo (0 : ℝ) K :=
        ⟨lt_of_le_of_ne hsub0 (Ne.symm hsub),
          (sub_le_self _ ht.1).trans_lt hxK⟩
      change P t * C (x - t) = P t * ((x - t) * T (x - t))
      congr 1
      dsimp only [C, gsPerturbCoord]
      rw [gsLocalize, indicator_of_mem hsubK]
  rw [← gs_convolution_apply_of_nonpos_eq_zero hPnonpos hTnonpos hx0,
    ← hDconv, ← hPCconv] at hcoord
  change x * gsPerturbIterate theta base K 1 x = _
  exact hcoord

/-- The first odd kernel-change residual, requiring the base equation only
on the compact interval visible to the convolution. -/
lemma gsCompact_kernelChange_residual_one
    {theta psi target base : ℝ → ℝ}
    (htheta : IsGSKernel theta) (hpsi : IsGSKernel psi)
    (htarget : IsGSKernel target)
    (hrel : ∀ t : ℝ, target t = psi t - t * gsDefectWeight theta t)
    {K x : ℝ} (hK : 1 ≤ K) (hbase : GSCompactSolution psi base K)
    (hx0 : 0 ≤ x) (hxK : x < K) :
    (gsKernelLocal target K ⋆[ContinuousLinearMap.mul ℝ ℝ]
        gsPerturbAlternating theta base K 1) x =
      x * gsPerturbAlternating theta base K 1 x +
        (gsWeightedDefectLocal theta K ⋆[ContinuousLinearMap.mul ℝ ℝ]
          gsPerturbIterate theta base K 1) x := by
  let Q : ℝ → ℝ := gsKernelLocal target K
  let H : ℝ → ℝ := gsKernelLocal psi K
  let P : ℝ → ℝ := gsDefectLocal theta K
  let D : ℝ → ℝ := gsWeightedDefectLocal theta K
  let T0 : ℝ → ℝ := gsPerturbIterate theta base K 0
  let T1 : ℝ → ℝ := gsPerturbIterate theta base K 1
  let C0 : ℝ → ℝ := gsPerturbCoord theta base K 0
  let S : ℝ → ℝ := gsPerturbAlternating theta base K 1
  have hQ : Integrable Q :=
    integrable_gsKernelLocal htarget (zero_le_one.trans hK)
  have hH : Integrable H :=
    integrable_gsKernelLocal hpsi (zero_le_one.trans hK)
  have hP : Integrable P := integrable_gsDefectLocal htheta hK
  have hD : Integrable D := integrable_gsWeightedDefectLocal htheta hK
  have hT0 : Integrable T0 :=
    integrable_gsLocalize_compactSolution hbase (zero_le_one.trans hK)
  have hT0bound : ∀ y : ℝ, ‖T0 y‖ ≤ 1 :=
    gsLocalize_compactSolution_bound hbase
  have hT1 : Integrable T1 := hP.integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) hT0
  let L : ℝ := ∫ t : ℝ, ‖P t‖
  have hL0 : 0 ≤ L := integral_nonneg fun _ ↦ norm_nonneg _
  have hT1bound : ∀ y : ℝ, ‖T1 y‖ ≤ L := by
    intro y
    change ‖(P ⋆[ContinuousLinearMap.mul ℝ ℝ] T0) y‖ ≤ L
    simpa [L] using gs_norm_convolution_le_integral_norm_mul hP
      (by norm_num : (0 : ℝ) ≤ 1) hT0bound (x := y)
  have hC0 : Integrable C0 :=
    integrable_gsCompactPerturbCoord_zero (theta := theta)
      hbase (zero_le_one.trans hK)
  have hC0bound : ∀ y : ℝ, ‖C0 y‖ ≤ K :=
    gsCompactPerturbCoord_zero_bound hbase (zero_le_one.trans hK)
  have hAint : Integrable (H ⋆[ContinuousLinearMap.mul ℝ ℝ] T0) :=
    hH.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hT0
  let CH : ℝ := (∫ t : ℝ, ‖H t‖)
  have hAbound : ∀ y : ℝ,
      ‖(H ⋆[ContinuousLinearMap.mul ℝ ℝ] T0) y‖ ≤ CH := by
    intro y
    simpa [CH] using gs_norm_convolution_le_integral_norm_mul hH
      (by norm_num : (0 : ℝ) ≤ 1) hT0bound (x := y)
  have hassoc :
      (H ⋆[ContinuousLinearMap.mul ℝ ℝ] T1) x =
        (P ⋆[ContinuousLinearMap.mul ℝ ℝ]
          (H ⋆[ContinuousLinearMap.mul ℝ ℝ] T0)) x := by
    change (H ⋆[ContinuousLinearMap.mul ℝ ℝ]
        (P ⋆[ContinuousLinearMap.mul ℝ ℝ] T0)) x = _
    calc
      _ = ((H ⋆[ContinuousLinearMap.mul ℝ ℝ] P) ⋆[
            ContinuousLinearMap.mul ℝ ℝ] T0) x :=
        (gs_convolution_assoc_of_integrable_bounded hH hP hT0
          hT0bound).symm
      _ = ((P ⋆[ContinuousLinearMap.mul ℝ ℝ] H) ⋆[
            ContinuousLinearMap.mul ℝ ℝ] T0) x := by
        rw [gs_convolution_comm H P]
      _ = _ := gs_convolution_assoc_of_integrable_bounded hP hH hT0
        hT0bound
  have hPC :
      (P ⋆[ContinuousLinearMap.mul ℝ ℝ] C0) x =
        (P ⋆[ContinuousLinearMap.mul ℝ ℝ]
          (H ⋆[ContinuousLinearMap.mul ℝ ℝ] T0)) x := by
    apply gs_convolution_congr_Icc
      (fun _t ht ↦ gsDefectLocal_nonpos theta K ht)
      (fun _t ht ↦ gsPerturbCoord_nonpos theta base K 0 ht)
      (fun _t ht ↦ gs_convolution_eq_zero_of_nonpos
        (fun _s hs ↦ gsKernelLocal_nonpos psi K hs)
        (fun _s hs ↦ gsPerturbIterate_nonpos theta base K 0 hs) ht)
      hx0
    intro y hy
    have hyK : y < K := hy.2.trans_lt hxK
    have hb := gsCompact_base_convolution hpsi hbase hy.1 hyK
    change (H ⋆[ContinuousLinearMap.mul ℝ ℝ] T0) y = y * T0 y at hb
    change C0 y = (H ⋆[ContinuousLinearMap.mul ℝ ℝ] T0) y
    by_cases hyzero : y = 0
    · subst y
      simpa [C0, gsPerturbCoord, gsLocalize] using hb.symm
    · have hypos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hyzero)
      rw [show C0 y = y * T0 y by
        dsimp only [C0, gsPerturbCoord]
        rw [gsLocalize, indicator_of_mem
          (show y ∈ Ioo (0 : ℝ) K from ⟨hypos, hyK⟩)]]
      exact hb.symm
  have hcoord := gsCompact_perturb_coordinate_zero htheta hK hbase hx0 hxK
  change x * T1 x =
    (D ⋆[ContinuousLinearMap.mul ℝ ℝ] T0) x +
      (P ⋆[ContinuousLinearMap.mul ℝ ℝ] C0) x at hcoord
  have hHT1 :
      (H ⋆[ContinuousLinearMap.mul ℝ ℝ] T1) x =
        x * T1 x - (D ⋆[ContinuousLinearMap.mul ℝ ℝ] T0) x := by
    rw [hassoc, ← hPC]
    linarith
  have hbaseX := gsCompact_base_convolution hpsi hbase hx0 hxK
  change (H ⋆[ContinuousLinearMap.mul ℝ ℝ] T0) x = x * T0 x at hbaseX
  have hQeq : Q = H - D := by
    funext t
    by_cases ht : t ∈ Ioo (0 : ℝ) K
    · simp only [Q, H, D, gsKernelLocal, gsWeightedDefectLocal,
        gsLocalize, indicator_of_mem ht, Pi.sub_apply]
      exact hrel t
    · simp [Q, H, D, gsKernelLocal, gsWeightedDefectLocal,
        gsLocalize, ht]
  have hHT0ex : ConvolutionExistsAt H T0 x (ContinuousLinearMap.mul ℝ ℝ) :=
    gs_convolutionExistsAt_of_integrable_bounded hH hT0 hT0bound
  have hDT0ex : ConvolutionExistsAt D T0 x (ContinuousLinearMap.mul ℝ ℝ) :=
    gs_convolutionExistsAt_of_integrable_bounded hD hT0 hT0bound
  have hHT1ex : ConvolutionExistsAt H T1 x (ContinuousLinearMap.mul ℝ ℝ) :=
    gs_convolutionExistsAt_of_integrable_bounded hH hT1 hT1bound
  have hDT1ex : ConvolutionExistsAt D T1 x (ContinuousLinearMap.mul ℝ ℝ) :=
    gs_convolutionExistsAt_of_integrable_bounded hD hT1 hT1bound
  have hQT (T : ℝ → ℝ)
      (hHT : ConvolutionExistsAt H T x (ContinuousLinearMap.mul ℝ ℝ))
      (hDT : ConvolutionExistsAt D T x (ContinuousLinearMap.mul ℝ ℝ)) :
      (Q ⋆[ContinuousLinearMap.mul ℝ ℝ] T) x =
        (H ⋆[ContinuousLinearMap.mul ℝ ℝ] T) x -
          (D ⋆[ContinuousLinearMap.mul ℝ ℝ] T) x := by
    rw [hQeq, convolution_def, convolution_def, convolution_def]
    rw [show (fun t : ℝ ↦
        (ContinuousLinearMap.mul ℝ ℝ ((H - D) t)) (T (x - t))) =
        (fun t ↦ (ContinuousLinearMap.mul ℝ ℝ (H t)) (T (x - t)) -
          (ContinuousLinearMap.mul ℝ ℝ (D t)) (T (x - t))) by
      funext t
      simp [ContinuousLinearMap.mul_apply']]
    exact integral_sub hHT hDT
  have hQT0 := hQT T0 hHT0ex hDT0ex
  have hQT1 := hQT T1 hHT1ex hDT1ex
  have hQT0ex : ConvolutionExistsAt Q T0 x (ContinuousLinearMap.mul ℝ ℝ) :=
    gs_convolutionExistsAt_of_integrable_bounded hQ hT0 hT0bound
  have hQT1ex : ConvolutionExistsAt Q T1 x (ContinuousLinearMap.mul ℝ ℝ) :=
    gs_convolutionExistsAt_of_integrable_bounded hQ hT1 hT1bound
  have hS : S = T0 - T1 := by
    funext y
    exact gsPerturbAlternating_one theta base K y
  have hQS :
      (Q ⋆[ContinuousLinearMap.mul ℝ ℝ] S) x =
        (Q ⋆[ContinuousLinearMap.mul ℝ ℝ] T0) x -
          (Q ⋆[ContinuousLinearMap.mul ℝ ℝ] T1) x := by
    rw [hS, convolution_def, convolution_def, convolution_def]
    rw [show (fun t : ℝ ↦
        (ContinuousLinearMap.mul ℝ ℝ (Q t)) ((T0 - T1) (x - t))) =
        (fun t ↦ (ContinuousLinearMap.mul ℝ ℝ (Q t)) (T0 (x - t)) -
          (ContinuousLinearMap.mul ℝ ℝ (Q t)) (T1 (x - t))) by
      funext t
      simp [ContinuousLinearMap.mul_apply']
      ring]
    exact integral_sub hQT0ex hQT1ex
  change (Q ⋆[ContinuousLinearMap.mul ℝ ℝ] S) x =
    x * S x + (D ⋆[ContinuousLinearMap.mul ℝ ℝ] T1) x
  rw [hQS, hQT0, hQT1, hbaseX, hHT1, hS]
  simp only [Pi.sub_apply]
  ring

lemma gsCompactPerturbIterate_one_le_logScale
    {theta psi base : ℝ → ℝ} (htheta : IsGSKernel theta)
    {K x : ℝ} (hK : 1 ≤ K) (hbase : GSCompactSolution psi base K)
    (hx1 : 1 ≤ x) (hxK : x < K) :
    gsPerturbIterate theta base K 1 x ≤ gsLogScale theta x := by
  let P : ℝ → ℝ := gsDefectLocal theta K
  let T : ℝ → ℝ := gsPerturbIterate theta base K 0
  let H : ℝ → ℝ := gsMomentLocal theta K 0
  have hP : Integrable P := integrable_gsDefectLocal htheta hK
  have hT : Integrable T :=
    integrable_gsLocalize_compactSolution hbase (zero_le_one.trans hK)
  have hH : Integrable H :=
    integrable_gsMomentLocal htheta 0 (zero_le_one.trans hK)
  have hTbound : ∀ y : ℝ, ‖T y‖ ≤ 1 :=
    gsLocalize_compactSolution_bound hbase
  have hHbound : ∀ y : ℝ, ‖H y‖ ≤ 1 := by
    intro y
    simpa [H] using gsMomentLocal_bound htheta 0 hK y
  have hPT : ConvolutionExistsAt P T x (ContinuousLinearMap.mul ℝ ℝ) :=
    gs_convolutionExistsAt_of_integrable_bounded hP hT hTbound
  have hPH : ConvolutionExistsAt P H x (ContinuousLinearMap.mul ℝ ℝ) :=
    gs_convolutionExistsAt_of_integrable_bounded hP hH hHbound
  have hTH : ∀ y : ℝ, T y ≤ H y := by
    intro y
    by_cases hy : y ∈ Ioo (0 : ℝ) K
    · change gsLocalize K base y ≤ gsLocalize K (gsMoment theta 0) y
      simp [gsLocalize, hy, (hbase.range y ⟨hy.1.le, hy.2.le⟩).2]
    · change gsLocalize K base y ≤ gsLocalize K (gsMoment theta 0) y
      simp [gsLocalize, hy]
  have hmono := convolution_mono_right hPT hPH
    (fun y ↦ gsDefectLocal_nonneg htheta K y) hTH
  have hrec := gsDefectLocal_convolution_momentLocal htheta 0
    (zero_le_one.trans hx1) hxK
  change (P ⋆[ContinuousLinearMap.mul ℝ ℝ] T) x ≤ _
  rw [← gsMoment_one theta hx1, ← hrec]
  exact hmono

lemma gsCompactPerturbFirstApprox_eq_one
    {theta psi base : ℝ → ℝ} (htheta : IsGSKernel theta)
    {K u : ℝ} (hbase : GSCompactSolution psi base K)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (huK : u < K) :
    gsPerturbFirstApprox theta base K u = 1 := by
  by_cases hu : u = 0
  · simp [gsPerturbFirstApprox, hu]
  · have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    have hT0 : gsPerturbIterate theta base K 0 u = 1 := by
      change gsLocalize K base u = 1
      rw [gsLocalize, indicator_of_mem
          (show u ∈ Ioo (0 : ℝ) K from ⟨hupos, huK⟩),
        hbase.one u hu0 hu1]
    have hT1 := gsPerturbIterate_one_eq_zero_of_le_one
      (psi := psi) (sigma := base) htheta hu0 hu1 huK
    rw [gsPerturbFirstApprox, if_neg hu, gsPerturbAlternating_one,
      hT0, hT1]
    norm_num

/-- Compact version of the first-order kernel-change lower bound. -/
theorem gsCompact_kernelChange_lower_first
    {theta psi target base targetSigma : ℝ → ℝ}
    (htheta : IsGSKernel theta) (hpsi : IsGSKernel psi)
    (htarget : IsGSKernel target)
    (htargetSigma : IsGSSolution target targetSigma)
    (hrel : ∀ t : ℝ, target t = psi t - t * gsDefectWeight theta t)
    {K u : ℝ} (hK : 1 ≤ K) (hbase : GSCompactSolution psi base K)
    (hu : 1 ≤ u) (huK : u < K) :
    base u - gsLogScale theta u ≤ targetSigma u := by
  let tau : ℝ → ℝ := gsPerturbFirstApprox theta base K
  let P : ℝ → ℝ := gsDefectLocal theta K
  let T0 : ℝ → ℝ := gsPerturbIterate theta base K 0
  let T1 : ℝ → ℝ := gsPerturbIterate theta base K 1
  let S : ℝ → ℝ := gsPerturbAlternating theta base K 1
  let L : ℝ := ∫ t : ℝ, ‖P t‖
  let B : ℝ := 2 + L
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hP : Integrable P := integrable_gsDefectLocal htheta hK
  have hT0 : Integrable T0 :=
    integrable_gsLocalize_compactSolution hbase (zero_le_one.trans hK)
  have hT0bound : ∀ y : ℝ, ‖T0 y‖ ≤ 1 :=
    gsLocalize_compactSolution_bound hbase
  have hT1 : Integrable T1 := hP.integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) hT0
  have hL0 : 0 ≤ L := integral_nonneg fun _ ↦ norm_nonneg _
  have hT1bound : ∀ y : ℝ, ‖T1 y‖ ≤ L := by
    intro y
    change ‖(P ⋆[ContinuousLinearMap.mul ℝ ℝ] T0) y‖ ≤ L
    simpa [L] using gs_norm_convolution_le_integral_norm_mul hP
      (by norm_num : (0 : ℝ) ≤ 1) hT0bound (x := y)
  have hS : S = T0 - T1 := by
    funext y
    exact gsPerturbAlternating_one theta base K y
  have hSint : Integrable S := by
    rw [hS]
    exact hT0.sub hT1
  have hSbound : ∀ y : ℝ, ‖S y‖ ≤ 1 + L := by
    intro y
    rw [hS, Pi.sub_apply]
    exact (norm_sub_le _ _).trans (add_le_add (hT0bound y) (hT1bound y))
  have hT0nonneg : ∀ y : ℝ, 0 ≤ T0 y := by
    intro y
    by_cases hy : y ∈ Ioo (0 : ℝ) K
    · change 0 ≤ gsLocalize K base y
      rw [gsLocalize, indicator_of_mem hy]
      exact (hbase.range y ⟨hy.1.le, hy.2.le⟩).1
    · change 0 ≤ gsLocalize K base y
      simp [gsLocalize, hy]
  have hT1nonneg : ∀ y : ℝ, 0 ≤ T1 y := by
    intro y
    change 0 ≤ (P ⋆[ContinuousLinearMap.mul ℝ ℝ] T0) y
    rw [convolution_def]
    apply integral_nonneg
    intro t
    simp only [ContinuousLinearMap.mul_apply']
    exact mul_nonneg (gsDefectLocal_nonneg htheta K t) (hT0nonneg (y - t))
  have hresNonneg (v : ℝ) :
      0 ≤ (gsWeightedDefectLocal theta K ⋆[ContinuousLinearMap.mul ℝ ℝ]
        T1) v := by
    rw [convolution_def]
    apply integral_nonneg
    intro t
    simp only [ContinuousLinearMap.mul_apply']
    exact mul_nonneg (gsWeightedDefectLocal_nonneg htheta K t)
      (hT1nonneg (v - t))
  have htauSub : ∀ v : ℝ, 1 ≤ v → v ≤ u →
      v * tau v ≤ ∫ t : ℝ in 0..v, target t * tau (v - t) := by
    intro v hv1 hvu
    have hv0 : 0 ≤ v := zero_le_one.trans hv1
    have hvK : v < K := hvu.trans_lt huK
    have hvne : v ≠ 0 := (zero_lt_one.trans_le hv1).ne'
    have hres := gsCompact_kernelChange_residual_one htheta hpsi htarget
      hrel hK hbase hv0 hvK
    have hconvEq :
        (gsKernelLocal target K ⋆[ContinuousLinearMap.mul ℝ ℝ] S) v =
          ∫ t : ℝ in 0..v, target t * tau (v - t) := by
      rw [gs_convolution_apply_of_nonpos_eq_zero
        (fun _t ht ↦ gsKernelLocal_nonpos target K ht)
        (fun _t ht ↦ gsPerturbAlternating_nonpos theta base K 1 ht) hv0]
      apply intervalIntegral.integral_congr_Ioo_of_le hv0
      intro t ht
      have htK : t ∈ Ioo (0 : ℝ) K := ⟨ht.1, ht.2.trans hvK⟩
      have hargpos : 0 < v - t := sub_pos.mpr ht.2
      change gsKernelLocal target K t * S (v - t) = target t * tau (v - t)
      rw [show gsKernelLocal target K t = target t by
        simp [gsKernelLocal, gsLocalize, htK]]
      simp [tau, S, gsPerturbFirstApprox, hargpos.ne']
    have htau : tau v = S v := by
      simp [tau, S, gsPerturbFirstApprox, hvne]
    rw [htau, ← hconvEq]
    change v * S v ≤ (gsKernelLocal target K ⋆[
      ContinuousLinearMap.mul ℝ ℝ] S) v
    rw [hres]
    exact le_add_of_nonneg_right (hresNonneg v)
  have htauInt : ∀ v : ℝ, 1 ≤ v → v ≤ u →
      IntervalIntegrable (fun t : ℝ ↦ target t * tau (v - t))
        volume 0 v := by
    intro v hv1 hvu
    have hv0 : 0 ≤ v := zero_le_one.trans hv1
    have hvK : v < K := hvu.trans_lt huK
    let Q : ℝ → ℝ := gsKernelLocal target K
    have hQ : Integrable Q :=
      integrable_gsKernelLocal htarget (zero_le_one.trans hK)
    have hex : ConvolutionExistsAt Q S v (ContinuousLinearMap.mul ℝ ℝ) :=
      gs_convolutionExistsAt_of_integrable_bounded hQ hSint hSbound
    have hi : Integrable (fun t : ℝ ↦ Q t * S (v - t)) := by
      simpa [ConvolutionExistsAt, ContinuousLinearMap.mul_apply'] using hex
    apply hi.intervalIntegrable.congr_uIoo
    intro t ht
    rw [uIoo_of_le hv0] at ht
    have htK : t ∈ Ioo (0 : ℝ) K := ⟨ht.1, ht.2.trans hvK⟩
    have hargpos : 0 < v - t := sub_pos.mpr ht.2
    change Q t * S (v - t) = target t * tau (v - t)
    rw [show Q t = target t by
      simp [Q, gsKernelLocal, gsLocalize, htK]]
    rw [show tau (v - t) = S (v - t) by
      simp [tau, S, gsPerturbFirstApprox, hargpos.ne']]
  have hbound : ∀ v ∈ Icc (0 : ℝ) u,
      max (tau v - targetSigma v) 0 ≤ B := by
    intro v hv
    by_cases hvzero : v = 0
    · subst v
      have ht0 : targetSigma 0 = 1 := htargetSigma.2.1 0 le_rfl
        (by norm_num)
      simp only [tau, gsPerturbFirstApprox, if_pos, ht0, sub_self,
        max_self, B]
      linarith
    · have htauEq : tau v = S v := by
        simp [tau, S, gsPerturbFirstApprox, hvzero]
      have htmem := gs_solution_mem_Icc htarget htargetSigma v hv.1
      have htAbs : |targetSigma v| ≤ 1 := by
        rw [abs_of_nonneg htmem.1]
        exact htmem.2
      have hSnorm := hSbound v
      have hSnormAbs : |S v| ≤ 1 + L := by
        simpa [Real.norm_eq_abs] using hSnorm
      apply max_le
      · calc
          tau v - targetSigma v ≤ |tau v - targetSigma v| := le_abs_self _
          _ ≤ |tau v| + |targetSigma v| := abs_sub _ _
          _ ≤ B := by rw [htauEq]; dsimp only [B]; linarith
      · dsimp only [B]
        linarith
  have hcompare := gs_local_subsolution_le_of_bounded htarget hu0
    (U := u) (B := B) (sigma := targetSigma) (tau := tau)
    (fun v hv0 hv1 ↦ by
      dsimp only [tau]
      rw [gsCompactPerturbFirstApprox_eq_one htheta hbase hv0 hv1
        (hv1.trans_lt (hu.trans_lt huK)),
        htargetSigma.2.1 v hv0 hv1])
    (fun v hv1 hvu ↦ by rw [← htargetSigma.2.2 v hv1])
    htauSub
    (fun v hv1 hvu ↦ intervalIntegrable_gs_solution_kernel
      htarget htargetSigma (zero_le_one.trans hv1))
    htauInt hbound
  have hle := hcompare u ⟨hu0, le_rfl⟩
  have hune : u ≠ 0 := (zero_lt_one.trans_le hu).ne'
  have hT0u : T0 u = base u := by
    change gsLocalize K base u = base u
    rw [gsLocalize, indicator_of_mem
      (show u ∈ Ioo (0 : ℝ) K from ⟨zero_lt_one.trans_le hu, huK⟩)]
  have hT1u := gsCompactPerturbIterate_one_le_logScale
    htheta hK hbase hu huK
  have htauEq : tau u = base u - T1 u := by
    rw [show tau u = S u by
      simp [tau, S, gsPerturbFirstApprox, hune],
      hS, Pi.sub_apply, hT0u]
  rw [htauEq] at hle
  linarith

/-- Odd Bonferroni inequalities for a solution constructed only on a compact
interval. -/
theorem gsCompact_oddBonferroni
    {chi base : ℝ → ℝ} (hchi : IsGSKernel chi)
    {K u : ℝ} (hK : 1 ≤ K) (hbase : GSCompactSolution chi base K)
    (hu : 1 ≤ u) (huK : u < K) (r : ℕ) :
    gsAlternatingMomentSum chi (2 * r + 1) u ≤ base u := by
  let N : ℕ := 2 * r + 1
  let tau : ℝ → ℝ := gsAlternatingMomentSum chi N
  let C : ℝ := ∑ j ∈ Finset.range (N + 1),
    gsLogScale chi u ^ j / j.factorial
  let B : ℝ := 1 + C
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hC0 : 0 ≤ C := gs_alternatingMomentSum_bound_nonneg hchi N hu
  have htauSub : ∀ v : ℝ, 1 ≤ v → v ≤ u →
      v * tau v ≤ ∫ t : ℝ in 0..v, chi t * tau (v - t) := by
    intro v hv1 hvu
    have hv0 : 0 ≤ v := zero_le_one.trans hv1
    have hvK : v < K := hvu.trans_lt huK
    have hid := gs_kernel_convolution_alternating_identity hchi N hK hv0 hvK
    have hconv := gs_weightedDefect_convolution_moment_nonneg hchi N hv0 hvK
    have hpow : (-1 : ℝ) ^ (N + 1) = 1 := by
      dsimp only [N]
      rw [show 2 * r + 1 + 1 = 2 * (r + 1) by omega, pow_mul]
      norm_num
    have hcoef : 0 ≤ (-1 : ℝ) ^ (N + 1) / N.factorial := by
      rw [hpow]
      positivity
    change v * gsAlternatingMomentSum chi N v ≤ _
    rw [hid]
    exact le_add_of_nonneg_right (mul_nonneg hcoef hconv)
  have hbound : ∀ v ∈ Icc (0 : ℝ) u,
      max (tau v - base v) 0 ≤ B := by
    intro v hv
    have habs := abs_gsAlternatingMomentSum_le hchi N hu hv.1 hv.2
    have hbmem := hbase.range v ⟨hv.1, hv.2.trans huK.le⟩
    have hbabs : |base v| ≤ 1 := by
      rw [abs_of_nonneg hbmem.1]
      exact hbmem.2
    apply max_le
    · calc
        tau v - base v ≤ |tau v - base v| := le_abs_self _
        _ ≤ |tau v| + |base v| := abs_sub _ _
        _ ≤ B := by dsimp only [tau, B, C] at habs ⊢; linarith
    · dsimp only [B]
      linarith
  have hcompare := gs_local_subsolution_le_of_bounded hchi hu0
    (U := u) (B := B) (sigma := base) (tau := tau)
    (fun v hv0 hv1 ↦ by
      dsimp only [tau]
      rw [gsAlternatingMomentSum_eq_one_of_le_one chi N hv0 hv1,
        hbase.one v hv0 hv1])
    (fun v hv1 hvu ↦ by rw [← hbase.equation v hv1 (hvu.trans_lt huK)])
    htauSub
    (fun v hv1 hvu ↦ hbase.integral v hv1 (hvu.trans_lt huK))
    (fun v hv1 hvu ↦ intervalIntegrable_gsKernel_mul_alternating hchi N
      (zero_le_one.trans hv1))
    hbound
  exact hcompare u ⟨hu0, le_rfl⟩

/-- Filled-kernel perturbation in the concrete form used in Proposition 6.1:
any odd truncation for the filled kernel remains a lower bound after
subtracting the removed logarithmic mass. -/
theorem gs_fill_odd_perturb_lower
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma)
    {u0 u : ℝ} (hu0 : 1 ≤ u0) (hu0u : u0 ≤ u) (hu : 1 ≤ u)
    (r : ℕ) :
    gsAlternatingMomentSum (gsFillAbove chi u0) (2 * r + 1) u -
        (gsLogScale chi u - gsLogScale chi u0) ≤ sigma u := by
  let K : ℝ := u + 1
  let N : ℕ := ⌈K⌉₊
  let base : ℝ → ℝ := gsAlternatingMomentSum (gsFillAbove chi u0) N
  have hK : 1 ≤ K := by dsimp only [K]; linarith
  have huK : u < K := by dsimp only [K]; linarith
  have hKN : K < (N : ℝ) + 1 := by
    have hceil : K ≤ N := Nat.le_ceil K
    exact hceil.trans_lt (by exact_mod_cast Nat.lt_succ_self N)
  have hfill := isGSKernel_gsFillAbove hchi u0
  have htail := isGSKernel_gsTailKernel hchi hu0
  have hbase : GSCompactSolution (gsFillAbove chi u0) base K :=
    gsCompactSolution_alternating hfill N hK hKN
  have hchange := gsCompact_kernelChange_lower_first htail hfill hchi hsigma
    (gsFillAbove_sub_weightedTail chi hu0) hK hbase hu huK
  have hodd := gsCompact_oddBonferroni hfill hK hbase hu huK r
  have htailLog := gsLogScale_gsTailKernel hchi hu0 hu0u
  dsimp only [base] at hodd hchange
  rw [htailLog] at hchange
  linarith

end

end Erdos783
