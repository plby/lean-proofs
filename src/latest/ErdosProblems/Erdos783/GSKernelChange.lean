/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos783.GSBonferroni
import ErdosProblems.Erdos783.GSModifiedKernel

/-! # Finite kernel-change expansion -/

open MeasureTheory Set Finset
open scoped BigOperators Convolution

namespace Erdos783

noncomputable section

/-- Compactly localized iterates of a defect density acting on a normalized
GS solution. -/
def gsPerturbIterate (theta sigma : ℝ → ℝ) (K : ℝ) : ℕ → ℝ → ℝ
  | 0 => gsLocalize K sigma
  | n + 1 => gsDefectLocal theta K ⋆[ContinuousLinearMap.mul ℝ ℝ]
      gsPerturbIterate theta sigma K n

def gsPerturbCoord (theta sigma : ℝ → ℝ) (K : ℝ) (n : ℕ) : ℝ → ℝ :=
  gsLocalize K (fun t ↦ t * gsPerturbIterate theta sigma K n t)

lemma gsPerturbIterate_nonpos (theta sigma : ℝ → ℝ) (K : ℝ) :
    ∀ n : ℕ, ∀ {t : ℝ}, t ≤ 0 → gsPerturbIterate theta sigma K n t = 0 := by
  intro n
  induction n with
  | zero =>
      intro t ht
      exact gsLocalize_eq_zero_of_nonpos K sigma ht
  | succ n ih =>
      intro t ht
      exact gs_convolution_eq_zero_of_nonpos
        (fun _s hs ↦ gsDefectLocal_nonpos theta K hs)
        (fun _s hs ↦ ih hs) ht

lemma gsPerturbCoord_nonpos (theta sigma : ℝ → ℝ) (K : ℝ) (n : ℕ)
    {t : ℝ} (ht : t ≤ 0) : gsPerturbCoord theta sigma K n t = 0 :=
  gsLocalize_eq_zero_of_nonpos K _ ht

lemma integrable_gsLocalize_solution
    {psi sigma : ℝ → ℝ} (hpsi : IsGSKernel psi)
    (hsigma : IsGSSolution psi sigma)
    {K : ℝ} (hK : 0 ≤ K) : Integrable (gsLocalize K sigma) := by
  apply integrable_gsLocalize hK
  exact (hsigma.1.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hK

lemma gsLocalize_solution_bound
    {psi sigma : ℝ → ℝ} (hpsi : IsGSKernel psi)
    (hsigma : IsGSSolution psi sigma) (K x : ℝ) :
    ‖gsLocalize K sigma x‖ ≤ 1 := by
  by_cases hx : x ∈ Ioo (0 : ℝ) K
  · rw [gsLocalize, indicator_of_mem hx, Real.norm_eq_abs,
      abs_of_nonneg (gs_solution_mem_Icc hpsi hsigma x hx.1.le).1]
    exact (gs_solution_mem_Icc hpsi hsigma x hx.1.le).2
  · simp [gsLocalize, hx]

lemma integrable_gsPerturbIterate
    {theta psi sigma : ℝ → ℝ} (htheta : IsGSKernel theta)
    (hpsi : IsGSKernel psi) (hsigma : IsGSSolution psi sigma)
    {K : ℝ} (hK : 1 ≤ K) :
    ∀ n : ℕ, Integrable (gsPerturbIterate theta sigma K n) := by
  intro n
  induction n with
  | zero =>
      exact integrable_gsLocalize_solution hpsi hsigma (zero_le_one.trans hK)
  | succ n ih =>
      exact (integrable_gsDefectLocal htheta hK).integrable_convolution
        (ContinuousLinearMap.mul ℝ ℝ) ih

lemma gsPerturbIterate_bound
    {theta psi sigma : ℝ → ℝ} (htheta : IsGSKernel theta)
    (hpsi : IsGSKernel psi) (hsigma : IsGSSolution psi sigma)
    {K : ℝ} (hK : 1 ≤ K) :
    ∀ n : ℕ, ∀ x : ℝ,
      ‖gsPerturbIterate theta sigma K n x‖ ≤
        (∫ t : ℝ, ‖gsDefectLocal theta K t‖) ^ n := by
  intro n
  induction n with
  | zero =>
      intro x
      change ‖gsLocalize K sigma x‖ ≤ 1
      exact gsLocalize_solution_bound hpsi hsigma K x
  | succ n ih =>
      intro x
      have hP := integrable_gsDefectLocal htheta hK
      have hL0 : 0 ≤ ∫ t : ℝ, ‖gsDefectLocal theta K t‖ :=
        integral_nonneg fun _ ↦ norm_nonneg _
      have h := gs_norm_convolution_le_integral_norm_mul hP
        (pow_nonneg hL0 n) ih (x := x)
      simpa [gsPerturbIterate, pow_succ, mul_comm] using h

lemma integrable_gsPerturbCoord
    {theta psi sigma : ℝ → ℝ} (htheta : IsGSKernel theta)
    (hpsi : IsGSKernel psi) (hsigma : IsGSSolution psi sigma)
    {K : ℝ} (hK : 1 ≤ K) (n : ℕ) :
    Integrable (gsPerturbCoord theta sigma K n) := by
  apply integrable_gsLocalize (zero_le_one.trans hK)
  have hT := integrable_gsPerturbIterate htheta hpsi hsigma hK n
  have hbase : IntervalIntegrable
      (gsPerturbIterate theta sigma K n) volume 0 K :=
    hT.intervalIntegrable
  have hmul := hbase.mul_continuousOn continuousOn_id
  convert hmul using 1
  ext t
  simp [id, mul_comm]

lemma gsPerturbCoord_bound
    {theta psi sigma : ℝ → ℝ} (htheta : IsGSKernel theta)
    (hpsi : IsGSKernel psi) (hsigma : IsGSSolution psi sigma)
    {K : ℝ} (hK : 1 ≤ K) (n : ℕ) (x : ℝ) :
    ‖gsPerturbCoord theta sigma K n x‖ ≤
      K * (∫ t : ℝ, ‖gsDefectLocal theta K t‖) ^ n := by
  by_cases hx : x ∈ Ioo (0 : ℝ) K
  · rw [gsPerturbCoord, gsLocalize, indicator_of_mem hx, norm_mul,
      Real.norm_eq_abs, abs_of_nonneg hx.1.le]
    exact mul_le_mul (le_of_lt hx.2)
      (gsPerturbIterate_bound htheta hpsi hsigma hK n x)
      (norm_nonneg _) (zero_le_one.trans hK)
  · have hz : gsPerturbCoord theta sigma K n x = 0 := by
      simp [gsPerturbCoord, gsLocalize, hx]
    rw [hz, norm_zero]
    exact mul_nonneg (zero_le_one.trans hK)
      (pow_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) _)

lemma gs_solution_kernel_convolution_base
    {psi sigma : ℝ → ℝ} (hpsi : IsGSKernel psi)
    (hsigma : IsGSSolution psi sigma)
    {K x : ℝ} (hK : 1 ≤ K) (hx0 : 0 ≤ x) (hxK : x < K) :
    (gsKernelLocal psi K ⋆[ContinuousLinearMap.mul ℝ ℝ]
      gsPerturbIterate (fun _ ↦ 1) sigma K 0) x =
      x * gsPerturbIterate (fun _ ↦ 1) sigma K 0 x := by
  change ((gsLocalize K psi) ⋆[ContinuousLinearMap.mul ℝ ℝ]
      (gsLocalize K sigma)) x = x * gsLocalize K sigma x
  rw [gsLocalize_convolution_apply hx0 hxK]
  by_cases hx : x = 0
  · subst x
    simp [gsLocalize]
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  rw [gsLocalize, indicator_of_mem (show x ∈ Ioo (0 : ℝ) K from ⟨hxpos, hxK⟩)]
  by_cases hx1 : 1 ≤ x
  · exact (hsigma.2.2 x hx1).symm
  · have hxle : x ≤ 1 := le_of_not_ge hx1
    rw [show (∫ t : ℝ in 0..x, psi t * sigma (x - t)) =
        ∫ _t : ℝ in 0..x, (1 : ℝ) by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hx0] at ht
      change psi t * sigma (x - t) = 1
      rw [hpsi.2.2.2 t ht.1 (ht.2.trans hxle),
        hsigma.2.1 (x - t) (sub_nonneg.mpr ht.2)
          ((sub_le_self _ ht.1).trans hxle)]
      norm_num]
    rw [hsigma.2.1 x hx0 hxle]
    simp

/-- Multiplication by the endpoint coordinate splits between the newest
perturbation variable and the previous iterate. -/
lemma gs_perturb_coordinate_identity
    {theta psi sigma : ℝ → ℝ} (htheta : IsGSKernel theta)
    (hpsi : IsGSKernel psi) (hsigma : IsGSSolution psi sigma)
    (n : ℕ) {K x : ℝ} (hK : 1 ≤ K) (hx0 : 0 ≤ x) (hxK : x < K) :
    x * gsPerturbIterate theta sigma K (n + 1) x =
      (gsWeightedDefectLocal theta K ⋆[ContinuousLinearMap.mul ℝ ℝ]
        gsPerturbIterate theta sigma K n) x +
      (gsDefectLocal theta K ⋆[ContinuousLinearMap.mul ℝ ℝ]
        gsPerturbCoord theta sigma K n) x := by
  let P : ℝ → ℝ := gsDefectLocal theta K
  let D : ℝ → ℝ := gsWeightedDefectLocal theta K
  let T : ℝ → ℝ := gsPerturbIterate theta sigma K n
  let C : ℝ → ℝ := gsPerturbCoord theta sigma K n
  have hPnonpos : ∀ t : ℝ, t ≤ 0 → P t = 0 :=
    fun _t ht ↦ gsDefectLocal_nonpos theta K ht
  have hDnonpos : ∀ t : ℝ, t ≤ 0 → D t = 0 :=
    fun _t ht ↦ gsWeightedDefectLocal_nonpos theta K ht
  have hTnonpos : ∀ t : ℝ, t ≤ 0 → T t = 0 :=
    fun _t ht ↦ gsPerturbIterate_nonpos theta sigma K n ht
  have hCnonpos : ∀ t : ℝ, t ≤ 0 → C t = 0 :=
    fun _t ht ↦ gsPerturbCoord_nonpos theta sigma K n ht
  have hP := integrable_gsDefectLocal htheta hK
  have hD := integrable_gsWeightedDefectLocal htheta hK
  have hT := integrable_gsPerturbIterate htheta hpsi hsigma hK n
  have hC := integrable_gsPerturbCoord htheta hpsi hsigma hK n
  let L : ℝ := ∫ t : ℝ, ‖P t‖
  have hL0 : 0 ≤ L := integral_nonneg fun _ ↦ norm_nonneg _
  have hTbound : ∀ y : ℝ, ‖T y‖ ≤ L ^ n := by
    exact gsPerturbIterate_bound htheta hpsi hsigma hK n
  have hCbound : ∀ y : ℝ, ‖C y‖ ≤ K * L ^ n := by
    exact gsPerturbCoord_bound htheta hpsi hsigma hK n
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
  change x * gsPerturbIterate theta sigma K (n + 1) x = _
  exact hcoord

/-- Coordinate-sum identity for perturbation iterates.  The base coordinate
is supplied by the GS equation for `sigma`; every subsequent coordinate is
distributed among the inserted defect variables. -/
theorem gs_kernel_convolution_perturb_identity
    {theta psi sigma : ℝ → ℝ} (htheta : IsGSKernel theta)
    (hpsi : IsGSKernel psi) (hsigma : IsGSSolution psi sigma) :
    ∀ n : ℕ, ∀ {K x : ℝ}, 1 ≤ K → 0 ≤ x → x < K →
      (gsKernelLocal psi K ⋆[ContinuousLinearMap.mul ℝ ℝ]
          gsPerturbIterate theta sigma K n) x +
        (n : ℝ) *
          (gsWeightedDefectLocal theta K ⋆[ContinuousLinearMap.mul ℝ ℝ]
            gsPerturbIterate theta sigma K n.pred) x =
        x * gsPerturbIterate theta sigma K n x := by
  intro n
  induction n with
  | zero =>
      intro K x hK hx0 hxK
      rw [Nat.cast_zero, zero_mul, add_zero]
      simpa [gsPerturbIterate] using
        (gs_solution_kernel_convolution_base hpsi hsigma hK hx0 hxK)
  | succ n ih =>
      intro K x hK hx0 hxK
      let H : ℝ → ℝ := gsKernelLocal psi K
      let P : ℝ → ℝ := gsDefectLocal theta K
      let D : ℝ → ℝ := gsWeightedDefectLocal theta K
      let Tn : ℝ → ℝ := gsPerturbIterate theta sigma K n
      let Tp : ℝ → ℝ := gsPerturbIterate theta sigma K n.pred
      let Ts : ℝ → ℝ := gsPerturbIterate theta sigma K (n + 1)
      let Cn : ℝ → ℝ := gsPerturbCoord theta sigma K n
      let A : ℝ → ℝ := H ⋆[ContinuousLinearMap.mul ℝ ℝ] Tn
      let B : ℝ → ℝ := D ⋆[ContinuousLinearMap.mul ℝ ℝ] Tp
      let G : ℝ → ℝ := A + (n : ℝ) • B
      have hH : Integrable H :=
        integrable_gsKernelLocal hpsi (zero_le_one.trans hK)
      have hP : Integrable P := integrable_gsDefectLocal htheta hK
      have hD : Integrable D := integrable_gsWeightedDefectLocal htheta hK
      have hTn : Integrable Tn :=
        integrable_gsPerturbIterate htheta hpsi hsigma hK n
      have hTp : Integrable Tp :=
        integrable_gsPerturbIterate htheta hpsi hsigma hK n.pred
      have hTs : Integrable Ts :=
        integrable_gsPerturbIterate htheta hpsi hsigma hK (n + 1)
      have hCn : Integrable Cn :=
        integrable_gsPerturbCoord htheta hpsi hsigma hK n
      let L : ℝ := ∫ t : ℝ, ‖P t‖
      have hL0 : 0 ≤ L := integral_nonneg fun _ ↦ norm_nonneg _
      have hTnbound : ∀ y : ℝ, ‖Tn y‖ ≤ L ^ n :=
        gsPerturbIterate_bound htheta hpsi hsigma hK n
      have hTpbound : ∀ y : ℝ, ‖Tp y‖ ≤ L ^ n.pred :=
        gsPerturbIterate_bound htheta hpsi hsigma hK n.pred
      have hreplaceD :
          (n : ℝ) * (D ⋆[ContinuousLinearMap.mul ℝ ℝ] Tn) x =
            (n : ℝ) *
              (D ⋆[ContinuousLinearMap.mul ℝ ℝ]
                (P ⋆[ContinuousLinearMap.mul ℝ ℝ] Tp)) x := by
        cases n with
        | zero => simp
        | succ m => rfl
      have hassocHP :
          (H ⋆[ContinuousLinearMap.mul ℝ ℝ]
              (P ⋆[ContinuousLinearMap.mul ℝ ℝ] Tn)) x =
            (P ⋆[ContinuousLinearMap.mul ℝ ℝ]
              (H ⋆[ContinuousLinearMap.mul ℝ ℝ] Tn)) x := by
        calc
          _ = ((H ⋆[ContinuousLinearMap.mul ℝ ℝ] P) ⋆[
                ContinuousLinearMap.mul ℝ ℝ] Tn) x :=
            (gs_convolution_assoc_of_integrable_bounded hH hP hTn
              hTnbound).symm
          _ = ((P ⋆[ContinuousLinearMap.mul ℝ ℝ] H) ⋆[
                ContinuousLinearMap.mul ℝ ℝ] Tn) x := by
            rw [gs_convolution_comm H P]
          _ = _ :=
            gs_convolution_assoc_of_integrable_bounded hP hH hTn hTnbound
      have hassocDP :
          (D ⋆[ContinuousLinearMap.mul ℝ ℝ]
              (P ⋆[ContinuousLinearMap.mul ℝ ℝ] Tp)) x =
            (P ⋆[ContinuousLinearMap.mul ℝ ℝ]
              (D ⋆[ContinuousLinearMap.mul ℝ ℝ] Tp)) x := by
        calc
          _ = ((D ⋆[ContinuousLinearMap.mul ℝ ℝ] P) ⋆[
                ContinuousLinearMap.mul ℝ ℝ] Tp) x :=
            (gs_convolution_assoc_of_integrable_bounded hD hP hTp
              hTpbound).symm
          _ = ((P ⋆[ContinuousLinearMap.mul ℝ ℝ] D) ⋆[
                ContinuousLinearMap.mul ℝ ℝ] Tp) x := by
            rw [gs_convolution_comm D P]
          _ = _ :=
            gs_convolution_assoc_of_integrable_bounded hP hD hTp hTpbound
      have hAint : Integrable A := hH.integrable_convolution
        (ContinuousLinearMap.mul ℝ ℝ) hTn
      have hBint : Integrable B := hD.integrable_convolution
        (ContinuousLinearMap.mul ℝ ℝ) hTp
      let CA : ℝ := (∫ t : ℝ, ‖H t‖) * L ^ n
      let CB : ℝ := (∫ t : ℝ, ‖D t‖) * L ^ n.pred
      have hCA0 : 0 ≤ CA := mul_nonneg
        (integral_nonneg fun _ ↦ norm_nonneg _) (pow_nonneg hL0 _)
      have hCB0 : 0 ≤ CB := mul_nonneg
        (integral_nonneg fun _ ↦ norm_nonneg _) (pow_nonneg hL0 _)
      have hAbound : ∀ y : ℝ, ‖A y‖ ≤ CA := by
        intro y
        exact gs_norm_convolution_le_integral_norm_mul hH
          (pow_nonneg hL0 _) hTnbound
      have hBbound : ∀ y : ℝ, ‖B y‖ ≤ CB := by
        intro y
        exact gs_norm_convolution_le_integral_norm_mul hD
          (pow_nonneg hL0 _) hTpbound
      have hPA : ConvolutionExistsAt P A x (ContinuousLinearMap.mul ℝ ℝ) :=
        gs_convolutionExistsAt_of_integrable_bounded hP hAint hAbound
      have hPB : ConvolutionExistsAt P B x (ContinuousLinearMap.mul ℝ ℝ) :=
        gs_convolutionExistsAt_of_integrable_bounded hP hBint hBbound
      have hPnB : ConvolutionExistsAt P ((n : ℝ) • B) x
          (ContinuousLinearMap.mul ℝ ℝ) := by
        rw [ConvolutionExistsAt] at hPB ⊢
        convert hPB.const_mul (n : ℝ) using 1
        ext t
        simp [smul_eq_mul, ContinuousLinearMap.mul_apply']
        ring
      have hdistrib :
          (P ⋆[ContinuousLinearMap.mul ℝ ℝ] G) x =
            (P ⋆[ContinuousLinearMap.mul ℝ ℝ] A) x +
              (n : ℝ) * (P ⋆[ContinuousLinearMap.mul ℝ ℝ] B) x := by
        have hd := hPA.distrib_add hPnB
        change (P ⋆[ContinuousLinearMap.mul ℝ ℝ]
            (A + (n : ℝ) • B)) x = _ at hd
        rw [convolution_smul] at hd
        simpa [G, Pi.smul_apply, smul_eq_mul] using hd
      have hCG :
          (P ⋆[ContinuousLinearMap.mul ℝ ℝ] Cn) x =
            (P ⋆[ContinuousLinearMap.mul ℝ ℝ] G) x := by
        apply gs_convolution_congr_Icc
          (fun _t ht ↦ gsDefectLocal_nonpos theta K ht)
          (fun _t ht ↦ gsPerturbCoord_nonpos theta sigma K n ht)
          (fun t ht ↦ by
            dsimp only [G, A, B]
            rw [Pi.add_apply, Pi.smul_apply]
            simp only [smul_eq_mul]
            rw [gs_convolution_eq_zero_of_nonpos
              (fun _s hs ↦ gsKernelLocal_nonpos psi K hs)
              (fun _s hs ↦ gsPerturbIterate_nonpos theta sigma K n hs) ht,
              gs_convolution_eq_zero_of_nonpos
                (fun _s hs ↦ gsWeightedDefectLocal_nonpos theta K hs)
                (fun _s hs ↦
                  gsPerturbIterate_nonpos theta sigma K n.pred hs) ht]
            ring)
          hx0
        intro y hy
        have hyK : y < K := hy.2.trans_lt hxK
        have hiy := ih (K := K) (x := y) hK hy.1 hyK
        dsimp only [Cn, G, A, B, gsPerturbCoord]
        rw [Pi.add_apply, Pi.smul_apply]
        simp only [smul_eq_mul]
        by_cases hyzero : y = 0
        · subst y
          have hz := hiy.symm
          simpa [H, D, Tn, Tp, gsLocalize] using hz
        · have hypos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hyzero)
          rw [gsLocalize, indicator_of_mem
            (show y ∈ Ioo (0 : ℝ) K from ⟨hypos, hyK⟩)]
          exact hiy.symm
      have hmiddle :
          (H ⋆[ContinuousLinearMap.mul ℝ ℝ] Ts) x +
              (n : ℝ) * (D ⋆[ContinuousLinearMap.mul ℝ ℝ] Tn) x =
            (P ⋆[ContinuousLinearMap.mul ℝ ℝ] Cn) x := by
        change (H ⋆[ContinuousLinearMap.mul ℝ ℝ]
            (P ⋆[ContinuousLinearMap.mul ℝ ℝ] Tn)) x + _ = _
        rw [hreplaceD, hassocHP, hassocDP, hCG, hdistrib]
      have hcoord := gs_perturb_coordinate_identity htheta hpsi hsigma
        n hK hx0 hxK
      change x * Ts x =
        (D ⋆[ContinuousLinearMap.mul ℝ ℝ] Tn) x +
          (P ⋆[ContinuousLinearMap.mul ℝ ℝ] Cn) x at hcoord
      change (H ⋆[ContinuousLinearMap.mul ℝ ℝ] Ts) x +
          ((n + 1 : ℕ) : ℝ) *
            (D ⋆[ContinuousLinearMap.mul ℝ ℝ] Tn) x = x * Ts x
      rw [hcoord, ← hmiddle]
      push_cast
      ring

def gsPerturbAlternating
    (theta sigma : ℝ → ℝ) (K : ℝ) (N : ℕ) : ℝ → ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    ((-1 : ℝ) ^ j / j.factorial) • gsPerturbIterate theta sigma K j

lemma gsPerturbAlternating_succ
    (theta sigma : ℝ → ℝ) (K : ℝ) (N : ℕ) :
    gsPerturbAlternating theta sigma K (N + 1) =
      gsPerturbAlternating theta sigma K N +
        ((-1 : ℝ) ^ (N + 1) / (N + 1).factorial) •
          gsPerturbIterate theta sigma K (N + 1) := by
  simp only [gsPerturbAlternating]
  rw [show N + 1 + 1 = (N + 1) + 1 by omega,
    Finset.sum_range_succ]

lemma integrable_gsPerturbAlternating
    {theta psi sigma : ℝ → ℝ} (htheta : IsGSKernel theta)
    (hpsi : IsGSKernel psi) (hsigma : IsGSSolution psi sigma)
    {K : ℝ} (hK : 1 ≤ K) (N : ℕ) :
    Integrable (gsPerturbAlternating theta sigma K N) := by
  unfold gsPerturbAlternating
  apply integrable_finsetSum'
  intro j hj
  exact (integrable_gsPerturbIterate htheta hpsi hsigma hK j).const_mul _

lemma gsPerturbAlternating_nonpos
    (theta sigma : ℝ → ℝ) (K : ℝ) (N : ℕ)
    {t : ℝ} (ht : t ≤ 0) :
    gsPerturbAlternating theta sigma K N t = 0 := by
  simp [gsPerturbAlternating, gsPerturbIterate_nonpos theta sigma K _ ht]

lemma gsPerturbAlternating_bound
    {theta psi sigma : ℝ → ℝ} (htheta : IsGSKernel theta)
    (hpsi : IsGSKernel psi) (hsigma : IsGSSolution psi sigma)
    {K : ℝ} (hK : 1 ≤ K) (N : ℕ) (x : ℝ) :
    ‖gsPerturbAlternating theta sigma K N x‖ ≤
      ∑ j ∈ Finset.range (N + 1),
        (∫ t : ℝ, ‖gsDefectLocal theta K t‖) ^ j / j.factorial := by
  rw [show gsPerturbAlternating theta sigma K N x =
      ∑ j ∈ Finset.range (N + 1),
        ((-1 : ℝ) ^ j / j.factorial) *
          gsPerturbIterate theta sigma K j x by
    simp [gsPerturbAlternating, smul_eq_mul]]
  calc
    ‖∑ j ∈ Finset.range (N + 1),
        ((-1 : ℝ) ^ j / j.factorial) *
          gsPerturbIterate theta sigma K j x‖ ≤
        ∑ j ∈ Finset.range (N + 1),
          ‖((-1 : ℝ) ^ j / j.factorial) *
            gsPerturbIterate theta sigma K j x‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (N + 1),
          (∫ t : ℝ, ‖gsDefectLocal theta K t‖) ^ j / j.factorial := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, Real.norm_eq_abs, abs_div, abs_pow,
        abs_neg, abs_one, one_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ j.factorial)]
      have hb := gsPerturbIterate_bound htheta hpsi hsigma hK j x
      calc
        1 / (j.factorial : ℝ) * ‖gsPerturbIterate theta sigma K j x‖ ≤
            1 / (j.factorial : ℝ) *
              (∫ t : ℝ, ‖gsDefectLocal theta K t‖) ^ j :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _ = (∫ t : ℝ, ‖gsDefectLocal theta K t‖) ^ j /
              j.factorial := by ring

/-- Convolution of one perturbation iterate with the target kernel.  The
defect-density relation is the exact analytic form of
`target = base - t * perturbation`. -/
lemma gs_kernelChange_convolution_iterate_identity
    {theta psi target sigma : ℝ → ℝ}
    (htheta : IsGSKernel theta) (hpsi : IsGSKernel psi)
    (htarget : IsGSKernel target) (hsigma : IsGSSolution psi sigma)
    (hrel : ∀ t : ℝ, target t = psi t - t * gsDefectWeight theta t)
    (n : ℕ) {K x : ℝ} (hK : 1 ≤ K) (hx0 : 0 ≤ x) (hxK : x < K) :
    (gsKernelLocal target K ⋆[ContinuousLinearMap.mul ℝ ℝ]
        gsPerturbIterate theta sigma K n) x =
      x * gsPerturbIterate theta sigma K n x -
        (n : ℝ) *
          (gsWeightedDefectLocal theta K ⋆[ContinuousLinearMap.mul ℝ ℝ]
            gsPerturbIterate theta sigma K n.pred) x -
        (gsWeightedDefectLocal theta K ⋆[ContinuousLinearMap.mul ℝ ℝ]
          gsPerturbIterate theta sigma K n) x := by
  let Q : ℝ → ℝ := gsKernelLocal target K
  let H : ℝ → ℝ := gsKernelLocal psi K
  let D : ℝ → ℝ := gsWeightedDefectLocal theta K
  let T : ℝ → ℝ := gsPerturbIterate theta sigma K n
  let Tp : ℝ → ℝ := gsPerturbIterate theta sigma K n.pred
  have hQ : Integrable Q :=
    integrable_gsKernelLocal htarget (zero_le_one.trans hK)
  have hH : Integrable H :=
    integrable_gsKernelLocal hpsi (zero_le_one.trans hK)
  have hD : Integrable D := integrable_gsWeightedDefectLocal htheta hK
  have hT : Integrable T :=
    integrable_gsPerturbIterate htheta hpsi hsigma hK n
  let L : ℝ := ∫ t : ℝ, ‖gsDefectLocal theta K t‖
  have hL0 : 0 ≤ L := integral_nonneg fun _ ↦ norm_nonneg _
  have hTbound : ∀ y : ℝ, ‖T y‖ ≤ L ^ n :=
    gsPerturbIterate_bound htheta hpsi hsigma hK n
  have hHT : ConvolutionExistsAt H T x (ContinuousLinearMap.mul ℝ ℝ) :=
    gs_convolutionExistsAt_of_integrable_bounded hH hT hTbound
  have hDT : ConvolutionExistsAt D T x (ContinuousLinearMap.mul ℝ ℝ) :=
    gs_convolutionExistsAt_of_integrable_bounded hD hT hTbound
  have hQeq : Q = H - D := by
    funext t
    by_cases ht : t ∈ Ioo (0 : ℝ) K
    · simp only [Q, H, D, gsKernelLocal, gsWeightedDefectLocal,
        gsLocalize, indicator_of_mem ht, Pi.sub_apply]
      exact hrel t
    · simp [Q, H, D, gsKernelLocal, gsWeightedDefectLocal,
        gsLocalize, ht]
  have hsplit :
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
  have hcoord := gs_kernel_convolution_perturb_identity
    htheta hpsi hsigma n hK hx0 hxK
  change (H ⋆[ContinuousLinearMap.mul ℝ ℝ] T) x +
      (n : ℝ) * (D ⋆[ContinuousLinearMap.mul ℝ ℝ] Tp) x = x * T x at hcoord
  change (Q ⋆[ContinuousLinearMap.mul ℝ ℝ] T) x = _
  rw [hsplit]
  linarith

/-- Exact residual of the finite alternating kernel-change expansion. -/
theorem gs_kernelChange_alternating_residual
    {theta psi target sigma : ℝ → ℝ}
    (htheta : IsGSKernel theta) (hpsi : IsGSKernel psi)
    (htarget : IsGSKernel target) (hsigma : IsGSSolution psi sigma)
    (hrel : ∀ t : ℝ, target t = psi t - t * gsDefectWeight theta t) :
    ∀ N : ℕ, ∀ {K x : ℝ}, 1 ≤ K → 0 ≤ x → x < K →
      (gsKernelLocal target K ⋆[ContinuousLinearMap.mul ℝ ℝ]
          gsPerturbAlternating theta sigma K N) x =
        x * gsPerturbAlternating theta sigma K N x +
          ((-1 : ℝ) ^ (N + 1) / N.factorial) *
            (gsWeightedDefectLocal theta K ⋆[ContinuousLinearMap.mul ℝ ℝ]
              gsPerturbIterate theta sigma K N) x := by
  intro N
  induction N with
  | zero =>
      intro K x hK hx0 hxK
      have h := gs_kernelChange_convolution_iterate_identity
        htheta hpsi htarget hsigma hrel 0 hK hx0 hxK
      rw [show gsPerturbAlternating theta sigma K 0 =
          gsLocalize K sigma by
        funext y
        simp [gsPerturbAlternating, gsPerturbIterate, smul_eq_mul]]
      convert h using 1 <;> norm_num [gsPerturbIterate] <;> ring
  | succ N ih =>
      intro K x hK hx0 hxK
      let Q : ℝ → ℝ := gsKernelLocal target K
      let D : ℝ → ℝ := gsWeightedDefectLocal theta K
      let TN : ℝ → ℝ := gsPerturbIterate theta sigma K N
      let TS : ℝ → ℝ := gsPerturbIterate theta sigma K (N + 1)
      let SN : ℝ → ℝ := gsPerturbAlternating theta sigma K N
      let a : ℝ := (-1 : ℝ) ^ (N + 1) / (N + 1).factorial
      have hQ : Integrable Q :=
        integrable_gsKernelLocal htarget (zero_le_one.trans hK)
      have hSN : Integrable SN :=
        integrable_gsPerturbAlternating htheta hpsi hsigma hK N
      have hTS : Integrable TS :=
        integrable_gsPerturbIterate htheta hpsi hsigma hK (N + 1)
      let L : ℝ := ∫ t : ℝ, ‖gsDefectLocal theta K t‖
      let CS : ℝ := ∑ j ∈ Finset.range (N + 1), L ^ j / j.factorial
      have hSNbound : ∀ y : ℝ, ‖SN y‖ ≤ CS :=
        gsPerturbAlternating_bound htheta hpsi hsigma hK N
      have hTSbound : ∀ y : ℝ, ‖TS y‖ ≤ L ^ (N + 1) :=
        gsPerturbIterate_bound htheta hpsi hsigma hK (N + 1)
      have hQSN : ConvolutionExistsAt Q SN x (ContinuousLinearMap.mul ℝ ℝ) :=
        gs_convolutionExistsAt_of_integrable_bounded hQ hSN hSNbound
      have hQTS : ConvolutionExistsAt Q TS x (ContinuousLinearMap.mul ℝ ℝ) :=
        gs_convolutionExistsAt_of_integrable_bounded hQ hTS hTSbound
      have hQaTS : ConvolutionExistsAt Q (a • TS) x
          (ContinuousLinearMap.mul ℝ ℝ) := by
        rw [ConvolutionExistsAt] at hQTS ⊢
        convert hQTS.const_mul a using 1
        ext t
        simp [smul_eq_mul, ContinuousLinearMap.mul_apply']
        ring
      have hsplit :
          (Q ⋆[ContinuousLinearMap.mul ℝ ℝ]
              gsPerturbAlternating theta sigma K (N + 1)) x =
            (Q ⋆[ContinuousLinearMap.mul ℝ ℝ] SN) x +
              a * (Q ⋆[ContinuousLinearMap.mul ℝ ℝ] TS) x := by
        rw [gsPerturbAlternating_succ]
        have hd := hQSN.distrib_add hQaTS
        rw [convolution_smul] at hd
        simpa [SN, TS, Pi.smul_apply, smul_eq_mul] using hd
      have hih := ih hK hx0 hxK
      have hterm := gs_kernelChange_convolution_iterate_identity
        htheta hpsi htarget hsigma hrel (N + 1) hK hx0 hxK
      change (Q ⋆[ContinuousLinearMap.mul ℝ ℝ] SN) x =
        x * SN x +
          ((-1 : ℝ) ^ (N + 1) / N.factorial) *
            (D ⋆[ContinuousLinearMap.mul ℝ ℝ] TN) x at hih
      change (Q ⋆[ContinuousLinearMap.mul ℝ ℝ] TS) x =
        x * TS x - ((N + 1 : ℕ) : ℝ) *
          (D ⋆[ContinuousLinearMap.mul ℝ ℝ] TN) x -
          (D ⋆[ContinuousLinearMap.mul ℝ ℝ] TS) x at hterm
      have hfact : (((N + 1).factorial : ℕ) : ℝ) =
          ((N + 1 : ℕ) : ℝ) * (N.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        norm_cast
      have hcoef : a * ((N + 1 : ℕ) : ℝ) =
          (-1 : ℝ) ^ (N + 1) / N.factorial := by
        dsimp only [a]
        rw [hfact]
        field_simp
      have hnext :
          (-1 : ℝ) ^ (N + 1 + 1) / (N + 1).factorial = -a := by
        dsimp only [a]
        rw [pow_succ]
        ring
      rw [hsplit, hih, hterm, gsPerturbAlternating_succ]
      change _ = x * (SN x + a * TS x) +
        ((-1 : ℝ) ^ (N + 1 + 1) / (N + 1).factorial) *
          (D ⋆[ContinuousLinearMap.mul ℝ ℝ] TS) x
      rw [← hcoef, hnext]
      ring

lemma gsDefectLocal_nonneg
    {theta : ℝ → ℝ} (htheta : IsGSKernel theta) (K t : ℝ) :
    0 ≤ gsDefectLocal theta K t := by
  by_cases ht : t ∈ Ioo (0 : ℝ) K
  · rw [gsDefectLocal, gsLocalize, indicator_of_mem ht]
    by_cases ht1 : t ≤ 1
    · simp [gsDefectWeight, htheta.2.2.2 t ht.1.le ht1]
    · exact gsDefectWeight_nonneg htheta (lt_of_not_ge ht1).le
  · simp [gsDefectLocal, gsLocalize, ht]

lemma gsWeightedDefectLocal_nonneg
    {theta : ℝ → ℝ} (htheta : IsGSKernel theta) (K t : ℝ) :
    0 ≤ gsWeightedDefectLocal theta K t := by
  by_cases ht : t ∈ Ioo (0 : ℝ) K
  · rw [gsWeightedDefectLocal, gsLocalize, indicator_of_mem ht]
    exact mul_nonneg ht.1.le (by
      by_cases ht1 : t ≤ 1
      · simp [gsDefectWeight, htheta.2.2.2 t ht.1.le ht1]
      · exact gsDefectWeight_nonneg htheta (lt_of_not_ge ht1).le)
  · simp [gsWeightedDefectLocal, gsLocalize, ht]

lemma gsPerturbIterate_nonneg
    {theta psi sigma : ℝ → ℝ} (htheta : IsGSKernel theta)
    (hpsi : IsGSKernel psi) (hsigma : IsGSSolution psi sigma)
    (K : ℝ) : ∀ n : ℕ, ∀ x : ℝ,
      0 ≤ gsPerturbIterate theta sigma K n x := by
  intro n
  induction n with
  | zero =>
      intro x
      by_cases hx : x ∈ Ioo (0 : ℝ) K
      · rw [gsPerturbIterate, gsLocalize, indicator_of_mem hx]
        exact (gs_solution_mem_Icc hpsi hsigma x hx.1.le).1
      · simp [gsPerturbIterate, gsLocalize, hx]
  | succ n ih =>
      intro x
      rw [gsPerturbIterate, convolution_def]
      apply integral_nonneg
      intro t
      simp only [ContinuousLinearMap.mul_apply']
      exact mul_nonneg (gsDefectLocal_nonneg htheta K t) (ih (x - t))

lemma gsPerturbIterate_one_eq_zero_of_le_one
    {theta psi sigma : ℝ → ℝ} (htheta : IsGSKernel theta)
    {K x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hxK : x < K) :
    gsPerturbIterate theta sigma K 1 x = 0 := by
  rw [gsPerturbIterate,
    gs_convolution_apply_of_nonpos_eq_zero
      (fun _t ht ↦ gsDefectLocal_nonpos theta K ht)
      (fun _t ht ↦ gsPerturbIterate_nonpos theta sigma K 0 ht) hx0]
  rw [show (∫ t : ℝ in 0..x,
      gsDefectLocal theta K t *
        gsPerturbIterate theta sigma K 0 (x - t)) =
      ∫ _t : ℝ in 0..x, (0 : ℝ) by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx0] at ht
    have htK : t ∈ Ioo (0 : ℝ) K ∨ t = 0 := by
      by_cases ht0 : t = 0
      · exact Or.inr ht0
      · exact Or.inl ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
          ht.2.trans_lt hxK⟩
    rcases htK with htK | rfl
    · have hthetaOne : theta t = 1 :=
        htheta.2.2.2 t ht.1 (ht.2.trans hx1)
      simp [gsDefectLocal, gsLocalize, htK, gsDefectWeight, hthetaOne]
    · simp [gsDefectLocal, gsLocalize]]
  simp

lemma gsPerturbIterate_one_le_logScale
    {theta psi sigma : ℝ → ℝ} (htheta : IsGSKernel theta)
    (hpsi : IsGSKernel psi) (hsigma : IsGSSolution psi sigma)
    {K x : ℝ} (hK : 1 ≤ K) (hx1 : 1 ≤ x) (hxK : x < K) :
    gsPerturbIterate theta sigma K 1 x ≤ gsLogScale theta x := by
  let P : ℝ → ℝ := gsDefectLocal theta K
  let T : ℝ → ℝ := gsPerturbIterate theta sigma K 0
  let H : ℝ → ℝ := gsMomentLocal theta K 0
  have hP : Integrable P := integrable_gsDefectLocal htheta hK
  have hT : Integrable T :=
    integrable_gsPerturbIterate htheta hpsi hsigma hK 0
  have hH : Integrable H :=
    integrable_gsMomentLocal htheta 0 (zero_le_one.trans hK)
  have hTbound : ∀ y : ℝ, ‖T y‖ ≤ 1 := by
    simpa [T] using gsPerturbIterate_bound htheta hpsi hsigma hK 0
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
    · change gsLocalize K sigma y ≤ gsLocalize K (gsMoment theta 0) y
      simp [gsLocalize, hy, (gs_solution_mem_Icc hpsi hsigma y hy.1.le).2]
    · change gsLocalize K sigma y ≤ gsLocalize K (gsMoment theta 0) y
      simp [gsLocalize, hy]
  have hmono := convolution_mono_right hPT hPH
    (fun y ↦ gsDefectLocal_nonneg htheta K y) hTH
  have hrec := gsDefectLocal_convolution_momentLocal htheta 0
    (zero_le_one.trans hx1) hxK
  change (P ⋆[ContinuousLinearMap.mul ℝ ℝ] T) x ≤ _
  rw [← gsMoment_one theta hx1, ← hrec]
  exact hmono

/-- Patch the harmless value at zero in the localized first perturbation
sum.  Changing this single value does not alter any interval integral. -/
def gsPerturbFirstApprox
    (theta sigma : ℝ → ℝ) (K u : ℝ) : ℝ :=
  if u = 0 then 1 else gsPerturbAlternating theta sigma K 1 u

lemma gsPerturbFirstApprox_eq_one
    {theta psi sigma : ℝ → ℝ} (htheta : IsGSKernel theta)
    (hsigma : IsGSSolution psi sigma)
    {K u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (huK : u < K) :
    gsPerturbFirstApprox theta sigma K u = 1 := by
  by_cases hu : u = 0
  · simp [gsPerturbFirstApprox, hu]
  · have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    have hT0 : gsPerturbIterate theta sigma K 0 u = 1 := by
      change gsLocalize K sigma u = 1
      rw [gsLocalize, indicator_of_mem
          (show u ∈ Ioo (0 : ℝ) K from ⟨hupos, huK⟩),
        hsigma.2.1 u hu0 hu1]
    have hT1 := gsPerturbIterate_one_eq_zero_of_le_one
      (psi := psi) (sigma := sigma) htheta hu0 hu1 huK
    rw [gsPerturbFirstApprox, if_neg hu]
    change (∑ j ∈ Finset.range 2,
      ((-1 : ℝ) ^ j / j.factorial) *
        gsPerturbIterate theta sigma K j u) = 1
    rw [show (∑ j ∈ Finset.range 2,
        ((-1 : ℝ) ^ j / j.factorial) *
          gsPerturbIterate theta sigma K j u) =
        gsPerturbIterate theta sigma K 0 u -
          gsPerturbIterate theta sigma K 1 u by
      norm_num [Finset.sum_range_succ]
      ring]
    rw [hT0, hT1]
    norm_num

lemma gsPerturbAlternating_one
    (theta sigma : ℝ → ℝ) (K u : ℝ) :
    gsPerturbAlternating theta sigma K 1 u =
      gsPerturbIterate theta sigma K 0 u -
        gsPerturbIterate theta sigma K 1 u := by
  change (∑ j ∈ Finset.range 2,
    ((-1 : ℝ) ^ j / j.factorial) *
      gsPerturbIterate theta sigma K j u) = _
  norm_num [Finset.sum_range_succ]
  ring

/-- First-order kernel-change inequality.  It is slightly stronger than the
`sinh` estimate used in Granville--Soundararajan: positivity of the base
solution lets the first odd perturbation truncation give loss at most the
removed logarithmic mass itself. -/
theorem gs_kernelChange_lower_first
    {theta psi target sigma targetSigma : ℝ → ℝ}
    (htheta : IsGSKernel theta) (hpsi : IsGSKernel psi)
    (htarget : IsGSKernel target) (hsigma : IsGSSolution psi sigma)
    (htargetSigma : IsGSSolution target targetSigma)
    (hrel : ∀ t : ℝ, target t = psi t - t * gsDefectWeight theta t)
    {u : ℝ} (hu : 1 ≤ u) :
    sigma u - gsLogScale theta u ≤ targetSigma u := by
  let U : ℝ := max 1 u
  let K : ℝ := U + 1
  let tau : ℝ → ℝ := gsPerturbFirstApprox theta sigma K
  let L : ℝ := ∫ t : ℝ, ‖gsDefectLocal theta K t‖
  let C : ℝ := ∑ j ∈ Finset.range 2, L ^ j / j.factorial
  let B : ℝ := 1 + C
  have hU0 : 0 ≤ U := by dsimp only [U]; positivity
  have hU1 : 1 ≤ U := le_max_left _ _
  have huU : u ≤ U := le_max_right _ _
  have hK1 : 1 ≤ K := by dsimp only [K]; linarith
  have hUK : U < K := by dsimp only [K]; linarith
  have hC0 : 0 ≤ C := by
    dsimp only [C, L]
    apply Finset.sum_nonneg
    intro j hj
    exact div_nonneg (pow_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) _)
      (by positivity)
  have hresNonneg (v : ℝ) :
      0 ≤ (gsWeightedDefectLocal theta K ⋆[ContinuousLinearMap.mul ℝ ℝ]
        gsPerturbIterate theta sigma K 1) v := by
    rw [convolution_def]
    apply integral_nonneg
    intro t
    simp only [ContinuousLinearMap.mul_apply']
    exact mul_nonneg (gsWeightedDefectLocal_nonneg htheta K t)
      (gsPerturbIterate_nonneg htheta hpsi hsigma K 1 (v - t))
  have htauSub : ∀ v : ℝ, 1 ≤ v → v ≤ U →
      v * tau v ≤ ∫ t : ℝ in 0..v, target t * tau (v - t) := by
    intro v hv1 hvU
    have hv0 : 0 ≤ v := zero_le_one.trans hv1
    have hvK : v < K := hvU.trans_lt hUK
    have hvne : v ≠ 0 := (zero_lt_one.trans_le hv1).ne'
    have hres := gs_kernelChange_alternating_residual
      htheta hpsi htarget hsigma hrel 1 hK1 hv0 hvK
    have hconvEq :
        (gsKernelLocal target K ⋆[ContinuousLinearMap.mul ℝ ℝ]
          gsPerturbAlternating theta sigma K 1) v =
        ∫ t : ℝ in 0..v, target t * tau (v - t) := by
      rw [gs_convolution_apply_of_nonpos_eq_zero
        (fun _t ht ↦ gsKernelLocal_nonpos target K ht)
        (fun _t ht ↦ gsPerturbAlternating_nonpos theta sigma K 1 ht) hv0]
      apply intervalIntegral.integral_congr_Ioo_of_le hv0
      intro t ht
      have htK : t ∈ Ioo (0 : ℝ) K := ⟨ht.1, ht.2.trans hvK⟩
      have hargpos : 0 < v - t := sub_pos.mpr ht.2
      change gsKernelLocal target K t *
          gsPerturbAlternating theta sigma K 1 (v - t) =
        target t * tau (v - t)
      rw [show gsKernelLocal target K t = target t by
        simp [gsKernelLocal, gsLocalize, htK]]
      simp [tau, gsPerturbFirstApprox, hargpos.ne']
    have htau : tau v = gsPerturbAlternating theta sigma K 1 v := by
      simp [tau, gsPerturbFirstApprox, hvne]
    rw [htau, ← hconvEq]
    rw [hres]
    norm_num
    exact hresNonneg v
  have htauInt : ∀ v : ℝ, 1 ≤ v → v ≤ U →
      IntervalIntegrable (fun t : ℝ ↦ target t * tau (v - t))
        volume 0 v := by
    intro v hv1 hvU
    have hv0 : 0 ≤ v := zero_le_one.trans hv1
    have hvK : v < K := hvU.trans_lt hUK
    let Q : ℝ → ℝ := gsKernelLocal target K
    let S : ℝ → ℝ := gsPerturbAlternating theta sigma K 1
    have hQ : Integrable Q :=
      integrable_gsKernelLocal htarget (zero_le_one.trans hK1)
    have hS : Integrable S :=
      integrable_gsPerturbAlternating htheta hpsi hsigma hK1 1
    have hSbound : ∀ y : ℝ, ‖S y‖ ≤ C := by
      exact gsPerturbAlternating_bound htheta hpsi hsigma hK1 1
    have hex : ConvolutionExistsAt Q S v (ContinuousLinearMap.mul ℝ ℝ) :=
      gs_convolutionExistsAt_of_integrable_bounded hQ hS hSbound
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
    simp [tau, S, gsPerturbFirstApprox, hargpos.ne']
  have hbound : ∀ v ∈ Icc (0 : ℝ) U,
      max (tau v - targetSigma v) 0 ≤ B := by
    intro v hv
    by_cases hvzero : v = 0
    · subst v
      have ht0 : targetSigma 0 = 1 := htargetSigma.2.1 0 le_rfl
        (by norm_num)
      simp only [tau, gsPerturbFirstApprox, if_pos, ht0, sub_self,
        max_self, B]
      linarith
    · have hvK : v < K := hv.2.trans_lt hUK
      have halt := gsPerturbAlternating_bound htheta hpsi hsigma hK1 1 v
      have htmem := gs_solution_mem_Icc htarget htargetSigma v hv.1
      have htAbs : |targetSigma v| ≤ 1 := by
        rw [abs_of_nonneg htmem.1]
        exact htmem.2
      have htauEq : tau v = gsPerturbAlternating theta sigma K 1 v := by
        simp [tau, gsPerturbFirstApprox, hvzero]
      have haltC : |gsPerturbAlternating theta sigma K 1 v| ≤ C := halt
      apply max_le
      · calc
          tau v - targetSigma v ≤ |tau v - targetSigma v| := le_abs_self _
          _ ≤ |tau v| + |targetSigma v| := abs_sub _ _
          _ ≤ B := by rw [htauEq]; dsimp only [B]; linarith
      · dsimp only [B]
        linarith
  have hcompare := gs_local_subsolution_le_of_bounded htarget hU0
    (U := U) (B := B) (sigma := targetSigma) (tau := tau)
    (fun v hv0 hv1 ↦ by
      dsimp only [tau]
      rw [gsPerturbFirstApprox_eq_one htheta hsigma hv0 hv1
        (hv1.trans_lt (hU1.trans_lt hUK)),
        htargetSigma.2.1 v hv0 hv1])
    (fun v hv1 hvU ↦ by rw [← htargetSigma.2.2 v hv1])
    htauSub
    (fun v hv1 hvU ↦ intervalIntegrable_gs_solution_kernel
      htarget htargetSigma (zero_le_one.trans hv1))
    htauInt hbound
  have hle := hcompare u ⟨zero_le_one.trans hu, huU⟩
  have hune : u ≠ 0 := (zero_lt_one.trans_le hu).ne'
  have huK : u < K := huU.trans_lt hUK
  have hT0 : gsPerturbIterate theta sigma K 0 u = sigma u := by
    change gsLocalize K sigma u = sigma u
    rw [gsLocalize, indicator_of_mem
      (show u ∈ Ioo (0 : ℝ) K from ⟨zero_lt_one.trans_le hu, huK⟩)]
  have hT1 := gsPerturbIterate_one_le_logScale htheta hpsi hsigma
    hK1 hu huK
  have htauEq : tau u = sigma u - gsPerturbIterate theta sigma K 1 u := by
    rw [show tau u = gsPerturbAlternating theta sigma K 1 u by
      simp [tau, gsPerturbFirstApprox, hune],
      gsPerturbAlternating_one, hT0]
  rw [htauEq] at hle
  linarith

end

end Erdos783
