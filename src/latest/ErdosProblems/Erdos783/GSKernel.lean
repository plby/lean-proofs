/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos783.GSRearrangement
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Granville--Soundararajan kernels and scales -/

open MeasureTheory Set

namespace Erdos783

noncomputable section

def IsGSKernel (chi : ℝ → ℝ) : Prop :=
  (∀ a b : ℝ, IntervalIntegrable chi volume a b) ∧
  (∀ t : ℝ, 0 ≤ t → 0 ≤ chi t) ∧
  (∀ t : ℝ, 0 ≤ t → chi t ≤ 1) ∧
  (∀ t : ℝ, 0 ≤ t → t ≤ 1 → chi t = 1)

def gsB (chi : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t : ℝ in 0..y, chi t

def gsLogScale (chi : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t : ℝ in 1..y, (1 - chi t) / t

def gsScale (chi : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.exp (gsLogScale chi y)

lemma gsB_sub {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {t y : ℝ} (ht : 0 ≤ t) (hty : t ≤ y) :
    gsB chi y - gsB chi t = ∫ v : ℝ in t..y, chi v := by
  have hleft := hchi.1 0 t
  have hright := hchi.1 t y
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  unfold gsB
  linarith

lemma intervalIntegrable_gsDefectKernel {chi : ℝ → ℝ}
    (hchi : IsGSKernel chi) {t y : ℝ} (ht : 0 < t) (hty : t ≤ y) :
    IntervalIntegrable (fun v : ℝ ↦ (1 - chi v) / v) volume t y := by
  have hdiff : IntervalIntegrable (fun v : ℝ ↦ 1 - chi v) volume t y :=
    intervalIntegrable_const.sub (hchi.1 t y)
  have hinv : ContinuousOn (fun v : ℝ ↦ v⁻¹) (uIcc t y) := by
    apply continuousOn_inv₀.mono
    intro v hv
    rw [uIcc_of_le hty] at hv
    exact Set.mem_compl_singleton_iff.mpr (ht.trans_le hv.1).ne'
  simpa only [div_eq_mul_inv] using hdiff.mul_continuousOn hinv

lemma gsLogScale_sub {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {t y : ℝ} (ht : 1 ≤ t) (hty : t ≤ y) :
    gsLogScale chi y - gsLogScale chi t =
      ∫ v : ℝ in t..y, (1 - chi v) / v := by
  have hleft := intervalIntegrable_gsDefectKernel hchi
    (t := (1 : ℝ)) (y := t) zero_lt_one ht
  have hright := intervalIntegrable_gsDefectKernel hchi
    (t := t) (y := y) (zero_lt_one.trans_le ht) hty
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  unfold gsLogScale
  linarith

lemma gsLogScale_mono {chi : ℝ → ℝ} (hchi : IsGSKernel chi) :
    MonotoneOn (gsLogScale chi) (Ici (1 : ℝ)) := by
  intro t ht y hy hty
  change 1 ≤ t at ht
  change 1 ≤ y at hy
  rw [← sub_nonneg, gsLogScale_sub hchi ht hty]
  apply intervalIntegral.integral_nonneg hty
  intro v hv
  exact div_nonneg
    (sub_nonneg.mpr (hchi.2.2.1 v (by linarith [ht, hv.1])))
    (by linarith [ht, hv.1])

lemma gsLogScale_nonneg {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {y : ℝ} (hy : 1 ≤ y) : 0 ≤ gsLogScale chi y := by
  simpa [gsLogScale] using
    gsLogScale_mono hchi (by simp) hy hy

@[simp] lemma gsB_zero (chi : ℝ → ℝ) : gsB chi 0 = 0 := by
  simp [gsB]

lemma gsB_one {chi : ℝ → ℝ} (hchi : IsGSKernel chi) :
    gsB chi 1 = 1 := by
  unfold gsB
  rw [show (∫ t : ℝ in (0 : ℝ)..1, chi t) =
      ∫ _t : ℝ in (0 : ℝ)..1, (1 : ℝ) by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hchi.2.2.2 t ht.1 ht.2]
  norm_num

@[simp] lemma gsLogScale_one (chi : ℝ → ℝ) :
    gsLogScale chi 1 = 0 := by simp [gsLogScale]

@[simp] lemma gsScale_one (chi : ℝ → ℝ) :
    gsScale chi 1 = 1 := by simp [gsScale]

lemma gsScale_eq_one {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : gsScale chi y = 1 := by
  have hzero : (∫ t : ℝ in y..1, (1 - chi t) / t) = 0 := by
    rw [show (∫ t : ℝ in y..1, (1 - chi t) / t) =
        ∫ _t : ℝ in y..1, (0 : ℝ) by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hy1] at ht
      dsimp only
      rw [hchi.2.2.2 t (hy0.trans ht.1) ht.2]
      norm_num]
    simp
  unfold gsScale gsLogScale
  rw [intervalIntegral.integral_symm, hzero, neg_zero, Real.exp_zero]

lemma gsScale_pos (chi : ℝ → ℝ) (y : ℝ) :
    0 < gsScale chi y := Real.exp_pos _

lemma gsScale_ratio {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {t y : ℝ} (ht : 1 ≤ t) (hty : t ≤ y) :
    Real.exp (∫ v : ℝ in t..y, (1 - chi v) / v) =
      gsScale chi y / gsScale chi t := by
  rw [← gsLogScale_sub hchi ht hty]
  simp only [gsScale, Real.exp_sub]

lemma gsScale_inv_ratio {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {t y : ℝ} (ht : 1 ≤ t) (hty : t ≤ y) :
    Real.exp (-∫ v : ℝ in t..y, (1 - chi v) / v) =
      gsScale chi t / gsScale chi y := by
  rw [Real.exp_neg, gsScale_ratio hchi ht hty]
  field_simp [ne_of_gt (gsScale_pos chi t), ne_of_gt (gsScale_pos chi y)]

lemma gs_scale_bounds {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {t y : ℝ} (ht : 1 ≤ t) (hty : t ≤ y) :
    y * gsScale chi t / gsScale chi y - t ≤ gsB chi y - gsB chi t ∧
      gsB chi y - gsB chi t ≤
        y - t * gsScale chi y / gsScale chi t := by
  have htPos : 0 < t := zero_lt_one.trans_le ht
  have hraw := gs_scale_inequalities_integrable htPos hty (hchi.1 t y)
    (fun v hv ↦ hchi.2.1 v (htPos.le.trans hv.1))
    (fun v hv ↦ hchi.2.2.1 v (htPos.le.trans hv.1))
  dsimp only at hraw
  rw [← gsB_sub hchi htPos.le hty,
    gsScale_inv_ratio hchi ht hty,
    gsScale_ratio hchi ht hty] at hraw
  simpa [div_eq_mul_inv, mul_assoc] using hraw

lemma gsB_mono {chi : ℝ → ℝ} (hchi : IsGSKernel chi) :
    MonotoneOn (gsB chi) (Ici (0 : ℝ)) := by
  intro t ht y hy hty
  rw [← sub_nonneg, gsB_sub hchi ht hty]
  exact intervalIntegral.integral_nonneg hty
    (fun v hv ↦ hchi.2.1 v (ht.trans hv.1))

lemma gsB_nonneg {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {y : ℝ} (hy : 0 ≤ y) : 0 ≤ gsB chi y := by
  simpa using gsB_mono hchi (by simp) hy hy

lemma gsB_le {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {y : ℝ} (hy : 0 ≤ y) : gsB chi y ≤ y := by
  unfold gsB
  calc
    (∫ t : ℝ in (0 : ℝ)..y, chi t) ≤
        ∫ _t : ℝ in (0 : ℝ)..y, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on hy (hchi.1 0 y)
        intervalIntegrable_const
      intro t ht
      exact hchi.2.2.1 t ht.1
    _ = y := by simp

lemma gsScale_mono {chi : ℝ → ℝ} (hchi : IsGSKernel chi) :
    MonotoneOn (gsScale chi) (Ici (1 : ℝ)) := by
  intro t ht y hy hty
  rw [gsScale, gsScale, Real.exp_le_exp, ← sub_nonneg,
    gsLogScale_sub hchi ht hty]
  apply intervalIntegral.integral_nonneg hty
  intro v hv
  exact div_nonneg
    (sub_nonneg.mpr (hchi.2.2.1 v (zero_le_one.trans (ht.trans hv.1))))
    (zero_le_one.trans (ht.trans hv.1))

lemma gsScale_ge_one {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {y : ℝ} (hy : 1 ≤ y) : 1 ≤ gsScale chi y := by
  simpa using gsScale_mono hchi (by simp) hy hy

lemma gsScale_mono_Ici_zero {chi : ℝ → ℝ} (hchi : IsGSKernel chi) :
    MonotoneOn (gsScale chi) (Ici (0 : ℝ)) := by
  intro t ht y hy hty
  by_cases hy1 : y ≤ 1
  · rw [gsScale_eq_one hchi ht (hty.trans hy1), gsScale_eq_one hchi hy hy1]
  · have hy1' : 1 ≤ y := le_of_not_ge hy1
    by_cases ht1 : t ≤ 1
    · rw [gsScale_eq_one hchi ht ht1]
      exact gsScale_ge_one hchi hy1'
    · exact gsScale_mono hchi (le_of_not_ge ht1) hy1' hty

lemma gsB_ge_div_scale {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {y : ℝ} (hy : 1 ≤ y) : y / gsScale chi y ≤ gsB chi y := by
  have h := (gs_scale_bounds hchi (t := (1 : ℝ)) (y := y)
    (by norm_num) hy).1
  rw [gsScale_one, gsB_one hchi] at h
  norm_num at h ⊢
  linarith

lemma gsScale_le_self {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {y : ℝ} (hy : 1 ≤ y) : gsScale chi y ≤ y := by
  have h := (gs_scale_bounds hchi (t := (1 : ℝ)) (y := y)
    (by norm_num) hy).2
  have hBmono := gsB_mono hchi (by norm_num : (1 : ℝ) ∈ Ici 0)
    (show y ∈ Ici 0 by exact zero_le_one.trans hy) hy
  rw [gsScale_one, gsB_one hchi] at h
  rw [gsB_one hchi] at hBmono
  norm_num at h hBmono ⊢
  linarith

lemma gsScale_div_antitone {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {t y : ℝ} (ht : 1 ≤ t) (hty : t ≤ y) :
    gsScale chi y / y ≤ gsScale chi t / t := by
  have hyPos : 0 < y := zero_lt_one.trans_le (ht.trans hty)
  have htPos : 0 < t := zero_lt_one.trans_le ht
  have h := (gs_scale_bounds hchi ht hty).2
  have hA0 : 0 ≤ gsB chi y - gsB chi t :=
    sub_nonneg.mpr (gsB_mono hchi (zero_le_one.trans ht)
      (zero_le_one.trans (ht.trans hty)) hty)
  have hratio : t * gsScale chi y / gsScale chi t ≤ y := by linarith
  have hEt : 0 < gsScale chi t := gsScale_pos chi t
  field_simp [hyPos.ne', htPos.ne', hEt.ne'] at hratio ⊢
  exact hratio

lemma continuousOn_gsB_Icc {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {K : ℝ} (hK : 0 ≤ K) : ContinuousOn (gsB chi) (Icc 0 K) := by
  unfold gsB
  have h := intervalIntegral.continuousOn_primitive_interval'
    (hchi.1 0 K) (show (0 : ℝ) ∈ uIcc 0 K by
      rw [uIcc_of_le hK]
      exact ⟨le_rfl, hK⟩)
  simpa [uIcc_of_le hK] using h

lemma continuousOn_gsLogScale_Icc {chi : ℝ → ℝ}
    (hchi : IsGSKernel chi) {K : ℝ} (hK : 1 ≤ K) :
    ContinuousOn (gsLogScale chi) (Icc 1 K) := by
  unfold gsLogScale
  have hint := intervalIntegrable_gsDefectKernel hchi zero_lt_one hK
  have h := intervalIntegral.continuousOn_primitive_interval'
    hint (show (1 : ℝ) ∈ uIcc 1 K by
      rw [uIcc_of_le hK]
      exact ⟨le_rfl, hK⟩)
  simpa [uIcc_of_le hK] using h

lemma continuousOn_gsScale_Icc {chi : ℝ → ℝ}
    (hchi : IsGSKernel chi) {K : ℝ} (hK : 1 ≤ K) :
    ContinuousOn (gsScale chi) (Icc 1 K) := by
  exact Real.continuous_exp.comp_continuousOn
    (continuousOn_gsLogScale_Icc hchi hK)

lemma continuousOn_gsScale_Icc_zero
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {K : ℝ} (hK : 1 ≤ K) :
    ContinuousOn (gsScale chi) (Icc 0 K) := by
  have hleft : ContinuousOn (gsScale chi) (Icc (0 : ℝ) 1) := by
    apply continuousOn_const.congr
    intro y hy
    exact gsScale_eq_one hchi hy.1 hy.2
  have hright : ContinuousOn (gsScale chi) (Icc 1 K) :=
    continuousOn_gsScale_Icc hchi hK
  rw [← Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1) hK]
  exact hleft.union_of_isClosed hright isClosed_Icc isClosed_Icc

end

end Erdos783
