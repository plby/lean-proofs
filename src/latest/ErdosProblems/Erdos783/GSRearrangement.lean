/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Rearrangement estimates for Erdős 783

This file proves the bathtub principle in the precise interval-integral form
used by Granville--Soundararajan, and derives their two scale inequalities.
-/

open MeasureTheory Set

namespace Erdos783

noncomputable section

/-- The lower half of the bathtub principle for an integrable density taking
values in `[0,1]` and a nondecreasing test function. -/
theorem gs_rearrangement_lower_integrable
    {a b A : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b) (hA0 : 0 ≤ A) (hA : A ≤ b - a)
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hfg : IntervalIntegrable (fun t ↦ f t * g t) volume a b)
    (hf0 : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hf1 : ∀ t ∈ Icc a b, f t ≤ 1)
    (hgmono : MonotoneOn g (Icc a b))
    (hmass : (∫ t : ℝ in a..b, f t) = A) :
    (∫ t : ℝ in a..(a + A), g t) ≤
      ∫ t : ℝ in a..b, f t * g t := by
  have hac : a ≤ a + A := by linarith
  have hcb : a + A ≤ b := by linarith
  have huab : uIcc a b = Icc a b := uIcc_of_le hab
  have huac : uIcc a (a + A) = Icc a (a + A) := uIcc_of_le hac
  have hucb : uIcc (a + A) b = Icc (a + A) b := uIcc_of_le hcb
  have hsubac : uIcc a (a + A) ⊆ uIcc a b := by
    rw [huac, huab]
    exact Icc_subset_Icc le_rfl hcb
  have hsubcb : uIcc (a + A) b ⊆ uIcc a b := by
    rw [hucb, huab]
    exact Icc_subset_Icc hac le_rfl
  have hfac := hf.mono_set hsubac
  have hfcb := hf.mono_set hsubcb
  have hgac := hg.mono_set hsubac
  have hfgac := hfg.mono_set hsubac
  have hfgcb := hfg.mono_set hsubcb
  have honeac : IntervalIntegrable (fun _t : ℝ ↦ (1 : ℝ)) volume a (a + A) :=
    intervalIntegrable_const
  have honefac : IntervalIntegrable (fun t ↦ 1 - f t) volume a (a + A) :=
    honeac.sub hfac
  have hmissingg : IntervalIntegrable
      (fun t ↦ (1 - f t) * g t) volume a (a + A) := by
    have h := hgac.sub hfgac
    convert h using 1
    ext t
    ring
  have hmassSplit :
      (∫ t : ℝ in a..(a + A), (1 - f t)) =
        ∫ t : ℝ in (a + A)..b, f t := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hfac hfcb
    have hconst : (∫ _t : ℝ in a..(a + A), (1 : ℝ)) = A := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul, mul_one]
      ring
    rw [intervalIntegral.integral_sub honeac hfac, hconst]
    rw [hmass] at hsplit
    linarith
  have hleftBound :
      (∫ t : ℝ in a..(a + A), (1 - f t) * g t) ≤
        g (a + A) * (∫ t : ℝ in a..(a + A), (1 - f t)) := by
    calc
      (∫ t : ℝ in a..(a + A), (1 - f t) * g t) ≤
          ∫ t : ℝ in a..(a + A), (1 - f t) * g (a + A) := by
        apply intervalIntegral.integral_mono_on hac hmissingg
          (honefac.mul_const (g (a + A)))
        intro t ht
        have hft : 0 ≤ 1 - f t := by
          linarith [hf1 t ⟨ht.1, ht.2.trans hcb⟩]
        have hgt : g t ≤ g (a + A) :=
          hgmono ⟨ht.1, ht.2.trans hcb⟩ ⟨hac, hcb⟩ ht.2
        exact mul_le_mul_of_nonneg_left hgt hft
      _ = g (a + A) * (∫ t : ℝ in a..(a + A), (1 - f t)) := by
        rw [intervalIntegral.integral_mul_const]
        ring
  have hrightBound :
      g (a + A) * (∫ t : ℝ in (a + A)..b, f t) ≤
        ∫ t : ℝ in (a + A)..b, f t * g t := by
    calc
      g (a + A) * (∫ t : ℝ in (a + A)..b, f t) =
          ∫ t : ℝ in (a + A)..b, f t * g (a + A) := by
        rw [intervalIntegral.integral_mul_const]
        ring
      _ ≤ ∫ t : ℝ in (a + A)..b, f t * g t := by
        apply intervalIntegral.integral_mono_on hcb
          (hfcb.mul_const (g (a + A))) hfgcb
        intro t ht
        have hft : 0 ≤ f t := hf0 t ⟨hac.trans ht.1, ht.2⟩
        have hgt : g (a + A) ≤ g t :=
          hgmono ⟨hac, hcb⟩ ⟨hac.trans ht.1, ht.2⟩ ht.1
        exact mul_le_mul_of_nonneg_left hgt hft
  have hmissingLe :
      (∫ t : ℝ in a..(a + A), (1 - f t) * g t) ≤
        ∫ t : ℝ in (a + A)..b, f t * g t := by
    calc
      _ ≤ g (a + A) * (∫ t : ℝ in a..(a + A), (1 - f t)) := hleftBound
      _ = g (a + A) * (∫ t : ℝ in (a + A)..b, f t) := by rw [hmassSplit]
      _ ≤ _ := hrightBound
  have hleftDecomp :
      (∫ t : ℝ in a..(a + A), g t) =
        (∫ t : ℝ in a..(a + A), f t * g t) +
          ∫ t : ℝ in a..(a + A), (1 - f t) * g t := by
    rw [← intervalIntegral.integral_add hfgac hmissingg]
    apply intervalIntegral.integral_congr
    intro t _ht
    ring
  have hrightDecomp :
      (∫ t : ℝ in a..b, f t * g t) =
        (∫ t : ℝ in a..(a + A), f t * g t) +
          ∫ t : ℝ in (a + A)..b, f t * g t := by
    exact (intervalIntegral.integral_add_adjacent_intervals hfgac hfgcb).symm
  rw [hleftDecomp, hrightDecomp]
  linarith

/-- The upper half of the bathtub principle. -/
theorem gs_rearrangement_upper_integrable
    {a b A : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b) (hA0 : 0 ≤ A) (hA : A ≤ b - a)
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hfg : IntervalIntegrable (fun t ↦ f t * g t) volume a b)
    (hf0 : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hf1 : ∀ t ∈ Icc a b, f t ≤ 1)
    (hgmono : MonotoneOn g (Icc a b))
    (hmass : (∫ t : ℝ in a..b, f t) = A) :
    (∫ t : ℝ in a..b, f t * g t) ≤
      ∫ t : ℝ in (b - A)..b, g t := by
  let F : ℝ → ℝ := fun t ↦ 1 - f t
  have hone : IntervalIntegrable (fun _t : ℝ ↦ (1 : ℝ)) volume a b :=
    intervalIntegrable_const
  have hF : IntervalIntegrable F volume a b := hone.sub hf
  have hFg : IntervalIntegrable (fun t ↦ F t * g t) volume a b := by
    have h := hg.sub hfg
    convert h using 1
    ext t
    dsimp only [F]
    ring
  have hF0 : ∀ t ∈ Icc a b, 0 ≤ F t := by
    intro t ht
    dsimp only [F]
    linarith [hf1 t ht]
  have hF1 : ∀ t ∈ Icc a b, F t ≤ 1 := by
    intro t ht
    dsimp only [F]
    linarith [hf0 t ht]
  have hFmass : (∫ t : ℝ in a..b, F t) = b - a - A := by
    dsimp only [F]
    rw [intervalIntegral.integral_sub hone hf,
      intervalIntegral.integral_const, hmass]
    simp only [smul_eq_mul, mul_one]
  have hlow := gs_rearrangement_lower_integrable
    hab (sub_nonneg.mpr hA) (by linarith : b - a - A ≤ b - a)
    hF hg hFg hF0 hF1 hgmono hFmass
  have hgleft : IntervalIntegrable g volume a (b - A) := by
    apply hg.mono_set
    rw [uIcc_of_le (by linarith : a ≤ b - A), uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl (by linarith)
  have hgright : IntervalIntegrable g volume (b - A) b := by
    apply hg.mono_set
    rw [uIcc_of_le (by linarith : b - A ≤ b), uIcc_of_le hab]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hsum :
      (∫ t : ℝ in a..b, f t * g t) +
          ∫ t : ℝ in a..b, F t * g t =
        ∫ t : ℝ in a..b, g t := by
    rw [← intervalIntegral.integral_add hfg hFg]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only [F]
    ring
  have hsplit :
      (∫ t : ℝ in a..b, g t) =
        (∫ t : ℝ in a..(b - A), g t) +
          ∫ t : ℝ in (b - A)..b, g t := by
    exact (intervalIntegral.integral_add_adjacent_intervals hgleft hgright).symm
  have habA : a + (b - a - A) = b - A := by ring
  rw [habA] at hlow
  linarith

/-- A weighted bathtub principle for an antitone test function.  The cutoff
`c` is characterized by saying that the weighted mass of `f` on `[a,b]`
equals the full weighted mass of `[c,b]`.  This form avoids a logarithmic
change of variables when the weight is `1/t`. -/
theorem gs_weighted_rearrangement_lower_antitone
    {a b c : ℝ} {f w g : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hfw : IntervalIntegrable (fun t => f t * w t) volume a b)
    (hw : IntervalIntegrable w volume a b)
    (hfwg : IntervalIntegrable (fun t => f t * w t * g t) volume a b)
    (hwg : IntervalIntegrable (fun t => w t * g t) volume a b)
    (hf0 : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hf1 : ∀ t ∈ Icc a b, f t ≤ 1)
    (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hganti : AntitoneOn g (Icc a b))
    (hmass : (∫ t : ℝ in a..b, f t * w t) = ∫ t : ℝ in c..b, w t) :
    (∫ t : ℝ in c..b, w t * g t) ≤
      ∫ t : ℝ in a..b, f t * w t * g t := by
  have hab : a ≤ b := hac.trans hcb
  have hsubLeft : uIcc a c ⊆ uIcc a b := by
    rw [uIcc_of_le hac, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hcb
  have hsubRight : uIcc c b ⊆ uIcc a b := by
    rw [uIcc_of_le hcb, uIcc_of_le hab]
    exact Icc_subset_Icc hac le_rfl
  have hfwLeft := hfw.mono_set hsubLeft
  have hfwRight := hfw.mono_set hsubRight
  have hwRight := hw.mono_set hsubRight
  have hfwgLeft := hfwg.mono_set hsubLeft
  have hfwgRight := hfwg.mono_set hsubRight
  have hwgRight := hwg.mono_set hsubRight
  have hmissingRight : IntervalIntegrable
      (fun t : ℝ => (1 - f t) * w t) volume c b := by
    have h := hwRight.sub hfwRight
    convert h using 1
    ext t
    ring
  have hmissingGRight : IntervalIntegrable
      (fun t : ℝ => (1 - f t) * w t * g t) volume c b := by
    have h := hwgRight.sub hfwgRight
    convert h using 1
    ext t
    ring
  have hmassSplit := intervalIntegral.integral_add_adjacent_intervals
    hfwLeft hfwRight
  have hmassBalance :
      (∫ t : ℝ in a..c, f t * w t) =
        ∫ t : ℝ in c..b, (1 - f t) * w t := by
    calc
      (∫ t : ℝ in a..c, f t * w t) =
          (∫ t : ℝ in c..b, w t) -
            ∫ t : ℝ in c..b, f t * w t := by
        rw [← hmass]
        linarith [hmassSplit]
      _ = ∫ t : ℝ in c..b, w t - f t * w t := by
        rw [intervalIntegral.integral_sub hwRight hfwRight]
      _ = ∫ t : ℝ in c..b, (1 - f t) * w t := by
        apply intervalIntegral.integral_congr
        intro t _ht
        ring
  have hleftBound :
      g c * (∫ t : ℝ in a..c, f t * w t) ≤
        ∫ t : ℝ in a..c, f t * w t * g t := by
    calc
      g c * (∫ t : ℝ in a..c, f t * w t) =
          ∫ t : ℝ in a..c, g c * (f t * w t) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ t : ℝ in a..c, f t * w t * g t := by
        apply intervalIntegral.integral_mono_on hac
          (hfwLeft.const_mul _) hfwgLeft
        intro t ht
        have hnonneg : 0 ≤ f t * w t := mul_nonneg
          (hf0 t ⟨ht.1, ht.2.trans hcb⟩)
          (hw0 t ⟨ht.1, ht.2.trans hcb⟩)
        have hg : g c ≤ g t := hganti
          ⟨ht.1, ht.2.trans hcb⟩ ⟨hac, hcb⟩ ht.2
        nlinarith [mul_le_mul_of_nonneg_right hg hnonneg]
  have hrightBound :
      (∫ t : ℝ in c..b, (1 - f t) * w t * g t) ≤
        g c * (∫ t : ℝ in c..b, (1 - f t) * w t) := by
    calc
      _ ≤ ∫ t : ℝ in c..b, g c * ((1 - f t) * w t) := by
        apply intervalIntegral.integral_mono_on hcb hmissingGRight
          (hmissingRight.const_mul _)
        intro t ht
        have hnonneg : 0 ≤ (1 - f t) * w t := mul_nonneg
          (sub_nonneg.mpr (hf1 t ⟨hac.trans ht.1, ht.2⟩))
          (hw0 t ⟨hac.trans ht.1, ht.2⟩)
        have hg : g t ≤ g c := hganti
          ⟨hac, hcb⟩ ⟨hac.trans ht.1, ht.2⟩ ht.1
        nlinarith [mul_le_mul_of_nonneg_left hg hnonneg]
      _ = g c * (∫ t : ℝ in c..b, (1 - f t) * w t) := by
        rw [intervalIntegral.integral_const_mul]
  have hmissingLe :
      (∫ t : ℝ in c..b, (1 - f t) * w t * g t) ≤
        ∫ t : ℝ in a..c, f t * w t * g t := by
    calc
      _ ≤ g c * (∫ t : ℝ in c..b, (1 - f t) * w t) := hrightBound
      _ = g c * (∫ t : ℝ in a..c, f t * w t) := by rw [hmassBalance]
      _ ≤ _ := hleftBound
  have htargetSplit := intervalIntegral.integral_add_adjacent_intervals
    hfwgLeft hfwgRight
  have hmodelSplit :
      (∫ t : ℝ in c..b, w t * g t) =
        (∫ t : ℝ in c..b, f t * w t * g t) +
          ∫ t : ℝ in c..b, (1 - f t) * w t * g t := by
    rw [← intervalIntegral.integral_add hfwgRight hmissingGRight]
    apply intervalIntegral.integral_congr
    intro t _ht
    ring
  rw [hmodelSplit]
  linarith

/-- The two Granville--Soundararajan scale inequalities. -/
theorem gs_scale_inequalities_integrable
    {t y : ℝ} {chi : ℝ → ℝ}
    (ht : 0 < t) (hty : t ≤ y)
    (hchi : IntervalIntegrable chi volume t y)
    (hchi0 : ∀ v ∈ Icc t y, 0 ≤ chi v)
    (hchi1 : ∀ v ∈ Icc t y, chi v ≤ 1) :
    let A := ∫ v : ℝ in t..y, chi v
    let M := ∫ v : ℝ in t..y, (1 - chi v) / v
    y * Real.exp (-M) - t ≤ A ∧
      A ≤ y - t * Real.exp M := by
  dsimp only
  let A : ℝ := ∫ v : ℝ in t..y, chi v
  let M : ℝ := ∫ v : ℝ in t..y, (1 - chi v) / v
  have hy : 0 < y := ht.trans_le hty
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact intervalIntegral.integral_nonneg hty (fun v hv ↦ hchi0 v hv)
  have hAupper : A ≤ y - t := by
    dsimp only [A]
    calc
      (∫ v : ℝ in t..y, chi v) ≤
          ∫ _v : ℝ in t..y, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hty
          hchi intervalIntegrable_const
        exact hchi1
      _ = y - t := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul, mul_one]
  let g : ℝ → ℝ := fun v ↦ -(max t v)⁻¹
  have hmaxPos (v : ℝ) : 0 < max t v := ht.trans_le (le_max_left _ _)
  have hg : Continuous g := by
    dsimp only [g]
    exact ((continuous_const.max continuous_id).inv₀
      (fun v ↦ (hmaxPos v).ne')).neg
  have hgmono : MonotoneOn g (Icc t y) := by
    intro v hv w hw hvw
    dsimp only [g]
    rw [max_eq_right (hv.1), max_eq_right (hw.1)]
    exact neg_le_neg ((inv_le_inv₀ (ht.trans_le hw.1)
      (ht.trans_le hv.1)).2 hvw)
  have hchig : IntervalIntegrable (fun v ↦ chi v * g v) volume t y :=
    hchi.mul_continuousOn hg.continuousOn
  have hlower := gs_rearrangement_lower_integrable
    hty hA0 hAupper hchi (hg.intervalIntegrable _ _) hchig
      hchi0 hchi1 hgmono (by rfl : (∫ v : ℝ in t..y, chi v) = A)
  have hupper := gs_rearrangement_upper_integrable
    hty hA0 hAupper hchi (hg.intervalIntegrable _ _) hchig
      hchi0 hchi1 hgmono (by rfl : (∫ v : ℝ in t..y, chi v) = A)
  have htA : 0 < t + A := by linarith
  have hyA : 0 < y - A := by linarith
  have hleftEval :
      (∫ v : ℝ in t..(t + A), g v) =
        -Real.log ((t + A) / t) := by
    rw [show (∫ v : ℝ in t..(t + A), g v) =
        ∫ v : ℝ in t..(t + A), -v⁻¹ by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le (by linarith : t ≤ t + A)] at hv
      dsimp only [g]
      rw [max_eq_right hv.1]]
    rw [intervalIntegral.integral_neg, integral_inv_of_pos ht htA]
  have hrightEval :
      (∫ v : ℝ in (y - A)..y, g v) =
        -Real.log (y / (y - A)) := by
    have htyA : t ≤ y - A := by linarith
    rw [show (∫ v : ℝ in (y - A)..y, g v) =
        ∫ v : ℝ in (y - A)..y, -v⁻¹ by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le (by linarith : y - A ≤ y)] at hv
      dsimp only [g]
      rw [max_eq_right (htyA.trans hv.1)]]
    rw [intervalIntegral.integral_neg, integral_inv_of_pos hyA hy]
  have hweightedEval :
      (∫ v : ℝ in t..y, chi v * g v) =
        M - Real.log (y / t) := by
    have hinvCont : ContinuousOn (fun v : ℝ ↦ v⁻¹) (uIcc t y) :=
      continuousOn_inv₀.mono (by
        intro v hv
        rw [uIcc_of_le hty] at hv
        exact Set.mem_compl_singleton_iff.mpr (ht.trans_le hv.1).ne')
    have hinv : IntervalIntegrable (fun v : ℝ ↦ v⁻¹) volume t y :=
      hinvCont.intervalIntegrable
    have hchiInv : IntervalIntegrable
        (fun v : ℝ ↦ chi v * v⁻¹) volume t y :=
      hchi.mul_continuousOn hinvCont
    have hM : M = Real.log (y / t) -
        ∫ v : ℝ in t..y, chi v * v⁻¹ := by
      dsimp only [M]
      rw [show (∫ v : ℝ in t..y, (1 - chi v) / v) =
          ∫ v : ℝ in t..y, (v⁻¹ - chi v * v⁻¹) by
        apply intervalIntegral.integral_congr
        intro v _hv
        simp only [div_eq_mul_inv]
        ring,
        intervalIntegral.integral_sub hinv hchiInv,
        integral_inv_of_pos ht hy]
    rw [show (∫ v : ℝ in t..y, chi v * g v) =
        -(∫ v : ℝ in t..y, chi v * v⁻¹) by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le hty] at hv
      dsimp only [g]
      rw [max_eq_right hv.1]
      ring]
    linarith
  rw [hleftEval, hweightedEval] at hlower
  rw [hweightedEval, hrightEval] at hupper
  have hlogLeft :
      Real.log (t / (t + A)) ≤ M + Real.log (t / y) := by
    rw [Real.log_div htA.ne' ht.ne', Real.log_div hy.ne' ht.ne'] at hlower
    rw [Real.log_div ht.ne' htA.ne', Real.log_div ht.ne' hy.ne']
    linarith
  have hlogRight :
      M + Real.log (t / y) ≤ Real.log ((y - A) / y) := by
    rw [Real.log_div hy.ne' hyA.ne', Real.log_div hy.ne' ht.ne'] at hupper
    rw [Real.log_div ht.ne' hy.ne', Real.log_div hyA.ne' hy.ne']
    linarith
  have hratioLeft :
      t / (t + A) ≤ Real.exp M * (t / y) := by
    have hexp := Real.exp_le_exp.mpr hlogLeft
    rw [Real.exp_log (div_pos ht htA), Real.exp_add,
      Real.exp_log (div_pos ht hy)] at hexp
    exact hexp
  have hratioRight :
      Real.exp M * (t / y) ≤ (y - A) / y := by
    have hexp := Real.exp_le_exp.mpr hlogRight
    rw [Real.exp_add, Real.exp_log (div_pos ht hy),
      Real.exp_log (div_pos hyA hy)] at hexp
    exact hexp
  constructor
  · have hExp : 0 < Real.exp M := Real.exp_pos M
    have hExpNeg : Real.exp (-M) = (Real.exp M)⁻¹ := by
      rw [Real.exp_neg]
    rw [hExpNeg]
    apply (sub_le_iff_le_add).2
    have := hratioLeft
    field_simp [ht.ne', htA.ne', hy.ne', hExp.ne'] at this ⊢
    nlinarith
  · have := hratioRight
    field_simp [hy.ne'] at this
    linarith

end

end Erdos783
