/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos783.GSMoments

/-! # Filling a Granville--Soundararajan kernel above a cutoff -/

open MeasureTheory Set Finset

namespace Erdos783

noncomputable section

/-- Replace a kernel by `1` at and above `u0`; equivalently, erase its
defect density there. -/
def gsFillAbove (chi : ℝ → ℝ) (u0 t : ℝ) : ℝ :=
  if t < u0 then chi t else 1

/-- The complementary defect kernel: it is identically one below `u0`
and agrees with `chi` from `u0` onward.  Its defect density is exactly the
part erased by `gsFillAbove`. -/
def gsTailKernel (chi : ℝ → ℝ) (u0 t : ℝ) : ℝ :=
  if t < u0 then 1 else chi t

lemma intervalIntegrable_gsFillAbove
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (u0 a b : ℝ) :
    IntervalIntegrable (gsFillAbove chi u0) volume a b := by
  rw [intervalIntegrable_iff']
  have hchiInt : Integrable chi (volume.restrict (uIcc a b)) := by
    exact (intervalIntegrable_iff').mp (hchi.1 a b)
  have hOne : Integrable (fun _t : ℝ => (1 : ℝ))
      (volume.restrict (uIcc a b)) := by
    exact (intervalIntegrable_iff').mp intervalIntegrable_const
  have hp := Integrable.piecewise (s := Iio u0)
    (μ := volume.restrict (uIcc a b))
    measurableSet_Iio hchiInt.integrableOn hOne.integrableOn
  change Integrable (gsFillAbove chi u0) (volume.restrict (uIcc a b))
  have heq : (Iio u0).piecewise chi (fun _t => (1 : ℝ)) =
      gsFillAbove chi u0 := by
    funext t
    simp [Set.piecewise, gsFillAbove]
  rw [← heq]
  exact hp

lemma isGSKernel_gsFillAbove
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (u0 : ℝ) :
    IsGSKernel (gsFillAbove chi u0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact intervalIntegrable_gsFillAbove hchi u0
  · intro t ht
    unfold gsFillAbove
    split_ifs
    · exact hchi.2.1 t ht
    · norm_num
  · intro t ht
    unfold gsFillAbove
    split_ifs
    · exact hchi.2.2.1 t ht
    · norm_num
  · intro t ht ht1
    unfold gsFillAbove
    split_ifs
    · exact hchi.2.2.2 t ht ht1
    · rfl

lemma intervalIntegrable_gsTailKernel
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (u0 a b : ℝ) :
    IntervalIntegrable (gsTailKernel chi u0) volume a b := by
  rw [intervalIntegrable_iff']
  have hchiInt : Integrable chi (volume.restrict (uIcc a b)) :=
    (intervalIntegrable_iff').mp (hchi.1 a b)
  have hOne : Integrable (fun _t : ℝ ↦ (1 : ℝ))
      (volume.restrict (uIcc a b)) :=
    (intervalIntegrable_iff').mp intervalIntegrable_const
  have hp := Integrable.piecewise (s := Iio u0)
    (μ := volume.restrict (uIcc a b))
    measurableSet_Iio hOne.integrableOn hchiInt.integrableOn
  change Integrable (gsTailKernel chi u0) (volume.restrict (uIcc a b))
  have heq : (Iio u0).piecewise (fun _t ↦ (1 : ℝ)) chi =
      gsTailKernel chi u0 := by
    funext t
    simp [Set.piecewise, gsTailKernel]
  rw [← heq]
  exact hp

lemma isGSKernel_gsTailKernel
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u0 : ℝ} (hu0 : 1 ≤ u0) :
    IsGSKernel (gsTailKernel chi u0) := by
  refine ⟨intervalIntegrable_gsTailKernel hchi u0, ?_, ?_, ?_⟩
  · intro t ht
    unfold gsTailKernel
    split_ifs
    · norm_num
    · exact hchi.2.1 t ht
  · intro t ht
    unfold gsTailKernel
    split_ifs
    · norm_num
    · exact hchi.2.2.1 t ht
  · intro t ht ht1
    unfold gsTailKernel
    split_ifs with htu0
    · rfl
    · exact hchi.2.2.2 t ht ht1

lemma gsDefectWeight_gsTailKernel_of_lt
    (chi : ℝ → ℝ) {u0 t : ℝ} (ht : t < u0) :
    gsDefectWeight (gsTailKernel chi u0) t = 0 := by
  simp [gsDefectWeight, gsTailKernel, ht]

lemma gsDefectWeight_gsTailKernel_of_ge
    (chi : ℝ → ℝ) {u0 t : ℝ} (ht : u0 ≤ t) :
    gsDefectWeight (gsTailKernel chi u0) t = gsDefectWeight chi t := by
  simp [gsDefectWeight, gsTailKernel, not_lt_of_ge ht]

lemma gsDefectWeight_fill_add_tail
    (chi : ℝ → ℝ) (u0 t : ℝ) :
    gsDefectWeight (gsFillAbove chi u0) t +
      gsDefectWeight (gsTailKernel chi u0) t = gsDefectWeight chi t := by
  by_cases ht : t < u0
  · simp [gsDefectWeight, gsFillAbove, gsTailKernel, ht]
  · simp [gsDefectWeight, gsFillAbove, gsTailKernel, ht]

lemma gsFillAbove_sub_weightedTail
    (chi : ℝ → ℝ) {u0 : ℝ} (hu0 : 1 ≤ u0) (t : ℝ) :
    chi t = gsFillAbove chi u0 t -
      t * gsDefectWeight (gsTailKernel chi u0) t := by
  by_cases ht : t < u0
  · simp [gsFillAbove, gsDefectWeight_gsTailKernel_of_lt chi ht, ht]
  · have ht0 : t ≠ 0 := by
      have : 1 ≤ t := hu0.trans (le_of_not_gt ht)
      positivity
    rw [gsFillAbove, if_neg ht,
      gsDefectWeight_gsTailKernel_of_ge chi (le_of_not_gt ht)]
    unfold gsDefectWeight
    field_simp [ht0]
    ring

lemma gsLogScale_gsTailKernel
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u0 u : ℝ} (hu0 : 1 ≤ u0) (hu0u : u0 ≤ u) :
    gsLogScale (gsTailKernel chi u0) u =
      gsLogScale chi u - gsLogScale chi u0 := by
  rw [gsLogScale_sub hchi hu0 hu0u]
  unfold gsLogScale
  have htail := isGSKernel_gsTailKernel hchi hu0
  have hleft : IntervalIntegrable
      (gsDefectWeight (gsTailKernel chi u0)) volume 1 u0 := by
    change IntervalIntegrable
      (fun v : ℝ ↦ (1 - gsTailKernel chi u0 v) / v) volume 1 u0
    exact intervalIntegrable_gsDefectKernel htail zero_lt_one hu0
  have hright : IntervalIntegrable
      (gsDefectWeight (gsTailKernel chi u0)) volume u0 u := by
    change IntervalIntegrable
      (fun v : ℝ ↦ (1 - gsTailKernel chi u0 v) / v) volume u0 u
    exact intervalIntegrable_gsDefectKernel htail
      (zero_lt_one.trans_le hu0) hu0u
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hz : (∫ t : ℝ in 1..u0,
      gsDefectWeight (gsTailKernel chi u0) t) = 0 := by
    rw [show (∫ t : ℝ in 1..u0,
        gsDefectWeight (gsTailKernel chi u0) t) =
        ∫ _t : ℝ in 1..u0, (0 : ℝ) by
      apply intervalIntegral.integral_congr_Ioo_of_le hu0
      intro t ht
      exact gsDefectWeight_gsTailKernel_of_lt chi ht.2]
    simp
  have hrightEq : (∫ t : ℝ in u0..u,
      gsDefectWeight (gsTailKernel chi u0) t) =
      ∫ t : ℝ in u0..u, (1 - chi t) / t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hu0u] at ht
    exact gsDefectWeight_gsTailKernel_of_ge chi ht.1
  rw [hz, zero_add, hrightEq] at hadd
  exact hadd.symm

lemma gsDefectWeight_gsFillAbove_of_lt
    (chi : ℝ → ℝ) {u0 t : ℝ} (ht : t < u0) :
    gsDefectWeight (gsFillAbove chi u0) t = gsDefectWeight chi t := by
  simp [gsDefectWeight, gsFillAbove, ht]

lemma gsDefectWeight_gsFillAbove_of_ge
    (chi : ℝ → ℝ) {u0 t : ℝ} (ht : u0 ≤ t) :
    gsDefectWeight (gsFillAbove chi u0) t = 0 := by
  simp [gsDefectWeight, gsFillAbove, not_lt_of_ge ht]

lemma gsLogScale_gsFillAbove_at
    (chi : ℝ → ℝ) {u0 : ℝ} (hu0 : 1 ≤ u0) :
    gsLogScale (gsFillAbove chi u0) u0 = gsLogScale chi u0 := by
  unfold gsLogScale
  apply intervalIntegral.integral_congr_Ioo_of_le hu0
  intro t ht
  change gsDefectWeight (gsFillAbove chi u0) t = gsDefectWeight chi t
  exact gsDefectWeight_gsFillAbove_of_lt chi ht.2

lemma gsLogScale_gsFillAbove_of_le
    (chi : ℝ → ℝ) {y u0 : ℝ} (hy : 1 ≤ y) (hyu0 : y ≤ u0) :
    gsLogScale (gsFillAbove chi u0) y = gsLogScale chi y := by
  unfold gsLogScale
  apply intervalIntegral.integral_congr_Ioo_of_le hy
  intro t ht
  change gsDefectWeight (gsFillAbove chi u0) t = gsDefectWeight chi t
  exact gsDefectWeight_gsFillAbove_of_lt chi (ht.2.trans_le hyu0)

lemma gsLogScale_gsFillAbove_of_ge
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u0 u : ℝ} (hu0 : 1 ≤ u0) (hu0u : u0 ≤ u) :
    gsLogScale (gsFillAbove chi u0) u = gsLogScale chi u0 := by
  have hfill := isGSKernel_gsFillAbove hchi u0
  rw [← gsLogScale_gsFillAbove_at chi hu0]
  rw [← sub_eq_zero]
  rw [gsLogScale_sub hfill hu0 hu0u]
  change (∫ t : ℝ in u0..u,
    gsDefectWeight (gsFillAbove chi u0) t) = 0
  rw [show (∫ t : ℝ in u0..u,
      gsDefectWeight (gsFillAbove chi u0) t) =
      ∫ _t : ℝ in u0..u, (0 : ℝ) by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hu0u] at ht
    exact gsDefectWeight_gsFillAbove_of_ge chi ht.1]
  simp

/-- The moments of the filled kernel are full powers whenever the product
box `[1,u0]^n` fits below the endpoint. -/
lemma gsMoment_gsFillAbove_eq_pow
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u0 : ℝ} (hu0 : 1 ≤ u0) (n : ℕ) {u : ℝ}
    (hfit : (n : ℝ) * u0 ≤ u) :
    gsMoment (gsFillAbove chi u0) n u = gsLogScale chi u0 ^ n := by
  rw [← gsLogScale_gsFillAbove_at chi hu0]
  exact gsMoment_eq_logScale_pow_of_supported
    (isGSKernel_gsFillAbove hchi u0) hu0
    (fun t ht => gsDefectWeight_gsFillAbove_of_ge chi ht) n hfit

end

end Erdos783
