/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos783.GSKernel

/-! # Granville--Soundararajan iterated moments and Bonferroni sums -/

open MeasureTheory Set Finset
open scoped BigOperators

namespace Erdos783

noncomputable section

/-- The nonnegative defect density `(1 - chi(t)) / t`. -/
def gsDefectWeight (chi : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 - chi t) / t

/-- The iterated Granville--Soundararajan moments, written recursively.
This is equation (4.5) in the writeup and is equivalent to the symmetric
simplex integral.  The explicit branch below `1` records that an empty
integration region has mass zero rather than using an oriented integral. -/
def gsMoment (chi : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, _u => 1
  | n + 1, u =>
      if 1 ≤ u then
        ∫ t : ℝ in 1..u, gsDefectWeight chi t * gsMoment chi n (u - t)
      else 0

@[simp] lemma gsMoment_zero (chi : ℝ → ℝ) (u : ℝ) :
    gsMoment chi 0 u = 1 := rfl

lemma gsMoment_one (chi : ℝ → ℝ) {u : ℝ} (hu : 1 ≤ u) :
    gsMoment chi 1 u = gsLogScale chi u := by
  simp [gsMoment, hu, gsDefectWeight, gsLogScale]

/-- Local finiteness: an `n`-fold simplex is empty when its endpoint is
strictly below `n`. -/
lemma gsMoment_eq_zero_of_lt {chi : ℝ → ℝ} {n : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hun : u < n) : gsMoment chi n u = 0 := by
  induction n generalizing u with
  | zero =>
      exfalso
      exact (not_lt_of_ge hu0) (by simpa using hun)
  | succ n ih =>
      rw [gsMoment]
      split_ifs with hu1
      · rw [show (∫ t : ℝ in 1..u,
            gsDefectWeight chi t * gsMoment chi n (u - t)) =
            ∫ _t : ℝ in 1..u, (0 : ℝ) by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hu1] at ht
          have hut0 : 0 ≤ u - t := sub_nonneg.mpr ht.2
          have hutn : u - t < n := by
            push_cast at hun ⊢
            nlinarith [ht.1]
          change gsDefectWeight chi t * gsMoment chi n (u - t) = 0
          rw [ih hut0 hutn, mul_zero]]
        simp
      · rfl

/-- The alternating moment polynomial through degree `k`. -/
def gsAlternatingMomentSum (chi : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℝ) ^ j * gsMoment chi j u / j.factorial

/-- The odd Bonferroni inequalities enjoyed by the locally finite moment
expansion of the canonical Volterra solution. -/
def GSOddBonferroni (chi sigma : ℝ → ℝ) : Prop :=
  ∀ u : ℝ, 0 ≤ u → ∀ r : ℕ,
    gsAlternatingMomentSum chi (2 * r + 1) u ≤ sigma u

lemma gsDefectWeight_nonneg {chi : ℝ → ℝ}
    (hchi : IsGSKernel chi) {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ gsDefectWeight chi t := by
  exact div_nonneg (sub_nonneg.mpr (hchi.2.2.1 t (by positivity)))
    (by positivity)

lemma gsMoment_nonneg {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) : 0 ≤ gsMoment chi n u := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      rw [gsMoment]
      split_ifs with hu1
      · apply intervalIntegral.integral_nonneg hu1
        intro t ht
        exact mul_nonneg (gsDefectWeight_nonneg hchi ht.1)
          (ih (sub_nonneg.mpr ht.2))
      · exact le_rfl

lemma intervalIntegrable_gsDefect_mul_moment_of_mono
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    (hmono : MonotoneOn (gsMoment chi n) (Ici (0 : ℝ)))
    {u : ℝ} (hu : 1 ≤ u) :
    IntervalIntegrable
      (fun t : ℝ => gsDefectWeight chi t * gsMoment chi n (u - t))
      volume 1 u := by
  have hdef : IntervalIntegrable (gsDefectWeight chi) volume 1 u := by
    change IntervalIntegrable (fun v : ℝ => (1 - chi v) / v) volume 1 u
    exact intervalIntegrable_gsDefectKernel hchi zero_lt_one hu
  let mext : ℝ → ℝ := fun x => gsMoment chi n (max 0 x)
  have hmextMono : Monotone mext := by
    intro a b hab
    apply hmono
    · exact mem_Ici.mpr (le_max_left _ _)
    · exact mem_Ici.mpr (le_max_left _ _)
    · exact max_le_max le_rfl hab
  have hmextMeas : Measurable (fun t : ℝ => mext (u - t)) :=
    hmextMono.measurable.comp (measurable_const.sub measurable_id)
  have hmomAE : AEStronglyMeasurable
      (fun t : ℝ => gsMoment chi n (u - t))
      (volume.restrict (uIoc 1 u)) := by
    apply hmextMeas.aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [uIoc_of_le hu] at ht
    dsimp only [mext]
    rw [max_eq_right (sub_nonneg.mpr ht.2)]
  have hdefAE : AEStronglyMeasurable (gsDefectWeight chi)
      (volume.restrict (uIoc 1 u)) := by
    rw [uIoc_of_le hu]
    exact hdef.1.1
  have htarget : AEStronglyMeasurable
      (fun t : ℝ => gsDefectWeight chi t * gsMoment chi n (u - t))
      (volume.restrict (uIoc 1 u)) := hdefAE.mul hmomAE
  have hbound : IntervalIntegrable
      (fun t : ℝ => gsDefectWeight chi t * gsMoment chi n u)
      volume 1 u := hdef.mul_const _
  apply hbound.mono_fun htarget
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [uIoc_of_le hu] at ht
  have hwt : 0 ≤ gsDefectWeight chi t := gsDefectWeight_nonneg hchi ht.1.le
  have harg0 : 0 ≤ u - t := sub_nonneg.mpr ht.2
  have hmono' : gsMoment chi n (u - t) ≤ gsMoment chi n u := by
    exact hmono (mem_Ici.mpr harg0)
      (mem_Ici.mpr (zero_le_one.trans hu))
      (sub_le_self _ (zero_le_one.trans ht.1.le))
  have hmarg0 : 0 ≤ gsMoment chi n (u - t) := gsMoment_nonneg hchi n harg0
  have hmu0 : 0 ≤ gsMoment chi n u :=
    gsMoment_nonneg hchi n (zero_le_one.trans hu)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hwt hmarg0),
    abs_of_nonneg (mul_nonneg hwt hmu0)]
  exact mul_le_mul_of_nonneg_left hmono' hwt

lemma gsMoment_succ_mono_of_mono
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    (hmono : MonotoneOn (gsMoment chi n) (Ici (0 : ℝ))) :
    MonotoneOn (gsMoment chi (n + 1)) (Ici (0 : ℝ)) := by
  intro v hv u hu hvu
  change 0 ≤ v at hv
  change 0 ≤ u at hu
  by_cases hv1 : 1 ≤ v
  · have hu1 : 1 ≤ u := hv1.trans hvu
    rw [gsMoment, if_pos hv1, gsMoment, if_pos hu1]
    let fv : ℝ → ℝ := fun t =>
      gsDefectWeight chi t * gsMoment chi n (v - t)
    let fu : ℝ → ℝ := fun t =>
      gsDefectWeight chi t * gsMoment chi n (u - t)
    have hfv : IntervalIntegrable fv volume 1 v :=
      intervalIntegrable_gsDefect_mul_moment_of_mono hchi n hmono hv1
    have hfu : IntervalIntegrable fu volume 1 u :=
      intervalIntegrable_gsDefect_mul_moment_of_mono hchi n hmono hu1
    have hfuv : IntervalIntegrable fu volume 1 v := by
      apply hfu.mono_set
      rw [uIcc_of_le hv1, uIcc_of_le hu1]
      exact Icc_subset_Icc le_rfl hvu
    have hpoint : ∀ t ∈ Icc (1 : ℝ) v, fv t ≤ fu t := by
      intro t ht
      apply mul_le_mul_of_nonneg_left
      · apply hmono
        · exact mem_Ici.mpr (sub_nonneg.mpr ht.2)
        · exact mem_Ici.mpr (sub_nonneg.mpr (ht.2.trans hvu))
        · linarith
      · exact gsDefectWeight_nonneg hchi ht.1
    have hfirst : (∫ t in 1..v, fv t) ≤ ∫ t in 1..v, fu t :=
      intervalIntegral.integral_mono_on hv1 hfv hfuv hpoint
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (1 : ℝ) u)] fu := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (gsDefectWeight_nonneg hchi ht.1.le)
        (gsMoment_nonneg hchi n (sub_nonneg.mpr ht.2))
    have hsecond : (∫ t in 1..v, fu t) ≤ ∫ t in 1..u, fu t :=
      intervalIntegral.integral_mono_interval le_rfl hv1 hvu hnonneg hfu
    exact hfirst.trans hsecond
  · rw [gsMoment, if_neg hv1]
    exact gsMoment_nonneg hchi (n + 1) hu

theorem gsMoment_mono_Ici_zero {chi : ℝ → ℝ}
    (hchi : IsGSKernel chi) (n : ℕ) :
    MonotoneOn (gsMoment chi n) (Ici (0 : ℝ)) := by
  induction n with
  | zero =>
      intro a ha b hb hab
      simp
  | succ n ih =>
      exact gsMoment_succ_mono_of_mono hchi n ih

lemma intervalIntegrable_gsDefect_mul_moment
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {u : ℝ} (hu : 1 ≤ u) :
    IntervalIntegrable
      (fun t : ℝ => gsDefectWeight chi t * gsMoment chi n (u - t))
      volume 1 u :=
  intervalIntegrable_gsDefect_mul_moment_of_mono hchi n
    (gsMoment_mono_Ici_zero hchi n) hu

lemma gsMoment_succ_le_logScale_mul
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {u : ℝ} (hu : 1 ≤ u) :
    gsMoment chi (n + 1) u ≤ gsLogScale chi u * gsMoment chi n u := by
  rw [gsMoment, if_pos hu]
  have hactual := intervalIntegrable_gsDefect_mul_moment hchi n hu
  have hdef : IntervalIntegrable (gsDefectWeight chi) volume 1 u := by
    change IntervalIntegrable (fun v : ℝ => (1 - chi v) / v) volume 1 u
    exact intervalIntegrable_gsDefectKernel hchi zero_lt_one hu
  have hmodel : IntervalIntegrable
      (fun t : ℝ => gsDefectWeight chi t * gsMoment chi n u)
      volume 1 u := hdef.mul_const _
  calc
    (∫ t : ℝ in 1..u,
        gsDefectWeight chi t * gsMoment chi n (u - t)) ≤
        ∫ t : ℝ in 1..u,
          gsDefectWeight chi t * gsMoment chi n u := by
      apply intervalIntegral.integral_mono_on hu hactual hmodel
      intro t ht
      apply mul_le_mul_of_nonneg_left
      · exact gsMoment_mono_Ici_zero hchi n
          (mem_Ici.mpr (sub_nonneg.mpr ht.2))
          (mem_Ici.mpr (zero_le_one.trans hu))
          (sub_le_self _ (zero_le_one.trans ht.1))
      · exact gsDefectWeight_nonneg hchi ht.1
    _ = gsLogScale chi u * gsMoment chi n u := by
      rw [intervalIntegral.integral_mul_const]
      rfl

lemma gsMoment_le_logScale_pow
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ)
    {u : ℝ} (hu : 1 ≤ u) :
    gsMoment chi n u ≤ gsLogScale chi u ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        gsMoment chi (n + 1) u ≤
            gsLogScale chi u * gsMoment chi n u :=
          gsMoment_succ_le_logScale_mul hchi n hu
        _ ≤ gsLogScale chi u * gsLogScale chi u ^ n := by
          exact mul_le_mul_of_nonneg_left ih (gsLogScale_nonneg hchi hu)
        _ = gsLogScale chi u ^ (n + 1) := by ring

/-- If the defect density is supported in `[1,u0]`, every moment whose full
product box fits below `u` is the corresponding power of the total mass. -/
lemma gsMoment_eq_logScale_pow_of_supported
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u0 : ℝ} (hu0 : 1 ≤ u0)
    (hsupport : ∀ t : ℝ, u0 ≤ t → gsDefectWeight chi t = 0) :
    ∀ (n : ℕ) {u : ℝ}, (n : ℝ) * u0 ≤ u →
      gsMoment chi n u = gsLogScale chi u0 ^ n := by
  intro n
  induction n with
  | zero =>
      intro u hu
      simp
  | succ n ih =>
      intro u hnu
      have hu0pos : 0 < u0 := zero_lt_one.trans_le hu0
      have hu0u : u0 ≤ u := by
        have hn0 : (0 : ℝ) ≤ n := by positivity
        push_cast at hnu
        nlinarith [mul_nonneg hn0 hu0pos.le]
      have hu1 : 1 ≤ u := hu0.trans hu0u
      rw [gsMoment, if_pos hu1]
      let f : ℝ → ℝ := fun t =>
        gsDefectWeight chi t * gsMoment chi n (u - t)
      have hfull : IntervalIntegrable f volume 1 u :=
        intervalIntegrable_gsDefect_mul_moment hchi n hu1
      have hleft : IntervalIntegrable f volume 1 u0 := by
        apply hfull.mono_set
        rw [uIcc_of_le hu0, uIcc_of_le hu1]
        exact Icc_subset_Icc le_rfl hu0u
      have hright : IntervalIntegrable f volume u0 u := by
        apply hfull.mono_set
        rw [uIcc_of_le hu0u, uIcc_of_le hu1]
        exact Icc_subset_Icc hu0 le_rfl
      have htail : (∫ t : ℝ in u0..u, f t) = 0 := by
        rw [show (∫ t : ℝ in u0..u, f t) =
            ∫ _t : ℝ in u0..u, (0 : ℝ) by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hu0u] at ht
          dsimp only [f]
          rw [hsupport t ht.1, zero_mul]]
        simp
      have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
      have hrestrict : (∫ t : ℝ in 1..u, f t) = ∫ t : ℝ in 1..u0, f t := by
        linarith
      rw [show (∫ t : ℝ in 1..u,
          gsDefectWeight chi t * gsMoment chi n (u - t)) =
          ∫ t : ℝ in 1..u0,
            gsDefectWeight chi t * gsLogScale chi u0 ^ n by
        rw [show (∫ t : ℝ in 1..u,
            gsDefectWeight chi t * gsMoment chi n (u - t)) =
            ∫ t : ℝ in 1..u, f t by rfl,
          hrestrict]
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hu0] at ht
        have hncast : (n : ℝ) * u0 ≤ u - t := by
          push_cast at hnu
          nlinarith [hnu, ht.2]
        dsimp only [f]
        rw [ih hncast]]
      rw [intervalIntegral.integral_mul_const]
      change gsLogScale chi u0 * gsLogScale chi u0 ^ n =
        gsLogScale chi u0 ^ (n + 1)
      ring

/-- Restricting the defining simplex to the product box `[1,y]^n` gives a
lower bound by the `n`-th power of the defect mass below `y`.  This is the
moment estimate used for the positive paired terms in Proposition 6.1. -/
lemma gsLogScale_pow_le_gsMoment
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {y : ℝ} (hy : 1 ≤ y) :
    ∀ (n : ℕ) {u : ℝ}, (n : ℝ) * y ≤ u →
      gsLogScale chi y ^ n ≤ gsMoment chi n u := by
  intro n
  induction n with
  | zero =>
      intro u _hu
      simp
  | succ n ih =>
      intro u hfit
      have hy0 : 0 ≤ y := zero_le_one.trans hy
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hyu : y ≤ u := by
        push_cast at hfit
        nlinarith [mul_nonneg hn0 hy0]
      have hu : 1 ≤ u := hy.trans hyu
      rw [gsMoment, if_pos hu]
      let f : ℝ → ℝ := fun t ↦
        gsDefectWeight chi t * gsMoment chi n (u - t)
      let g : ℝ → ℝ := fun t ↦
        gsDefectWeight chi t * gsLogScale chi y ^ n
      have hf : IntervalIntegrable f volume 1 u :=
        intervalIntegrable_gsDefect_mul_moment hchi n hu
      have hfy : IntervalIntegrable f volume 1 y := by
        apply hf.mono_set
        rw [uIcc_of_le hy, uIcc_of_le hu]
        exact Icc_subset_Icc le_rfl hyu
      have hdef : IntervalIntegrable (gsDefectWeight chi) volume 1 y := by
        change IntervalIntegrable (fun v : ℝ ↦ (1 - chi v) / v) volume 1 y
        exact intervalIntegrable_gsDefectKernel hchi zero_lt_one hy
      have hg : IntervalIntegrable g volume 1 y := hdef.mul_const _
      have hpoint : ∀ t ∈ Icc (1 : ℝ) y, g t ≤ f t := by
        intro t ht
        have hnfit : (n : ℝ) * y ≤ u - t := by
          push_cast at hfit
          nlinarith [hfit, ht.2]
        exact mul_le_mul_of_nonneg_left (ih hnfit)
          (gsDefectWeight_nonneg hchi ht.1)
      have hrestricted :
          (∫ t : ℝ in 1..y, g t) ≤ ∫ t : ℝ in 1..y, f t :=
        intervalIntegral.integral_mono_on hy hg hfy hpoint
      have hfNonneg : 0 ≤ᵐ[volume.restrict (Ioc (1 : ℝ) u)] f := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact mul_nonneg (gsDefectWeight_nonneg hchi ht.1.le)
          (gsMoment_nonneg hchi n (sub_nonneg.mpr ht.2))
      have hextend : (∫ t : ℝ in 1..y, f t) ≤ ∫ t : ℝ in 1..u, f t :=
        intervalIntegral.integral_mono_interval le_rfl hy hyu hfNonneg hf
      calc
        gsLogScale chi y ^ (n + 1) =
            gsLogScale chi y * gsLogScale chi y ^ n := by ring
        _ = ∫ t : ℝ in 1..y, g t := by
          rw [intervalIntegral.integral_mul_const]
          rfl
        _ ≤ ∫ t : ℝ in 1..y, f t := hrestricted
        _ ≤ ∫ t : ℝ in 1..u, f t := hextend

lemma gsMoment_one_mono_Ici_zero {chi : ℝ → ℝ}
    (hchi : IsGSKernel chi) :
    MonotoneOn (gsMoment chi 1) (Ici (0 : ℝ)) := by
  intro v hv u hu hvu
  change 0 ≤ v at hv
  change 0 ≤ u at hu
  by_cases hv1 : 1 ≤ v
  · have hu1 : 1 ≤ u := hv1.trans hvu
    rw [gsMoment_one chi hv1, gsMoment_one chi hu1]
    exact gsLogScale_mono hchi hv1 hu1 hvu
  · have hvlt : v < 1 := lt_of_not_ge hv1
    rw [gsMoment]
    simp only [if_neg hv1]
    exact gsMoment_nonneg hchi 1 hu

lemma gsMoment_one_eq_logScale_max (chi : ℝ → ℝ) (u : ℝ) :
    gsMoment chi 1 u = gsLogScale chi (max 1 u) := by
  by_cases hu : 1 ≤ u
  · rw [gsMoment_one chi hu, max_eq_right hu]
  · rw [gsMoment, if_neg hu, max_eq_left (le_of_not_ge hu)]
    simp [gsLogScale]

lemma continuousOn_gsMoment_one_Icc
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {K : ℝ} (_hK : 0 ≤ K) :
    ContinuousOn (gsMoment chi 1) (Icc 0 K) := by
  rw [show gsMoment chi 1 = fun u => gsLogScale chi (max 1 u) by
    funext u
    exact gsMoment_one_eq_logScale_max chi u]
  exact (continuousOn_gsLogScale_Icc hchi (le_max_left 1 K)).comp
    (continuous_const.max continuous_id).continuousOn
    (by
      intro x hx
      exact ⟨le_max_left _ _, max_le_max le_rfl hx.2⟩)

lemma intervalIntegrable_gsDefect_mul_moment_one
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u : ℝ} (hu : 1 ≤ u) :
    IntervalIntegrable
      (fun t : ℝ => gsDefectWeight chi t * gsMoment chi 1 (u - t))
      volume 1 u := by
  have hdef : IntervalIntegrable (gsDefectWeight chi) volume 1 u := by
    change IntervalIntegrable (fun v : ℝ => (1 - chi v) / v) volume 1 u
    exact intervalIntegrable_gsDefectKernel hchi zero_lt_one hu
  have hsub : ContinuousOn (fun t : ℝ => u - t) (Icc 1 u) :=
    continuousOn_const.sub continuousOn_id
  have hmap : MapsTo (fun t : ℝ => u - t) (Icc 1 u) (Icc 0 u) := by
    intro t ht
    exact ⟨sub_nonneg.mpr ht.2, sub_le_self _ (by linarith [ht.1])⟩
  have hmom : ContinuousOn (fun t : ℝ => gsMoment chi 1 (u - t))
      (uIcc 1 u) := by
    rw [uIcc_of_le hu]
    exact (continuousOn_gsMoment_one_Icc hchi (by linarith)).comp hsub hmap
  exact hdef.mul_continuousOn hmom

lemma gsMoment_two_mono_Ici_zero {chi : ℝ → ℝ}
    (hchi : IsGSKernel chi) :
    MonotoneOn (gsMoment chi 2) (Ici (0 : ℝ)) := by
  intro v hv u hu hvu
  change 0 ≤ v at hv
  change 0 ≤ u at hu
  by_cases hv1 : 1 ≤ v
  · have hu1 : 1 ≤ u := hv1.trans hvu
    rw [gsMoment, if_pos hv1, gsMoment, if_pos hu1]
    let fv : ℝ → ℝ := fun t =>
      gsDefectWeight chi t * gsMoment chi 1 (v - t)
    let fu : ℝ → ℝ := fun t =>
      gsDefectWeight chi t * gsMoment chi 1 (u - t)
    have hfv : IntervalIntegrable fv volume 1 v :=
      intervalIntegrable_gsDefect_mul_moment_one hchi hv1
    have hfu : IntervalIntegrable fu volume 1 u :=
      intervalIntegrable_gsDefect_mul_moment_one hchi hu1
    have hfuv : IntervalIntegrable fu volume 1 v := by
      apply hfu.mono_set
      rw [uIcc_of_le hv1, uIcc_of_le hu1]
      exact Icc_subset_Icc le_rfl hvu
    have hpoint : ∀ t ∈ Icc (1 : ℝ) v, fv t ≤ fu t := by
      intro t ht
      apply mul_le_mul_of_nonneg_left
      · apply gsMoment_one_mono_Ici_zero hchi
        · exact sub_nonneg.mpr ht.2
        · exact sub_nonneg.mpr (ht.2.trans hvu)
        · linarith
      · exact gsDefectWeight_nonneg hchi ht.1
    have hfirst : (∫ t in 1..v, fv t) ≤ ∫ t in 1..v, fu t :=
      intervalIntegral.integral_mono_on hv1 hfv hfuv hpoint
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (1 : ℝ) u)] fu := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (gsDefectWeight_nonneg hchi ht.1.le)
        (gsMoment_nonneg hchi 1 (sub_nonneg.mpr ht.2))
    have hsecond : (∫ t in 1..v, fu t) ≤ ∫ t in 1..u, fu t :=
      intervalIntegral.integral_mono_interval le_rfl hv1 hvu hnonneg hfu
    exact hfirst.trans hsecond
  · rw [gsMoment, if_neg hv1]
    exact gsMoment_nonneg hchi 2 hu

lemma intervalIntegrable_gsDefect_mul_moment_two
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u : ℝ} (hu : 1 ≤ u) :
    IntervalIntegrable
      (fun t : ℝ => gsDefectWeight chi t * gsMoment chi 2 (u - t))
      volume 1 u := by
  have hdef : IntervalIntegrable (gsDefectWeight chi) volume 1 u := by
    change IntervalIntegrable (fun v : ℝ => (1 - chi v) / v) volume 1 u
    exact intervalIntegrable_gsDefectKernel hchi zero_lt_one hu
  let mext : ℝ → ℝ := fun x => gsMoment chi 2 (max 0 x)
  have hmextMono : Monotone mext := by
    intro a b hab
    apply gsMoment_two_mono_Ici_zero hchi
    · exact mem_Ici.mpr (le_max_left _ _)
    · exact mem_Ici.mpr (le_max_left _ _)
    · exact max_le_max le_rfl hab
  have hmextMeas : Measurable (fun t : ℝ => mext (u - t)) :=
    hmextMono.measurable.comp (measurable_const.sub measurable_id)
  have hmomAE : AEStronglyMeasurable
      (fun t : ℝ => gsMoment chi 2 (u - t))
      (volume.restrict (uIoc 1 u)) := by
    apply hmextMeas.aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [uIoc_of_le hu] at ht
    dsimp only [mext]
    rw [max_eq_right (sub_nonneg.mpr ht.2)]
  have hdefAE : AEStronglyMeasurable (gsDefectWeight chi)
      (volume.restrict (uIoc 1 u)) := by
    rw [uIoc_of_le hu]
    exact hdef.1.1
  have htarget : AEStronglyMeasurable
      (fun t : ℝ => gsDefectWeight chi t * gsMoment chi 2 (u - t))
      (volume.restrict (uIoc 1 u)) := hdefAE.mul hmomAE
  have hbound : IntervalIntegrable
      (fun t : ℝ => gsDefectWeight chi t * gsMoment chi 2 u)
      volume 1 u := hdef.mul_const _
  apply hbound.mono_fun htarget
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [uIoc_of_le hu] at ht
  have hwt : 0 ≤ gsDefectWeight chi t := gsDefectWeight_nonneg hchi ht.1.le
  have harg0 : 0 ≤ u - t := sub_nonneg.mpr ht.2
  have hmono : gsMoment chi 2 (u - t) ≤ gsMoment chi 2 u := by
    exact gsMoment_two_mono_Ici_zero hchi (mem_Ici.mpr harg0)
      (mem_Ici.mpr (zero_le_one.trans hu))
      (sub_le_self _ (zero_le_one.trans ht.1.le))
  have hmarg0 : 0 ≤ gsMoment chi 2 (u - t) := gsMoment_nonneg hchi 2 harg0
  have hmu0 : 0 ≤ gsMoment chi 2 u :=
    gsMoment_nonneg hchi 2 (zero_le_one.trans hu)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hwt hmarg0),
    abs_of_nonneg (mul_nonneg hwt hmu0)]
  exact mul_le_mul_of_nonneg_left hmono hwt

lemma gsMoment_three_le_logScale_mul_two
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u : ℝ} (hu : 1 ≤ u) :
    gsMoment chi 3 u ≤ gsLogScale chi u * gsMoment chi 2 u := by
  rw [gsMoment, if_pos hu]
  have hactual := intervalIntegrable_gsDefect_mul_moment_two hchi hu
  have hdef : IntervalIntegrable (gsDefectWeight chi) volume 1 u := by
    change IntervalIntegrable (fun v : ℝ => (1 - chi v) / v) volume 1 u
    exact intervalIntegrable_gsDefectKernel hchi zero_lt_one hu
  have hmodel : IntervalIntegrable
      (fun t : ℝ => gsDefectWeight chi t * gsMoment chi 2 u)
      volume 1 u := hdef.mul_const _
  calc
    (∫ t : ℝ in 1..u,
        gsDefectWeight chi t * gsMoment chi 2 (u - t)) ≤
        ∫ t : ℝ in 1..u,
          gsDefectWeight chi t * gsMoment chi 2 u := by
      apply intervalIntegral.integral_mono_on hu hactual hmodel
      intro t ht
      apply mul_le_mul_of_nonneg_left
      · exact gsMoment_two_mono_Ici_zero hchi
          (mem_Ici.mpr (sub_nonneg.mpr ht.2))
          (mem_Ici.mpr (zero_le_one.trans hu))
          (sub_le_self _ (zero_le_one.trans ht.1))
      · exact gsDefectWeight_nonneg hchi ht.1
    _ = gsLogScale chi u * gsMoment chi 2 u := by
      rw [intervalIntegral.integral_mul_const]
      rfl

/-- A two-variable simplex is covered by the two regions in which the first
or second coordinate is at most `u/2`. -/
lemma gsMoment_two_le_two_half
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) {u : ℝ} (hu0 : 0 ≤ u) :
    gsMoment chi 2 u ≤
      2 * gsMoment chi 1 (u / 2) * gsMoment chi 1 u := by
  by_cases hu2 : 2 ≤ u
  · have hu1 : 1 ≤ u := by linarith
    have hh1 : 1 ≤ u / 2 := by linarith
    have hhu : u / 2 ≤ u := by linarith
    rw [gsMoment, if_pos hu1]
    let f : ℝ → ℝ := fun t =>
      gsDefectWeight chi t * gsMoment chi 1 (u - t)
    have hfull : IntervalIntegrable f volume 1 u :=
      intervalIntegrable_gsDefect_mul_moment_one hchi hu1
    have hleft : IntervalIntegrable f volume 1 (u / 2) := by
      apply hfull.mono_set
      rw [uIcc_of_le hh1, uIcc_of_le hu1]
      exact Icc_subset_Icc le_rfl hhu
    have hright : IntervalIntegrable f volume (u / 2) u := by
      apply hfull.mono_set
      rw [uIcc_of_le hhu, uIcc_of_le hu1]
      exact Icc_subset_Icc hh1 le_rfl
    have hdef : IntervalIntegrable (gsDefectWeight chi) volume 1 u := by
      change IntervalIntegrable (fun v : ℝ => (1 - chi v) / v) volume 1 u
      exact intervalIntegrable_gsDefectKernel hchi zero_lt_one hu1
    have hdefLeft : IntervalIntegrable (gsDefectWeight chi) volume 1 (u / 2) := by
      apply hdef.mono_set
      rw [uIcc_of_le hh1, uIcc_of_le hu1]
      exact Icc_subset_Icc le_rfl hhu
    have hdefRight : IntervalIntegrable (gsDefectWeight chi) volume (u / 2) u := by
      apply hdef.mono_set
      rw [uIcc_of_le hhu, uIcc_of_le hu1]
      exact Icc_subset_Icc hh1 le_rfl
    have hleftBound :
        (∫ t : ℝ in 1..(u / 2), f t) ≤
          gsMoment chi 1 (u / 2) * gsMoment chi 1 u := by
      calc
        (∫ t : ℝ in 1..(u / 2), f t) ≤
            ∫ t : ℝ in 1..(u / 2),
              gsDefectWeight chi t * gsMoment chi 1 u := by
          apply intervalIntegral.integral_mono_on hh1 hleft
            (hdefLeft.mul_const _)
          intro t ht
          apply mul_le_mul_of_nonneg_left
          · exact gsMoment_one_mono_Ici_zero hchi
              (mem_Ici.mpr (sub_nonneg.mpr (ht.2.trans hhu)))
              (mem_Ici.mpr hu0) (sub_le_self _ (zero_le_one.trans ht.1))
          · exact gsDefectWeight_nonneg hchi ht.1
        _ = gsMoment chi 1 (u / 2) * gsMoment chi 1 u := by
          rw [intervalIntegral.integral_mul_const,
            show (∫ t : ℝ in 1..(u / 2), gsDefectWeight chi t) =
                gsLogScale chi (u / 2) by rfl,
            gsMoment_one chi hh1]
    have hrightPoint : ∀ t ∈ Icc (u / 2) u,
        f t ≤ gsDefectWeight chi t * gsMoment chi 1 (u / 2) := by
      intro t ht
      apply mul_le_mul_of_nonneg_left
      · exact gsMoment_one_mono_Ici_zero hchi
          (mem_Ici.mpr (sub_nonneg.mpr ht.2))
          (mem_Ici.mpr (by linarith : 0 ≤ u / 2)) (by linarith [ht.1])
      · exact gsDefectWeight_nonneg hchi (hh1.trans ht.1)
    have hrightFirst :
        (∫ t : ℝ in (u / 2)..u, f t) ≤
          ∫ t : ℝ in (u / 2)..u,
            gsDefectWeight chi t * gsMoment chi 1 (u / 2) := by
      exact intervalIntegral.integral_mono_on hhu hright
        (hdefRight.mul_const _) hrightPoint
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (1 : ℝ) u)]
        (fun t : ℝ => gsDefectWeight chi t * gsMoment chi 1 (u / 2)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (gsDefectWeight_nonneg hchi ht.1.le)
        (gsMoment_nonneg hchi 1 (by linarith : 0 ≤ u / 2))
    have hrightExtend :
        (∫ t : ℝ in (u / 2)..u,
            gsDefectWeight chi t * gsMoment chi 1 (u / 2)) ≤
          ∫ t : ℝ in 1..u,
            gsDefectWeight chi t * gsMoment chi 1 (u / 2) := by
      exact intervalIntegral.integral_mono_interval hh1 hhu le_rfl
        hnonneg (hdef.mul_const _)
    have hrightBound :
        (∫ t : ℝ in (u / 2)..u, f t) ≤
          gsMoment chi 1 (u / 2) * gsMoment chi 1 u := by
      calc
        (∫ t : ℝ in (u / 2)..u, f t) ≤
            ∫ t : ℝ in (u / 2)..u,
              gsDefectWeight chi t * gsMoment chi 1 (u / 2) := hrightFirst
        _ ≤ ∫ t : ℝ in 1..u,
              gsDefectWeight chi t * gsMoment chi 1 (u / 2) := hrightExtend
        _ = gsMoment chi 1 (u / 2) * gsMoment chi 1 u := by
          rw [intervalIntegral.integral_mul_const,
            show (∫ t : ℝ in 1..u, gsDefectWeight chi t) =
                gsLogScale chi u by rfl,
            gsMoment_one chi hu1]
          ring
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
    dsimp only [f] at hsplit
    nlinarith
  · have hult : u < 2 := lt_of_not_ge hu2
    rw [gsMoment_eq_zero_of_lt hu0 hult]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (gsMoment_nonneg hchi 1 (by linarith : 0 ≤ u / 2)))
      (gsMoment_nonneg hchi 1 hu0)

/-- A three-variable simplex is covered by the three regions in which one
coordinate is at most `u/3`.  Written recursively, the first region is split
off directly and the other two are controlled by the two-variable estimate. -/
lemma gsMoment_three_le_three_third
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) {u : ℝ} (hu0 : 0 ≤ u) :
    gsMoment chi 3 u ≤
      3 * gsMoment chi 1 (u / 3) * gsMoment chi 2 u := by
  by_cases hu3 : 3 ≤ u
  · have hu1 : 1 ≤ u := by linarith
    have hh1 : 1 ≤ u / 3 := by linarith
    have hhu : u / 3 ≤ u := by linarith
    rw [gsMoment, if_pos hu1]
    let f : ℝ → ℝ := fun t =>
      gsDefectWeight chi t * gsMoment chi 2 (u - t)
    let g : ℝ → ℝ := fun t =>
      gsDefectWeight chi t * gsMoment chi 1 (u - t)
    have hfull : IntervalIntegrable f volume 1 u :=
      intervalIntegrable_gsDefect_mul_moment_two hchi hu1
    have hgfull : IntervalIntegrable g volume 1 u :=
      intervalIntegrable_gsDefect_mul_moment_one hchi hu1
    have hleft : IntervalIntegrable f volume 1 (u / 3) := by
      apply hfull.mono_set
      rw [uIcc_of_le hh1, uIcc_of_le hu1]
      exact Icc_subset_Icc le_rfl hhu
    have hright : IntervalIntegrable f volume (u / 3) u := by
      apply hfull.mono_set
      rw [uIcc_of_le hhu, uIcc_of_le hu1]
      exact Icc_subset_Icc hh1 le_rfl
    have hgright : IntervalIntegrable g volume (u / 3) u := by
      apply hgfull.mono_set
      rw [uIcc_of_le hhu, uIcc_of_le hu1]
      exact Icc_subset_Icc hh1 le_rfl
    have hdef : IntervalIntegrable (gsDefectWeight chi) volume 1 u := by
      change IntervalIntegrable (fun v : ℝ => (1 - chi v) / v) volume 1 u
      exact intervalIntegrable_gsDefectKernel hchi zero_lt_one hu1
    have hdefLeft : IntervalIntegrable (gsDefectWeight chi) volume 1 (u / 3) := by
      apply hdef.mono_set
      rw [uIcc_of_le hh1, uIcc_of_le hu1]
      exact Icc_subset_Icc le_rfl hhu
    have hleftBound :
        (∫ t : ℝ in 1..(u / 3), f t) ≤
          gsMoment chi 1 (u / 3) * gsMoment chi 2 u := by
      calc
        (∫ t : ℝ in 1..(u / 3), f t) ≤
            ∫ t : ℝ in 1..(u / 3),
              gsDefectWeight chi t * gsMoment chi 2 u := by
          apply intervalIntegral.integral_mono_on hh1 hleft
            (hdefLeft.mul_const _)
          intro t ht
          apply mul_le_mul_of_nonneg_left
          · exact gsMoment_two_mono_Ici_zero hchi
              (mem_Ici.mpr (sub_nonneg.mpr (ht.2.trans hhu)))
              (mem_Ici.mpr hu0) (sub_le_self _ (zero_le_one.trans ht.1))
          · exact gsDefectWeight_nonneg hchi ht.1
        _ = gsMoment chi 1 (u / 3) * gsMoment chi 2 u := by
          rw [intervalIntegral.integral_mul_const,
            show (∫ t : ℝ in 1..(u / 3), gsDefectWeight chi t) =
                gsLogScale chi (u / 3) by rfl,
            gsMoment_one chi hh1]
    have hxi0 : 0 ≤ gsMoment chi 1 (u / 3) :=
      gsMoment_nonneg hchi 1 (by linarith)
    have hrightPoint : ∀ t ∈ Icc (u / 3) u,
        f t ≤ 2 * gsMoment chi 1 (u / 3) * g t := by
      intro t ht
      have hs0 : 0 ≤ u - t := sub_nonneg.mpr ht.2
      have hpair := gsMoment_two_le_two_half hchi hs0
      have hhalf : (u - t) / 2 ≤ u / 3 := by linarith [ht.1]
      have hmhalf : gsMoment chi 1 ((u - t) / 2) ≤
          gsMoment chi 1 (u / 3) :=
        gsMoment_one_mono_Ici_zero hchi
          (mem_Ici.mpr (by linarith : 0 ≤ (u - t) / 2))
          (mem_Ici.mpr (by linarith : 0 ≤ u / 3)) hhalf
      have hmone0 : 0 ≤ gsMoment chi 1 (u - t) :=
        gsMoment_nonneg hchi 1 hs0
      have hpair' : gsMoment chi 2 (u - t) ≤
          2 * gsMoment chi 1 (u / 3) * gsMoment chi 1 (u - t) := by
        calc
          gsMoment chi 2 (u - t) ≤
              2 * gsMoment chi 1 ((u - t) / 2) *
                gsMoment chi 1 (u - t) := hpair
          _ ≤ 2 * gsMoment chi 1 (u / 3) *
                gsMoment chi 1 (u - t) := by
            gcongr
      have hwt : 0 ≤ gsDefectWeight chi t :=
        gsDefectWeight_nonneg hchi (hh1.trans ht.1)
      dsimp only [f, g]
      nlinarith [mul_le_mul_of_nonneg_left hpair' hwt]
    have hrightFirst :
        (∫ t : ℝ in (u / 3)..u, f t) ≤
          ∫ t : ℝ in (u / 3)..u,
            2 * gsMoment chi 1 (u / 3) * g t := by
      exact intervalIntegral.integral_mono_on hhu hright
        (hgright.const_mul _) hrightPoint
    have hgNonneg : 0 ≤ᵐ[volume.restrict (Ioc (1 : ℝ) u)] g := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (gsDefectWeight_nonneg hchi ht.1.le)
        (gsMoment_nonneg hchi 1 (sub_nonneg.mpr ht.2))
    have hgExtend : (∫ t : ℝ in (u / 3)..u, g t) ≤ ∫ t : ℝ in 1..u, g t :=
      intervalIntegral.integral_mono_interval hh1 hhu le_rfl hgNonneg hgfull
    have hgEq : (∫ t : ℝ in 1..u, g t) = gsMoment chi 2 u := by
      rw [show gsMoment chi 2 u =
          ∫ t : ℝ in 1..u,
            gsDefectWeight chi t * gsMoment chi 1 (u - t) by
        rw [gsMoment, if_pos hu1]]
    have hrightBound :
        (∫ t : ℝ in (u / 3)..u, f t) ≤
          2 * gsMoment chi 1 (u / 3) * gsMoment chi 2 u := by
      calc
        (∫ t : ℝ in (u / 3)..u, f t) ≤
            ∫ t : ℝ in (u / 3)..u,
              2 * gsMoment chi 1 (u / 3) * g t := hrightFirst
        _ = 2 * gsMoment chi 1 (u / 3) *
              (∫ t : ℝ in (u / 3)..u, g t) := by
          rw [intervalIntegral.integral_const_mul]
        _ ≤ 2 * gsMoment chi 1 (u / 3) *
              (∫ t : ℝ in 1..u, g t) := by
          exact mul_le_mul_of_nonneg_left hgExtend (mul_nonneg (by norm_num) hxi0)
        _ = 2 * gsMoment chi 1 (u / 3) * gsMoment chi 2 u := by
          rw [hgEq]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
    dsimp only [f] at hsplit
    nlinarith
  · have hult : u < 3 := lt_of_not_ge hu3
    rw [gsMoment_eq_zero_of_lt hu0 hult]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (gsMoment_nonneg hchi 1 (by linarith : 0 ≤ u / 3)))
      (gsMoment_nonneg hchi 2 hu0)

/-- The form of the three-coordinate cover used in equation (6.3). -/
lemma gsMoment_three_le_three_logScale_third
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) {u : ℝ} (hu : 3 ≤ u) :
    gsMoment chi 3 u ≤
      3 * gsLogScale chi (u / 3) * gsMoment chi 2 u := by
  simpa [gsMoment_one chi (by linarith : 1 ≤ u / 3)] using
    gsMoment_three_le_three_third hchi (by linarith : 0 ≤ u)

/-- The degree-three odd truncation, after absorbing an upper bound for the
third moment into the second.  This is the algebraic part of (6.3). -/
lemma gs_lower_three_of_odd
    {chi sigma : ℝ → ℝ} (hodd : GSOddBonferroni chi sigma)
    {u xi : ℝ} (hu : 1 ≤ u)
    (hI3 : gsMoment chi 3 u ≤ 3 * xi * gsMoment chi 2 u) :
    1 - gsLogScale chi u +
        (1 - xi) / 2 * gsMoment chi 2 u ≤ sigma u := by
  have h := hodd u (zero_le_one.trans hu) 1
  have hs : gsAlternatingMomentSum chi 3 u =
      1 - gsLogScale chi u + gsMoment chi 2 u / 2 -
        gsMoment chi 3 u / 6 := by
    rw [gsAlternatingMomentSum]
    simp [Finset.sum_range_succ, gsMoment_one chi hu]
    ring
  norm_num at h
  rw [hs] at h
  linarith

end

end Erdos783
