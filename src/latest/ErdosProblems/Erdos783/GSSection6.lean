/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos783.GSModifiedKernel
import ErdosProblems.Erdos783.GSChampion

/-! # Section 6 estimates for the Granville--Soundararajan extremal theorem -/

open MeasureTheory Set Finset
namespace Erdos783
noncomputable section

lemma integral_inv_div_scale
    (chi : ℝ → ℝ) {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ in y / gsScale chi y..y, 1 / t) = gsLogScale chi y := by
  have hc : 0 < y / gsScale chi y := div_pos hy (gsScale_pos chi y)
  rw [integral_one_div_of_pos hc hy]
  have hyne : y ≠ 0 := hy.ne'
  have harg : y / (y / gsScale chi y) = gsScale chi y := by
    field_simp [hyne, ne_of_gt (gsScale_pos chi y)]
  rw [harg, gsScale, Real.log_exp]

lemma integral_inv_scale_ratio
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {y u : ℝ} (hy : 1 ≤ y) (hyu : y ≤ u) :
    (∫ t : ℝ in u * gsScale chi y / gsScale chi u..u, 1 / t) =
      gsLogScale chi u - gsLogScale chi y := by
  have hu : 0 < u := zero_lt_one.trans_le (hy.trans hyu)
  have hc : 0 < u * gsScale chi y / gsScale chi u :=
    div_pos (mul_pos hu (gsScale_pos chi y)) (gsScale_pos chi u)
  rw [integral_one_div_of_pos hc hu]
  have hune : u ≠ 0 := hu.ne'
  have harg : u / (u * gsScale chi y / gsScale chi u) =
      gsScale chi u / gsScale chi y := by
    field_simp [hune, ne_of_gt (gsScale_pos chi y),
      ne_of_gt (gsScale_pos chi u)]
  rw [harg, gsScale, gsScale, ← Real.exp_sub, Real.log_exp]

lemma intervalIntegrable_inv_mul_moment_one
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbu : b ≤ u) :
    IntervalIntegrable
      (fun t : ℝ => (1 / t) * gsMoment chi 1 (u - t)) volume a b := by
  have hinv : ContinuousOn (fun t : ℝ => 1 / t) (Icc a b) := by
    exact continuousOn_const.div₀ continuousOn_id
      (fun t ht => (ha.trans_le ht.1).ne')
  have hsub : ContinuousOn (fun t : ℝ => u - t) (Icc a b) :=
    continuousOn_const.sub continuousOn_id
  have hmap : MapsTo (fun t : ℝ => u - t) (Icc a b) (Icc 0 u) := by
    intro t ht
    exact ⟨sub_nonneg.mpr (ht.2.trans hbu), sub_le_self _ (ha.le.trans ht.1)⟩
  have hmom : ContinuousOn (fun t : ℝ => gsMoment chi 1 (u - t))
      (Icc a b) :=
    (continuousOn_gsMoment_one_Icc hchi (by linarith)).comp hsub hmap
  have hprod : ContinuousOn
      (fun t : ℝ => (1 / t) * gsMoment chi 1 (u - t)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact hinv.mul hmom
  exact hprod.intervalIntegrable

lemma gsMoment_two_rearranged
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u y : ℝ} (hu : 1 ≤ u) (hy : 1 ≤ y) (hyu : y ≤ u) :
    (∫ t : ℝ in y / gsScale chi y..y,
        gsMoment chi 1 (u - t) / t) +
      (∫ t : ℝ in u * gsScale chi y / gsScale chi u..u,
        gsMoment chi 1 (u - t) / t) ≤ gsMoment chi 2 u := by
  have hactual := intervalIntegrable_gsDefect_mul_moment_one hchi hu
  have hleftActual : IntervalIntegrable
      (fun t : ℝ => gsDefectWeight chi t * gsMoment chi 1 (u - t))
      volume 1 y := by
    apply hactual.mono_set
    rw [uIcc_of_le hy, uIcc_of_le hu]
    exact Icc_subset_Icc le_rfl hyu
  have hrightActual : IntervalIntegrable
      (fun t : ℝ => gsDefectWeight chi t * gsMoment chi 1 (u - t))
      volume y u := by
    apply hactual.mono_set
    rw [uIcc_of_le hyu, uIcc_of_le hu]
    exact Icc_subset_Icc hy le_rfl
  have hinvFull : IntervalIntegrable (fun t : ℝ => 1 / t) volume 1 u := by
    have hcont : ContinuousOn (fun t : ℝ => 1 / t) (uIcc (1 : ℝ) u) := by
      rw [uIcc_of_le hu]
      exact continuousOn_const.div₀ continuousOn_id
        (fun t ht => (zero_lt_one.trans_le ht.1).ne')
    exact hcont.intervalIntegrable
  have hinvLeft : IntervalIntegrable (fun t : ℝ => 1 / t) volume 1 y := by
    apply hinvFull.mono_set
    rw [uIcc_of_le hy, uIcc_of_le hu]
    exact Icc_subset_Icc le_rfl hyu
  have hinvRight : IntervalIntegrable (fun t : ℝ => 1 / t) volume y u := by
    apply hinvFull.mono_set
    rw [uIcc_of_le hyu, uIcc_of_le hu]
    exact Icc_subset_Icc hy le_rfl
  have hmodelLeft := intervalIntegrable_inv_mul_moment_one hchi
    (a := (1 : ℝ)) (b := y) (u := u) zero_lt_one hy hyu
  have hmodelRight := intervalIntegrable_inv_mul_moment_one hchi
    (a := y) (b := u) (u := u) (zero_lt_one.trans_le hy) hyu le_rfl
  have hanti : AntitoneOn (fun t : ℝ => gsMoment chi 1 (u - t)) (Icc 1 u) := by
    intro s hs t ht hst
    exact gsMoment_one_mono_Ici_zero hchi
      (mem_Ici.mpr (sub_nonneg.mpr ht.2))
      (mem_Ici.mpr (sub_nonneg.mpr hs.2)) (by linarith)
  have hantiLeft : AntitoneOn (fun t : ℝ => gsMoment chi 1 (u - t))
      (Icc 1 y) := hanti.mono (Icc_subset_Icc le_rfl hyu)
  have hantiRight : AntitoneOn (fun t : ℝ => gsMoment chi 1 (u - t))
      (Icc y u) := hanti.mono (Icc_subset_Icc hy le_rfl)
  have hcLeft0 : 0 < y / gsScale chi y :=
    div_pos (zero_lt_one.trans_le hy) (gsScale_pos chi y)
  have hcLeft1 : 1 ≤ y / gsScale chi y := by
    apply (le_div_iff₀ (gsScale_pos chi y)).mpr
    simpa using gsScale_le_self hchi hy
  have hcLeftY : y / gsScale chi y ≤ y := by
    have hE1 := gsScale_ge_one hchi hy
    exact (div_le_iff₀ (gsScale_pos chi y)).mpr
      (by nlinarith [zero_lt_one.trans_le hy])
  have hcRight0 : 0 < u * gsScale chi y / gsScale chi u :=
    div_pos (mul_pos (zero_lt_one.trans_le (hy.trans hyu)) (gsScale_pos chi y))
      (gsScale_pos chi u)
  have hcRightY : y ≤ u * gsScale chi y / gsScale chi u := by
    have hdiv := gsScale_div_antitone hchi hy hyu
    have hy0 : 0 < y := zero_lt_one.trans_le hy
    have hu0 : 0 < u := hy0.trans_le hyu
    have hEy0 := gsScale_pos chi y
    have hEu0 := gsScale_pos chi u
    field_simp [hy0.ne', hu0.ne', hEy0.ne', hEu0.ne'] at hdiv ⊢
    nlinarith
  have hcRightU : u * gsScale chi y / gsScale chi u ≤ u := by
    have hmono := gsScale_mono hchi hy (hy.trans hyu) hyu
    have hu0 : 0 < u := zero_lt_one.trans_le (hy.trans hyu)
    have hEu0 := gsScale_pos chi u
    apply (div_le_iff₀ hEu0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmono hu0.le]
  have hleftMass :
      (∫ t : ℝ in 1..y, (1 - chi t) * (1 / t)) =
        ∫ t : ℝ in y / gsScale chi y..y, 1 / t := by
    rw [show (∫ t : ℝ in 1..y, (1 - chi t) * (1 / t)) =
        gsLogScale chi y by
      unfold gsLogScale
      apply intervalIntegral.integral_congr
      intro t _ht
      ring]
    exact (integral_inv_div_scale chi (zero_lt_one.trans_le hy)).symm
  have hrightMass :
      (∫ t : ℝ in y..u, (1 - chi t) * (1 / t)) =
        ∫ t : ℝ in u * gsScale chi y / gsScale chi u..u, 1 / t := by
    rw [show (∫ t : ℝ in y..u, (1 - chi t) * (1 / t)) =
        gsLogScale chi u - gsLogScale chi y by
      rw [gsLogScale_sub hchi hy hyu]
      apply intervalIntegral.integral_congr
      intro t _ht
      ring]
    exact (integral_inv_scale_ratio hchi hy hyu).symm
  have hleft := gs_weighted_rearrangement_lower_antitone
    (f := fun t : ℝ => 1 - chi t) (w := fun t : ℝ => 1 / t)
    (g := fun t : ℝ => gsMoment chi 1 (u - t))
    hcLeft1 hcLeftY
    (by
      convert (intervalIntegrable_gsDefectKernel hchi zero_lt_one hy) using 1
      ext t
      ring)
    hinvLeft
    (by
      convert hleftActual using 1
      ext t
      simp only [gsDefectWeight]
      ring)
    hmodelLeft
    (by intro t ht; linarith [hchi.2.2.1 t (by linarith [ht.1])])
    (by intro t ht; linarith [hchi.2.1 t (by linarith [ht.1])])
    (by intro t ht; exact one_div_nonneg.mpr (by linarith [ht.1]))
    hantiLeft hleftMass
  have hright := gs_weighted_rearrangement_lower_antitone
    (f := fun t : ℝ => 1 - chi t) (w := fun t : ℝ => 1 / t)
    (g := fun t : ℝ => gsMoment chi 1 (u - t))
    hcRightY hcRightU
    (by
      convert (intervalIntegrable_gsDefectKernel hchi
        (zero_lt_one.trans_le hy) hyu) using 1
      ext t
      ring)
    hinvRight
    (by
      convert hrightActual using 1
      ext t
      simp only [gsDefectWeight]
      ring)
    hmodelRight
    (by intro t ht; linarith [hchi.2.2.1 t (by linarith [hy, ht.1])])
    (by intro t ht; linarith [hchi.2.1 t (by linarith [hy, ht.1])])
    (by intro t ht; exact one_div_nonneg.mpr (by linarith [hy, ht.1]))
    hantiRight hrightMass
  have hleft' :
      (∫ t : ℝ in y / gsScale chi y..y,
          gsMoment chi 1 (u - t) / t) ≤
        ∫ t : ℝ in 1..y,
          gsDefectWeight chi t * gsMoment chi 1 (u - t) := by
    convert hleft using 1 <;>
      apply intervalIntegral.integral_congr <;> intro t _ht <;>
      simp only [gsDefectWeight] <;> ring
  have hright' :
      (∫ t : ℝ in u * gsScale chi y / gsScale chi u..u,
          gsMoment chi 1 (u - t) / t) ≤
        ∫ t : ℝ in y..u,
          gsDefectWeight chi t * gsMoment chi 1 (u - t) := by
    convert hright using 1 <;>
      apply intervalIntegral.integral_congr <;> intro t _ht <;>
      simp only [gsDefectWeight] <;> ring
  rw [gsMoment, if_pos hu]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hleftActual hrightActual
  calc
    _ ≤ (∫ t : ℝ in 1..y,
            gsDefectWeight chi t * gsMoment chi 1 (u - t)) +
          ∫ t : ℝ in y..u,
            gsDefectWeight chi t * gsMoment chi 1 (u - t) :=
      add_le_add hleft' hright'
    _ = _ := hsplit

lemma gsMoment_one_ge_log_scale_ratio
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {t u : ℝ} (ht : 1 ≤ t) (htu : t ≤ u) :
    Real.log (gsScale chi u * t / u) ≤ gsMoment chi 1 t := by
  have hu : 1 ≤ u := ht.trans htu
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hu0 : 0 < u := ht0.trans_le htu
  have hratio := gsScale_div_antitone hchi ht htu
  have hscale : gsScale chi u * t / u ≤ gsScale chi t := by
    have hEt0 := gsScale_pos chi t
    have hEu0 := gsScale_pos chi u
    field_simp [ht0.ne', hu0.ne', hEt0.ne', hEu0.ne'] at hratio ⊢
    nlinarith
  have harg0 : 0 < gsScale chi u * t / u :=
    div_pos (mul_pos (gsScale_pos chi u) ht0) hu0
  have hlog := Real.strictMonoOn_log.monotoneOn harg0 (gsScale_pos chi t) hscale
  rw [gsMoment_one chi ht]
  simpa [gsScale] using hlog

lemma gsMoment_one_ge_at
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) :
    gsMoment chi 1 s ≤ gsMoment chi 1 t :=
  gsMoment_one_mono_Ici_zero hchi (mem_Ici.mpr hs0)
    (mem_Ici.mpr (hs0.trans hst)) hst

def gsGamma (e : ℝ) : ℝ :=
  ∫ t : ℝ in 1..(e - 1), Real.log (e - t) / t

lemma scaled_gamma_integral
    {u e : ℝ} (hu : 0 < u) (he : 0 < e) :
    (∫ v : ℝ in u / e..u * (1 - 1 / e),
        Real.log (e * (u - v) / u) / v) = gsGamma e := by
  let f : ℝ → ℝ := fun t => Real.log (e - t) / t
  have hc : e / u ≠ 0 := div_ne_zero he.ne' hu.ne'
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (f := f) (a := u / e) (b := u * (1 - 1 / e)) (e / u)
  simp only [smul_eq_mul] at hchange
  have hca : e / u * (u / e) = 1 := by field_simp [hu.ne', he.ne']
  have hcb : e / u * (u * (1 - 1 / e)) = e - 1 := by
    field_simp [hu.ne', he.ne']
  rw [hca, hcb] at hchange
  change (∫ v : ℝ in u / e..u * (1 - 1 / e),
      Real.log (e * (u - v) / u) / v) = ∫ t : ℝ in 1..e - 1, f t
  rw [← hchange]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _hv
  dsimp only [f]
  field_simp [hu.ne', he.ne']

lemma intervalIntegrable_log_complement_div
    {u e a b : ℝ} (hu : 0 < u) (he : 0 < e)
    (ha : 0 < a) (hab : a ≤ b) (hbu : b < u) :
    IntervalIntegrable
      (fun v : ℝ => Real.log (e * (u - v) / u) / v) volume a b := by
  have harg : ContinuousOn (fun v : ℝ => e * (u - v) / u) (Icc a b) := by
    fun_prop
  have hargPos : ∀ v ∈ Icc a b, 0 < e * (u - v) / u := by
    intro v hv
    exact div_pos (mul_pos he (sub_pos.mpr (hv.2.trans_lt hbu))) hu
  have hcont : ContinuousOn
      (fun v : ℝ => Real.log (e * (u - v) / u) / v) (Icc a b) := by
    exact (Real.continuousOn_log.comp harg
      (fun v hv => (hargPos v hv).ne')).div₀ continuousOn_id
      (fun v hv => (ha.trans_le hv.1).ne')
  have hcont' : ContinuousOn
      (fun v : ℝ => Real.log (e * (u - v) / u) / v) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact hcont
  exact hcont'.intervalIntegrable

lemma gsMoment_two_lower_segments
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u : ℝ} (hu3 : 3 ≤ u)
    (he2 : 2 < gsScale chi u) (heUpper : gsScale chi u ≤ 13 / 5)
    (hcut : gsScale chi (u / gsScale chi u) ≤ gsScale chi u - 1) :
    let e := gsScale chi u
    let y := u / 3
    let ey := gsScale chi y
    (∫ v : ℝ in y / ey..y, Real.log (e * (u - v) / u) / v) +
      (∫ v : ℝ in u * ey / e..u * (1 - 1 / e),
        Real.log (e * (u - v) / u) / v) +
      gsLogScale chi y * Real.log (2 * e / (3 * (e - 1))) ≤
        gsMoment chi 2 u := by
  dsimp only
  let e := gsScale chi u
  let y := u / 3
  let ey := gsScale chi y
  let c₁ := y / ey
  let c₂ := u * ey / e
  let u₁ := u * (1 - 1 / e)
  let z := 2 * u / 3
  have hu : 1 ≤ u := by linarith
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hy : 1 ≤ y := by dsimp only [y]; linarith
  have hyu : y ≤ u := by dsimp only [y]; linarith
  have hePos : 0 < e := by exact gsScale_pos chi u
  have heyPos : 0 < ey := by exact gsScale_pos chi y
  have heOne : 1 ≤ e := gsScale_ge_one hchi hu
  have heyOne : 1 ≤ ey := gsScale_ge_one hchi hy
  have heu : e ≤ u := gsScale_le_self hchi hu
  have heThree : e ≤ 3 := by dsimp only [e] at heUpper ⊢; norm_num at heUpper ⊢; linarith
  have hyCutArg : y ≤ u / e := by
    dsimp only [y]
    apply (div_le_div_iff_of_pos_left hu0 (by norm_num) hePos).mpr
    exact heThree
  have huDivE : 1 ≤ u / e := by
    exact (le_div_iff₀ hePos).mpr (by simpa only [one_mul] using heu)
  have heyCut : ey ≤ e - 1 := by
    calc
      ey ≤ gsScale chi (u / e) :=
        gsScale_mono hchi hy huDivE hyCutArg
      _ ≤ e - 1 := by simpa only [e] using hcut
  have hc₁Pos : 0 < c₁ := div_pos (zero_lt_one.trans_le hy) heyPos
  have hc₁y : c₁ ≤ y := by
    dsimp only [c₁]
    apply (div_le_iff₀ heyPos).mpr
    nlinarith
  have hc₂Pos : 0 < c₂ := div_pos (mul_pos hu0 heyPos) hePos
  have hu₁Pos : 0 < u₁ := by
    dsimp only [u₁]
    have : 0 < 1 - 1 / e := by
      rw [sub_pos]
      exact (div_lt_one hePos).mpr (by linarith)
    positivity
  have hu₁lt : u₁ < u := by
    have hgap : u - u₁ = u / e := by
      dsimp only [u₁]
      field_simp [hePos.ne']
      ring
    have hgapPos : 0 < u / e := div_pos hu0 hePos
    linarith
  have hc₂u₁ : c₂ ≤ u₁ := by
    dsimp only [c₂, u₁]
    rw [show u * (1 - 1 / e) = u * (e - 1) / e by
      field_simp [hePos.ne']]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left heyCut hu0.le) hePos.le
  have hu₁z : u₁ ≤ z := by
    dsimp only [u₁, z]
    have heNe : e ≠ 0 := hePos.ne'
    field_simp [heNe]
    nlinarith [mul_le_mul_of_nonneg_left heThree hu0.le]
  have hzu : z ≤ u := by dsimp only [z]; linarith
  have hraw := gsMoment_two_rearranged hchi hu hy hyu
  change
    (∫ t : ℝ in c₁..y, gsMoment chi 1 (u - t) / t) +
      (∫ t : ℝ in c₂..u, gsMoment chi 1 (u - t) / t) ≤
        gsMoment chi 2 u at hraw
  have hmodelLeft := intervalIntegrable_inv_mul_moment_one hchi
    hc₁Pos hc₁y hyu
  have hmodelRight := intervalIntegrable_inv_mul_moment_one hchi
    hc₂Pos (hc₂u₁.trans (hu₁z.trans hzu)) le_rfl
  have hlogLeft := intervalIntegrable_log_complement_div hu0 hePos
    hc₁Pos hc₁y (by dsimp only [y]; linarith)
  have hlogRight := intervalIntegrable_log_complement_div hu0 hePos
    hc₂Pos hc₂u₁ hu₁lt
  have hleftLower :
      (∫ v : ℝ in c₁..y, Real.log (e * (u - v) / u) / v) ≤
        ∫ v : ℝ in c₁..y, gsMoment chi 1 (u - v) / v := by
    have hm := intervalIntegral.integral_mono_on hc₁y hlogLeft hmodelLeft (by
      intro v hv
      have ht1 : 1 ≤ u - v := by
        have hvu : v ≤ y := hv.2
        dsimp only [y] at hvu
        linarith
      have htU : u - v ≤ u := by linarith [hc₁Pos.le.trans hv.1]
      have hpoint := gsMoment_one_ge_log_scale_ratio hchi ht1 htU
      change Real.log (e * (u - v) / u) ≤ gsMoment chi 1 (u - v) at hpoint
      have hv0 : 0 ≤ v := hc₁Pos.le.trans hv.1
      simpa [div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_left hpoint (inv_nonneg.mpr hv0))
    convert hm using 1 <;>
      apply intervalIntegral.integral_congr <;> intro v _hv <;> ring
  have hmodelC₂Z : IntervalIntegrable
      (fun v : ℝ => (1 / v) * gsMoment chi 1 (u - v)) volume c₂ z := by
    apply hmodelRight.mono_set
    rw [uIcc_of_le (hc₂u₁.trans hu₁z),
      uIcc_of_le (hc₂u₁.trans (hu₁z.trans hzu))]
    exact Icc_subset_Icc le_rfl hzu
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc c₂ u)]
      (fun v : ℝ => (1 / v) * gsMoment chi 1 (u - v)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact mul_nonneg (one_div_nonneg.mpr (hc₂Pos.le.trans hv.1.le))
      (gsMoment_nonneg hchi 1 (sub_nonneg.mpr hv.2))
  have hrestrict :
      (∫ v : ℝ in c₂..z, (1 / v) * gsMoment chi 1 (u - v)) ≤
        ∫ v : ℝ in c₂..u, (1 / v) * gsMoment chi 1 (u - v) :=
    intervalIntegral.integral_mono_interval le_rfl
      (hc₂u₁.trans hu₁z) hzu hnonneg hmodelRight
  have hmodelC₂U₁ : IntervalIntegrable
      (fun v : ℝ => (1 / v) * gsMoment chi 1 (u - v)) volume c₂ u₁ := by
    apply hmodelC₂Z.mono_set
    rw [uIcc_of_le hc₂u₁, uIcc_of_le (hc₂u₁.trans hu₁z)]
    exact Icc_subset_Icc le_rfl hu₁z
  have hmodelU₁Z : IntervalIntegrable
      (fun v : ℝ => (1 / v) * gsMoment chi 1 (u - v)) volume u₁ z := by
    apply hmodelC₂Z.mono_set
    rw [uIcc_of_le hu₁z, uIcc_of_le (hc₂u₁.trans hu₁z)]
    exact Icc_subset_Icc hc₂u₁ le_rfl
  have hrightSplit := intervalIntegral.integral_add_adjacent_intervals
    hmodelC₂U₁ hmodelU₁Z
  have hrightLogLower :
      (∫ v : ℝ in c₂..u₁, Real.log (e * (u - v) / u) / v) ≤
        ∫ v : ℝ in c₂..u₁, (1 / v) * gsMoment chi 1 (u - v) := by
    apply intervalIntegral.integral_mono_on hc₂u₁ hlogRight hmodelC₂U₁
    intro v hv
    have ht1 : 1 ≤ u - v := by
      have hvu₁ : v ≤ u₁ := hv.2
      have hue : 1 ≤ u / e := huDivE
      dsimp only [u₁] at hvu₁
      have heNe : e ≠ 0 := hePos.ne'
      field_simp [heNe] at hvu₁
      nlinarith
    have htU : u - v ≤ u := by linarith [hc₂Pos.le.trans hv.1]
    have hpoint := gsMoment_one_ge_log_scale_ratio hchi ht1 htU
    change Real.log (e * (u - v) / u) ≤ gsMoment chi 1 (u - v) at hpoint
    have hv0 : 0 ≤ v := hc₂Pos.le.trans hv.1
    simpa [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hpoint (inv_nonneg.mpr hv0)
  have hxi : gsMoment chi 1 y = gsLogScale chi y := gsMoment_one chi hy
  have hmiddleModel : IntervalIntegrable
      (fun v : ℝ => gsLogScale chi y / v) volume u₁ z := by
    have hinv : IntervalIntegrable (fun v : ℝ => 1 / v) volume u₁ z := by
      have hcont : ContinuousOn (fun v : ℝ => 1 / v) (uIcc u₁ z) := by
        rw [uIcc_of_le hu₁z]
        exact continuousOn_const.div₀ continuousOn_id
          (fun v hv => (hu₁Pos.trans_le hv.1).ne')
      exact hcont.intervalIntegrable
    convert hinv.const_mul (gsLogScale chi y) using 1
    ext v
    ring
  have hmiddleLower :
      (∫ v : ℝ in u₁..z, gsLogScale chi y / v) ≤
        ∫ v : ℝ in u₁..z, (1 / v) * gsMoment chi 1 (u - v) := by
    apply intervalIntegral.integral_mono_on hu₁z hmiddleModel hmodelU₁Z
    intro v hv
    have hyArg : y ≤ u - v := by
      dsimp only [y, z]
      dsimp only [z] at hv
      norm_num at hv ⊢
      linarith
    have hmono := gsMoment_one_ge_at hchi (by linarith : 0 ≤ y) hyArg
    rw [hxi] at hmono
    have hv0 : 0 ≤ v := hu₁Pos.le.trans hv.1
    simpa [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hv0)
  have hmiddleEval :
      (∫ v : ℝ in u₁..z, gsLogScale chi y / v) =
        gsLogScale chi y * Real.log (2 * e / (3 * (e - 1))) := by
    rw [show (fun v : ℝ => gsLogScale chi y / v) =
        fun v : ℝ => gsLogScale chi y * (1 / v) by
      funext v; ring,
      intervalIntegral.integral_const_mul,
      integral_one_div_of_pos hu₁Pos (by dsimp only [z]; positivity)]
    congr 2
    dsimp only [u₁, z]
    field_simp [hePos.ne', hu0.ne']
  have hrightLower :
      (∫ v : ℝ in c₂..u₁, Real.log (e * (u - v) / u) / v) +
          gsLogScale chi y * Real.log (2 * e / (3 * (e - 1))) ≤
        ∫ v : ℝ in c₂..u, gsMoment chi 1 (u - v) / v := by
    have hsum := add_le_add hrightLogLower hmiddleLower
    rw [hmiddleEval] at hsum
    have hconv :
        (∫ v : ℝ in c₂..z, (1 / v) * gsMoment chi 1 (u - v)) =
          (∫ v : ℝ in c₂..u₁, (1 / v) * gsMoment chi 1 (u - v)) +
            ∫ v : ℝ in u₁..z, (1 / v) * gsMoment chi 1 (u - v) :=
      hrightSplit.symm
    rw [← hconv] at hsum
    have := hsum.trans hrestrict
    calc
      _ ≤ ∫ v : ℝ in c₂..u, (1 / v) * gsMoment chi 1 (u - v) := this
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro v _hv
        ring
  dsimp only [e, y, ey, c₁, c₂, u₁, z] at *
  linarith

lemma scaled_first_correction
    {u e ey : ℝ} (hu : 0 < u) (he : 0 < e) (hey : 0 < ey) :
    (∫ v : ℝ in u / (3 * ey)..u / 3,
        Real.log (e * (u - v) / u) / v) =
      ∫ t : ℝ in 1..ey,
        Real.log (e * (1 - t / (3 * ey))) / t := by
  let f : ℝ → ℝ := fun t =>
    Real.log (e * (1 - t / (3 * ey))) / t
  have hc : 3 * ey / u ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hey.ne') hu.ne'
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (f := f) (a := u / (3 * ey)) (b := u / 3) (3 * ey / u)
  simp only [smul_eq_mul] at hchange
  have hca : 3 * ey / u * (u / (3 * ey)) = 1 := by
    field_simp [hu.ne', hey.ne']
  have hcb : 3 * ey / u * (u / 3) = ey := by
    field_simp [hu.ne', hey.ne']
  rw [hca, hcb] at hchange
  change (∫ v : ℝ in u / (3 * ey)..u / 3,
      Real.log (e * (u - v) / u) / v) = ∫ t : ℝ in 1..ey, f t
  rw [← hchange, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _hv
  dsimp only [f]
  field_simp [hu.ne', hey.ne']

lemma scaled_partial_gamma
    {u e ey : ℝ} (hu : 0 < u) (he : 0 < e) :
    (∫ v : ℝ in u / e..u * ey / e,
        Real.log (e * (u - v) / u) / v) =
      ∫ t : ℝ in 1..ey, Real.log (e - t) / t := by
  let f : ℝ → ℝ := fun t => Real.log (e - t) / t
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (f := f) (a := u / e) (b := u * ey / e) (e / u)
  simp only [smul_eq_mul] at hchange
  have hca : e / u * (u / e) = 1 := by field_simp [hu.ne', he.ne']
  have hcb : e / u * (u * ey / e) = ey := by field_simp [hu.ne', he.ne']
  rw [hca, hcb] at hchange
  change (∫ v : ℝ in u / e..u * ey / e,
      Real.log (e * (u - v) / u) / v) = ∫ t : ℝ in 1..ey, f t
  rw [← hchange, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _hv
  dsimp only [f]
  field_simp [hu.ne', he.ne']

lemma section62_integral_gap
    {e ey : ℝ} (he2 : 2 < e) (heUpper : e ≤ 13 / 5)
    (heyOne : 1 ≤ ey) (heyUpper : ey ≤ e - 1) :
    Real.log ey * Real.log (e * (1 - 1 / (3 * ey)) / (e - 1)) ≤
      (∫ t : ℝ in 1..ey,
        Real.log (e * (1 - t / (3 * ey))) / t) -
      ∫ t : ℝ in 1..ey, Real.log (e - t) / t := by
  have hePos : 0 < e := by linarith
  have heyPos : 0 < ey := zero_lt_one.trans_le heyOne
  have heThree : e < 3 := by norm_num at heUpper ⊢; linarith
  have hthree : e < 3 * ey := by nlinarith
  let A : ℝ → ℝ := fun t => e * (1 - t / (3 * ey))
  let B : ℝ → ℝ := fun t => e - t
  let R : ℝ → ℝ := fun t => A t / B t
  have hApos : ∀ t ∈ Icc (1 : ℝ) ey, 0 < A t := by
    intro t ht
    dsimp only [A]
    have hfrac : t / (3 * ey) ≤ 1 / 3 := by
      apply (div_le_iff₀ (by positivity : 0 < 3 * ey)).mpr
      calc
        t ≤ ey := ht.2
        _ = (1 / 3 : ℝ) * (3 * ey) := by ring
    have : 0 < 1 - t / (3 * ey) := by nlinarith
    positivity
  have hBpos : ∀ t ∈ Icc (1 : ℝ) ey, 0 < B t := by
    intro t ht
    dsimp only [B]
    linarith [ht.2, heyUpper]
  have hRpos : ∀ t ∈ Icc (1 : ℝ) ey, 0 < R t := by
    intro t ht
    exact div_pos (hApos t ht) (hBpos t ht)
  have hRmono : ∀ t ∈ Icc (1 : ℝ) ey, R 1 ≤ R t := by
    intro t ht
    dsimp only [R]
    apply (div_le_div_iff₀ (hBpos 1 ⟨le_rfl, heyOne⟩) (hBpos t ht)).mpr
    dsimp only [A, B]
    have hprod : 0 ≤ (3 * ey - e) * (t - 1) :=
      mul_nonneg (sub_nonneg.mpr hthree.le) (sub_nonneg.mpr ht.1)
    field_simp [heyPos.ne']
    nlinarith [mul_nonneg hePos.le hprod]
  have hlogMono : ∀ t ∈ Icc (1 : ℝ) ey,
      Real.log (R 1) ≤ Real.log (R t) := by
    intro t ht
    exact Real.strictMonoOn_log.monotoneOn
      (hRpos 1 ⟨le_rfl, heyOne⟩) (hRpos t ht) (hRmono t ht)
  have hAcont : ContinuousOn A (Icc (1 : ℝ) ey) := by
    dsimp only [A]
    fun_prop
  have hBcont : ContinuousOn B (Icc (1 : ℝ) ey) := by
    dsimp only [B]
    fun_prop
  have hRcont : ContinuousOn R (Icc (1 : ℝ) ey) := by
    dsimp only [R]
    exact hAcont.div₀ hBcont (fun t ht => (hBpos t ht).ne')
  have hGapInt : IntervalIntegrable
      (fun t : ℝ => Real.log (R t) / t) volume 1 ey := by
    have hcont : ContinuousOn (fun t : ℝ => Real.log (R t) / t)
        (uIcc (1 : ℝ) ey) := by
      rw [uIcc_of_le heyOne]
      exact (Real.continuousOn_log.comp hRcont
        (fun t ht => (hRpos t ht).ne')).div₀ continuousOn_id
        (fun t ht => (zero_lt_one.trans_le ht.1).ne')
    exact hcont.intervalIntegrable
  have hConstInt : IntervalIntegrable
      (fun t : ℝ => Real.log (R 1) / t) volume 1 ey := by
    have hinv : IntervalIntegrable (fun t : ℝ => 1 / t) volume 1 ey := by
      have hcont : ContinuousOn (fun t : ℝ => 1 / t) (uIcc (1 : ℝ) ey) := by
        rw [uIcc_of_le heyOne]
        exact continuousOn_const.div₀ continuousOn_id
          (fun t ht => (zero_lt_one.trans_le ht.1).ne')
      exact hcont.intervalIntegrable
    convert hinv.const_mul (Real.log (R 1)) using 1
    ext t
    ring
  have hIntegralLower :
      (∫ t : ℝ in 1..ey, Real.log (R 1) / t) ≤
        ∫ t : ℝ in 1..ey, Real.log (R t) / t := by
    apply intervalIntegral.integral_mono_on heyOne hConstInt hGapInt
    intro t ht
    exact div_le_div_of_nonneg_right (hlogMono t ht)
      (zero_lt_one.trans_le ht.1).le
  have hLeftInt : IntervalIntegrable
      (fun t : ℝ => Real.log (A t) / t) volume 1 ey := by
    have hcont : ContinuousOn (fun t : ℝ => Real.log (A t) / t)
        (uIcc (1 : ℝ) ey) := by
      rw [uIcc_of_le heyOne]
      exact (Real.continuousOn_log.comp hAcont
        (fun t ht => (hApos t ht).ne')).div₀ continuousOn_id
        (fun t ht => (zero_lt_one.trans_le ht.1).ne')
    exact hcont.intervalIntegrable
  have hRightInt : IntervalIntegrable
      (fun t : ℝ => Real.log (B t) / t) volume 1 ey := by
    have hcont : ContinuousOn (fun t : ℝ => Real.log (B t) / t)
        (uIcc (1 : ℝ) ey) := by
      rw [uIcc_of_le heyOne]
      exact (Real.continuousOn_log.comp hBcont
        (fun t ht => (hBpos t ht).ne')).div₀ continuousOn_id
        (fun t ht => (zero_lt_one.trans_le ht.1).ne')
    exact hcont.intervalIntegrable
  have hGapEq :
      (∫ t : ℝ in 1..ey, Real.log (R t) / t) =
        (∫ t : ℝ in 1..ey, Real.log (A t) / t) -
          ∫ t : ℝ in 1..ey, Real.log (B t) / t := by
    rw [← intervalIntegral.integral_sub hLeftInt hRightInt]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (1 : ℝ) ey := by
      simpa [uIcc_of_le heyOne] using ht
    change Real.log (R t) / t = Real.log (A t) / t - Real.log (B t) / t
    rw [show Real.log (R t) = Real.log (A t) - Real.log (B t) by
      dsimp only [R]
      exact Real.log_div (hApos t ht').ne' (hBpos t ht').ne']
    ring
  have hConstEval :
      (∫ t : ℝ in 1..ey, Real.log (R 1) / t) =
        Real.log ey * Real.log (R 1) := by
    rw [show (fun t : ℝ => Real.log (R 1) / t) =
        fun t : ℝ => Real.log (R 1) * (1 / t) by funext t; ring,
      intervalIntegral.integral_const_mul,
      integral_one_div_of_pos zero_lt_one heyPos]
    ring
  rw [hConstEval, hGapEq] at hIntegralLower
  dsimp only [R, A, B] at hIntegralLower
  simpa only [one_div] using hIntegralLower

lemma gsMoment_two_lower_explicit
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u : ℝ} (hu3 : 3 ≤ u)
    (he2 : 2 < gsScale chi u) (heUpper : gsScale chi u ≤ 13 / 5)
    (hcut : gsScale chi (u / gsScale chi u) ≤ gsScale chi u - 1) :
    let e := gsScale chi u
    let ey := gsScale chi (u / 3)
    let xi := gsLogScale chi (u / 3)
    gsGamma e + xi *
      (Real.log (2 * e / (3 * (e - 1))) +
        Real.log (e * (1 - 1 / (3 * ey)) / (e - 1))) ≤
      gsMoment chi 2 u := by
  dsimp only
  let e := gsScale chi u
  let y := u / 3
  let ey := gsScale chi y
  let xi := gsLogScale chi y
  let a := u / e
  let c₁ := y / ey
  let c₂ := u * ey / e
  let u₁ := u * (1 - 1 / e)
  let L := ∫ v : ℝ in c₁..y, Real.log (e * (u - v) / u) / v
  let R := ∫ v : ℝ in c₂..u₁, Real.log (e * (u - v) / u) / v
  let Q := ∫ v : ℝ in a..c₂, Real.log (e * (u - v) / u) / v
  have hu : 1 ≤ u := by linarith
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hy : 1 ≤ y := by dsimp only [y]; linarith
  have hePos : 0 < e := gsScale_pos chi u
  have heyPos : 0 < ey := gsScale_pos chi y
  have heyOne : 1 ≤ ey := gsScale_ge_one hchi hy
  have heu : e ≤ u := gsScale_le_self hchi hu
  have heThree : e ≤ 3 := by
    dsimp only [e] at heUpper ⊢
    norm_num at heUpper ⊢
    linarith
  have hyCutArg : y ≤ u / e := by
    dsimp only [y]
    apply (div_le_div_iff_of_pos_left hu0 (by norm_num) hePos).mpr
    exact heThree
  have huDivE : 1 ≤ u / e :=
    (le_div_iff₀ hePos).mpr (by simpa only [one_mul] using heu)
  have heyCut : ey ≤ e - 1 := by
    calc
      ey ≤ gsScale chi (u / e) := gsScale_mono hchi hy huDivE hyCutArg
      _ ≤ e - 1 := by simpa only [e] using hcut
  have hseg := gsMoment_two_lower_segments hchi hu3 he2 heUpper hcut
  change L + R + xi * Real.log (2 * e / (3 * (e - 1))) ≤
    gsMoment chi 2 u at hseg
  have hL : L = ∫ t : ℝ in 1..ey,
      Real.log (e * (1 - t / (3 * ey))) / t := by
    dsimp only [L, c₁, y]
    have h := scaled_first_correction (u := u) (e := e) (ey := ey)
      hu0 hePos heyPos
    convert h using 1
    field_simp [heyPos.ne']
  have hQ : Q = ∫ t : ℝ in 1..ey, Real.log (e - t) / t := by
    dsimp only [Q, a, c₂]
    exact scaled_partial_gamma hu0 hePos
  have hxi : Real.log ey = xi := by
    dsimp only [ey, xi, e, y, gsScale]
    rw [Real.log_exp]
  have hgap : xi * Real.log (e * (1 - 1 / (3 * ey)) / (e - 1)) ≤ L - Q := by
    have hg := section62_integral_gap
      (e := e) (ey := ey) (by simpa only [e] using he2)
      (by simpa only [e] using heUpper) heyOne heyCut
    rw [hxi, ← hL, ← hQ] at hg
    exact hg
  have haPos : 0 < a := by dsimp only [a]; exact div_pos hu0 hePos
  have hc₂Pos : 0 < c₂ := by dsimp only [c₂]; positivity
  have hc₂u₁ : c₂ ≤ u₁ := by
    dsimp only [c₂, u₁]
    rw [show u * (1 - 1 / e) = u * (e - 1) / e by
      field_simp [hePos.ne']]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left heyCut hu0.le) hePos.le
  have hu₁lt : u₁ < u := by
    have hgap' : u - u₁ = u / e := by
      dsimp only [u₁]
      field_simp [hePos.ne']
      ring
    have : 0 < u / e := div_pos hu0 hePos
    linarith
  have hlogFull := intervalIntegrable_log_complement_div hu0 hePos
    haPos (by
      dsimp only [a, u₁]
      have heNe : e ≠ 0 := hePos.ne'
      field_simp [heNe]
      nlinarith) hu₁lt
  have hlogQ : IntervalIntegrable
      (fun v : ℝ => Real.log (e * (u - v) / u) / v) volume a c₂ := by
    apply hlogFull.mono_set
    rw [Set.uIcc_of_le (by
      dsimp only [a, c₂]
      exact div_le_div_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_left heyOne hu0.le) hePos.le),
      Set.uIcc_of_le (by
        dsimp only [a, u₁]
        have heNe : e ≠ 0 := hePos.ne'
        field_simp [heNe]
        nlinarith)]
    exact Icc_subset_Icc le_rfl hc₂u₁
  have hlogR : IntervalIntegrable
      (fun v : ℝ => Real.log (e * (u - v) / u) / v) volume c₂ u₁ := by
    apply hlogFull.mono_set
    rw [Set.uIcc_of_le hc₂u₁, Set.uIcc_of_le (by
      dsimp only [a, u₁]
      have heNe : e ≠ 0 := hePos.ne'
      field_simp [heNe]
      nlinarith)]
    exact Icc_subset_Icc (by
      dsimp only [a, c₂]
      exact div_le_div_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_left heyOne hu0.le) hePos.le) le_rfl
  have hGammaSplit : gsGamma e = Q + R := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hlogQ hlogR
    have hfullEq := scaled_gamma_integral hu0 hePos
    dsimp only [Q, R, a, c₂, u₁]
    rw [← hfullEq]
    exact hsplit.symm
  rw [hGammaSplit]
  nlinarith

lemma log_one_add_quadratic_upper
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 3 / 5) :
    Real.log (1 + x) ≤ x - 3 / 10 * x ^ 2 := by
  let f : ℝ → ℝ := fun z => z - 3 / 10 * z ^ 2 - Real.log (1 + z)
  have hcont : ContinuousOn f (Icc (0 : ℝ) (3 / 5)) := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    dsimp only [f]
    fun_prop (disch := (norm_num at hz ⊢; linarith))
  have hdiff : DifferentiableOn ℝ f (interior (Icc (0 : ℝ) (3 / 5))) := by
    intro z hz
    have hz' : z ∈ Ioo (0 : ℝ) (3 / 5) := by
      simpa [interior_Icc] using hz
    dsimp only [f]
    have hne : 1 + z ≠ 0 := by norm_num at hz' ⊢; linarith
    fun_prop
  have hderiv : ∀ z ∈ interior (Icc (0 : ℝ) (3 / 5)),
      0 ≤ deriv f z := by
    intro z hz
    have hz' : z ∈ Ioo (0 : ℝ) (3 / 5) := by
      simpa [interior_Icc] using hz
    have hf : HasDerivAt f (1 - 3 / 5 * z - 1 / (1 + z)) z := by
      dsimp only [f]
      convert (((hasDerivAt_id z).sub
        (((hasDerivAt_const z (3 / 10 : ℝ)).mul
          ((hasDerivAt_id z).pow 2)))).sub
          (((hasDerivAt_id z).add_const 1).log
            (by norm_num at hz' ⊢; linarith))) using 1
      all_goals try rfl
      · ext w
        dsimp
        ring
      · simp only [Function.id_def]
        ring
    rw [hf.deriv]
    have hznonneg : 0 ≤ z := hz'.1.le
    have h2 : 0 ≤ 2 - 3 * z := by norm_num at hz' ⊢; linarith
    have hden : 0 < 1 + z := by linarith
    rw [show 1 - 3 / 5 * z - 1 / (1 + z) =
        z * (2 - 3 * z) / (5 * (1 + z)) by
      field_simp [hden.ne']
      ring]
    positivity
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) (3 / 5))
    hcont hdiff hderiv
  have h0 : f 0 = 0 := by simp [f]
  have hfx := hmono (by constructor <;> norm_num) ⟨hx0, hx⟩ hx0
  rw [h0] at hfx
  dsimp only [f] at hfx
  linarith

lemma gsGamma_le_seven_fiftieths
    {e : ℝ} (he2 : 2 ≤ e) (heUpper : e ≤ 13 / 5) :
    gsGamma e ≤ 7 / 50 := by
  let d : ℝ := e - 2
  let p : ℝ → ℝ := fun t =>
    (e - t - 1 - 3 / 10 * (e - t - 1) ^ 2) * (13 / 8 - 5 * t / 8)
  have hd0 : 0 ≤ d := by dsimp only [d]; linarith
  have hd : d ≤ 3 / 5 := by dsimp only [d]; norm_num at heUpper ⊢; linarith
  have hinterval : 1 ≤ e - 1 := by linarith
  have hpoint : ∀ t ∈ Icc (1 : ℝ) (e - 1),
      Real.log (e - t) / t ≤ p t := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht.1
    have htUpper : t ≤ 8 / 5 := by
      norm_num at heUpper ⊢
      linarith [ht.2]
    let y : ℝ := e - t - 1
    have hy0 : 0 ≤ y := by dsimp only [y]; linarith [ht.2]
    have hy : y ≤ 3 / 5 := by
      dsimp only [y]
      norm_num at heUpper ⊢
      linarith [ht.1]
    have hlog := log_one_add_quadratic_upper hy0 hy
    have harg : e - t = 1 + y := by dsimp only [y]; ring
    rw [← harg] at hlog
    have hlog0 : 0 ≤ Real.log (e - t) := by
      exact Real.log_nonneg (by linarith)
    have hpoly0 : 0 ≤ y - 3 / 10 * y ^ 2 := by
      have : 0 ≤ 1 - 3 / 10 * y := by nlinarith
      nlinarith [mul_nonneg hy0 this]
    have hinv : 1 / t ≤ 13 / 8 - 5 * t / 8 := by
      rw [div_le_iff₀ ht0]
      have hfac : 0 ≤ (t - 1) * (8 - 5 * t) :=
        mul_nonneg (sub_nonneg.mpr ht.1) (by nlinarith)
      nlinarith
    calc
      Real.log (e - t) / t ≤ (y - 3 / 10 * y ^ 2) / t :=
        div_le_div_of_nonneg_right hlog ht0.le
      _ = (y - 3 / 10 * y ^ 2) * (1 / t) := by ring
      _ ≤ (y - 3 / 10 * y ^ 2) * (13 / 8 - 5 * t / 8) :=
        mul_le_mul_of_nonneg_left hinv hpoly0
      _ = p t := by dsimp only [p, y]
  have hlogInt : IntervalIntegrable
      (fun t : ℝ => Real.log (e - t) / t) volume 1 (e - 1) := by
    have hcont : ContinuousOn (fun t : ℝ => Real.log (e - t) / t)
        (Icc (1 : ℝ) (e - 1)) := by
      apply ContinuousOn.div₀
      · exact Real.continuousOn_log.comp
          (continuousOn_const.sub continuousOn_id) (by
            intro t ht
            exact (by linarith [ht.2] : e - t ≠ 0))
      · exact continuousOn_id
      · intro t ht
        exact (zero_lt_one.trans_le ht.1).ne'
    exact hcont.intervalIntegrable_of_Icc hinterval
  have hpInt : IntervalIntegrable p volume 1 (e - 1) := by
    have hcont : Continuous p := by
      dsimp only [p]
      fun_prop
    exact hcont.continuousOn.intervalIntegrable
  have hintLe : gsGamma e ≤ ∫ t : ℝ in 1..(e - 1), p t := by
    unfold gsGamma
    exact intervalIntegral.integral_mono_on hinterval hlogInt hpInt hpoint
  let A : ℝ := d - 3 / 10 * d ^ 2
  let B : ℝ := -1 + 3 / 5 * d - 5 / 8 * A
  let C : ℝ := 13 / 40 - 3 / 8 * d
  let F : ℝ → ℝ := fun t =>
    A * (t - 1) + (B / 2) * (t - 1) ^ 2 +
      (C / 3) * (t - 1) ^ 3 + (3 / 64) * (t - 1) ^ 4
  have hFcont : ContinuousOn F (Icc (1 : ℝ) (e - 1)) := by
    dsimp only [F]
    fun_prop
  have hFderiv : ∀ t ∈ Ioo (1 : ℝ) (e - 1), HasDerivAt F (p t) t := by
    intro t ht
    have hx : HasDerivAt (fun z : ℝ => z - 1) 1 t :=
      (hasDerivAt_id t).sub_const 1
    have h1 : HasDerivAt (fun z : ℝ => A * (z - 1)) A t := by
      simpa only [mul_one] using hx.const_mul A
    have h2 : HasDerivAt (fun z : ℝ => (B / 2) * (z - 1) ^ 2)
        (B * (t - 1)) t := by
      convert (hx.pow 2).const_mul (B / 2) using 1
      all_goals first | rfl | ring
    have h3 : HasDerivAt (fun z : ℝ => (C / 3) * (z - 1) ^ 3)
        (C * (t - 1) ^ 2) t := by
      convert (hx.pow 3).const_mul (C / 3) using 1
      all_goals first | rfl | ring
    have h4 : HasDerivAt (fun z : ℝ => (3 / 64) * (z - 1) ^ 4)
        (3 / 16 * (t - 1) ^ 3) t := by
      convert (hx.pow 4).const_mul (3 / 64 : ℝ) using 1
      all_goals first | rfl | ring
    have hraw : HasDerivAt F
        (A + B * (t - 1) + C * (t - 1) ^ 2 + 3 / 16 * (t - 1) ^ 3) t := by
      dsimp only [F]
      exact ((h1.add h2).add h3).add h4
    convert hraw using 1
    dsimp only [p, A, B, C, d]
    ring
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hinterval hFcont hFderiv hpInt
  have hpEval : (∫ t : ℝ in 1..(e - 1), p t) =
      d ^ 2 * (15 * d ^ 2 - 196 * d + 480) / 960 := by
    rw [hfund]
    dsimp only [F, A, B, C]
    have heq : e - 1 - 1 = d := by dsimp only [d]; ring
    rw [heq]
    ring
  rw [hpEval] at hintLe
  have hdprod : 0 ≤ d * (3 / 5 - d) :=
    mul_nonneg hd0 (sub_nonneg.mpr hd)
  have hd2 : d ^ 2 ≤ 9 / 25 := by nlinarith [hdprod]
  have hR : 0 ≤ 375 * d ^ 3 - 4675 * d ^ 2 + 9195 * d + 5517 := by
    have hd3 : 0 ≤ d ^ 3 := by positivity
    nlinarith
  have hfac : 0 ≤ (3 - 5 * d) *
      (375 * d ^ 3 - 4675 * d ^ 2 + 9195 * d + 5517) :=
    mul_nonneg (by nlinarith) hR
  have hpoly : d ^ 2 * (15 * d ^ 2 - 196 * d + 480) / 960 ≤
      5517 / 40000 := by
    nlinarith
  norm_num at hintLe hpoly ⊢
  linarith

lemma section62_scalar
    {e ey : ℝ} (he2 : 2 < e) (heUpper : e ≤ 13 / 5)
    (heyOne : 1 ≤ ey) (heyUpper : ey ≤ e - 1) :
    gsGamma e ≤ (1 - Real.log ey) *
      (Real.log (2 * e / (3 * (e - 1))) +
        Real.log (e * (1 - 1 / (3 * ey)) / (e - 1))) := by
  have hePos : 0 < e := by linarith
  have heSub : 0 < e - 1 := by linarith
  have heyPos : 0 < ey := zero_lt_one.trans_le heyOne
  have heyEight : ey ≤ 8 / 5 := by
    norm_num at heUpper ⊢
    linarith
  let xi : ℝ := Real.log ey
  let a : ℝ := 2 * e / (3 * (e - 1))
  let b : ℝ := e * (1 - 1 / (3 * ey)) / (e - 1)
  let x : ℝ := (ey - 1) / (2 * ey)
  have hxi0 : 0 ≤ xi := by
    dsimp only [xi]
    exact Real.log_nonneg heyOne
  have hxiHalf : xi ≤ 1 / 2 := by
    have hlogmono := Real.log_le_log heyPos heyEight
    have hnum := log_eight_fifths_bounds.2
    dsimp only [xi]
    norm_num at hnum ⊢
    linarith
  have haPos : 0 < a := by
    dsimp only [a]
    positivity
  have hbFactor : 0 < 1 - 1 / (3 * ey) := by
    have : 1 / (3 * ey) ≤ 1 / 3 := by
      apply (div_le_div_iff_of_pos_left zero_lt_one (by positivity) (by positivity)).mpr
      nlinarith
    nlinarith
  have hbPos : 0 < b := by
    dsimp only [b]
    positivity
  have haThirteen : 13 / 12 ≤ a := by
    dsimp only [a]
    rw [le_div_iff₀ (by positivity : 0 < 3 * (e - 1))]
    norm_num at heUpper ⊢
    nlinarith
  have hlogThirteen : (2 / 25 : ℝ) ≤ Real.log (13 / 12) := by
    have h := logAtanhPartial_le_log_of_eq
      (q := (13 / 12 : ℝ)) (x := (1 / 25 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) 1
    norm_num [logAtanhPartial] at h ⊢
    exact h
  have haLog : (2 / 25 : ℝ) ≤ Real.log a := by
    exact hlogThirteen.trans
      (Real.strictMonoOn_log.monotoneOn (by norm_num) haPos haThirteen)
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hxiSub : xi ≤ ey - 1 := by
    dsimp only [xi]
    exact Real.log_le_sub_one_of_pos heyPos
  have hrat : (ey - 1) / 4 ≤ 2 * x / (x + 2) := by
    have hxform : 2 * x / (x + 2) = 2 * (ey - 1) / (5 * ey - 1) := by
      dsimp only [x]
      field_simp [heyPos.ne']
      ring
    rw [hxform, le_div_iff₀ (by nlinarith : 0 < 5 * ey - 1)]
    have hnonneg : 0 ≤ ey - 1 := sub_nonneg.mpr heyOne
    have hfactor : 0 ≤ (ey - 1) * (9 - 5 * ey) :=
      mul_nonneg hnonneg (by nlinarith [heyEight])
    nlinarith
  have hxLog : xi / 4 ≤ Real.log (1 + x) := by
    calc
      xi / 4 ≤ (ey - 1) / 4 := div_le_div_of_nonneg_right hxiSub (by norm_num)
      _ ≤ 2 * x / (x + 2) := hrat
      _ ≤ Real.log (1 + x) := Real.le_log_one_add_of_nonneg hx0
  have harg : b = a * (1 + x) := by
    dsimp only [a, b, x]
    field_simp [heSub.ne', heyPos.ne']
    ring
  have hxPos : 0 < 1 + x := by positivity
  have hbLog : Real.log b = Real.log a + Real.log (1 + x) := by
    rw [harg, Real.log_mul haPos.ne' hxPos.ne']
  have hsum : 4 / 25 + xi / 4 ≤ Real.log a + Real.log b := by
    rw [hbLog]
    nlinarith [haLog, hxLog]
  have hfactor : 0 ≤ 1 - xi := by nlinarith
  have hprod : 7 / 50 ≤ (1 - xi) * (4 / 25 + xi / 4) := by
    have hmiddle : 0 ≤ xi * (1 / 2 - xi) :=
      mul_nonneg hxi0 (sub_nonneg.mpr hxiHalf)
    have hlast : 0 ≤ 1 - 2 * xi := by nlinarith
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num) hmiddle,
      mul_nonneg (show (0 : ℝ) ≤ 7 / 400 by norm_num) hlast]
  have hscaled : (1 - xi) * (4 / 25 + xi / 4) ≤
      (1 - xi) * (Real.log a + Real.log b) :=
    mul_le_mul_of_nonneg_left hsum hfactor
  have hgamma := gsGamma_le_seven_fiftieths he2.le heUpper
  dsimp only [xi, a, b] at hgamma hprod hscaled ⊢
  linarith


def gsMiddleIntegral (e : ℝ) : ℝ :=
  ∫ t : ℝ in 1..e / 2, Real.log ((e - t) / t) / t

lemma gsGamma_split_reflect {e : ℝ} (he2 : 2 ≤ e) :
    gsGamma e =
      (∫ t : ℝ in 1..e / 2, Real.log (e - t) / t) +
      ∫ t : ℝ in 1..e / 2, Real.log t / (e - t) := by
  have hePos : 0 < e := by linarith
  have hm : 1 ≤ e / 2 := by linarith
  have hmUpper : e / 2 ≤ e - 1 := by linarith
  have hfull : IntervalIntegrable
      (fun t : ℝ => Real.log (e - t) / t) volume 1 (e - 1) := by
    convert intervalIntegrable_log_complement_div
      (u := e) (e := e) (a := (1 : ℝ)) (b := e - 1)
        hePos hePos zero_lt_one (by linarith) (by linarith) using 1
    ext t
    have hmul : e * (e - t) / e = e - t := by field_simp [hePos.ne']
    rw [hmul]
  have hleft : IntervalIntegrable
      (fun t : ℝ => Real.log (e - t) / t) volume 1 (e / 2) := by
    apply hfull.mono_set
    rw [uIcc_of_le hm, uIcc_of_le (by linarith : 1 ≤ e - 1)]
    exact Icc_subset_Icc le_rfl hmUpper
  have hright : IntervalIntegrable
      (fun t : ℝ => Real.log (e - t) / t) volume (e / 2) (e - 1) := by
    apply hfull.mono_set
    rw [uIcc_of_le hmUpper, uIcc_of_le (by linarith : 1 ≤ e - 1)]
    exact Icc_subset_Icc hm le_rfl
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hreflect :
      (∫ t : ℝ in e / 2..e - 1, Real.log (e - t) / t) =
        ∫ t : ℝ in 1..e / 2, Real.log t / (e - t) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun s : ℝ => Real.log s / (e - s)) e
      (a := e / 2) (b := e - 1)
    have hehalf : e - e / 2 = e / 2 := by ring
    rw [hehalf] at h
    simpa only [sub_sub_cancel_left, sub_sub_cancel] using h
  unfold gsGamma
  rw [← hsplit, hreflect]

lemma gamma_left_integration_by_parts {e : ℝ} (he2 : 2 ≤ e) :
    (∫ t : ℝ in 1..e / 2, Real.log (e - t) / t) =
      Real.log (e / 2) ^ 2 +
        ∫ t : ℝ in 1..e / 2, Real.log t / (e - t) := by
  have hePos : 0 < e := by linarith
  have hm : 1 ≤ e / 2 := by linarith
  let u : ℝ → ℝ := fun t => Real.log (e - t)
  let v : ℝ → ℝ := fun t => Real.log t
  let u' : ℝ → ℝ := fun t => -1 / (e - t)
  let v' : ℝ → ℝ := fun t => 1 / t
  have hu : ContinuousOn u (uIcc (1 : ℝ) (e / 2)) := by
    rw [uIcc_of_le hm]
    intro t ht
    dsimp only [u]
    apply ContinuousAt.continuousWithinAt
    exact (Real.continuousAt_log (by linarith [ht.2] : e - t ≠ 0)).comp_of_eq
      (continuousAt_const.sub continuousAt_id) rfl
  have hv : ContinuousOn v (uIcc (1 : ℝ) (e / 2)) := by
    rw [uIcc_of_le hm]
    intro t ht
    dsimp only [v]
    exact (Real.continuousAt_log (zero_lt_one.trans_le ht.1).ne').continuousWithinAt
  have huder : ∀ t ∈ Ioo (min (1 : ℝ) (e / 2)) (max 1 (e / 2)),
      HasDerivAt u (u' t) t := by
    intro t ht
    simp only [min_eq_left hm, max_eq_right hm] at ht
    have hne : e - t ≠ 0 := by linarith [ht.2]
    dsimp only [u, u']
    convert (((hasDerivAt_const t e).sub (hasDerivAt_id t)).log hne) using 1 <;>
      try rfl
    change -1 / (e - t) = (0 - 1) * (e - t)⁻¹
    ring
  have hvder : ∀ t ∈ Ioo (min (1 : ℝ) (e / 2)) (max 1 (e / 2)),
      HasDerivAt v (v' t) t := by
    intro t ht
    simp only [min_eq_left hm, max_eq_right hm] at ht
    dsimp only [v, v']
    simpa only [one_div] using Real.hasDerivAt_log (by linarith [ht.1] : t ≠ 0)
  have hu' : IntervalIntegrable u' volume 1 (e / 2) := by
    have hc : ContinuousOn u' (Icc (1 : ℝ) (e / 2)) := by
      intro t ht
      dsimp only [u']
      have hne : e - t ≠ 0 := by linarith [ht.2]
      exact (continuousAt_const.div₀
        (continuousAt_const.sub continuousAt_id) hne).continuousWithinAt
    exact hc.intervalIntegrable_of_Icc hm
  have hv' : IntervalIntegrable v' volume 1 (e / 2) := by
    have hc : ContinuousOn v' (Icc (1 : ℝ) (e / 2)) := by
      intro t ht
      dsimp only [v']
      exact (continuousAt_const.div₀ continuousAt_id
        (zero_lt_one.trans_le ht.1).ne').continuousWithinAt
    exact hc.intervalIntegrable_of_Icc hm
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu hv huder hvder hu' hv'
  have hleft : (∫ t : ℝ in 1..e / 2, u t * v' t) =
      ∫ t : ℝ in 1..e / 2, Real.log (e - t) / t := by
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only [u, v']
    ring
  have hright : (∫ t : ℝ in 1..e / 2, u' t * v t) =
      -(∫ t : ℝ in 1..e / 2, Real.log t / (e - t)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only [u', v]
    ring
  rw [hleft, hright] at hip
  dsimp only [u, v] at hip
  have hmarg : e - e / 2 = e / 2 := by ring
  rw [hmarg, Real.log_one] at hip
  norm_num at hip
  linarith

lemma integral_log_div {x : ℝ} (hx : 1 ≤ x) :
    (∫ t : ℝ in 1..x, Real.log t / t) = Real.log x ^ 2 / 2 := by
  let F : ℝ → ℝ := fun t => Real.log t ^ 2 / 2
  let f : ℝ → ℝ := fun t => Real.log t / t
  have hFcont : ContinuousOn F (Icc (1 : ℝ) x) := by
    intro t ht
    dsimp only [F]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := exact (zero_lt_one.trans_le ht.1).ne')
  have hFder : ∀ t ∈ Ioo (1 : ℝ) x, HasDerivAt F (f t) t := by
    intro t ht
    dsimp only [F, f]
    have hlog := Real.hasDerivAt_log (by linarith [ht.1] : t ≠ 0)
    convert (hlog.pow 2).div_const 2 using 1 <;>
      norm_num [Function.id_def]
    all_goals first | rfl | ring
  have hf : IntervalIntegrable f volume 1 x := by
    have hc : ContinuousOn f (Icc (1 : ℝ) x) := by
      intro t ht
      dsimp only [f]
      fun_prop (disch := exact (zero_lt_one.trans_le ht.1).ne')
    exact hc.intervalIntegrable_of_Icc hx
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hx hFcont hFder hf
  dsimp only [F, f] at h ⊢
  rw [Real.log_one] at h
  norm_num at h
  exact h

lemma gsGamma_eq_two_middle {e : ℝ} (he2 : 2 ≤ e) :
    gsGamma e = 2 * gsMiddleIntegral e := by
  have hsplit := gsGamma_split_reflect he2
  have hibp := gamma_left_integration_by_parts he2
  have hlog := integral_log_div (show 1 ≤ e / 2 by linarith)
  have hcombine : gsMiddleIntegral e =
      (∫ t : ℝ in 1..e / 2, Real.log (e - t) / t) -
        ∫ t : ℝ in 1..e / 2, Real.log t / t := by
    unfold gsMiddleIntegral
    rw [← intervalIntegral.integral_sub]
    · apply intervalIntegral.integral_congr
      intro t ht
      change Real.log ((e - t) / t) / t =
        Real.log (e - t) / t - Real.log t / t
      rw [Real.log_div (by
        rw [uIcc_of_le (show 1 ≤ e / 2 by linarith)] at ht
        exact (by linarith [ht.2] : e - t ≠ 0))
        (by
          rw [uIcc_of_le (show 1 ≤ e / 2 by linarith)] at ht
          exact (zero_lt_one.trans_le ht.1).ne')]
      ring
    · have hc : ContinuousOn (fun t : ℝ => Real.log (e - t) / t)
          (Icc (1 : ℝ) (e / 2)) := by
        intro t ht
        apply ContinuousAt.continuousWithinAt
        fun_prop (disch :=
          first | exact (by linarith [ht.2] : e - t ≠ 0)
                | exact (zero_lt_one.trans_le ht.1).ne')
      exact hc.intervalIntegrable_of_Icc (by linarith)
    · have hc : ContinuousOn (fun t : ℝ => Real.log t / t)
          (Icc (1 : ℝ) (e / 2)) := by
        intro t ht
        apply ContinuousAt.continuousWithinAt
        fun_prop (disch := exact (zero_lt_one.trans_le ht.1).ne')
      exact hc.intervalIntegrable_of_Icc (by linarith)
  rw [hcombine, hibp, hlog]
  linarith

lemma gsMiddleIntegral_eq_shifted {e : ℝ} (he2 : 2 ≤ e) :
    gsMiddleIntegral e =
      ∫ r : ℝ in 2..e, Real.log (r - 1) / r := by
  have hePos : 0 < e := by linarith
  have hm : 1 ≤ e / 2 := by linarith
  let phi : ℝ → ℝ := fun t => e / t
  let phi' : ℝ → ℝ := fun t => -e / t ^ 2
  let g : ℝ → ℝ := fun r => Real.log (r - 1) / r
  have hphi : ∀ t ∈ uIcc (1 : ℝ) (e / 2),
      HasDerivAt phi (phi' t) t := by
    intro t ht
    rw [uIcc_of_le hm] at ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht.1).ne'
    have h := (hasDerivAt_inv ht0).const_mul e
    change HasDerivAt phi (e * -(t ^ 2)⁻¹) t at h
    convert h using 1
    dsimp only [phi', div_eq_mul_inv]
    ring
  have hphi' : ContinuousOn phi' (uIcc (1 : ℝ) (e / 2)) := by
    rw [uIcc_of_le hm]
    intro t ht
    dsimp only [phi']
    apply ContinuousAt.continuousWithinAt
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht.1).ne'
    fun_prop (disch := exact pow_ne_zero 2 ht0)
  have hgIci : ContinuousOn g (Ici (2 : ℝ)) := by
    intro r hr
    change 2 ≤ r at hr
    dsimp only [g]
    apply ContinuousAt.continuousWithinAt
    have hr0 : r ≠ 0 := by linarith
    have hr1 : r - 1 ≠ 0 := by linarith
    fun_prop
  have himage : phi '' uIcc (1 : ℝ) (e / 2) ⊆ Ici (2 : ℝ) := by
    rintro r ⟨t, ht, rfl⟩
    rw [uIcc_of_le hm] at ht
    dsimp only [phi]
    apply (le_div_iff₀ (zero_lt_one.trans_le ht.1)).2
    linarith [ht.2]
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    hphi hphi' (hgIci.mono himage)
  change
    (∫ t : ℝ in 1..e / 2, (g ∘ phi) t * phi' t) =
      ∫ r : ℝ in phi 1..phi (e / 2), g r at hsubst
  have hleft : (fun t : ℝ => (g ∘ phi) t * phi' t) =
      fun t : ℝ => -(Real.log ((e - t) / t) / t) := by
    funext t
    by_cases ht : t = 0
    · subst t
      simp [g, phi, phi']
    · dsimp only [g, phi, phi', Function.comp_apply]
      have heq : e / t - 1 = (e - t) / t := by field_simp [ht]
      rw [heq]
      field_simp [ht]
  have hphiOne : phi 1 = e := by simp [phi]
  have hphiMid : phi (e / 2) = 2 := by
    simp [phi, hePos.ne']
  rw [hleft, intervalIntegral.integral_neg, hphiOne, hphiMid] at hsubst
  have hsymm : (∫ r : ℝ in e..2, g r) = -(∫ r : ℝ in 2..e, g r) := by
    exact intervalIntegral.integral_symm 2 e
  rw [hsymm] at hsubst
  unfold gsMiddleIntegral
  linarith

lemma gsGamma_eq_shifted {e : ℝ} (he2 : 2 ≤ e) :
    gsGamma e = 2 * (∫ r : ℝ in 2..e, Real.log (r - 1) / r) := by
  rw [gsGamma_eq_two_middle he2, gsMiddleIntegral_eq_shifted he2]

lemma dickmanRho_eq_one_sub_log_add_shifted
    {e : ℝ} (he2 : 2 ≤ e) (he3 : e ≤ 3) :
    dickmanRho e = 1 - Real.log e +
      ∫ r : ℝ in 2..e, Real.log (r - 1) / r := by
  have he1 : 1 ≤ e := by linarith
  have hePos : 0 < e := by linarith
  have hkernel : IntervalIntegrable
      (fun t : ℝ => dickmanRho (t - 1) / t) volume 1 e := by
    have hc : ContinuousOn (fun t : ℝ => dickmanRho (t - 1) / t)
        (Icc (1 : ℝ) e) := by
      apply ContinuousOn.div
      · exact continuousOn_dickmanRho_Ici_zero.comp
          (continuousOn_id.sub continuousOn_const) (by
            intro t ht
            exact mem_Ici.mpr (sub_nonneg.mpr ht.1))
      · exact continuousOn_id
      · intro t ht
        exact (zero_lt_one.trans_le ht.1).ne'
    exact hc.intervalIntegrable_of_Icc he1
  have hleft : IntervalIntegrable
      (fun t : ℝ => dickmanRho (t - 1) / t) volume 1 2 := by
    apply hkernel.mono_set
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2), uIcc_of_le he1]
    exact Icc_subset_Icc le_rfl he2
  have hright : IntervalIntegrable
      (fun t : ℝ => dickmanRho (t - 1) / t) volume 2 e := by
    apply hkernel.mono_set
    rw [uIcc_of_le he2, uIcc_of_le he1]
    exact Icc_subset_Icc (by norm_num) le_rfl
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hleftEval :
      (∫ t : ℝ in 1..2, dickmanRho (t - 1) / t) = Real.log 2 := by
    calc
      _ = ∫ t : ℝ in 1..2, 1 / t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
        change dickmanRho (t - 1) / t = 1 / t
        rw [dickmanRho_profile.2.1 (t - 1) (by linarith [ht.1]) (by linarith [ht.2])]
      _ = Real.log 2 := by
        rw [integral_one_div_of_pos zero_lt_one (by norm_num)]
        norm_num
  have hinv : IntervalIntegrable (fun t : ℝ => 1 / t) volume 2 e := by
    have hc : ContinuousOn (fun t : ℝ => 1 / t) (Icc (2 : ℝ) e) := by
      intro t ht
      exact (continuousAt_const.div₀ continuousAt_id (by linarith [ht.1] : t ≠ 0)).continuousWithinAt
    exact hc.intervalIntegrable_of_Icc he2
  have hlog : IntervalIntegrable (fun t : ℝ => Real.log (t - 1) / t)
      volume 2 e := by
    have hc : ContinuousOn (fun t : ℝ => Real.log (t - 1) / t)
        (Icc (2 : ℝ) e) := by
      intro t ht
      apply ContinuousAt.continuousWithinAt
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have ht1 : t - 1 ≠ 0 := by linarith [ht.1]
      fun_prop
    exact hc.intervalIntegrable_of_Icc he2
  have hrightEval :
      (∫ t : ℝ in 2..e, dickmanRho (t - 1) / t) =
        Real.log (e / 2) - ∫ t : ℝ in 2..e, Real.log (t - 1) / t := by
    calc
      _ = ∫ t : ℝ in 2..e, (1 / t - Real.log (t - 1) / t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le he2] at ht
        change dickmanRho (t - 1) / t = 1 / t - Real.log (t - 1) / t
        rw [dickmanRho_eq_one_sub_log (by linarith [ht.1]) (by linarith [ht.2, he3])]
        ring
      _ = (∫ t : ℝ in 2..e, 1 / t) -
          ∫ t : ℝ in 2..e, Real.log (t - 1) / t := by
        rw [intervalIntegral.integral_sub hinv hlog]
      _ = _ := by rw [integral_one_div_of_pos (by norm_num) hePos]
  have hrho := dickmanRho_eq_one_sub_integral e he1
  rw [← hsplit, hleftEval, hrightEval] at hrho
  have hlogSplit : Real.log 2 + Real.log (e / 2) = Real.log e := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (div_ne_zero hePos.ne' (by norm_num))]
    congr 1
    field_simp
  linarith [hrho, hlogSplit]

lemma dickmanRho_eq_gamma
    {e : ℝ} (he2 : 2 ≤ e) (he3 : e ≤ 3) :
    dickmanRho e = 1 - Real.log e + gsGamma e / 2 := by
  rw [dickmanRho_eq_one_sub_log_add_shifted he2 he3,
    gsGamma_eq_shifted he2]
  ring


end
end Erdos783
