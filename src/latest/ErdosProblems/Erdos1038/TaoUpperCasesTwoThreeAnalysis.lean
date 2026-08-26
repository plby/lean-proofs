import ErdosProblems.Erdos1038.TaoUpperIntervalTrials

/-!
# Analytic control for Tao's second and third trial measures

This file records the exact first derivatives of the scalar potentials in
equations (2.5) and (2.6), their continuity on the relevant ranges, and an
analytic tail estimate that reduces Case 2 to a compact interval.
-/

open Set

namespace Erdos1038

noncomputable section

def taoCaseTwoPotentialDerivative (t : ℝ) : ℝ :=
  -1 / t + taoCaseTwoA *
    (Real.log |taoUpperEdge - t| -
      Real.log |taoCaseTwoLeftEndpoint - t|)

def taoCaseThreePotentialDerivative (t : ℝ) : ℝ :=
  -1 / t + taoCaseThreeA *
      (Real.log |taoUpperEdge - t| -
        Real.log |taoCaseThreeLeftA - t|) +
    taoCaseThreeB *
      (Real.log |taoUpperEdge - t| -
        Real.log |taoCaseThreeLeftB - t|) +
    taoCaseThreeC / (taoUpperEdge - t)

def taoCaseTwoPotentialSecondDerivative (t : ℝ) : ℝ :=
  1 / t ^ 2 + taoCaseTwoA *
    (-1 / (taoUpperEdge - t) +
      1 / (taoCaseTwoLeftEndpoint - t))

theorem hasDerivAt_taoLogPrimitive_const_sub
    {c t : ℝ} (hct : c - t ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ taoLogPrimitive (c - x))
      (Real.log |c - t|) t := by
  have hinner : HasDerivAt (fun x : ℝ ↦ c - x) (-1) t := by
    convert! (hasDerivAt_const t c).sub (hasDerivAt_id t) using 1
    ring
  have hcomp := (hasDerivAt_taoLogPrimitive hct).comp t hinner
  convert! hcomp using 1
  ring

theorem hasDerivAt_log_abs_const_sub
    {c t : ℝ} (hct : c - t ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ Real.log |c - x|)
      (-1 / (c - t)) t := by
  have hinner : HasDerivAt (fun x : ℝ ↦ c - x) (-1) t := by
    convert! (hasDerivAt_const t c).sub (hasDerivAt_id t) using 1
    ring
  have hcomp := (Real.hasDerivAt_log hct).comp t hinner
  rw [show (fun x : ℝ ↦ Real.log |c - x|) =
      fun x : ℝ ↦ Real.log (c - x) by
    funext x
    exact Real.log_abs (c - x)]
  convert! hcomp using 1
  ring

theorem hasDerivAt_taoCaseTwoPotential {t : ℝ}
    (ht : t ≠ 0)
    (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseTwoLeftEndpoint - t ≠ 0) :
    HasDerivAt taoCaseTwoPotential
      (taoCaseTwoPotentialDerivative t) t := by
  have hzero : HasDerivAt (fun x : ℝ ↦ -Real.log x) (-1 / t) t := by
    convert! (Real.hasDerivAt_log ht).neg using 1
    ring
  have hinterval :=
    (hasDerivAt_taoLogPrimitive_const_sub hM).sub
      (hasDerivAt_taoLogPrimitive_const_sub ha)
  have hscaled := hinterval.const_mul taoCaseTwoA
  convert! hzero.add hscaled using 1

theorem hasDerivAt_taoCaseTwoPotentialDerivative {t : ℝ}
    (ht : t ≠ 0)
    (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseTwoLeftEndpoint - t ≠ 0) :
    HasDerivAt taoCaseTwoPotentialDerivative
      (taoCaseTwoPotentialSecondDerivative t) t := by
  have hrecip : HasDerivAt (fun x : ℝ ↦ -1 / x) (1 / t ^ 2) t := by
    convert! (hasDerivAt_const t (-1 : ℝ)).div (hasDerivAt_id t) ht using 1
    simp only [id_eq]
    field_simp [ht]
    ring
  have hlogs := (hasDerivAt_log_abs_const_sub hM).sub
    (hasDerivAt_log_abs_const_sub ha)
  have hscaled := hlogs.const_mul taoCaseTwoA
  convert! hrecip.add hscaled using 1
  unfold taoCaseTwoPotentialSecondDerivative
  ring

theorem hasDerivAt_deriv_taoCaseTwoPotential {t : ℝ}
    (ht : t ≠ 0)
    (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseTwoLeftEndpoint - t ≠ 0) :
    HasDerivAt (deriv taoCaseTwoPotential)
      (taoCaseTwoPotentialSecondDerivative t) t := by
  have htM : t ≠ taoUpperEdge := (sub_ne_zero.mp hM).symm
  have hta : t ≠ taoCaseTwoLeftEndpoint := (sub_ne_zero.mp ha).symm
  have heq : Filter.EventuallyEq (nhds t)
      (deriv taoCaseTwoPotential) taoCaseTwoPotentialDerivative := by
    filter_upwards [eventually_ne_nhds ht, eventually_ne_nhds htM,
      eventually_ne_nhds hta] with y hy0 hyM hya
    exact (hasDerivAt_taoCaseTwoPotential hy0
      (sub_ne_zero.mpr hyM.symm) (sub_ne_zero.mpr hya.symm)).deriv
  exact (hasDerivAt_taoCaseTwoPotentialDerivative ht hM ha).congr_of_eventuallyEq
    heq

theorem deriv2_taoCaseTwoPotential {t : ℝ}
    (ht : t ≠ 0)
    (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseTwoLeftEndpoint - t ≠ 0) :
    deriv^[2] taoCaseTwoPotential t =
      taoCaseTwoPotentialSecondDerivative t := by
  rw [show deriv^[2] taoCaseTwoPotential t =
      deriv (deriv taoCaseTwoPotential) t by rfl]
  exact (hasDerivAt_deriv_taoCaseTwoPotential ht hM ha).deriv

theorem hasDerivAt_taoCaseThreePotential {t : ℝ}
    (ht : t ≠ 0)
    (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseThreeLeftA - t ≠ 0)
    (hb : taoCaseThreeLeftB - t ≠ 0) :
    HasDerivAt taoCaseThreePotential
      (taoCaseThreePotentialDerivative t) t := by
  have hzero : HasDerivAt (fun x : ℝ ↦ -Real.log x) (-1 / t) t := by
    convert! (Real.hasDerivAt_log ht).neg using 1
    ring
  have hA := ((hasDerivAt_taoLogPrimitive_const_sub hM).sub
    (hasDerivAt_taoLogPrimitive_const_sub ha)).const_mul taoCaseThreeA
  have hB := ((hasDerivAt_taoLogPrimitive_const_sub hM).sub
    (hasDerivAt_taoLogPrimitive_const_sub hb)).const_mul taoCaseThreeB
  have hC := (hasDerivAt_log_abs_const_sub hM).const_mul (-taoCaseThreeC)
  convert! ((hzero.add hA).add hB).add hC using 1
  · funext x
    unfold taoCaseThreePotential
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · unfold taoCaseThreePotentialDerivative
    ring

theorem continuousOn_taoCaseTwoPotential_Ioi :
    ContinuousOn taoCaseTwoPotential (Ioi (0 : ℝ)) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have ht0 : t ≠ 0 := ht.ne'
  have hzero : ContinuousAt (fun x : ℝ ↦ -Real.log x) t :=
    (Real.continuousAt_log ht0).neg
  have hM : ContinuousAt
      (fun x : ℝ ↦ taoLogPrimitive (taoUpperEdge - x)) t :=
    continuous_taoLogPrimitive.continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  have ha : ContinuousAt
      (fun x : ℝ ↦ taoLogPrimitive (taoCaseTwoLeftEndpoint - x)) t :=
    continuous_taoLogPrimitive.continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  exact hzero.add ((hM.sub ha).const_mul taoCaseTwoA)

theorem tao_case_three_inputCeiling_lt_upperEdge :
    taoCaseThreeInputCeiling < taoUpperEdge := by
  unfold taoCaseThreeInputCeiling taoUpperEdge
  nlinarith [seven_fifths_lt_sqrt_two]

theorem continuousOn_taoCaseThreePotential_input :
    ContinuousOn taoCaseThreePotential
      (Icc taoCaseThreeInputFloor taoCaseThreeInputCeiling) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have htPos : 0 < t := by
    unfold taoCaseThreeInputFloor at ht
    norm_num at ht ⊢
    linarith
  have hMPos : 0 < taoUpperEdge - t :=
    sub_pos.mpr (ht.2.trans_lt tao_case_three_inputCeiling_lt_upperEdge)
  have hzero : ContinuousAt (fun x : ℝ ↦ -Real.log x) t :=
    (Real.continuousAt_log htPos.ne').neg
  have hprimM : ContinuousAt
      (fun x : ℝ ↦ taoLogPrimitive (taoUpperEdge - x)) t :=
    continuous_taoLogPrimitive.continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  have hprimA : ContinuousAt
      (fun x : ℝ ↦ taoLogPrimitive (taoCaseThreeLeftA - x)) t :=
    continuous_taoLogPrimitive.continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  have hprimB : ContinuousAt
      (fun x : ℝ ↦ taoLogPrimitive (taoCaseThreeLeftB - x)) t :=
    continuous_taoLogPrimitive.continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  have hlogM : ContinuousAt
      (fun x : ℝ ↦ Real.log |taoUpperEdge - x|) t := by
    simpa only [Real.log_abs] using!
      (Real.continuousAt_log hMPos.ne').comp
        (continuousAt_const.sub continuousAt_id)
  exact (((hzero.add ((hprimM.sub hprimA).const_mul taoCaseThreeA)).add
    ((hprimM.sub hprimB).const_mul taoCaseThreeB)).sub
      (hlogM.const_mul taoCaseThreeC))

theorem tao_case_two_leftEndpoint_le_upperEdge :
    taoCaseTwoLeftEndpoint ≤ taoUpperEdge := by
  unfold taoCaseTwoLeftEndpoint taoUpperEdge
  nlinarith [seven_fifths_lt_sqrt_two]

theorem taoCaseTwoA_nonneg : 0 ≤ taoCaseTwoA := by
  norm_num [taoCaseTwoA]

theorem taoCaseTwoA_pos : 0 < taoCaseTwoA := by
  norm_num [taoCaseTwoA]

theorem tao_case_two_floor_pos : 0 < taoCaseTwoFloor := by
  norm_num [taoCaseTwoFloor]

theorem tao_case_two_floor_lt_leftEndpoint :
    taoCaseTwoFloor < taoCaseTwoLeftEndpoint := by
  norm_num [taoCaseTwoFloor, taoCaseTwoLeftEndpoint]

theorem tao_case_two_leftEndpoint_lt_upperEdge :
    taoCaseTwoLeftEndpoint < taoUpperEdge := by
  unfold taoCaseTwoLeftEndpoint taoUpperEdge
  nlinarith [seven_fifths_lt_sqrt_two]

theorem tao_case_two_upperEdge_sub_leftEndpoint_lt_one :
    taoUpperEdge - taoCaseTwoLeftEndpoint < 1 := by
  unfold taoUpperEdge taoCaseTwoLeftEndpoint
  nlinarith [sqrt_two_lt_three_halves]

theorem taoCaseTwoPotentialSecondDerivative_pos_of_left
    {t : ℝ} (ht : t ∈ Ioo taoCaseTwoFloor taoCaseTwoLeftEndpoint) :
    0 < taoCaseTwoPotentialSecondDerivative t := by
  have htPos : 0 < t := tao_case_two_floor_pos.trans ht.1
  have haPos : 0 < taoCaseTwoLeftEndpoint - t := sub_pos.mpr ht.2
  have hMPos : 0 < taoUpperEdge - t :=
    sub_pos.mpr (ht.2.trans tao_case_two_leftEndpoint_lt_upperEdge)
  have hInv :
      0 < -1 / (taoUpperEdge - t) +
        1 / (taoCaseTwoLeftEndpoint - t) := by
    have hden : taoCaseTwoLeftEndpoint - t < taoUpperEdge - t := by
      linarith [tao_case_two_leftEndpoint_lt_upperEdge]
    have hlt : 1 / (taoUpperEdge - t) <
        1 / (taoCaseTwoLeftEndpoint - t) :=
      one_div_lt_one_div_of_lt haPos hden
    rw [neg_div]
    linarith
  have hfirst : 0 < 1 / t ^ 2 :=
    div_pos zero_lt_one (sq_pos_of_pos htPos)
  have hsecond : 0 < taoCaseTwoA *
      (-1 / (taoUpperEdge - t) +
        1 / (taoCaseTwoLeftEndpoint - t)) :=
    mul_pos taoCaseTwoA_pos hInv
  unfold taoCaseTwoPotentialSecondDerivative
  linarith

theorem taoCaseTwoPotentialSecondDerivative_neg_of_middle
    {t : ℝ} (ht : t ∈ Ioo taoCaseTwoLeftEndpoint taoUpperEdge) :
    taoCaseTwoPotentialSecondDerivative t < 0 := by
  have haTwo : 2 < taoCaseTwoLeftEndpoint := by
    norm_num [taoCaseTwoLeftEndpoint]
  have htTwo : 2 < t := haTwo.trans ht.1
  have htSq : 4 < t ^ 2 := by nlinarith
  have hfirst : 1 / t ^ 2 < (1 / 4 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num) htSq
  have huPos : 0 < t - taoCaseTwoLeftEndpoint := sub_pos.mpr ht.1
  have hvPos : 0 < taoUpperEdge - t := sub_pos.mpr ht.2
  have huOne : t - taoCaseTwoLeftEndpoint < 1 := by
    linarith [tao_case_two_upperEdge_sub_leftEndpoint_lt_one]
  have hvOne : taoUpperEdge - t < 1 := by
    linarith [tao_case_two_upperEdge_sub_leftEndpoint_lt_one]
  have hInvU : 1 < 1 / (t - taoCaseTwoLeftEndpoint) :=
    one_lt_one_div huPos huOne
  have hInvV : 1 < 1 / (taoUpperEdge - t) :=
    one_lt_one_div hvPos hvOne
  have hbracket :
      -1 / (taoUpperEdge - t) +
          1 / (taoCaseTwoLeftEndpoint - t) < -2 := by
    rw [show taoCaseTwoLeftEndpoint - t =
      -(t - taoCaseTwoLeftEndpoint) by ring,
      one_div_neg_eq_neg_one_div]
    rw [neg_div]
    linarith
  have hscaled := mul_lt_mul_of_pos_left hbracket taoCaseTwoA_pos
  have hASevenTenths : (7 / 10 : ℝ) < taoCaseTwoA := by
    norm_num [taoCaseTwoA]
  have hscaledBound : taoCaseTwoA *
      (-1 / (taoUpperEdge - t) +
        1 / (taoCaseTwoLeftEndpoint - t)) < -(7 / 5 : ℝ) := by
    calc
      taoCaseTwoA *
          (-1 / (taoUpperEdge - t) +
            1 / (taoCaseTwoLeftEndpoint - t)) <
          taoCaseTwoA * (-2) := hscaled
      _ < -(7 / 5 : ℝ) := by nlinarith
  unfold taoCaseTwoPotentialSecondDerivative
  linarith

theorem taoCaseTwoPotentialSecondDerivative_pos_of_right
    {t : ℝ} (ht : taoUpperEdge < t) :
    0 < taoCaseTwoPotentialSecondDerivative t := by
  have huPos : 0 < t - taoUpperEdge := sub_pos.mpr ht
  have hvPos : 0 < t - taoCaseTwoLeftEndpoint :=
    sub_pos.mpr (tao_case_two_leftEndpoint_lt_upperEdge.trans ht)
  have huv : t - taoUpperEdge < t - taoCaseTwoLeftEndpoint := by
    linarith [tao_case_two_leftEndpoint_lt_upperEdge]
  have hInv := one_div_lt_one_div_of_lt huPos huv
  have hbracket :
      0 < -1 / (taoUpperEdge - t) +
        1 / (taoCaseTwoLeftEndpoint - t) := by
    rw [show taoUpperEdge - t = -(t - taoUpperEdge) by ring,
      show taoCaseTwoLeftEndpoint - t =
        -(t - taoCaseTwoLeftEndpoint) by ring,
      neg_div_neg_eq, one_div_neg_eq_neg_one_div]
    linarith
  have htPos : 0 < t := by
    have hMPos : 0 < taoUpperEdge := by
      unfold taoUpperEdge
      positivity
    exact hMPos.trans ht
  have hfirst : 0 < 1 / t ^ 2 :=
    div_pos zero_lt_one (sq_pos_of_pos htPos)
  have hsecond := mul_pos taoCaseTwoA_pos hbracket
  unfold taoCaseTwoPotentialSecondDerivative
  linarith

theorem taoCaseTwoPotential_convexOn_left :
    ConvexOn ℝ (Icc taoCaseTwoFloor taoCaseTwoLeftEndpoint)
      taoCaseTwoPotential := by
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
  · exact continuousOn_taoCaseTwoPotential_Ioi.mono fun _ ht ↦
      tao_case_two_floor_pos.trans_le ht.1
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_taoCaseTwoPotential
      (tao_case_two_floor_pos.trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans tao_case_two_leftEndpoint_lt_upperEdge)).ne'
      (sub_pos.mpr ht.2).ne').differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_deriv_taoCaseTwoPotential
      (tao_case_two_floor_pos.trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans tao_case_two_leftEndpoint_lt_upperEdge)).ne'
      (sub_pos.mpr ht.2).ne').differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [deriv2_taoCaseTwoPotential
      (tao_case_two_floor_pos.trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans tao_case_two_leftEndpoint_lt_upperEdge)).ne'
      (sub_pos.mpr ht.2).ne']
    exact (taoCaseTwoPotentialSecondDerivative_pos_of_left ht).le

theorem taoCaseTwoPotential_concaveOn_middle :
    ConcaveOn ℝ (Icc taoCaseTwoLeftEndpoint taoUpperEdge)
      taoCaseTwoPotential := by
  have haPos : 0 < taoCaseTwoLeftEndpoint := by
    norm_num [taoCaseTwoLeftEndpoint]
  apply concaveOn_of_deriv2_nonpos (convex_Icc _ _)
  · exact continuousOn_taoCaseTwoPotential_Ioi.mono fun _ ht ↦
      (by
        exact haPos.trans_le ht.1)
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_taoCaseTwoPotential
      (haPos.trans ht.1).ne'
      (sub_pos.mpr ht.2).ne'
      (sub_neg.mpr ht.1).ne).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_deriv_taoCaseTwoPotential
      (haPos.trans ht.1).ne'
      (sub_pos.mpr ht.2).ne'
      (sub_neg.mpr ht.1).ne).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [deriv2_taoCaseTwoPotential (haPos.trans ht.1).ne'
      (sub_pos.mpr ht.2).ne' (sub_neg.mpr ht.1).ne]
    exact (taoCaseTwoPotentialSecondDerivative_neg_of_middle ht).le

theorem taoCaseTwoPotential_convexOn_right :
    ConvexOn ℝ (Icc taoUpperEdge (taoUpperEdge + 1))
      taoCaseTwoPotential := by
  have hMPos : 0 < taoUpperEdge := by
    unfold taoUpperEdge
    positivity
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
  · exact continuousOn_taoCaseTwoPotential_Ioi.mono fun _ ht ↦ by
      exact hMPos.trans_le ht.1
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_taoCaseTwoPotential
      (hMPos.trans ht.1).ne'
      (sub_neg.mpr ht.1).ne
      (sub_neg.mpr (tao_case_two_leftEndpoint_lt_upperEdge.trans ht.1)).ne
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_deriv_taoCaseTwoPotential
      (hMPos.trans ht.1).ne'
      (sub_neg.mpr ht.1).ne
      (sub_neg.mpr (tao_case_two_leftEndpoint_lt_upperEdge.trans ht.1)).ne
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [deriv2_taoCaseTwoPotential (hMPos.trans ht.1).ne'
      (sub_neg.mpr ht.1).ne
      (sub_neg.mpr (tao_case_two_leftEndpoint_lt_upperEdge.trans ht.1)).ne]
    exact (taoCaseTwoPotentialSecondDerivative_pos_of_right ht.1).le

/-- Past `2 * sqrt 2 + 1`, every distance from the interval-density support
is at least one.  Thus the continuous part of the potential is nonpositive,
while the atom at zero contributes strictly negatively. -/
theorem taoCaseTwoPotential_neg_of_upperEdge_add_one_le
    {t : ℝ} (ht : taoUpperEdge + 1 ≤ t) :
    taoCaseTwoPotential t < 0 := by
  have htOne : 1 < t := by
    have hMPos : 0 < taoUpperEdge := by
      unfold taoUpperEdge
      positivity
    linarith
  have hlogt : -Real.log t < 0 := neg_lt_zero.mpr (Real.log_pos htOne)
  have hkernelNonneg :
      0 ≤ ∫ s in taoCaseTwoLeftEndpoint..taoUpperEdge,
        Real.log |t - s| := by
    apply intervalIntegral.integral_nonneg tao_case_two_leftEndpoint_le_upperEdge
    intro s hs
    have hdist : 1 ≤ t - s := by
      linarith [hs.2]
    rw [abs_of_nonneg (le_trans (by norm_num) hdist)]
    exact Real.log_nonneg hdist
  have hkernel :
      (∫ s in taoCaseTwoLeftEndpoint..taoUpperEdge,
          -Real.log |t - s|) ≤ 0 := by
    rw [intervalIntegral.integral_neg]
    linarith
  have hscaled :
      taoCaseTwoA *
          (∫ s in taoCaseTwoLeftEndpoint..taoUpperEdge,
            -Real.log |t - s|) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos taoCaseTwoA_nonneg hkernel
  rw [← tao_case_two_trial_eq_potential (lt_trans zero_lt_one htOne)]
  unfold taoPointIntervalTrialPotential
  rw [abs_of_pos (lt_trans zero_lt_one htOne)]
  linarith

/-- Therefore the numerical part of Case 2 only needs the compact segment
from `0.7987` to `2 * sqrt 2 + 1`. -/
theorem tao_case_two_of_compact_certificate
    (hcompact : ∀ t ∈ Icc taoCaseTwoFloor (taoUpperEdge + 1),
      taoCaseTwoPotential t < 0) :
    ∀ t, taoCaseTwoFloor ≤ t → taoCaseTwoPotential t < 0 := by
  intro t ht
  by_cases hupper : t ≤ taoUpperEdge + 1
  · exact hcompact t ⟨ht, hupper⟩
  · exact taoCaseTwoPotential_neg_of_upperEdge_add_one_le
      (le_of_not_ge hupper)

end

end Erdos1038
