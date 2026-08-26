import ErdosProblems.Erdos1038.TaoUpperCasesTwoThreeAnalysis
import ErdosProblems.Erdos1038.RationalInterval
import Mathlib.Analysis.Convex.Deriv

/-!
# Curvature analysis for Tao's Case 3

The third scalar potential is convex up to its first density endpoint,
strictly increasing between the two density endpoints, concave through its
only shallow interior maximum, and convex again near the upper input edge.
The narrow transition between the last two curvature regimes is left for a
single checked interval enclosure.
-/

open Set

namespace Erdos1038

noncomputable section

def taoCaseThreePotentialSecondDerivative (t : ℝ) : ℝ :=
  1 / t ^ 2 +
    taoCaseThreeA *
      (-1 / (taoUpperEdge - t) +
        1 / (taoCaseThreeLeftA - t)) +
    taoCaseThreeB *
      (-1 / (taoUpperEdge - t) +
        1 / (taoCaseThreeLeftB - t)) +
    taoCaseThreeC / (taoUpperEdge - t) ^ 2

theorem hasDerivAt_taoCaseThreePotentialDerivative {t : ℝ}
    (ht : t ≠ 0) (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseThreeLeftA - t ≠ 0)
    (hb : taoCaseThreeLeftB - t ≠ 0) :
    HasDerivAt taoCaseThreePotentialDerivative
      (taoCaseThreePotentialSecondDerivative t) t := by
  have hrecip : HasDerivAt (fun x : ℝ ↦ -1 / x) (1 / t ^ 2) t := by
    convert! (hasDerivAt_const t (-1 : ℝ)).div (hasDerivAt_id t) ht using 1
    simp only [id_eq]
    field_simp [ht]
    ring
  have hA := ((hasDerivAt_log_abs_const_sub hM).sub
    (hasDerivAt_log_abs_const_sub ha)).const_mul taoCaseThreeA
  have hB := ((hasDerivAt_log_abs_const_sub hM).sub
    (hasDerivAt_log_abs_const_sub hb)).const_mul taoCaseThreeB
  have hC : HasDerivAt
      (fun x : ℝ ↦ taoCaseThreeC / (taoUpperEdge - x))
      (taoCaseThreeC / (taoUpperEdge - t) ^ 2) t := by
    have hden : HasDerivAt (fun x : ℝ ↦ taoUpperEdge - x) (-1) t := by
      convert! (hasDerivAt_const t taoUpperEdge).sub (hasDerivAt_id t) using 1
      ring
    convert! (hasDerivAt_const t taoCaseThreeC).div hden hM using 1
    field_simp [hM]
    ring
  convert! (((hrecip.add hA).add hB).add hC) using 1
  unfold taoCaseThreePotentialSecondDerivative
  ring

theorem hasDerivAt_deriv_taoCaseThreePotential {t : ℝ}
    (ht : t ≠ 0) (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseThreeLeftA - t ≠ 0)
    (hb : taoCaseThreeLeftB - t ≠ 0) :
    HasDerivAt (deriv taoCaseThreePotential)
      (taoCaseThreePotentialSecondDerivative t) t := by
  have htM : t ≠ taoUpperEdge := (sub_ne_zero.mp hM).symm
  have hta : t ≠ taoCaseThreeLeftA := (sub_ne_zero.mp ha).symm
  have htb : t ≠ taoCaseThreeLeftB := (sub_ne_zero.mp hb).symm
  have heq : Filter.EventuallyEq (nhds t)
      (deriv taoCaseThreePotential) taoCaseThreePotentialDerivative := by
    filter_upwards [eventually_ne_nhds ht, eventually_ne_nhds htM,
      eventually_ne_nhds hta, eventually_ne_nhds htb] with y hy0 hyM hya hyb
    exact (hasDerivAt_taoCaseThreePotential hy0
      (sub_ne_zero.mpr hyM.symm) (sub_ne_zero.mpr hya.symm)
      (sub_ne_zero.mpr hyb.symm)).deriv
  exact (hasDerivAt_taoCaseThreePotentialDerivative ht hM ha hb).congr_of_eventuallyEq
    heq

theorem deriv2_taoCaseThreePotential {t : ℝ}
    (ht : t ≠ 0) (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseThreeLeftA - t ≠ 0)
    (hb : taoCaseThreeLeftB - t ≠ 0) :
    deriv^[2] taoCaseThreePotential t =
      taoCaseThreePotentialSecondDerivative t := by
  rw [show deriv^[2] taoCaseThreePotential t =
      deriv (deriv taoCaseThreePotential) t by rfl]
  exact (hasDerivAt_deriv_taoCaseThreePotential ht hM ha hb).deriv

theorem tao_case_three_inputFloor_pos :
    0 < taoCaseThreeInputFloor := by
  norm_num [taoCaseThreeInputFloor]

theorem tao_case_three_inputFloor_lt_leftA :
    taoCaseThreeInputFloor < taoCaseThreeLeftA := by
  norm_num [taoCaseThreeInputFloor, taoCaseThreeLeftA]

theorem tao_case_three_leftA_lt_leftB :
    taoCaseThreeLeftA < taoCaseThreeLeftB := by
  norm_num [taoCaseThreeLeftA, taoCaseThreeLeftB]

theorem tao_case_three_leftA_lt_upperEdge :
    taoCaseThreeLeftA < taoUpperEdge := by
  unfold taoCaseThreeLeftA taoUpperEdge
  nlinarith [seven_fifths_lt_sqrt_two]

theorem tao_case_three_leftB_lt_upperEdge :
    taoCaseThreeLeftB < taoUpperEdge := by
  unfold taoCaseThreeLeftB taoUpperEdge
  nlinarith [seven_fifths_lt_sqrt_two]

theorem tao_case_three_leftB_lt_transitionLow :
    taoCaseThreeLeftB < (253 / 100 : ℝ) := by
  norm_num [taoCaseThreeLeftB]

theorem tao_case_three_transitionHigh_lt_inputCeiling :
    (51 / 20 : ℝ) < taoCaseThreeInputCeiling := by
  norm_num [taoCaseThreeInputCeiling]

theorem taoCaseThreePotentialSecondDerivative_pos_of_left
    {t : ℝ} (ht : t ∈ Ioo taoCaseThreeInputFloor taoCaseThreeLeftA) :
    0 < taoCaseThreePotentialSecondDerivative t := by
  have htPos : 0 < t := tao_case_three_inputFloor_pos.trans ht.1
  have haPos : 0 < taoCaseThreeLeftA - t := sub_pos.mpr ht.2
  have hbPos : 0 < taoCaseThreeLeftB - t :=
    sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_leftB)
  have hMPos : 0 < taoUpperEdge - t :=
    sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_upperEdge)
  have hAinv : 0 < -1 / (taoUpperEdge - t) +
      1 / (taoCaseThreeLeftA - t) := by
    have hden : taoCaseThreeLeftA - t < taoUpperEdge - t := by
      linarith [tao_case_three_leftA_lt_upperEdge]
    have := one_div_lt_one_div_of_lt haPos hden
    rw [neg_div]
    linarith
  have hBinv : 0 < -1 / (taoUpperEdge - t) +
      1 / (taoCaseThreeLeftB - t) := by
    have hden : taoCaseThreeLeftB - t < taoUpperEdge - t := by
      linarith [tao_case_three_leftB_lt_upperEdge]
    have := one_div_lt_one_div_of_lt hbPos hden
    rw [neg_div]
    linarith
  have hfirst : 0 < 1 / t ^ 2 :=
    div_pos zero_lt_one (sq_pos_of_pos htPos)
  have hA : 0 < taoCaseThreeA *
      (-1 / (taoUpperEdge - t) +
        1 / (taoCaseThreeLeftA - t)) :=
    mul_pos (by norm_num [taoCaseThreeA]) hAinv
  have hB : 0 < taoCaseThreeB *
      (-1 / (taoUpperEdge - t) +
        1 / (taoCaseThreeLeftB - t)) :=
    mul_pos (by norm_num [taoCaseThreeB]) hBinv
  have hC : 0 < taoCaseThreeC / (taoUpperEdge - t) ^ 2 :=
    div_pos (by norm_num [taoCaseThreeC]) (sq_pos_of_pos hMPos)
  unfold taoCaseThreePotentialSecondDerivative
  linarith

theorem taoCaseThreePotential_convexOn_left :
    ConvexOn ℝ (Icc taoCaseThreeInputFloor taoCaseThreeLeftA)
      taoCaseThreePotential := by
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
  · exact continuousOn_taoCaseThreePotential_input.mono fun _ ht ↦
      ⟨ht.1, ht.2.trans (by
        norm_num [taoCaseThreeLeftA, taoCaseThreeInputCeiling])⟩
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_taoCaseThreePotential
      (tao_case_three_inputFloor_pos.trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_upperEdge)).ne'
      (sub_pos.mpr ht.2).ne'
      (sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_leftB)).ne'
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_deriv_taoCaseThreePotential
      (tao_case_three_inputFloor_pos.trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_upperEdge)).ne'
      (sub_pos.mpr ht.2).ne'
      (sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_leftB)).ne'
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [deriv2_taoCaseThreePotential
      (tao_case_three_inputFloor_pos.trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_upperEdge)).ne'
      (sub_pos.mpr ht.2).ne'
      (sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_leftB)).ne']
    exact (taoCaseThreePotentialSecondDerivative_pos_of_left ht).le

theorem taoCaseThreePotentialDerivative_pos_of_middle
    {t : ℝ} (ht : t ∈ Ioo taoCaseThreeLeftA taoCaseThreeLeftB) :
    0 < taoCaseThreePotentialDerivative t := by
  have haPos : 0 < taoCaseThreeLeftA := by
    norm_num [taoCaseThreeLeftA]
  have htPos : 0 < t := haPos.trans ht.1
  have hMPos : 0 < taoUpperEdge - t :=
    sub_pos.mpr (ht.2.trans tao_case_three_leftB_lt_upperEdge)
  have htaPos : 0 < t - taoCaseThreeLeftA := sub_pos.mpr ht.1
  have hbtPos : 0 < taoCaseThreeLeftB - t := sub_pos.mpr ht.2
  have hthreshold :
      4 * taoCaseThreeLeftB - 3 * taoCaseThreeLeftA < taoUpperEdge := by
    unfold taoCaseThreeLeftA taoCaseThreeLeftB taoUpperEdge
    nlinarith [seven_fifths_lt_sqrt_two]
  have hratioA : (3 : ℝ) <
      (taoUpperEdge - t) / (t - taoCaseThreeLeftA) := by
    rw [lt_div_iff₀ htaPos]
    nlinarith [ht.2, hthreshold]
  have hratioB : (4 : ℝ) <
      (taoUpperEdge - t) / (taoCaseThreeLeftB - t) := by
    rw [lt_div_iff₀ hbtPos]
    nlinarith [ht.1, hthreshold]
  have hlogThree : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_three
  have hlogFour : (4 / 3 : ℝ) < Real.log 4 := by
    have hbound := logLowerRat_le_log
      (n := 3) (r := (4 : Rat)) (by norm_num)
    have hrat : (4 / 3 : ℝ) <
        ((logLowerRat 3 4 : Rat) : ℝ) := by
      norm_num [logLowerRat, logAtanhParameterRat, atanhLowerRat]
    exact hrat.trans_le hbound
  have hlogA : (1 : ℝ) <
      Real.log |taoUpperEdge - t| -
        Real.log |taoCaseThreeLeftA - t| := by
    rw [abs_of_pos hMPos,
      abs_of_neg (sub_neg.mpr ht.1)]
    rw [show -(taoCaseThreeLeftA - t) =
      t - taoCaseThreeLeftA by ring]
    rw [← Real.log_div hMPos.ne' htaPos.ne']
    exact hlogThree.trans
      (Real.log_lt_log (by norm_num) hratioA)
  have hlogB : (4 / 3 : ℝ) <
      Real.log |taoUpperEdge - t| -
        Real.log |taoCaseThreeLeftB - t| := by
    rw [abs_of_pos hMPos, abs_of_pos hbtPos]
    rw [← Real.log_div hMPos.ne' hbtPos.ne']
    exact hlogFour.trans
      (Real.log_lt_log (by norm_num) hratioB)
  have hrecip :
      -1 / taoCaseThreeLeftA < -1 / t := by
    have hinv := one_div_lt_one_div_of_lt haPos ht.1
    simpa only [neg_div] using! neg_lt_neg hinv
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := by
    norm_num
  have hMUpper : taoUpperEdge < (283 / 100 : ℝ) := by
    unfold taoUpperEdge
    have hsqrtNonneg := Real.sqrt_nonneg 2
    nlinarith
  have hC : (1 / 8 : ℝ) <
      taoCaseThreeC / (taoUpperEdge - t) := by
    rw [lt_div_iff₀ hMPos]
    have htLower : (163 / 100 : ℝ) < t := by
      simpa only [taoCaseThreeLeftA] using! ht.1
    norm_num only [taoCaseThreeC]
    nlinarith [htLower, hMUpper]
  have hApos : 0 < taoCaseThreeA := by
    norm_num [taoCaseThreeA]
  have hBpos : 0 < taoCaseThreeB := by
    norm_num [taoCaseThreeB]
  have hscaledA := mul_lt_mul_of_pos_left hlogA hApos
  have hscaledB := mul_lt_mul_of_pos_left hlogB hBpos
  have hbase : 0 <
      -1 / taoCaseThreeLeftA + taoCaseThreeA * 1 +
        taoCaseThreeB * (4 / 3) + (1 / 8 : ℝ) := by
    norm_num [taoCaseThreeLeftA, taoCaseThreeA, taoCaseThreeB]
  unfold taoCaseThreePotentialDerivative
  nlinarith

theorem taoCaseThreePotential_strictMonoOn_middle :
    StrictMonoOn taoCaseThreePotential
      (Icc taoCaseThreeLeftA taoCaseThreeLeftB) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact continuousOn_taoCaseThreePotential_input.mono fun _ ht ↦ by
      constructor
      · exact (by
          norm_num [taoCaseThreeInputFloor, taoCaseThreeLeftA] at ht ⊢
          linarith [ht.1])
      · exact (by
          norm_num [taoCaseThreeInputCeiling, taoCaseThreeLeftB] at ht ⊢
          linarith [ht.2])
  · rw [interior_Icc]
    intro t ht
    rw [(hasDerivAt_taoCaseThreePotential
      (by
        have : 0 < taoCaseThreeLeftA := by
          norm_num [taoCaseThreeLeftA]
        exact (this.trans ht.1).ne')
      (sub_pos.mpr (ht.2.trans tao_case_three_leftB_lt_upperEdge)).ne'
      (sub_neg.mpr ht.1).ne
      (sub_pos.mpr ht.2).ne').deriv]
    exact taoCaseThreePotentialDerivative_pos_of_middle ht

private theorem taoCaseThreePotentialSecondDerivative_eq_right
    {t : ℝ} :
    taoCaseThreePotentialSecondDerivative t =
      1 / t ^ 2 -
        (taoCaseThreeA + taoCaseThreeB) / (taoUpperEdge - t) -
        taoCaseThreeA / (t - taoCaseThreeLeftA) -
        taoCaseThreeB / (t - taoCaseThreeLeftB) +
        taoCaseThreeC / (taoUpperEdge - t) ^ 2 := by
  rw [taoCaseThreePotentialSecondDerivative,
    show taoCaseThreeLeftA - t =
      -(t - taoCaseThreeLeftA) by ring,
    show taoCaseThreeLeftB - t =
      -(t - taoCaseThreeLeftB) by ring,
    one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div]
  ring

theorem taoCaseThreePotentialSecondDerivative_neg_of_right_low
    {t : ℝ} (htLower : taoCaseThreeLeftB < t)
    (htUpper : t ≤ (11 / 5 : ℝ)) :
    taoCaseThreePotentialSecondDerivative t < 0 := by
  have htPos : 0 < t := by
    have : 0 < taoCaseThreeLeftB := by
      norm_num [taoCaseThreeLeftB]
    exact this.trans htLower
  have htaPos : 0 < t - taoCaseThreeLeftA :=
    sub_pos.mpr (tao_case_three_leftA_lt_leftB.trans htLower)
  have htbPos : 0 < t - taoCaseThreeLeftB := sub_pos.mpr htLower
  have hMPos : 0 < taoUpperEdge - t := by
    have hM : (14 / 5 : ℝ) < taoUpperEdge := by
      unfold taoUpperEdge
      nlinarith [seven_fifths_lt_sqrt_two]
    linarith
  rw [taoCaseThreePotentialSecondDerivative_eq_right]
  have htBound : (19 / 10 : ℝ) < t := by
    norm_num [taoCaseThreeLeftB] at htLower ⊢
    linarith
  have htSq : (10 / 3 : ℝ) < t ^ 2 := by
    nlinarith
  have hfirst : 1 / t ^ 2 < (3 / 10 : ℝ) := by
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 10 / 3) htSq
    norm_num at h ⊢
    exact h
  have hu : (3 / 5 : ℝ) < taoUpperEdge - t := by
    have hM : (14 / 5 : ℝ) < taoUpperEdge := by
      unfold taoUpperEdge
      nlinarith [seven_fifths_lt_sqrt_two]
    linarith
  have huSq : (9 / 25 : ℝ) < (taoUpperEdge - t) ^ 2 := by
    nlinarith
  have hC : taoCaseThreeC / (taoUpperEdge - t) ^ 2 <
      (13 / 30 : ℝ) := by
    rw [div_lt_iff₀ (sq_pos_of_pos hMPos)]
    unfold taoCaseThreeC
    nlinarith
  have htaUpper : t - taoCaseThreeLeftA ≤ (57 / 100 : ℝ) := by
    unfold taoCaseThreeLeftA
    linarith
  have htbUpper : t - taoCaseThreeLeftB ≤ (281 / 1000 : ℝ) := by
    unfold taoCaseThreeLeftB
    linarith
  have hA : -taoCaseThreeA / (t - taoCaseThreeLeftA) ≤
      -taoCaseThreeA / (57 / 100 : ℝ) := by
    have hinv := one_div_le_one_div_of_le htaPos htaUpper
    have hmul := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ taoCaseThreeA by norm_num [taoCaseThreeA])
    convert! neg_le_neg hmul using 1 <;> ring
  have hB : -taoCaseThreeB / (t - taoCaseThreeLeftB) ≤
      -taoCaseThreeB / (281 / 1000 : ℝ) := by
    have hinv := one_div_le_one_div_of_le htbPos htbUpper
    have hmul := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ taoCaseThreeB by norm_num [taoCaseThreeB])
    convert! neg_le_neg hmul using 1 <;> ring
  have hshared :
      -(taoCaseThreeA + taoCaseThreeB) / (taoUpperEdge - t) < 0 := by
    exact div_neg_of_neg_of_pos (by
      norm_num [taoCaseThreeA, taoCaseThreeB]) hMPos
  have hbase :
      (3 / 10 : ℝ) + 13 / 30 -
        taoCaseThreeA / (57 / 100) -
        taoCaseThreeB / (281 / 1000) < 0 := by
    norm_num [taoCaseThreeA, taoCaseThreeB]
  ring_nf at hfirst hC hA hB hshared hbase ⊢
  linarith

theorem taoCaseThreePotentialSecondDerivative_neg_of_right_high
    {t : ℝ} (htLower : (11 / 5 : ℝ) ≤ t)
    (htUpper : t < (253 / 100 : ℝ)) :
    taoCaseThreePotentialSecondDerivative t < 0 := by
  have htPos : 0 < t := by linarith
  have htaPos : 0 < t - taoCaseThreeLeftA := by
    norm_num [taoCaseThreeLeftA] at htLower ⊢
    linarith
  have htbPos : 0 < t - taoCaseThreeLeftB := by
    norm_num [taoCaseThreeLeftB] at htLower ⊢
    linarith
  have hMPos : 0 < taoUpperEdge - t := by
    have hM : (14 / 5 : ℝ) < taoUpperEdge := by
      unfold taoUpperEdge
      nlinarith [seven_fifths_lt_sqrt_two]
    linarith
  rw [taoCaseThreePotentialSecondDerivative_eq_right]
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsqrtNonneg := Real.sqrt_nonneg 2
  have hsqrtLower : (707 / 500 : ℝ) < Real.sqrt 2 := by
    nlinarith
  have hu : (149 / 500 : ℝ) < taoUpperEdge - t := by
    unfold taoUpperEdge
    linarith
  have huSq : (149 / 500 : ℝ) ^ 2 <
      (taoUpperEdge - t) ^ 2 := by
    nlinarith
  let K : ℝ := taoCaseThreeA + taoCaseThreeB
  have hKpos : 0 < K := by
    dsimp only [K]
    norm_num [taoCaseThreeA, taoCaseThreeB]
  have hquadBase : taoCaseThreeC <
      (7 / 20 : ℝ) * (149 / 500) ^ 2 +
        K * (149 / 500) := by
    dsimp only [K]
    norm_num [taoCaseThreeA, taoCaseThreeB, taoCaseThreeC]
  have hquad : taoCaseThreeC <
      (7 / 20 : ℝ) * (taoUpperEdge - t) ^ 2 +
        K * (taoUpperEdge - t) := by
    have hscaledSq := mul_lt_mul_of_pos_left huSq
      (by norm_num : (0 : ℝ) < 7 / 20)
    have hscaled := mul_lt_mul_of_pos_left hu hKpos
    linarith
  have hcombined :
      taoCaseThreeC / (taoUpperEdge - t) ^ 2 -
          K / (taoUpperEdge - t) < (7 / 20 : ℝ) := by
    rw [show taoCaseThreeC / (taoUpperEdge - t) ^ 2 -
        K / (taoUpperEdge - t) =
      (taoCaseThreeC - K * (taoUpperEdge - t)) /
        (taoUpperEdge - t) ^ 2 by
          field_simp [hMPos.ne']]
    rw [div_lt_iff₀ (sq_pos_of_pos hMPos)]
    linarith
  have htSq : (121 / 25 : ℝ) ≤ t ^ 2 := by
    nlinarith
  have hfirst : 1 / t ^ 2 ≤ (25 / 121 : ℝ) := by
    have h := one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 121 / 25) htSq
    norm_num at h ⊢
    exact h
  have htaUpper : t - taoCaseThreeLeftA < (9 / 10 : ℝ) := by
    unfold taoCaseThreeLeftA
    linarith
  have htbUpper : t - taoCaseThreeLeftB < (611 / 1000 : ℝ) := by
    unfold taoCaseThreeLeftB
    linarith
  have hA : -taoCaseThreeA / (t - taoCaseThreeLeftA) <
      -taoCaseThreeA / (9 / 10 : ℝ) := by
    have hinv := one_div_lt_one_div_of_lt htaPos htaUpper
    have hmul := mul_lt_mul_of_pos_left hinv
      (show 0 < taoCaseThreeA by norm_num [taoCaseThreeA])
    convert! neg_lt_neg hmul using 1 <;> ring
  have hB : -taoCaseThreeB / (t - taoCaseThreeLeftB) <
      -taoCaseThreeB / (611 / 1000 : ℝ) := by
    have hinv := one_div_lt_one_div_of_lt htbPos htbUpper
    have hmul := mul_lt_mul_of_pos_left hinv
      (show 0 < taoCaseThreeB by norm_num [taoCaseThreeB])
    convert! neg_lt_neg hmul using 1 <;> ring
  have hbase : (25 / 121 : ℝ) + 7 / 20 -
      taoCaseThreeA / (9 / 10) -
      taoCaseThreeB / (611 / 1000) < 0 := by
    norm_num [taoCaseThreeA, taoCaseThreeB]
  dsimp only [K] at hcombined
  ring_nf at hcombined hfirst hA hB hbase ⊢
  linarith

theorem taoCaseThreePotentialSecondDerivative_neg_of_right
    {t : ℝ} (ht : t ∈ Ioo taoCaseThreeLeftB (253 / 100 : ℝ)) :
    taoCaseThreePotentialSecondDerivative t < 0 := by
  by_cases hsplit : t ≤ (11 / 5 : ℝ)
  · exact taoCaseThreePotentialSecondDerivative_neg_of_right_low
      ht.1 hsplit
  · exact taoCaseThreePotentialSecondDerivative_neg_of_right_high
      (le_of_not_ge hsplit) ht.2

theorem taoCaseThreePotential_concaveOn_right :
    ConcaveOn ℝ (Icc taoCaseThreeLeftB (253 / 100 : ℝ))
      taoCaseThreePotential := by
  apply concaveOn_of_deriv2_nonpos (convex_Icc _ _)
  · exact continuousOn_taoCaseThreePotential_input.mono fun _ ht ↦ by
      constructor
      · have hfloor : taoCaseThreeInputFloor < taoCaseThreeLeftB := by
          norm_num [taoCaseThreeInputFloor, taoCaseThreeLeftB]
        exact hfloor.le.trans ht.1
      · have hceiling : (253 / 100 : ℝ) < taoCaseThreeInputCeiling := by
          norm_num [taoCaseThreeInputCeiling]
        exact ht.2.trans hceiling.le
  · rw [interior_Icc]
    intro t ht
    have hMbound : (253 / 100 : ℝ) < taoUpperEdge := by
      unfold taoUpperEdge
      nlinarith [seven_fifths_lt_sqrt_two]
    exact (hasDerivAt_taoCaseThreePotential
      (by
        have h : 0 < taoCaseThreeLeftB := by
          norm_num [taoCaseThreeLeftB]
        exact (h.trans ht.1).ne')
      (sub_pos.mpr (ht.2.trans hMbound)).ne'
      (sub_neg.mpr (tao_case_three_leftA_lt_leftB.trans ht.1)).ne
      (sub_neg.mpr ht.1).ne
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    have hMbound : (253 / 100 : ℝ) < taoUpperEdge := by
      unfold taoUpperEdge
      nlinarith [seven_fifths_lt_sqrt_two]
    exact (hasDerivAt_deriv_taoCaseThreePotential
      (by
        have h : 0 < taoCaseThreeLeftB := by
          norm_num [taoCaseThreeLeftB]
        exact (h.trans ht.1).ne')
      (sub_pos.mpr (ht.2.trans hMbound)).ne'
      (sub_neg.mpr (tao_case_three_leftA_lt_leftB.trans ht.1)).ne
      (sub_neg.mpr ht.1).ne
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    have hMbound : (253 / 100 : ℝ) < taoUpperEdge := by
      unfold taoUpperEdge
      nlinarith [seven_fifths_lt_sqrt_two]
    rw [deriv2_taoCaseThreePotential
      (by
        have h : 0 < taoCaseThreeLeftB := by
          norm_num [taoCaseThreeLeftB]
        exact (h.trans ht.1).ne')
      (sub_pos.mpr (ht.2.trans hMbound)).ne'
      (sub_neg.mpr (tao_case_three_leftA_lt_leftB.trans ht.1)).ne
      (sub_neg.mpr ht.1).ne]
    exact (taoCaseThreePotentialSecondDerivative_neg_of_right ht).le

theorem taoCaseThreePotentialSecondDerivative_pos_of_upper
    {t : ℝ} (ht : t ∈ Ioo (51 / 20 : ℝ)
      taoCaseThreeInputCeiling) :
    0 < taoCaseThreePotentialSecondDerivative t := by
  have htPos : 0 < t :=
    (by norm_num : (0 : ℝ) < 51 / 20).trans ht.1
  have hMPos : 0 < taoUpperEdge - t :=
    sub_pos.mpr (ht.2.trans tao_case_three_inputCeiling_lt_upperEdge)
  have htaPos : 0 < t - taoCaseThreeLeftA := by
    norm_num [taoCaseThreeLeftA] at ht ⊢
    linarith [ht.1]
  have htbPos : 0 < t - taoCaseThreeLeftB := by
    norm_num [taoCaseThreeLeftB] at ht ⊢
    linarith [ht.1]
  rw [taoCaseThreePotentialSecondDerivative_eq_right]
  let K : ℝ := taoCaseThreeA + taoCaseThreeB
  let U : ℝ := 6961 / 25000
  have hKpos : 0 < K := by
    dsimp only [K]
    norm_num [taoCaseThreeA, taoCaseThreeB]
  have hUpos : 0 < U := by
    dsimp only [U]
    norm_num
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsqrtNonneg := Real.sqrt_nonneg 2
  have hsqrtUpper : Real.sqrt 2 < (70711 / 50000 : ℝ) := by
    nlinarith
  have huUpper : taoUpperEdge - t < U := by
    dsimp only [U]
    unfold taoUpperEdge
    linarith [ht.1, hsqrtUpper]
  have huSq : (taoUpperEdge - t) ^ 2 < U ^ 2 := by
    nlinarith
  have hnumU : 0 < taoCaseThreeC - K * U := by
    dsimp only [K, U]
    norm_num [taoCaseThreeA, taoCaseThreeB, taoCaseThreeC]
  have hnum : taoCaseThreeC - K * U <
      taoCaseThreeC - K * (taoUpperEdge - t) := by
    nlinarith
  have hinvSq : 1 / U ^ 2 < 1 / (taoUpperEdge - t) ^ 2 :=
    one_div_lt_one_div_of_lt (sq_pos_of_pos hMPos) huSq
  have hcombined :
      taoCaseThreeC / U ^ 2 - K / U <
        taoCaseThreeC / (taoUpperEdge - t) ^ 2 -
          K / (taoUpperEdge - t) := by
    rw [show taoCaseThreeC / U ^ 2 - K / U =
        (taoCaseThreeC - K * U) / U ^ 2 by
          field_simp [hUpos.ne']
      , show taoCaseThreeC / (taoUpperEdge - t) ^ 2 -
          K / (taoUpperEdge - t) =
        (taoCaseThreeC - K * (taoUpperEdge - t)) /
          (taoUpperEdge - t) ^ 2 by
          field_simp [hMPos.ne']]
    have hfirstStep :
        (taoCaseThreeC - K * U) / U ^ 2 <
          (taoCaseThreeC - K * U) /
            (taoUpperEdge - t) ^ 2 := by
      simpa only [div_eq_mul_inv, one_mul] using!
        mul_lt_mul_of_pos_left hinvSq hnumU
    have hsecondStep :
        (taoCaseThreeC - K * U) /
            (taoUpperEdge - t) ^ 2 <
          (taoCaseThreeC - K * (taoUpperEdge - t)) /
            (taoUpperEdge - t) ^ 2 := by
      exact div_lt_div_of_pos_right hnum
        (sq_pos_of_pos hMPos)
    exact hfirstStep.trans hsecondStep
  have htSq : t ^ 2 < 8 := by
    have hMPos' : 0 < taoUpperEdge := by
      unfold taoUpperEdge
      positivity
    have htM : t < taoUpperEdge :=
      ht.2.trans tao_case_three_inputCeiling_lt_upperEdge
    have hMsq : taoUpperEdge ^ 2 = 8 := by
      unfold taoUpperEdge
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    nlinarith
  have hfirst : (1 / 8 : ℝ) < 1 / t ^ 2 := by
    have h := one_div_lt_one_div_of_lt (sq_pos_of_pos htPos) htSq
    norm_num at h ⊢
    exact h
  have htaLower : (51 / 20 : ℝ) - taoCaseThreeLeftA <
      t - taoCaseThreeLeftA := by linarith [ht.1]
  have htbLower : (51 / 20 : ℝ) - taoCaseThreeLeftB <
      t - taoCaseThreeLeftB := by linarith [ht.1]
  have hA : -taoCaseThreeA /
        ((51 / 20 : ℝ) - taoCaseThreeLeftA) <
      -taoCaseThreeA / (t - taoCaseThreeLeftA) := by
    have hinv := one_div_lt_one_div_of_lt (by
      norm_num [taoCaseThreeLeftA]) htaLower
    have hmul := mul_lt_mul_of_pos_left hinv
      (show 0 < taoCaseThreeA by norm_num [taoCaseThreeA])
    convert! neg_lt_neg hmul using 1 <;> ring
  have hB : -taoCaseThreeB /
        ((51 / 20 : ℝ) - taoCaseThreeLeftB) <
      -taoCaseThreeB / (t - taoCaseThreeLeftB) := by
    have hinv := one_div_lt_one_div_of_lt (by
      norm_num [taoCaseThreeLeftB]) htbLower
    have hmul := mul_lt_mul_of_pos_left hinv
      (show 0 < taoCaseThreeB by norm_num [taoCaseThreeB])
    convert! neg_lt_neg hmul using 1 <;> ring
  have hbase : 0 < (1 / 8 : ℝ) -
      taoCaseThreeA / ((51 / 20 : ℝ) - taoCaseThreeLeftA) -
      taoCaseThreeB / ((51 / 20 : ℝ) - taoCaseThreeLeftB) +
      (taoCaseThreeC / U ^ 2 - K / U) := by
    dsimp only [K, U]
    norm_num [taoCaseThreeA, taoCaseThreeB, taoCaseThreeC,
      taoCaseThreeLeftA, taoCaseThreeLeftB]
  dsimp only [K] at hcombined ⊢
  ring_nf at hcombined hfirst hA hB hbase ⊢
  linarith

theorem taoCaseThreePotential_convexOn_upper :
    ConvexOn ℝ (Icc (51 / 20 : ℝ) taoCaseThreeInputCeiling)
      taoCaseThreePotential := by
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
  · exact continuousOn_taoCaseThreePotential_input.mono fun _ ht ↦
      ⟨(by
        have h : taoCaseThreeInputFloor ≤ (51 / 20 : ℝ) := by
          norm_num [taoCaseThreeInputFloor]
        exact h.trans ht.1), ht.2⟩
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_taoCaseThreePotential
      ((by norm_num : (0 : ℝ) < 51 / 20).trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans
        tao_case_three_inputCeiling_lt_upperEdge)).ne'
      (sub_neg.mpr (by
        have h : taoCaseThreeLeftA < (51 / 20 : ℝ) := by
          norm_num [taoCaseThreeLeftA]
        exact h.trans ht.1)).ne
      (sub_neg.mpr (by
        have h : taoCaseThreeLeftB < (51 / 20 : ℝ) := by
          norm_num [taoCaseThreeLeftB]
        exact h.trans ht.1)).ne
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_deriv_taoCaseThreePotential
      ((by norm_num : (0 : ℝ) < 51 / 20).trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans
        tao_case_three_inputCeiling_lt_upperEdge)).ne'
      (sub_neg.mpr (by
        have h : taoCaseThreeLeftA < (51 / 20 : ℝ) := by
          norm_num [taoCaseThreeLeftA]
        exact h.trans ht.1)).ne
      (sub_neg.mpr (by
        have h : taoCaseThreeLeftB < (51 / 20 : ℝ) := by
          norm_num [taoCaseThreeLeftB]
        exact h.trans ht.1)).ne
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [deriv2_taoCaseThreePotential
      ((by norm_num : (0 : ℝ) < 51 / 20).trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans
        tao_case_three_inputCeiling_lt_upperEdge)).ne'
      (sub_neg.mpr (by
        have h : taoCaseThreeLeftA < (51 / 20 : ℝ) := by
          norm_num [taoCaseThreeLeftA]
        exact h.trans ht.1)).ne
      (sub_neg.mpr (by
        have h : taoCaseThreeLeftB < (51 / 20 : ℝ) := by
          norm_num [taoCaseThreeLeftB]
        exact h.trans ht.1)).ne]
    exact (taoCaseThreePotentialSecondDerivative_pos_of_upper ht).le

end

end Erdos1038
