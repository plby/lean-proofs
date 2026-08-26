import ErdosProblems.Erdos1038.TaoUpperCaseThreeInterval
import ErdosProblems.Erdos1038.TaoUpperCaseTwoCertificate
import ErdosProblems.Erdos1038.KernelDecision

set_option maxRecDepth 100000

/-!
# Complete checked scalar certificate for Tao's Case 3

The analytic shape theorems reduce the third potential inequality to seven
exact rational interval checks: three scalar endpoints, two values of one
supporting tangent, one narrow transition interval, and the input ceiling.
-/

open Set

namespace Erdos1038

noncomputable section

def taoCaseThreeTangentPointRat : Rat := 8771 / 4000

theorem taoCaseThree_floor_certificate :
    ∃ R, evalTaoCaseThreePotentialInterval 50
      (RatInterval.point (953 / 1250)) = some R ∧ R.hi < 0 := by
  kernel_decide

theorem taoCaseThree_leftA_certificate :
    ∃ R, evalTaoCaseThreePotentialAtLeftA 50 = some R ∧ R.hi < 0 := by
  kernel_decide

theorem taoCaseThree_leftB_certificate :
    ∃ R, evalTaoCaseThreePotentialAtLeftB 50 = some R ∧ R.hi < 0 := by
  kernel_decide

theorem taoCaseThree_left_tangent_certificate :
    ∃ R, evalTaoCaseThreeTangentInterval 50
      taoCaseThreeTangentPointRat (1919 / 1000) = some R ∧ R.hi < 0 := by
  kernel_decide

theorem taoCaseThree_right_tangent_certificate :
    ∃ R, evalTaoCaseThreeTangentInterval 50
      taoCaseThreeTangentPointRat (253 / 100) = some R ∧ R.hi < 0 := by
  kernel_decide

theorem taoCaseThree_transition_certificate :
    ∃ R, evalTaoCaseThreePotentialInterval 50
      ⟨253 / 100, 51 / 20⟩ = some R ∧ R.hi < 0 := by
  kernel_decide

theorem taoCaseThree_ceiling_certificate :
    ∃ R, evalTaoCaseThreePotentialInterval 80
      (RatInterval.point (27987 / 10000)) = some R ∧ R.hi < 0 := by
  kernel_decide

theorem taoCaseThreePotential_floor_neg :
    taoCaseThreePotential taoCaseThreeInputFloor < 0 := by
  have hPoint := RatInterval.point_contains (953 / 1250 : Rat)
  have hContains :
      (RatInterval.point (953 / 1250)).Contains
        taoCaseThreeInputFloor := by
    simpa only [taoCaseThreeInputFloor, Rat.cast_div,
      Rat.cast_ofNat] using! hPoint
  exact taoCaseThreePotential_neg_of_interval_certificate
    hContains taoCaseThree_floor_certificate

theorem taoCaseThreePotential_leftA_neg :
    taoCaseThreePotential taoCaseThreeLeftA < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseThree_leftA_certificate
  have hContains := evalTaoCaseThreePotentialAtLeftA_contains hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

theorem taoCaseThreePotential_leftB_neg :
    taoCaseThreePotential taoCaseThreeLeftB < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseThree_leftB_certificate
  have hContains := evalTaoCaseThreePotentialAtLeftB_contains hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

theorem taoCaseThreePotential_ceiling_neg :
    taoCaseThreePotential taoCaseThreeInputCeiling < 0 := by
  have hPoint := RatInterval.point_contains (27987 / 10000 : Rat)
  have hContains :
      (RatInterval.point (27987 / 10000)).Contains
        taoCaseThreeInputCeiling := by
    simpa only [taoCaseThreeInputCeiling, Rat.cast_div,
      Rat.cast_ofNat] using! hPoint
  exact taoCaseThreePotential_neg_of_interval_certificate
    hContains taoCaseThree_ceiling_certificate

theorem taoCaseThreePotential_neg_on_transition :
    ∀ t ∈ Icc (253 / 100 : ℝ) (51 / 20 : ℝ),
      taoCaseThreePotential t < 0 := by
  intro t ht
  have hContains : (RatInterval.mk (253 / 100) (51 / 20)).Contains t := by
    simpa only [RatInterval.Contains, Rat.cast_div,
      Rat.cast_ofNat] using! ht
  exact taoCaseThreePotential_neg_of_interval_certificate
    hContains taoCaseThree_transition_certificate

private theorem taoCaseThree_left_tangent_neg :
    taoCaseThreePotential (taoCaseThreeTangentPointRat : ℝ) +
      taoCaseThreePotentialDerivative (taoCaseThreeTangentPointRat : ℝ) *
        (taoCaseThreeLeftB - (taoCaseThreeTangentPointRat : ℝ)) < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseThree_left_tangent_certificate
  have hContains := evalTaoCaseThreeTangentInterval_contains hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  have hValue := hContains.2.trans_lt hhiReal
  simpa only [taoCaseThreeLeftB, Rat.cast_div,
    Rat.cast_ofNat] using! hValue

private theorem taoCaseThree_right_tangent_neg :
    taoCaseThreePotential (taoCaseThreeTangentPointRat : ℝ) +
      taoCaseThreePotentialDerivative (taoCaseThreeTangentPointRat : ℝ) *
        ((253 / 100 : ℝ) - (taoCaseThreeTangentPointRat : ℝ)) < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseThree_right_tangent_certificate
  have hContains := evalTaoCaseThreeTangentInterval_contains hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  simpa only [Rat.cast_div, Rat.cast_ofNat] using!
    hContains.2.trans_lt hhiReal

theorem taoCaseThreePotential_neg_on_concave_right :
    ∀ t ∈ Icc taoCaseThreeLeftB (253 / 100 : ℝ),
      taoCaseThreePotential t < 0 := by
  intro t ht
  let q : ℝ := taoCaseThreeTangentPointRat
  have hqOpen : q ∈ Ioo taoCaseThreeLeftB (253 / 100 : ℝ) := by
    constructor <;>
      norm_num [q, taoCaseThreeTangentPointRat, taoCaseThreeLeftB]
  have hq : q ∈ Icc taoCaseThreeLeftB (253 / 100 : ℝ) :=
    ⟨hqOpen.1.le, hqOpen.2.le⟩
  have hqPos : 0 < q := by
    norm_num [q, taoCaseThreeTangentPointRat]
  have hM : taoUpperEdge - q ≠ 0 := by
    have hqM : q < taoUpperEdge := by
      have hqC : q < (253 / 100 : ℝ) := hqOpen.2
      have hCM : (253 / 100 : ℝ) < taoUpperEdge := by
        unfold taoUpperEdge
        nlinarith [seven_fifths_lt_sqrt_two]
      exact hqC.trans hCM
    exact (sub_pos.mpr hqM).ne'
  have ha : taoCaseThreeLeftA - q ≠ 0 := by
    have : taoCaseThreeLeftA < q :=
      tao_case_three_leftA_lt_leftB.trans hqOpen.1
    exact (sub_neg.mpr this).ne
  have hb : taoCaseThreeLeftB - q ≠ 0 :=
    (sub_neg.mpr hqOpen.1).ne
  have hderiv : HasDerivAt taoCaseThreePotential
      (taoCaseThreePotentialDerivative q) q :=
    hasDerivAt_taoCaseThreePotential hqPos.ne' hM ha hb
  have htangent := ConcaveOn.le_tangent_of_hasDerivAt
    taoCaseThreePotential_concaveOn_right hq ht hderiv
  by_cases hD : 0 ≤ taoCaseThreePotentialDerivative q
  · have hdelta : t - q ≤ (253 / 100 : ℝ) - q := by
      linarith [ht.2]
    have hmul := mul_le_mul_of_nonneg_left hdelta hD
    calc
      taoCaseThreePotential t ≤
          taoCaseThreePotential q +
            taoCaseThreePotentialDerivative q * (t - q) := htangent
      _ ≤ taoCaseThreePotential q +
          taoCaseThreePotentialDerivative q *
            ((253 / 100 : ℝ) - q) := by linarith
      _ < 0 := by
        simpa only [q] using! taoCaseThree_right_tangent_neg
  · have hDnonpos : taoCaseThreePotentialDerivative q ≤ 0 :=
      le_of_not_ge hD
    have hdelta : taoCaseThreeLeftB - q ≤ t - q := by
      linarith [ht.1]
    have hmul := mul_le_mul_of_nonpos_left hdelta hDnonpos
    calc
      taoCaseThreePotential t ≤
          taoCaseThreePotential q +
            taoCaseThreePotentialDerivative q * (t - q) := htangent
      _ ≤ taoCaseThreePotential q +
          taoCaseThreePotentialDerivative q *
            (taoCaseThreeLeftB - q) := by linarith
      _ < 0 := by
        simpa only [q] using! taoCaseThree_left_tangent_neg

/-- The complete checked scalar inequality (2.6). -/
theorem taoCaseThreePotential_neg_on_input :
    ∀ t ∈ Icc taoCaseThreeInputFloor taoCaseThreeInputCeiling,
      taoCaseThreePotential t < 0 := by
  intro t ht
  by_cases hta : t ≤ taoCaseThreeLeftA
  · have hle := taoCaseThreePotential_convexOn_left.le_max_of_mem_Icc
      ⟨le_rfl, tao_case_three_inputFloor_lt_leftA.le⟩
      ⟨tao_case_three_inputFloor_lt_leftA.le, le_rfl⟩
      ⟨ht.1, hta⟩
    exact hle.trans_lt (max_lt taoCaseThreePotential_floor_neg
      taoCaseThreePotential_leftA_neg)
  · have hat : taoCaseThreeLeftA < t := lt_of_not_ge hta
    by_cases htb : t ≤ taoCaseThreeLeftB
    · exact (taoCaseThreePotential_strictMonoOn_middle.monotoneOn
        ⟨hat.le, htb⟩
        ⟨tao_case_three_leftA_lt_leftB.le, le_rfl⟩ htb).trans_lt
          taoCaseThreePotential_leftB_neg
    · have hbt : taoCaseThreeLeftB < t := lt_of_not_ge htb
      by_cases htc : t ≤ (253 / 100 : ℝ)
      · exact taoCaseThreePotential_neg_on_concave_right t ⟨hbt.le, htc⟩
      · have hct : (253 / 100 : ℝ) < t := lt_of_not_ge htc
        by_cases htd : t ≤ (51 / 20 : ℝ)
        · exact taoCaseThreePotential_neg_on_transition t ⟨hct.le, htd⟩
        · have hdt : (51 / 20 : ℝ) < t := lt_of_not_ge htd
          have hDneg : taoCaseThreePotential (51 / 20 : ℝ) < 0 :=
            taoCaseThreePotential_neg_on_transition _ ⟨by norm_num, le_rfl⟩
          have hle := taoCaseThreePotential_convexOn_upper.le_max_of_mem_Icc
            ⟨le_rfl, tao_case_three_transitionHigh_lt_inputCeiling.le⟩
            ⟨tao_case_three_transitionHigh_lt_inputCeiling.le, le_rfl⟩
            ⟨hdt.le, ht.2⟩
          exact hle.trans_lt (max_lt hDneg
            taoCaseThreePotential_ceiling_neg)

/-- Complete Case 3 trial-potential conclusion on every translated root
interval in the third parameter range. -/
theorem tao_case_three_trial_potential_neg
    {t0 : ℝ}
    (ht0Lower : taoCaseThreeCenterFloor ≤ t0)
    (ht0Upper : t0 ≤ taoCaseThreeCenterCeiling) :
    ∀ t ∈ Icc (t0 - 1) (t0 + 1),
      taoTwoIntervalEndpointTrialPotential
        taoCaseThreeA taoCaseThreeLeftA
        taoCaseThreeB taoCaseThreeLeftB
        taoCaseThreeC taoUpperEdge t < 0 :=
  tao_case_three_reduction taoCaseThreePotential_neg_on_input
    ht0Lower ht0Upper

end

end Erdos1038
