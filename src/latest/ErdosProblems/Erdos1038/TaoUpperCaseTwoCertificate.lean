import ErdosProblems.Erdos1038.TaoUpperCasesTwoThreeInterval
import ErdosProblems.Erdos1038.KernelDecision
import Mathlib.Analysis.Convex.Deriv

set_option maxRecDepth 100000

/-!
# Complete checked scalar certificate for Tao's Case 2

The interval-density scalar (2.5) is convex to the left of the density
endpoint, concave between that endpoint and `2 * sqrt 2`, and convex for
one further unit.  A checked supporting tangent handles the only shallow
maximum.  Beyond that compact range the analytic tail estimate from
`TaoUpperCasesTwoThreeAnalysis` applies.
-/

open Set

namespace Erdos1038

noncomputable section

def taoCaseTwoTangentPointRat : Rat := 618079 / 250000

theorem taoCaseTwoTangentPoint_eq :
    (taoCaseTwoTangentPointRat : ℝ) = (2472316 / 1000000 : ℝ) := by
  norm_num [taoCaseTwoTangentPointRat]

theorem taoCaseTwo_floor_certificate :
    ∃ R, evalTaoCaseTwoPotentialInterval 50
        (RatInterval.point (7987 / 10000)) = some R ∧ R.hi < 0 := by
  kernel_decide

theorem taoCaseTwo_leftEndpoint_certificate :
    ∃ R, evalTaoCaseTwoPotentialAtLeftEndpoint 50 = some R ∧
      R.hi < 0 := by
  kernel_decide

theorem taoCaseTwo_upperEdge_certificate :
    ∃ R, evalTaoCaseTwoPotentialAtUpperEdge 50 = some R ∧
      R.hi < 0 := by
  kernel_decide

theorem taoCaseTwo_tangent_derivative_certificate :
    ∃ R, evalTaoCaseTwoDerivativeInterval 50
        (RatInterval.point taoCaseTwoTangentPointRat) = some R ∧
      R.hi < 0 := by
  kernel_decide

theorem taoCaseTwo_left_tangent_certificate :
    ∃ R, evalTaoCaseTwoLeftTangentInterval 50
        taoCaseTwoTangentPointRat = some R ∧ R.hi < 0 := by
  kernel_decide

theorem taoCaseTwoPotential_floor_neg :
    taoCaseTwoPotential taoCaseTwoFloor < 0 := by
  have hPoint := RatInterval.point_contains (7987 / 10000 : Rat)
  have hContains :
      (RatInterval.point (7987 / 10000)).Contains taoCaseTwoFloor := by
    simpa only [taoCaseTwoFloor, Rat.cast_div, Rat.cast_ofNat] using! hPoint
  exact taoCaseTwoPotential_neg_of_interval_certificate
    hContains taoCaseTwo_floor_certificate

theorem taoCaseTwoPotential_leftEndpoint_neg :
    taoCaseTwoPotential taoCaseTwoLeftEndpoint < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseTwo_leftEndpoint_certificate
  have hContains := evalTaoCaseTwoPotentialAtLeftEndpoint_contains hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

theorem taoCaseTwoPotential_upperEdge_neg :
    taoCaseTwoPotential taoUpperEdge < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseTwo_upperEdge_certificate
  have hContains := evalTaoCaseTwoPotentialAtUpperEdge_contains hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

theorem taoCaseTwoPotentialDerivative_tangentPoint_neg :
    taoCaseTwoPotentialDerivative (taoCaseTwoTangentPointRat : ℝ) < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseTwo_tangent_derivative_certificate
  have hContains := evalTaoCaseTwoDerivativeInterval_contains
    (RatInterval.point_contains taoCaseTwoTangentPointRat) hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

theorem taoCaseTwoPotential_leftTangent_neg :
    taoCaseTwoPotential (taoCaseTwoTangentPointRat : ℝ) +
        taoCaseTwoPotentialDerivative (taoCaseTwoTangentPointRat : ℝ) *
          (taoCaseTwoLeftEndpoint - (taoCaseTwoTangentPointRat : ℝ)) < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseTwo_left_tangent_certificate
  have hContains := evalTaoCaseTwoLeftTangentInterval_contains hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

/-- A differentiable concave function lies below each of its tangent
lines.  This real-variable form avoids introducing subgradient machinery. -/
theorem ConcaveOn.le_tangent_of_hasDerivAt
    {S : Set ℝ} {f : ℝ → ℝ} {q x d : ℝ}
    (hconc : ConcaveOn ℝ S f) (hq : q ∈ S) (hx : x ∈ S)
    (hderiv : HasDerivAt f d q) :
    f x ≤ f q + d * (x - q) := by
  rcases lt_trichotomy x q with hxq | rfl | hqx
  · have hs := hconc.deriv_le_slope hx hq hxq hderiv.differentiableAt
    rw [hderiv.deriv] at hs
    have hqsub : 0 < q - x := sub_pos.mpr hxq
    have hne : q - x ≠ 0 := hqsub.ne'
    have hslope : (q - x) * slope f x q = f q - f x := by
      rw [slope, vsub_eq_sub, smul_eq_mul]
      field_simp [hne]
    have hmul := mul_le_mul_of_nonneg_left hs hqsub.le
    rw [hslope] at hmul
    nlinarith
  · simp
  · have hs := hconc.slope_le_deriv hq hx hqx hderiv.differentiableAt
    rw [hderiv.deriv] at hs
    have hxsub : 0 < x - q := sub_pos.mpr hqx
    have hne : x - q ≠ 0 := hxsub.ne'
    have hslope : (x - q) * slope f q x = f x - f q := by
      rw [slope, vsub_eq_sub, smul_eq_mul]
      field_simp [hne]
    have hmul := mul_le_mul_of_nonneg_left hs hxsub.le
    rw [hslope] at hmul
    nlinarith

theorem tao_case_two_tangentPoint_mem_middle :
    (taoCaseTwoTangentPointRat : ℝ) ∈
      Ioo taoCaseTwoLeftEndpoint taoUpperEdge := by
  constructor
  · norm_num [taoCaseTwoTangentPointRat, taoCaseTwoLeftEndpoint]
  · rw [taoCaseTwoTangentPoint_eq]
    unfold taoUpperEdge
    nlinarith [seven_fifths_lt_sqrt_two]

theorem taoCaseTwoPotential_neg_on_middle :
    ∀ t ∈ Icc taoCaseTwoLeftEndpoint taoUpperEdge,
      taoCaseTwoPotential t < 0 := by
  intro t ht
  let q : ℝ := taoCaseTwoTangentPointRat
  have hq : q ∈ Icc taoCaseTwoLeftEndpoint taoUpperEdge :=
    ⟨tao_case_two_tangentPoint_mem_middle.1.le,
      tao_case_two_tangentPoint_mem_middle.2.le⟩
  have hqPos : 0 < q := by
    exact (show 0 < taoCaseTwoLeftEndpoint by
      norm_num [taoCaseTwoLeftEndpoint]).trans
        tao_case_two_tangentPoint_mem_middle.1
  have hMne : taoUpperEdge - q ≠ 0 :=
    (sub_pos.mpr tao_case_two_tangentPoint_mem_middle.2).ne'
  have hane : taoCaseTwoLeftEndpoint - q ≠ 0 :=
    (sub_neg.mpr tao_case_two_tangentPoint_mem_middle.1).ne
  have hderiv : HasDerivAt taoCaseTwoPotential
      (taoCaseTwoPotentialDerivative q) q :=
    hasDerivAt_taoCaseTwoPotential hqPos.ne' hMne hane
  have htangent := ConcaveOn.le_tangent_of_hasDerivAt
    taoCaseTwoPotential_concaveOn_middle hq ht hderiv
  have hDneg : taoCaseTwoPotentialDerivative q < 0 := by
    simpa only [q] using! taoCaseTwoPotentialDerivative_tangentPoint_neg
  have hleftTangent :
      taoCaseTwoPotential q + taoCaseTwoPotentialDerivative q *
          (taoCaseTwoLeftEndpoint - q) < 0 := by
    simpa only [q] using! taoCaseTwoPotential_leftTangent_neg
  by_cases htq : t ≤ q
  · have hdelta : taoCaseTwoLeftEndpoint - q ≤ t - q := by
      linarith [ht.1]
    have hmul := mul_le_mul_of_nonpos_left hdelta hDneg.le
    exact htangent.trans_lt (by linarith)
  · have hqt : q < t := lt_of_not_ge htq
    have hmul : taoCaseTwoPotentialDerivative q * (t - q) < 0 :=
      mul_neg_of_neg_of_pos hDneg (sub_pos.mpr hqt)
    have hqNeg : taoCaseTwoPotential q < 0 := by
      have hleftDelta : taoCaseTwoLeftEndpoint - q < 0 :=
        sub_neg.mpr tao_case_two_tangentPoint_mem_middle.1
      have hleftProduct :
          0 < taoCaseTwoPotentialDerivative q *
            (taoCaseTwoLeftEndpoint - q) :=
        mul_pos_of_neg_of_neg hDneg hleftDelta
      linarith
    exact htangent.trans_lt (by linarith)

theorem taoCaseTwoPotential_neg_on_compact :
    ∀ t ∈ Icc taoCaseTwoFloor (taoUpperEdge + 1),
      taoCaseTwoPotential t < 0 := by
  intro t ht
  by_cases hta : t ≤ taoCaseTwoLeftEndpoint
  · have hle := taoCaseTwoPotential_convexOn_left.le_max_of_mem_Icc
      ⟨le_rfl, tao_case_two_floor_lt_leftEndpoint.le⟩
      ⟨tao_case_two_floor_lt_leftEndpoint.le, le_rfl⟩
      ⟨ht.1, hta⟩
    exact hle.trans_lt (max_lt taoCaseTwoPotential_floor_neg
      taoCaseTwoPotential_leftEndpoint_neg)
  · have hat : taoCaseTwoLeftEndpoint < t := lt_of_not_ge hta
    by_cases htM : t ≤ taoUpperEdge
    · exact taoCaseTwoPotential_neg_on_middle t ⟨hat.le, htM⟩
    · have hMt : taoUpperEdge < t := lt_of_not_ge htM
      have hle := taoCaseTwoPotential_convexOn_right.le_max_of_mem_Icc
        ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
        ⟨hMt.le, ht.2⟩
      have hrightNeg : taoCaseTwoPotential (taoUpperEdge + 1) < 0 :=
        taoCaseTwoPotential_neg_of_upperEdge_add_one_le le_rfl
      exact hle.trans_lt (max_lt taoCaseTwoPotential_upperEdge_neg hrightNeg)

/-- The complete scalar inequality (2.5), including its infinite tail. -/
theorem taoCaseTwoPotential_neg_of_floor_le :
    ∀ t, taoCaseTwoFloor ≤ t → taoCaseTwoPotential t < 0 :=
  tao_case_two_of_compact_certificate taoCaseTwoPotential_neg_on_compact

/-- Complete Case 2 trial-potential conclusion on every translated root
interval with center at least `1.7987`. -/
theorem tao_case_two_trial_potential_neg
    {t0 : ℝ} (ht0 : taoCaseTwoCenterFloor ≤ t0) :
    ∀ t ∈ Icc (t0 - 1) (t0 + 1),
      taoPointIntervalTrialPotential taoCaseTwoA
        taoCaseTwoLeftEndpoint taoUpperEdge t < 0 :=
  tao_case_two_reduction taoCaseTwoPotential_neg_of_floor_le ht0

end

end Erdos1038
