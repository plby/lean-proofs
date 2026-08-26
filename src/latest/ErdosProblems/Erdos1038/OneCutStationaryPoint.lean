import ErdosProblems.Erdos1038.OneCutSecondDerivative
import ErdosProblems.Erdos1038.OneCutStationaryBox
import ErdosProblems.Erdos1038.KernelDecision

set_option maxRecDepth 100000

/-!
# Construction and uniqueness of the one-cut stationary point
-/

open Set

namespace Erdos1038

noncomputable section

open OneCutStationaryBox

namespace OneCutStationaryPoint

theorem stationary_second_positive_certified :
    stationaryNewton.SecondPositiveCertified 80 6 := by
  kernel_decide

theorem qLeft_lt_qRight : (qLeftRat : ℝ) < (qRightRat : ℝ) := by
  norm_num [qLeftRat, qRightRat, qCenterRat, qRadiusRat]

private theorem stationary_contains {q : ℝ}
    (hq : q ∈ Icc (qLeftRat : ℝ) (qRightRat : ℝ)) :
    stationaryNewton.broad.q.Contains q := by
  exact hq

theorem continuousOn_lambdaDerivativeFormula_stationary :
    ContinuousOn LambdaDerivativeFormula
      (Icc (qLeftRat : ℝ) (qRightRat : ℝ)) := by
  intro q hq
  exact (stationaryNewton.lambdaDerivativeFormula_continuousAt_of_certified
    stationary_second_positive_certified (stationary_contains hq)).continuousWithinAt

theorem strictMonoOn_lambdaDerivativeFormula_stationary :
    StrictMonoOn LambdaDerivativeFormula
      (Icc (qLeftRat : ℝ) (qRightRat : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    continuousOn_lambdaDerivativeFormula_stationary
  intro q hq
  exact stationaryNewton.lambdaDerivativeFormula_deriv_pos_of_certified
    stationary_second_positive_certified
    (stationary_contains (interior_subset hq))

theorem existsUnique_stationaryPoint :
    ∃! c : ℝ,
      c ∈ Ioo (qLeftRat : ℝ) (qRightRat : ℝ) ∧
        LambdaDerivativeFormula c = 0 := by
  have hzeroMem : (0 : ℝ) ∈
      Icc (LambdaDerivativeFormula (qLeftRat : ℝ))
        (LambdaDerivativeFormula (qRightRat : ℝ)) :=
    ⟨OneCutStationaryBox.derivative_negative_at_left.le,
      OneCutStationaryBox.derivative_positive_at_right.le⟩
  obtain ⟨c, hcIcc, hzero⟩ :=
    (intermediate_value_Icc qLeft_lt_qRight.le
      continuousOn_lambdaDerivativeFormula_stationary) hzeroMem
  have hcLeft : (qLeftRat : ℝ) < c := by
    refine lt_of_le_of_ne hcIcc.1 ?_
    intro heq
    rw [← heq] at hzero
    linarith [OneCutStationaryBox.derivative_negative_at_left]
  have hcRight : c < (qRightRat : ℝ) := by
    refine lt_of_le_of_ne hcIcc.2 ?_
    intro heq
    rw [heq] at hzero
    linarith [OneCutStationaryBox.derivative_positive_at_right]
  refine ⟨c, ⟨⟨hcLeft, hcRight⟩, hzero⟩, ?_⟩
  intro d hd
  exact strictMonoOn_lambdaDerivativeFormula_stationary.injOn
    ⟨hd.1.1.le, hd.1.2.le⟩ ⟨hcLeft.le, hcRight.le⟩
    (hd.2.trans hzero.symm)

def c : ℝ := Classical.choose existsUnique_stationaryPoint

theorem c_mem : c ∈ Ioo (qLeftRat : ℝ) (qRightRat : ℝ) :=
  (Classical.choose_spec existsUnique_stationaryPoint).1.1

theorem c_derivative_zero : LambdaDerivativeFormula c = 0 :=
  (Classical.choose_spec existsUnique_stationaryPoint).1.2

theorem derivative_negative_between_left_c {q : ℝ}
    (hq : q ∈ Ioo (qLeftRat : ℝ) c) :
    LambdaDerivativeFormula q < 0 := by
  have hmono := strictMonoOn_lambdaDerivativeFormula_stationary
    ⟨hq.1.le, hq.2.le.trans c_mem.2.le⟩
    ⟨c_mem.1.le, c_mem.2.le⟩ hq.2
  rwa [c_derivative_zero] at hmono

theorem derivative_positive_between_c_right {q : ℝ}
    (hq : q ∈ Ioo c (qRightRat : ℝ)) :
    0 < LambdaDerivativeFormula q := by
  have hmono := strictMonoOn_lambdaDerivativeFormula_stationary
    ⟨c_mem.1.le, c_mem.2.le⟩
    ⟨c_mem.1.le.trans hq.1.le, hq.2.le⟩ hq.1
  rwa [c_derivative_zero] at hmono

theorem c_decimal_box :
    (qStarLowerRat : ℝ) < c ∧ c < (qStarUpperRat : ℝ) := by
  constructor
  · exact (by
      norm_num [qStarLowerRat, qLeftRat, qCenterRat, qRadiusRat] :
        (qStarLowerRat : ℝ) < (qLeftRat : ℝ)).trans c_mem.1
  · exact c_mem.2.trans (by
      norm_num [qStarUpperRat, qRightRat, qCenterRat, qRadiusRat] :
        (qRightRat : ℝ) < (qStarUpperRat : ℝ))

theorem c_lambda_decimal_box :
    (lambdaLowerRat : ℝ) < Lambda c ∧
      Lambda c < (lambdaUpperRat : ℝ) :=
  OneCutStationaryBox.lambda_between_at_stationary_interval
    ⟨c_mem.1.le, c_mem.2.le⟩

end OneCutStationaryPoint

end

end Erdos1038
