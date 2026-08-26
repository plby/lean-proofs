import ErdosProblems.Erdos1038.OneCutNewtonBox
import ErdosProblems.Erdos1038.KernelDecision

set_option maxRecDepth 100000

/-!
# Exact stationary-point endpoint boxes for the one-cut certificate

The two point boxes below lie on opposite sides of the numerical stationary
point.  Their broad root bounds are certified by residual signs, after which
one parametric Newton step gives the narrow root bounds used for the derivative
sign tests.
-/

namespace Erdos1038

noncomputable section

namespace OneCutStationaryBox

def qCenterRat : Rat :=
  2571553686652745032257637166391965344 / 10 ^ 38

def qRadiusRat : Rat := 1 / 10 ^ 31

def qLeftRat : Rat := qCenterRat - qRadiusRat

def qRightRat : Rat := qCenterRat + qRadiusRat

def stationaryBroad (q : Rat) : BulkBox :=
  { q := RatInterval.point q
    zp :=
      ⟨459328250456373452918215 / 10 ^ 24,
        459328250456373452918216 / 10 ^ 24⟩
    zm :=
      ⟨1425299118949901221706180 / 10 ^ 24,
        1425299118949901221706181 / 10 ^ 24⟩ }

def leftNewton : NewtonBulkBox :=
  { broad := stationaryBroad qLeftRat
    plus :=
      { center := 459328250456373452918215392771 / 10 ^ 30
        tight :=
          ⟨45932825045637345291821539277060 / 10 ^ 32,
            45932825045637345291821539277061 / 10 ^ 32⟩ }
    minus :=
      { center := 1425299118949901221706180796514 / 10 ^ 30
        tight :=
          ⟨142529911894990122170618079651392 / 10 ^ 32,
            142529911894990122170618079651393 / 10 ^ 32⟩ } }

def rightNewton : NewtonBulkBox :=
  { broad := stationaryBroad qRightRat
    plus :=
      { center := 459328250456373452918215392770 / 10 ^ 30
        tight :=
          ⟨45932825045637345291821539277024 / 10 ^ 32,
            45932825045637345291821539277025 / 10 ^ 32⟩ }
    minus :=
      { center := 1425299118949901221706180796514 / 10 ^ 30
        tight :=
          ⟨142529911894990122170618079651395 / 10 ^ 32,
            142529911894990122170618079651396 / 10 ^ 32⟩ } }

def stationaryNewton : NewtonBulkBox :=
  { broad :=
      { q := ⟨qLeftRat, qRightRat⟩
        zp :=
          ⟨459328250456373452918215 / 10 ^ 24,
            459328250456373452918216 / 10 ^ 24⟩
        zm :=
          ⟨1425299118949901221706180 / 10 ^ 24,
            1425299118949901221706181 / 10 ^ 24⟩ }
    plus :=
      { center := 459328250456373452918215392770 / 10 ^ 30
        tight :=
          ⟨459328250456373452918215392770 / 10 ^ 30 - 4 / 10 ^ 32,
            459328250456373452918215392770 / 10 ^ 30 + 90 / 10 ^ 32⟩ }
    minus :=
      { center := 1425299118949901221706180796514 / 10 ^ 30
        tight :=
          ⟨1425299118949901221706180796514 / 10 ^ 30 - 133 / 10 ^ 32,
            1425299118949901221706180796514 / 10 ^ 30 + 121 / 10 ^ 32⟩ } }

theorem left_certified : leftNewton.Certified 80 6 := by
  kernel_decide

theorem right_certified : rightNewton.Certified 80 6 := by
  kernel_decide

theorem left_derivative_negative :
    leftNewton.TightNegativeCertified 80 6 := by
  kernel_decide

theorem right_derivative_positive :
    rightNewton.TightPositiveCertified 80 6 := by
  kernel_decide

theorem stationary_certified : stationaryNewton.Certified 80 6 := by
  kernel_decide

theorem stationary_value_certified :
    stationaryNewton.LambdaBetweenCertified 80 6
      lambdaLowerRat lambdaUpperRat := by
  kernel_decide

theorem derivative_negative_at_left :
    LambdaDerivativeFormula (qLeftRat : ℝ) < 0 := by
  apply leftNewton.lambdaDerivativeFormula_neg_of_tight_certified
    left_derivative_negative
  exact RatInterval.point_contains qLeftRat

theorem derivative_positive_at_right :
    0 < LambdaDerivativeFormula (qRightRat : ℝ) := by
  apply rightNewton.lambdaDerivativeFormula_pos_of_tight_certified
    right_derivative_positive
  exact RatInterval.point_contains qRightRat

theorem lambda_between_at_stationary_interval {q : ℝ}
    (hq : (qLeftRat : ℝ) ≤ q ∧ q ≤ (qRightRat : ℝ)) :
    (lambdaLowerRat : ℝ) < Lambda q ∧
      Lambda q < (lambdaUpperRat : ℝ) := by
  exact stationaryNewton.lambda_between_of_certified
    stationary_value_certified hq

end OneCutStationaryBox

end

end Erdos1038
