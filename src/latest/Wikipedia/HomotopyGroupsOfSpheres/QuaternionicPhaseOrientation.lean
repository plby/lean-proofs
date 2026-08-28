import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPhaseDifferential
import Mathlib.Topology.Order.IntermediateValue

/-!
# The phase-family differentials have the same orientation

Compare each derivative with the derivative at phase zero. These are
automorphisms of one fixed seven-dimensional real space. Their determinants
are continuous and nonzero, and equal one at phase zero, so they stay positive.
This is an orientation comparison, not a calculation of the total degree.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix

def phaseDerivativeComparison (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) : ParameterSpace z →L[ℝ] ParameterSpace z :=
  (phaseDerivativeEquiv z hz 0).symm.toContinuousLinearMap.comp
    (fderiv ℝ (phaseCoordinates z a) 0)

def phaseDerivativeComparisonEquiv (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) : ParameterSpace z ≃L[ℝ] ParameterSpace z :=
  (phaseDerivativeEquiv z hz a).trans (phaseDerivativeEquiv z hz 0).symm

theorem phaseDerivativeComparisonEquiv_coe (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) :
    (phaseDerivativeComparisonEquiv z hz a : ParameterSpace z →L[ℝ] ParameterSpace z) =
      phaseDerivativeComparison z hz a := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem phaseDerivativeComparison_zero (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    phaseDerivativeComparison z hz 0 = ContinuousLinearMap.id ℝ (ParameterSpace z) := by
  apply ContinuousLinearMap.ext
  intro v
  exact (phaseDerivativeEquiv z hz 0).symm_apply_apply v

theorem continuous_phaseDerivativeComparison (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    Continuous (phaseDerivativeComparison z hz) :=
  continuous_const.clm_comp (continuous_phaseDerivative z hz)

theorem phaseDerivativeComparison_det_ne_zero (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) : (phaseDerivativeComparison z hz a).det ≠ 0 := by
  rw [← phaseDerivativeComparisonEquiv_coe]
  exact (phaseDerivativeComparisonEquiv z hz a).toLinearEquiv.isUnit_det'.ne_zero

theorem phaseDerivativeComparison_det_pos (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) : 0 < (phaseDerivativeComparison z hz a).det := by
  have hc : Continuous (fun t : ℝ ↦ (phaseDerivativeComparison z hz t).det) :=
    ContinuousLinearMap.continuous_det.comp (continuous_phaseDerivativeComparison z hz)
  have h0 : (phaseDerivativeComparison z hz 0).det = 1 := by
    rw [phaseDerivativeComparison_zero]
    exact LinearMap.det_id
  by_contra h
  have ha : (phaseDerivativeComparison z hz a).det ≤ 0 := le_of_not_gt h
  have hmem : (0 : ℝ) ∈ Set.Icc (phaseDerivativeComparison z hz a).det
      (phaseDerivativeComparison z hz 0).det := ⟨ha, by rw [h0]; norm_num⟩
  obtain ⟨b, hb⟩ := intermediate_value_univ a 0 hc hmem
  exact phaseDerivativeComparison_det_ne_zero z hz b hb

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
