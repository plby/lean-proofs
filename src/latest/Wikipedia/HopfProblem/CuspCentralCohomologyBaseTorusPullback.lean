import Wikipedia.HopfProblem.CuspCentralCohomologyBaseTorus
import Wikipedia.HopfProblem.CuspCentralCohomologyBaseProjection
import Wikipedia.HopfProblem.CuspCentralCohomologyCoordinatesGenerators

/-!
# The actual marked pullback of the base-torus dual class

The geometric base projection composed with the actual marked collapse
is the first-two-coordinate projection. Its proved homology formula,
together with naturality of native singular-cohomology evaluation,
identifies the pullback of `T_B^∨` with the pure ordered dual-minor class
labelled `γu`. The statement concerns actual native pullbacks, not only
membership in a rank-four invariant submodule.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open CuspRetraction CuspCentralHomology.SpecializationModel
open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

/-- The native pullback evaluates as precisely the first ordered minor. -/
theorem baseTorusDualClass_markedPullback_evaluate
    (a : SingularHomology (ProductTorus 4) 2) :
    singularEvaluation (ProductTorus 4) 2
      (singularCohomologyPullback (markedCollapse C r hr) 2
        (baseTorusDualClass C r hr hC)) a = coordinateTorusH2Coordinates a 0 := by
  rw [singularEvaluation_naturality, baseTorusDualClass_evaluate]
  exact baseTorusH2Functional_markedCollapse C r hr hC a

/-- Exact native cohomology coordinates, including the positive unit coefficient. -/
theorem baseTorusDualClass_markedPullback_coordinates :
    coordinateTorusH2CohomologyCoordinates
      (singularCohomologyPullback (markedCollapse C r hr) 2
        (baseTorusDualClass C r hr hC)) = Pi.single 0 1 := by
  funext i
  change coordinateTorusCohomologyCoordinates 2 coordinateTorusH2Coordinates _ i = _
  rw [coordinateTorusCohomologyCoordinates_apply_coordinate,
    baseTorusDualClass_markedPullback_evaluate, LinearEquiv.apply_symm_apply]
  by_cases hi : i = 0
  · subst i
    simp
  · simp [hi, Ne.symm hi]

/-- The displayed source class is the actual evaluation-dual `γu` class. -/
theorem baseTorusDualClass_markedPullback :
    singularCohomologyPullback (markedCollapse C r hr) 2
      (baseTorusDualClass C r hr hC) = coordinateTorusH2DualClass 0 := by
  apply coordinateTorusH2CohomologyCoordinates.injective
  rw [baseTorusDualClass_markedPullback_coordinates, coordinateTorusH2DualClass_coordinates]

theorem baseTorusDualClass_markedPullback_coordinateVector :
    coordinateTorusH2CohomologyCoordinates
      (singularCohomologyPullback (markedCollapse C r hr) 2
        (baseTorusDualClass C r hr hC)) = ![1, 0, 0, 0, 0, 0] := by
  rw [baseTorusDualClass_markedPullback_coordinates]
  funext i
  fin_cases i <;> rfl

end Wikipedia.HopfProblem.CuspCentralCohomology
