import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusBasisGeometric
import Wikipedia.HopfProblem.CuspCentralCohomologyEvaluation

/-!
# Native cohomology classes dual to the three named double curves

The native degree-two cohomology classes are obtained from the canonical
evaluation isomorphism and the already established geometric homology
coordinates. Those coordinates come from the literal named double-curve
fundamental classes and the actual base-torus section. No new coordinate
equivalence or replacement definition of cohomology is introduced.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open ToricSpace CuspRetraction CuspCentralHomology
open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : SmallDrift C r)

/-- The native cohomology class dual to the indicated literal named
double curve in the fixed geometric four-element homology basis. -/
def doubleCurveDualClass (j : Fin 3) : SingularCohomology (QuotientCentralFibre C r) 2 :=
  (centralEvaluationEquiv C r hr hC 2).symm
    ((LinearMap.proj j.castSucc : (Fin 4 → ℤ) →ₗ[ℤ] ℤ).comp
      (baseTorusH2Coordinates C r hr hr1 hC hR).toLinearMap)

theorem doubleCurveDualClass_evaluation (j : Fin 3) :
    centralEvaluationEquiv C r hr hC 2 (doubleCurveDualClass C r hr hr1 hC hR j) =
      (LinearMap.proj j.castSucc : (Fin 4 → ℤ) →ₗ[ℤ] ℤ).comp
        (baseTorusH2Coordinates C r hr hr1 hC hR).toLinearMap :=
  (centralEvaluationEquiv C r hr hC 2).apply_symm_apply _

/-- Evaluation is exactly the named curve's coordinate in the already
proved geometric homology marking. -/
@[simp] theorem doubleCurveDualClass_evaluate (j : Fin 3)
    (a : SingularHomology (QuotientCentralFibre C r) 2) :
    singularEvaluation (QuotientCentralFibre C r) 2
      (doubleCurveDualClass C r hr hr1 hC hR j) a =
      baseTorusH2Coordinates C r hr hr1 hC hR a j.castSucc :=
  LinearMap.congr_fun (doubleCurveDualClass_evaluation C r hr hr1 hC hR j) a

@[simp] theorem doubleCurveDualClass_evaluate_curve (j k : Fin 3) :
    singularEvaluation (QuotientCentralFibre C r) 2
      (doubleCurveDualClass C r hr hr1 hC hR j)
      (centralDoubleCurveH2Class C r hr hr1 hC hR k) = if j = k then 1 else 0 := by
  rw [doubleCurveDualClass_evaluate, baseTorusH2Coordinates_curve]
  simp [Pi.single_apply]

/-- The coefficients are computed on the literal named curve's own
oriented fundamental class, pushed forward by its actual inclusion. -/
@[simp] theorem doubleCurveDualClass_evaluate_namedCurve (j k : Fin 3) :
    singularEvaluation (QuotientCentralFibre C r) 2
      (doubleCurveDualClass C r hr hr1 hC hR j)
      (singularHomologyMap (centralDoubleCurveCentralInclusion C r hr k) 2
        (centralDoubleCurveOrientedFundamentalClass C r hr hr1 hC hR k)) =
      if j = k then 1 else 0 := by
  rw [centralDoubleCurveCentralInclusion_fundamentalClass,
    doubleCurveDualClass_evaluate_curve]

/-- Naturality gives the same coefficient for the native cohomology
pullback to the named curve itself. -/
@[simp] theorem doubleCurveDualClass_pullback_evaluate_namedCurve (j k : Fin 3) :
    singularEvaluation (CuspQuotient.doubleCurve C r hr k) 2
      (singularCohomologyPullback (centralDoubleCurveCentralInclusion C r hr k) 2
        (doubleCurveDualClass C r hr hr1 hC hR j))
      (centralDoubleCurveOrientedFundamentalClass C r hr hr1 hC hR k) =
      if j = k then 1 else 0 := by
  rw [singularEvaluation_naturality, doubleCurveDualClass_evaluate_namedCurve]

/-- The named curve dual classes all vanish on the actual base-torus class. -/
@[simp] theorem doubleCurveDualClass_evaluate_base (j : Fin 3) :
    singularEvaluation (QuotientCentralFibre C r) 2
      (doubleCurveDualClass C r hr hr1 hC hR j) (baseTorusH2Class C r hr) = 0 := by
  rw [doubleCurveDualClass_evaluate, baseTorusH2Coordinates_base]
  fin_cases j <;> simp

theorem doubleCurveDualClass_evaluate_basis (j : Fin 3) (k : Fin 4) :
    singularEvaluation (QuotientCentralFibre C r) 2
      (doubleCurveDualClass C r hr hr1 hC hR j)
      (baseTorusH2Basis C r hr hr1 hC hR k) = if j.castSucc = k then 1 else 0 := by
  rw [doubleCurveDualClass_evaluate, baseTorusH2Basis_apply]
  change ((baseTorusH2CoordinateAssembly C r hr hr1 hC hR).symm
    (baseTorusH2CoordinateAssembly C r hr hr1 hC hR (Pi.single k 1))) j.castSucc = _
  rw [LinearEquiv.symm_apply_apply]
  simp [Pi.single_apply, eq_comm]

/-- The existing geometric coordinates retain every actual boundary
coordinate and give zero in the actual base-torus coordinate. -/
theorem baseTorusH2Coordinates_boundary
    (a : SingularHomology (centralBoundary C r hr) 2) :
    baseTorusH2Coordinates C r hr hr1 hC hR (boundaryH2Inclusion C r hr a) =
      ![(centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR a) 0,
        (centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR a) 1,
        (centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR a) 2, 0] := by
  apply (baseTorusH2CoordinateAssembly C r hr hr1 hC hR).injective
  change baseTorusH2CoordinateAssembly C r hr hr1 hC hR
    ((baseTorusH2CoordinateAssembly C r hr hr1 hC hR).symm (boundaryH2Inclusion C r hr a)) = _
  rw [LinearEquiv.apply_symm_apply, baseTorusH2CoordinateAssembly_apply]
  have hv :
      (![(centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR a) 0,
        (centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR a) 1,
        (centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR a) 2] : Fin 3 → ℤ) =
      centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR a := by
    funext j
    fin_cases j <;> rfl
  change boundaryH2Inclusion C r hr a =
    boundaryH2Inclusion C r hr
      ((centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR).symm
        ![(centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR a) 0,
          (centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR a) 1,
          (centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR a) 2]) +
      baseTorusSectionHomologyMap C r hr 2 (baseTorusH2Marking.symm 0)
  rw [hv, LinearEquiv.symm_apply_apply, map_zero, map_zero, add_zero]

/-- On an arbitrary actual boundary class, evaluation is the fixed
geometric boundary coordinate, with its previously established sign. -/
theorem doubleCurveDualClass_evaluate_boundary (j : Fin 3)
    (a : SingularHomology (centralBoundary C r hr) 2) :
    singularEvaluation (QuotientCentralFibre C r) 2
      (doubleCurveDualClass C r hr hr1 hC hR j)
      (singularHomologyMap (centralBoundaryInclusion C r hr) 2 a) =
      centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR a j := by
  rw [doubleCurveDualClass_evaluate]
  change baseTorusH2Coordinates C r hr hr1 hC hR (boundaryH2Inclusion C r hr a) j.castSucc = _
  rw [baseTorusH2Coordinates_boundary]
  fin_cases j <;> rfl

end Wikipedia.HopfProblem.CuspCentralCohomology
