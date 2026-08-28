import Wikipedia.HopfProblem.CuspCentralCohomologyEvaluation
import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusBasisGeometric

/-!
# The native cohomology class dual to the actual base torus

The class is defined in native singular cohomology by pulling the
oriented generator of the marked two-torus back along the actual base
projection. Naturality of the canonical evaluation pairing identifies
it with the dual of the geometric base-torus functional. It evaluates
to one on the actual base section and to zero on the three literal
named double-curve fundamental classes.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open ToricSpace CuspRetraction CuspCentralHomology
open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology

/-- Canonical evaluation for the native degree-two cohomology of the
actual marked base two-torus. -/
def baseTorusEvaluationEquiv :
    SingularCohomology (ProductTorus 2) 2 ≃ₗ[ℤ]
      Module.Dual ℤ (SingularHomology (ProductTorus 2) 2) := by
  letI (n : ℕ) : Module.Projective ℤ (SingularHomology (ProductTorus 2) n) := by
    let := productTorus_homology_free 2 n
    infer_instance
  exact singularEvaluationEquiv (ProductTorus 2) 2

@[simp] theorem baseTorusEvaluationEquiv_apply
    (a : SingularCohomology (ProductTorus 2) 2) :
    baseTorusEvaluationEquiv a = singularEvaluation (ProductTorus 2) 2 a := rfl

/-- The native cohomology generator dual to the fixed top class of the
marked base two-torus. -/
def baseTorusTopCohomologyClass : SingularCohomology (ProductTorus 2) 2 :=
  baseTorusEvaluationEquiv.symm baseTorusH2Marking.toLinearMap

@[simp] theorem baseTorusTopCohomologyClass_evaluate
    (a : SingularHomology (ProductTorus 2) 2) :
    singularEvaluation (ProductTorus 2) 2 baseTorusTopCohomologyClass a =
      baseTorusH2Marking a := by
  change baseTorusEvaluationEquiv
    (baseTorusEvaluationEquiv.symm baseTorusH2Marking.toLinearMap) a = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

/-- The actual native class `T_B^∨`, defined by the geometric base
projection rather than by a replacement cohomology group. -/
def baseTorusDualClass : SingularCohomology (QuotientCentralFibre C r) 2 :=
  singularCohomologyPullback (baseTorusProjectionMap C r hr hC) 2
    baseTorusTopCohomologyClass

/-- Evaluation is the actual base-projection functional on integral homology. -/
@[simp] theorem baseTorusDualClass_evaluate
    (a : SingularHomology (QuotientCentralFibre C r) 2) :
    singularEvaluation (QuotientCentralFibre C r) 2 (baseTorusDualClass C r hr hC) a =
      baseTorusH2Functional C r hr hC a := by
  rw [baseTorusDualClass, singularEvaluation_naturality, baseTorusTopCohomologyClass_evaluate]
  rfl

theorem baseTorusDualClass_evaluation :
    centralEvaluationEquiv C r hr hC 2 (baseTorusDualClass C r hr hC) =
      baseTorusH2Functional C r hr hC := by
  apply LinearMap.ext
  intro a
  exact baseTorusDualClass_evaluate C r hr hC a

/-- This is exactly the native class corresponding to the geometric
dual functional under the proved canonical evaluation isomorphism. -/
theorem baseTorusDualClass_eq_evaluationDual :
    baseTorusDualClass C r hr hC =
      (centralEvaluationEquiv C r hr hC 2).symm (baseTorusH2Functional C r hr hC) := by
  apply (centralEvaluationEquiv C r hr hC 2).injective
  rw [LinearEquiv.apply_symm_apply, baseTorusDualClass_evaluation]

/-- The actual base-section top class has coefficient one. -/
@[simp] theorem baseTorusDualClass_evaluate_base :
    singularEvaluation (QuotientCentralFibre C r) 2 (baseTorusDualClass C r hr hC)
      (baseTorusH2Class C r hr) = 1 := by
  rw [baseTorusDualClass_evaluate, baseTorusH2Functional_class]

variable (hr1 : r < 1) (hR : SmallDrift C r)

include hr1 hR

/-- The full actual double-locus image is annihilated. -/
theorem baseTorusDualClass_evaluate_boundary
    (a : SingularHomology (centralBoundary C r hr) 2) :
    singularEvaluation (QuotientCentralFibre C r) 2 (baseTorusDualClass C r hr hC)
      (singularHomologyMap (centralBoundaryInclusion C r hr) 2 a) = 0 := by
  rw [baseTorusDualClass_evaluate]
  exact baseTorusH2Functional_boundary C r hr hC hr1 hR a

/-- In particular the three named geometric curve generators have coefficient zero. -/
@[simp] theorem baseTorusDualClass_evaluate_namedCurve (j : Fin 3) :
    singularEvaluation (QuotientCentralFibre C r) 2 (baseTorusDualClass C r hr hC)
      (singularHomologyMap (centralDoubleCurveCentralInclusion C r hr j) 2
        (centralDoubleCurveOrientedFundamentalClass C r hr hr1 hC hR j)) = 0 := by
  rw [centralDoubleCurveCentralInclusion_fundamentalClass]
  exact baseTorusDualClass_evaluate_boundary C r hr hC hr1 hR
    (centralDoubleCurveFundamentalClass C r hr hr1 hC hR j)

/-- The class is the fourth dual coordinate of the actual geometric basis. -/
theorem baseTorusDualClass_evaluate_basis_first (j : Fin 3) :
    singularEvaluation (QuotientCentralFibre C r) 2 (baseTorusDualClass C r hr hC)
      (baseTorusH2Basis C r hr hr1 hC hR j.castSucc) = 0 := by
  rw [baseTorusH2Basis_namedCurve]
  exact baseTorusDualClass_evaluate_namedCurve C r hr hC hr1 hR j

@[simp] theorem baseTorusDualClass_evaluate_basis_last :
    singularEvaluation (QuotientCentralFibre C r) 2 (baseTorusDualClass C r hr hC)
      (baseTorusH2Basis C r hr hr1 hC hR 3) = 1 := by
  rw [baseTorusH2Basis_last, baseTorusDualClass_evaluate_base]

end Wikipedia.HopfProblem.CuspCentralCohomology
