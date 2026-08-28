import Wikipedia.HopfProblem.PeriodTorusCohomologyCupEvaluation
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupDecomposition
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupFormal
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingEta

/-!
# The original native η class is the constructed cup cocycle

The already defined distinguished integral class is identified with the
explicit Alexander--Whitney cocycle by evaluation on every genuine pair
of positive period loops.  Thus its native cup square has the exact
formal-prism evaluation in the declared real period orientation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin SingularCohomologyCup
open PeriodTorusCohomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- Exact periods identify the original native class with the actual cup-cocycle pullback. -/
theorem etaClass_eq_coordinate_pullback (p : PeriodDomain) :
    etaClass p =
      singularCohomologyPullback (periodTorusCircleHomeomorph p : C(_, _)) 2
        coordinateEtaClass := by
  apply cohomology_ext_periodLoops p
  intro x y
  rw [etaClass_evaluate_periodLoops, coordinateEtaPullback_pair_evaluation,
    formalEtaEvaluation_periodProduct]

/-- The distinguished native class is the stated sum of actual positive degree-one cups. -/
theorem etaClass_eq_periodCups (p : PeriodDomain) :
    etaClass p =
      cupProduct p.Torus 1 1 (periodOneClass p 1) (periodOneClass p 2) +
        (6 : ℤ) • cupProduct p.Torus 1 1 (periodOneClass p 0) (periodOneClass p 3) := by
  rw [etaClass_eq_coordinate_pullback, coordinateEtaPullback_eq_cups]

/-- The native η square on the actual positive top generator is the precise formal-prism value. -/
theorem etaCupSquare_formal_evaluation (p : PeriodDomain) :
    singularEvaluation p.Torus 4 (cupProduct p.Torus 2 2 (etaClass p) (etaClass p))
      (positivePeriodTopClass p) = formalEtaSquareEvaluation formalPositiveTop := by
  rw [etaClass_eq_coordinate_pullback]
  exact coordinateEtaPullback_square_top_evaluation p

/-- Evaluation on every actual top class follows from the genuine positive generator. -/
theorem etaCupSquare_formal_evaluation_all (p : PeriodDomain)
    (a : SingularHomology p.Torus 4) :
    singularEvaluation p.Torus 4 (cupProduct p.Torus 2 2 (etaClass p) (etaClass p)) a =
      periodTorusH4Equiv p a * formalEtaSquareEvaluation formalPositiveTop := by
  have h := congrArg
    (singularEvaluation p.Torus 4 (cupProduct p.Torus 2 2 (etaClass p) (etaClass p)))
    (positivePeriodTopClass_spans p a)
  rw [map_zsmul, etaCupSquare_formal_evaluation, zsmul_eq_mul, Int.cast_id] at h
  exact h

/-- The actual native top-degree class is its proved formal-prism multiple of the positive dual. -/
theorem etaCupSquare_eq_formal_multiple (p : PeriodDomain) :
    cupProduct p.Torus 2 2 (etaClass p) (etaClass p) =
      formalEtaSquareEvaluation formalPositiveTop • positivePeriodTopCohomologyClass p := by
  apply (evaluationEquiv p 4).injective
  apply LinearMap.ext
  intro a
  change singularEvaluation p.Torus 4
      (cupProduct p.Torus 2 2 (etaClass p) (etaClass p)) a =
    singularEvaluation p.Torus 4
      (formalEtaSquareEvaluation formalPositiveTop • positivePeriodTopCohomologyClass p) a
  rw [etaCupSquare_formal_evaluation_all, map_zsmul, LinearMap.smul_apply,
    positivePeriodTopCohomologyClass_evaluate, zsmul_eq_mul, Int.cast_id]
  exact mul_comm _ _

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
