import Wikipedia.HopfProblem.PeriodTorusCohomologyCupEta
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupFormalTop

/-!
# The native period-torus cup square

The actual integral singular-cohomology cup square of the distinguished
class evaluates to twelve on the genuine positive product of the four
period loops.  This uses the Alexander--Whitney cup and the realized
prism chains, not a prescribed exterior-algebra multiplication.

The sign refers to the declared real period order `(γ, u, w, δ)`.
No identification with the complex orientation is made here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomology SingularCohomologyCup PeriodTorusCohomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The actual cup square is positive twelve on the positive real period product. -/
theorem etaCupSquare_evaluate_positivePeriodTop (p : PeriodDomain) :
    singularEvaluation p.Torus 4 (cupProduct p.Torus 2 2 (etaClass p) (etaClass p))
      (positivePeriodTopClass p) = 12 :=
  (etaCupSquare_formal_evaluation p).trans formalEtaSquareEvaluation_positiveTop

/-- Evaluation of the native cup square on every actual top-degree homology class. -/
theorem etaCupSquare_evaluate (p : PeriodDomain) (a : SingularHomology p.Torus 4) :
    singularEvaluation p.Torus 4 (cupProduct p.Torus 2 2 (etaClass p) (etaClass p)) a =
      periodTorusH4Equiv p a * 12 := by
  rw [etaCupSquare_formal_evaluation_all, formalEtaSquareEvaluation_positiveTop]

/-- The native square is twelve times the dual of the genuine positive period product. -/
theorem etaCupSquare_eq_twelve (p : PeriodDomain) :
    cupProduct p.Torus 2 2 (etaClass p) (etaClass p) =
      (12 : ℤ) • positivePeriodTopCohomologyClass p :=
  (etaCupSquare_eq_formal_multiple p).trans
    (congrArg (fun n : ℤ => n • positivePeriodTopCohomologyClass p)
      formalEtaSquareEvaluation_positiveTop)

/-- In particular, the actual native cup square does not vanish. -/
theorem etaCupSquare_ne_zero (p : PeriodDomain) :
    cupProduct p.Torus 2 2 (etaClass p) (etaClass p) ≠ 0 := by
  intro h
  have he := etaCupSquare_evaluate_positivePeriodTop p
  rw [h, map_zero, LinearMap.zero_apply] at he
  norm_num at he

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
