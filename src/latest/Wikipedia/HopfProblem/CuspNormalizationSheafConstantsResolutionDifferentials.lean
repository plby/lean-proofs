import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionSums
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionEndpoints

/-!
# The actual alternating endpoint differential on constants

The last differential is assembled from the independently defined
constant-sheaf evaluations at the two actual triple points.  Its signs
are the source's `g₁ - g₂ + g₃`, in the same source ordering as the
holomorphic sequence. No complex identity or exactness is assumed.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff ZeroObject

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The independent actual constant evaluation is onto the actual
single-point skyscraper, with no analytic hypotheses on the cusp atlas. -/
instance curveConstantEvaluation_epi (k : Fin 3) (t : Fin 2) :
    Epi (curveConstantEvaluation C ε hε k t) :=
  SheafConstants.constantEvaluationAt_epi (sourceCurveMap C ε hε k)
    (curveTriplePoint C ε hε k t) (triplePoint C ε hε t)
    (sourceCurveMap_curveTriplePoint C ε hε k t)

/-- Actual signed constant evaluation at one of the actual triple points. -/
def constantDeltaOneAt (t : Fin 2) :
    boundaryConstantSheaf C ε hε ⟶ triplePointSheaf C ε hε t :=
  biproduct.π (curveConstantSheaf C ε hε) 0 ≫ curveConstantEvaluation C ε hε 0 t -
    biproduct.π (curveConstantSheaf C ε hε) 1 ≫ curveConstantEvaluation C ε hε 1 t +
    biproduct.π (curveConstantSheaf C ε hε) 2 ≫ curveConstantEvaluation C ε hε 2 t

/-- The actual last nonzero map of the constant normalization sequence. -/
def constantDeltaOne : boundaryConstantSheaf C ε hε ⟶ tripleSheaf C ε hε :=
  biproduct.lift (constantDeltaOneAt C ε hε)

@[reassoc (attr := simp)] theorem constantDeltaOne_component (t : Fin 2) :
    constantDeltaOne C ε hε ≫ biproduct.π (triplePointSheaf C ε hε) t =
      constantDeltaOneAt C ε hε t :=
  biproduct.lift_π _ _

/-- The first summand has positive source sign. -/
@[reassoc (attr := simp)] theorem constantDeltaOneAt_first (t : Fin 2) :
    biproduct.ι (curveConstantSheaf C ε hε) 0 ≫ constantDeltaOneAt C ε hε t =
      curveConstantEvaluation C ε hε 0 t := by
  simp [constantDeltaOneAt, Preadditive.comp_add, Preadditive.comp_sub]

/-- The second summand has negative source sign. -/
@[reassoc (attr := simp)] theorem constantDeltaOneAt_second (t : Fin 2) :
    biproduct.ι (curveConstantSheaf C ε hε) 1 ≫ constantDeltaOneAt C ε hε t =
      -curveConstantEvaluation C ε hε 1 t := by
  simp [constantDeltaOneAt, Preadditive.comp_add, Preadditive.comp_sub]

/-- The third summand has positive source sign. -/
@[reassoc (attr := simp)] theorem constantDeltaOneAt_third (t : Fin 2) :
    biproduct.ι (curveConstantSheaf C ε hε) 2 ≫ constantDeltaOneAt C ε hε t =
      curveConstantEvaluation C ε hε 2 t := by
  simp [constantDeltaOneAt, Preadditive.comp_add, Preadditive.comp_sub]

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
