import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsNormalization
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsCurves
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsTriple

/-!
# Literal global values of the normalization-resolution maps

The evaluations here are the actual sheaf-morphism components at the
top open set. They agree with literal values of the original
holomorphic functions at the actual source points.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

open SheafResolution SheafCohomologyResolution CuspQuotient ToricCharts ToricSpace
open CuspQuotient.NormalizationCurves

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- Actual curve evaluation at P or Q is literal function evaluation. -/
theorem curveEvaluation_global (k : Fin 3) (t : Fin 2)
    (s : Sections (curveSheaf C ε hε hε1 hC hR k)) :
    triplePointGlobalLinearEquiv C ε hε t
        ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
          (curveEvaluation C ε hε hε1 hC hR k t) s) =
      curveValue C ε hε hε1 hC hR k s (curveTriplePoint C ε hε k t) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact SheafEvaluation.evaluationAt_app 𝓘(ℂ) (sourceCurveMap C ε hε k)
    (curveTriplePoint C ε hε k t) (triplePoint C ε hε t)
    (sourceCurveMap_curveTriplePoint C ε hε k t) ⊤ trivial s

/-- Both actual endpoint evaluations return the same scalar of the
actual global section on the corresponding compact curve. -/
theorem curveEvaluation_global_scalar (k : Fin 3) (t : Fin 2)
    (s : Sections (curveSheaf C ε hε hε1 hC hR k)) :
    triplePointGlobalLinearEquiv C ε hε t
        ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
          (curveEvaluation C ε hε hε1 hC hR k t) s) =
      curveGlobalLinearEquiv C ε hε hε1 hC hR k s :=
  (curveEvaluation_global C ε hε hε1 hC hR k t s).trans
    (curveValue_eq_scalar C ε hε hε1 hC hR k s (curveTriplePoint C ε hε k t))

/-- Evaluation of an actual normalization section at a specified
actual point over P or Q is literal evaluation of its function. -/
theorem normalizationPointEvaluation_global (y : rayDivisor 0) (t : Fin 2)
    (hy : normalizationMap C ε hε y = triplePoint C ε hε t)
    (s : Sections (normalizationSheaf C ε hε)) :
    triplePointGlobalLinearEquiv C ε hε t
        ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
          (normalizationPointEvaluation C ε hε y t hy) s) = normalizationValue C ε hε s y :=
  SheafEvaluation.evaluationAt_app 𝓘(ℂ, CoordinateSpace 2) (normalizationMap C ε hε)
    y (triplePoint C ε hε t) hy ⊤ trivial s

/-- The signed boundary restriction is the literal difference of
the values at the actual positive and negative normalization lifts. -/
theorem boundaryDifference_global_value (k : Fin 3)
    (s : Sections (normalizationSheaf C ε hε)) (x : sourceDoubleCurve C ε hε k) :
    curveValue C ε hε hε1 hC hR k
        ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
          (boundaryDifference C ε hε hε1 hC hR k) s) x =
      normalizationValue C ε hε s (sourcePlusLift C ε hε k x) -
        normalizationValue C ε hε s (sourceMinusLift C ε hε k x) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  rfl

/-- Constancy on the actual compact normalization makes every
actual boundary-difference global section have scalar zero. -/
theorem boundaryDifference_global_scalar_zero (k : Fin 3)
    (s : Sections (normalizationSheaf C ε hε)) :
    curveGlobalLinearEquiv C ε hε hε1 hC hR k
        ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
          (boundaryDifference C ε hε hε1 hC hR k) s) = 0 := by
  rw [curveGlobalLinearEquiv_apply, boundaryDifference_global_value,
    normalizationValue_eq C ε hε s
      (sourcePlusLift C ε hε k (curveTriplePoint C ε hε k 0))
      (sourceMinusLift C ε hε k (curveTriplePoint C ε hε k 0)), sub_self]

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
