import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsCusp
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluation
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspEndpoints

/-!
# Actual endpoint evaluations in the constant normalization sequence

These maps evaluate the independently constructed actual constant
pushforwards at the actual source-ordered points `P,Q` of each double
curve. Their targets are the same genuine skyscraper sheaves as in the
holomorphic sequence. The comparison squares and the positive/negative
lift formulas follow from proved actual evaluation naturality.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace
open CuspQuotient.NormalizationCurves

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- Independent actual constant evaluation at either actual triple point
of a source-ordered double curve. -/
def curveConstantEvaluation (k : Fin 3) (t : Fin 2) :
    curveConstantSheaf C ε hε k ⟶ triplePointSheaf C ε hε t :=
  SheafConstants.constantEvaluationAt (sourceCurveMap C ε hε k)
    (curveTriplePoint C ε hε k t) (triplePoint C ε hε t)
    (sourceCurveMap_curveTriplePoint C ε hε k t)

/-- Independent constant evaluation at an actual normalization-fibre point. -/
def normalizationConstantPointEvaluation (y : rayDivisor 0) (t : Fin 2)
    (hy : normalizationMap C ε hε y = triplePoint C ε hε t) :
    normalizationConstantSheaf C ε hε ⟶ triplePointSheaf C ε hε t :=
  SheafConstants.constantEvaluationAt (normalizationMap C ε hε)
    y (triplePoint C ε hε t) hy

/-- The actual endpoint square commutes for every double curve and both
actual triple points, with identity on the scalar skyscraper target. -/
theorem curveEvaluation_constants_naturality (k : Fin 3) (t : Fin 2) :
    curveConstantsMap C ε hε hε1 hC hR k ≫ curveEvaluation C ε hε hε1 hC hR k t =
      curveConstantEvaluation C ε hε k t := by
  let _ := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact SheafConstants.evaluationAt_holomorphicAdditiveMap
    𝓘(ℂ, ℂ) (sourceCurveMap C ε hε k)
    (curveTriplePoint C ε hε k t) (triplePoint C ε hε t)
    (sourceCurveMap_curveTriplePoint C ε hε k t)

/-- The analogous independent evaluation square on the normalization. -/
theorem normalizationPointEvaluation_constants_naturality (y : rayDivisor 0) (t : Fin 2)
    (hy : normalizationMap C ε hε y = triplePoint C ε hε t) :
    normalizationConstantsMap C ε hε ≫ normalizationPointEvaluation C ε hε y t hy =
      normalizationConstantPointEvaluation C ε hε y t hy :=
  SheafConstants.evaluationAt_holomorphicAdditiveMap 𝓘(ℂ, CoordinateSpace 2)
    (normalizationMap C ε hε) y (triplePoint C ε hε t) hy

/-- Constant evaluation after the actual positive boundary lift evaluates
at that actual lifted normalization point. -/
theorem plusConstantPullback_curveConstantEvaluation (k : Fin 3) (t : Fin 2) :
    plusConstantPullback C ε hε hε1 hC hR k ≫ curveConstantEvaluation C ε hε k t =
      normalizationConstantPointEvaluation C ε hε
        (sourcePlusLift C ε hε k (curveTriplePoint C ε hε k t)) t
        ((normalization_sourcePlusLift C ε hε k _).trans
          (sourceCurveMap_curveTriplePoint C ε hε k t)) := by
  let _ := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let g : ContMDiffMap 𝓘(ℂ, ℂ) 𝓘(ℂ, CoordinateSpace 2)
      (sourceDoubleCurve C ε hε k) (rayDivisor 0) ω :=
    ⟨sourcePlusLift C ε hε k, sourcePlusLift_holomorphic C ε hε hε1 hC hR k⟩
  exact SheafConstants.constantEvaluationAt_naturality
    (normalizationMap C ε hε) (sourceCurveMap C ε hε k)
    (SheafConstants.holomorphicTopMap 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ) g)
    (normalization_sourcePlusLift C ε hε k) (curveTriplePoint C ε hε k t)
    (triplePoint C ε hε t) (sourceCurveMap_curveTriplePoint C ε hε k t)

/-- The same actual constant evaluation formula for the negative lift. -/
theorem minusConstantPullback_curveConstantEvaluation (k : Fin 3) (t : Fin 2) :
    minusConstantPullback C ε hε hε1 hC hR k ≫ curveConstantEvaluation C ε hε k t =
      normalizationConstantPointEvaluation C ε hε
        (sourceMinusLift C ε hε k (curveTriplePoint C ε hε k t)) t
        ((normalization_sourceMinusLift C ε hε k _).trans
          (sourceCurveMap_curveTriplePoint C ε hε k t)) := by
  let _ := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let g : ContMDiffMap 𝓘(ℂ, ℂ) 𝓘(ℂ, CoordinateSpace 2)
      (sourceDoubleCurve C ε hε k) (rayDivisor 0) ω :=
    ⟨sourceMinusLift C ε hε k, sourceMinusLift_holomorphic C ε hε hε1 hC hR k⟩
  exact SheafConstants.constantEvaluationAt_naturality
    (normalizationMap C ε hε) (sourceCurveMap C ε hε k)
    (SheafConstants.holomorphicTopMap 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ) g)
    (normalization_sourceMinusLift C ε hε k) (curveTriplePoint C ε hε k t)
    (triplePoint C ε hε t) (sourceCurveMap_curveTriplePoint C ε hε k t)

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
