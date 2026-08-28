import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionCuspRetractionBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionStalkEvaluation
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionEndpoints

/-!
# Actual curve-stalk retractions preserve the endpoint evaluations

The actual constant and holomorphic curve direct images use the same
source-ordered points above the two triple points. The finite-fibre
scalar-evaluation retraction preserves both endpoint maps at every base
point, including the points where the skyscraper target has zero stalk.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace NormalizationCurves

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- At every actual base point the curve-stalk retraction preserves
evaluation to either of the two actual scalar skyscraper sheaves. -/
theorem curveEvaluation_stalkConstantRetraction_naturality
    (k : Fin 3) (t : Fin 2) (x : CentralSpace C ε) :
    curveStalkConstantRetractionHom C ε hε hε1 hC hR k x ≫
        (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
          (curveConstantEvaluation C ε hε k t) =
      (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
        (curveEvaluation C ε hε hε1 hC hR k t) := by
  let _ := quotient_t2Space C ε hε hε1 hC hR
  let _ := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact SheafConstants.holomorphicStalkConstantRetraction_evaluationAt 𝓘(ℂ, ℂ)
    (sourceCurveMap C ε hε k) (SheafCurveStalk.sourceCurveMap_isClosedMap C ε hε k)
    x (sourceCurveMap_fibre_finite C ε hε k x)
    (curveTriplePoint C ε hε k t) (triplePoint C ε hε t)
    (sourceCurveMap_curveTriplePoint C ε hε k t)

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
