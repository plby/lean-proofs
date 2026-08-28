import Wikipedia.HopfProblem.CuspNormalizationSheafCuspEndpoints

/-!
# Surjective actual curve evaluation at triple-point stalks

Actual constant holomorphic sections make each curve-evaluation map
surjective on the stalk at its actual triple-point support.
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

/-- Each actual curve-evaluation stalk map is surjective at its actual
triple-point support, as witnessed by constant holomorphic sections. -/
theorem curveEvaluation_stalk_surjective (k : Fin 3) (t : Fin 2) :
    Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat
        (triplePoint C ε hε t)).map (curveEvaluation C ε hε hε1 hC hR k t).hom) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact SheafEvaluation.evaluationAt_stalk_surjective 𝓘(ℂ, ℂ)
    (sourceCurveMap C ε hε k) (curveTriplePoint C ε hε k t) (triplePoint C ε hε t)
    (sourceCurveMap_curveTriplePoint C ε hε k t)

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
