import Wikipedia.HopfProblem.CuspNormalizationSheafCuspSums
import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluation

/-!
# Actual evaluations at the two triple points

The last differential uses literal evaluation on each actual double curve.
Its compatibility with restriction from the normalization is the proved
naturality of genuine holomorphic evaluation, applied to the actual lifts.
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

/-- The actual source-ordered triple point on each double curve. -/
def curveTriplePoint (k : Fin 3) (t : Fin 2) : sourceDoubleCurve C ε hε k :=
  ![sourceP C ε hε k, sourceQ C ε hε k] t

@[simp] theorem curveTriplePoint_zero (k : Fin 3) :
    curveTriplePoint C ε hε k 0 = sourceP C ε hε k := rfl

@[simp] theorem curveTriplePoint_one (k : Fin 3) :
    curveTriplePoint C ε hε k 1 = sourceQ C ε hε k := rfl

@[simp] theorem sourceCurveMap_curveTriplePoint (k : Fin 3) (t : Fin 2) :
    sourceCurveMap C ε hε k (curveTriplePoint C ε hε k t) = triplePoint C ε hε t := by
  fin_cases t <;> rfl

/-- Literal evaluation on the actual `k`-th curve, with values in the
genuine skyscraper at its actual `t`-th triple point. -/
def curveEvaluation (k : Fin 3) (t : Fin 2) :
    curveSheaf C ε hε hε1 hC hR k ⟶ triplePointSheaf C ε hε t := by
  letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact SheafEvaluation.evaluationAt 𝓘(ℂ, ℂ) (sourceCurveMap C ε hε k)
    (curveTriplePoint C ε hε k t) (triplePoint C ε hε t)
    (sourceCurveMap_curveTriplePoint C ε hε k t)

/-- Evaluation at a specified actual point of the normalization fibre. -/
def normalizationPointEvaluation (y : rayDivisor 0) (t : Fin 2)
    (hy : normalizationMap C ε hε y = triplePoint C ε hε t) :
    normalizationSheaf C ε hε ⟶ triplePointSheaf C ε hε t :=
  SheafEvaluation.evaluationAt 𝓘(ℂ, CoordinateSpace 2) (normalizationMap C ε hε)
    y (triplePoint C ε hε t) hy

/-- Evaluation after the positive restriction is evaluation at the
actual positive lift, as an equality of genuine sheaf morphisms. -/
theorem plusPullback_curveEvaluation (k : Fin 3) (t : Fin 2) :
    plusPullback C ε hε hε1 hC hR k ≫ curveEvaluation C ε hε hε1 hC hR k t =
      normalizationPointEvaluation C ε hε
        (sourcePlusLift C ε hε k (curveTriplePoint C ε hε k t)) t
        ((normalization_sourcePlusLift C ε hε k _).trans
          (sourceCurveMap_curveTriplePoint C ε hε k t)) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let g : ContMDiffMap 𝓘(ℂ, ℂ) 𝓘(ℂ, CoordinateSpace 2)
      (sourceDoubleCurve C ε hε k) (rayDivisor 0) ω :=
    ⟨sourcePlusLift C ε hε k, sourcePlusLift_holomorphic C ε hε hε1 hC hR k⟩
  exact SheafEvaluation.evaluationAt_naturality 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ)
    (normalizationMap C ε hε) (sourceCurveMap C ε hε k) g
    (normalization_sourcePlusLift C ε hε k) (curveTriplePoint C ε hε k t)
    (triplePoint C ε hε t) (sourceCurveMap_curveTriplePoint C ε hε k t)

/-- The same actual evaluation formula for the negative restriction. -/
theorem minusPullback_curveEvaluation (k : Fin 3) (t : Fin 2) :
    minusPullback C ε hε hε1 hC hR k ≫ curveEvaluation C ε hε hε1 hC hR k t =
      normalizationPointEvaluation C ε hε
        (sourceMinusLift C ε hε k (curveTriplePoint C ε hε k t)) t
        ((normalization_sourceMinusLift C ε hε k _).trans
          (sourceCurveMap_curveTriplePoint C ε hε k t)) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let g : ContMDiffMap 𝓘(ℂ, ℂ) 𝓘(ℂ, CoordinateSpace 2)
      (sourceDoubleCurve C ε hε k) (rayDivisor 0) ω :=
    ⟨sourceMinusLift C ε hε k, sourceMinusLift_holomorphic C ε hε hε1 hC hR k⟩
  exact SheafEvaluation.evaluationAt_naturality 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ)
    (normalizationMap C ε hε) (sourceCurveMap C ε hε k) g
    (normalization_sourceMinusLift C ε hε k) (curveTriplePoint C ε hε k t)
    (triplePoint C ε hε t) (sourceCurveMap_curveTriplePoint C ε hε k t)

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
