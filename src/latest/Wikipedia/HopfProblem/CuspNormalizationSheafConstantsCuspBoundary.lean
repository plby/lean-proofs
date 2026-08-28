import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsCuspTerms
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsOverBase

/-!
# Actual constant restrictions along the cusp double curves

The two maps are induced by the actual source-oriented lifts of each
double curve into the normalization component. Their difference uses
the same signs as the holomorphic resolution. Naturality proves the
termwise comparison for each lift and hence for the actual difference.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace
open CuspQuotient.NormalizationCurves

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- Actual constant-sheaf restriction along the source's positive lift. -/
def plusConstantPullback (k : Fin 3) :
    normalizationConstantSheaf C ε hε ⟶ curveConstantSheaf C ε hε k := by
  letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let g : ContMDiffMap 𝓘(ℂ, ℂ) 𝓘(ℂ, CoordinateSpace 2)
      (sourceDoubleCurve C ε hε k) (rayDivisor 0) ω :=
    ⟨sourcePlusLift C ε hε k, sourcePlusLift_holomorphic C ε hε hε1 hC hR k⟩
  exact SheafConstants.additiveOverBaseMap
    (normalizationMap C ε hε) (sourceCurveMap C ε hε k)
    (SheafConstants.holomorphicTopMap 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ) g)
    (normalization_sourcePlusLift C ε hε k)

/-- Actual constant-sheaf restriction along the source's negative lift. -/
def minusConstantPullback (k : Fin 3) :
    normalizationConstantSheaf C ε hε ⟶ curveConstantSheaf C ε hε k := by
  letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let g : ContMDiffMap 𝓘(ℂ, ℂ) 𝓘(ℂ, CoordinateSpace 2)
      (sourceDoubleCurve C ε hε k) (rayDivisor 0) ω :=
    ⟨sourceMinusLift C ε hε k, sourceMinusLift_holomorphic C ε hε hε1 hC hR k⟩
  exact SheafConstants.additiveOverBaseMap
    (normalizationMap C ε hε) (sourceCurveMap C ε hε k)
    (SheafConstants.holomorphicTopMap 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ) g)
    (normalization_sourceMinusLift C ε hε k)

/-- The actual source-oriented boundary difference on the constant terms. -/
def constantBoundaryDifference (k : Fin 3) :
    normalizationConstantSheaf C ε hε ⟶ curveConstantSheaf C ε hε k :=
  plusConstantPullback C ε hε hε1 hC hR k - minusConstantPullback C ε hε hε1 hC hR k

/-- The constants-to-holomorphic square for the actual positive lift. -/
theorem plus_constants_naturality (k : Fin 3) :
    normalizationConstantsMap C ε hε ≫ plusPullback C ε hε hε1 hC hR k =
      plusConstantPullback C ε hε hε1 hC hR k ≫ curveConstantsMap C ε hε hε1 hC hR k := by
  let _ := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let g : ContMDiffMap 𝓘(ℂ, ℂ) 𝓘(ℂ, CoordinateSpace 2)
      (sourceDoubleCurve C ε hε k) (rayDivisor 0) ω :=
    ⟨sourcePlusLift C ε hε k, sourcePlusLift_holomorphic C ε hε hε1 hC hR k⟩
  exact SheafConstants.additive_holomorphic_overBase_naturality
    𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ)
    (normalizationMap C ε hε) (sourceCurveMap C ε hε k) g
    (normalization_sourcePlusLift C ε hε k)

/-- The constants-to-holomorphic square for the actual negative lift. -/
theorem minus_constants_naturality (k : Fin 3) :
    normalizationConstantsMap C ε hε ≫ minusPullback C ε hε hε1 hC hR k =
      minusConstantPullback C ε hε hε1 hC hR k ≫ curveConstantsMap C ε hε hε1 hC hR k := by
  let _ := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let g : ContMDiffMap 𝓘(ℂ, ℂ) 𝓘(ℂ, CoordinateSpace 2)
      (sourceDoubleCurve C ε hε k) (rayDivisor 0) ω :=
    ⟨sourceMinusLift C ε hε k, sourceMinusLift_holomorphic C ε hε hε1 hC hR k⟩
  exact SheafConstants.additive_holomorphic_overBase_naturality
    𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ)
    (normalizationMap C ε hε) (sourceCurveMap C ε hε k) g
    (normalization_sourceMinusLift C ε hε k)

/-- The actual signed boundary maps commute with the constants inclusions. -/
theorem boundary_constants_naturality (k : Fin 3) :
    normalizationConstantsMap C ε hε ≫ boundaryDifference C ε hε hε1 hC hR k =
      constantBoundaryDifference C ε hε hε1 hC hR k ≫
        curveConstantsMap C ε hε hε1 hC hR k := by
  unfold boundaryDifference constantBoundaryDifference
  rw [Preadditive.comp_sub, Preadditive.sub_comp,
    plus_constants_naturality, minus_constants_naturality]

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
