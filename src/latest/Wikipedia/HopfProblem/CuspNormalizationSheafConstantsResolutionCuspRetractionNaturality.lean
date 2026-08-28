import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionCuspRetractionBasic

/-!
# Actual cusp stalk retractions commute with the signed curve pullbacks

The positive and negative maps are the already constructed geometric
lifts of the actual source-ordered double curves.  The generic finite
pushforward retraction theorem applies to those exact maps.  Additivity
then gives compatibility with their actual signed difference.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace NormalizationCurves

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual positive lift commutes with the actual scalar-value
retractions on the normalization and curve stalks. -/
theorem plus_stalkConstantRetraction_naturality (k : Fin 3) (x : CentralSpace C ε) :
    (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
        (plusPullback C ε hε hε1 hC hR k) ≫
      curveStalkConstantRetractionHom C ε hε hε1 hC hR k x =
        normalizationStalkConstantRetractionHom C ε hε hε1 hC hR x ≫
          (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
            (plusConstantPullback C ε hε hε1 hC hR k) := by
  let _ := quotient_t2Space C ε hε hε1 hC hR
  let _ := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let g : ContMDiffMap 𝓘(ℂ, ℂ) 𝓘(ℂ, CoordinateSpace 2)
      (sourceDoubleCurve C ε hε k) (rayDivisor 0) ω :=
    ⟨sourcePlusLift C ε hε k, sourcePlusLift_holomorphic C ε hε hε1 hC hR k⟩
  exact SheafConstants.holomorphicStalkConstantRetraction_naturality_hom
    𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ)
    (normalizationMap C ε hε) (normalization_isClosedMap C ε hε)
    (sourceCurveMap C ε hε k) (SheafCurveStalk.sourceCurveMap_isClosedMap C ε hε k)
    g (normalization_sourcePlusLift C ε hε k) x
    (normalization_fibre_finite C ε hε hε1 hC hR x)
    (sourceCurveMap_fibre_finite C ε hε k x)

/-- The actual negative lift commutes with the same actual stalk retractions. -/
theorem minus_stalkConstantRetraction_naturality (k : Fin 3) (x : CentralSpace C ε) :
    (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
        (minusPullback C ε hε hε1 hC hR k) ≫
      curveStalkConstantRetractionHom C ε hε hε1 hC hR k x =
        normalizationStalkConstantRetractionHom C ε hε hε1 hC hR x ≫
          (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
            (minusConstantPullback C ε hε hε1 hC hR k) := by
  let _ := quotient_t2Space C ε hε hε1 hC hR
  let _ := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let g : ContMDiffMap 𝓘(ℂ, ℂ) 𝓘(ℂ, CoordinateSpace 2)
      (sourceDoubleCurve C ε hε k) (rayDivisor 0) ω :=
    ⟨sourceMinusLift C ε hε k, sourceMinusLift_holomorphic C ε hε hε1 hC hR k⟩
  exact SheafConstants.holomorphicStalkConstantRetraction_naturality_hom
    𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ)
    (normalizationMap C ε hε) (normalization_isClosedMap C ε hε)
    (sourceCurveMap C ε hε k) (SheafCurveStalk.sourceCurveMap_isClosedMap C ε hε k)
    g (normalization_sourceMinusLift C ε hε k) x
    (normalization_fibre_finite C ε hε hε1 hC hR x)
    (sourceCurveMap_fibre_finite C ε hε k x)

/-- The source-oriented signed difference commutes with the actual
normalization and curve stalk retractions. -/
theorem boundaryDifference_stalkConstantRetraction_naturality
    (k : Fin 3) (x : CentralSpace C ε) :
    (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
        (boundaryDifference C ε hε hε1 hC hR k) ≫
      curveStalkConstantRetractionHom C ε hε hε1 hC hR k x =
        normalizationStalkConstantRetractionHom C ε hε hε1 hC hR x ≫
          (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
            (constantBoundaryDifference C ε hε hε1 hC hR k) := by
  ext s
  let K := SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x
  have hp := ConcreteCategory.congr_hom
    (plus_stalkConstantRetraction_naturality C ε hε hε1 hC hR k x) s
  have hm := ConcreteCategory.congr_hom
    (minus_stalkConstantRetraction_naturality C ε hε hε1 hC hR k x) s
  exact (congrArg (curveStalkConstantRetraction C ε hε hε1 hC hR k x)
    (ConcreteCategory.congr_hom
      (K.map_sub (f := plusPullback C ε hε hε1 hC hR k)
        (g := minusPullback C ε hε hε1 hC hR k)) s)).trans
    ((map_sub (curveStalkConstantRetraction C ε hε hε1 hC hR k x) _ _).trans
      ((congrArg₂ (fun a b : (curveConstantSheaf C ε hε k).presheaf.stalk x => a - b)
        hp hm).trans
        (ConcreteCategory.congr_hom
          (K.map_sub (f := plusConstantPullback C ε hε hε1 hC hR k)
            (g := minusConstantPullback C ε hε hε1 hC hR k))
          (normalizationStalkConstantRetraction C ε hε hε1 hC hR x s)).symm))

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
