import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionTerms

/-!
# Scalar compatibility of the actual normalization resolution arrows
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution

open SheafResolution CuspQuotient ToricCharts ToricSpace
open CuspQuotient.NormalizationCurves

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual reduced-to-normalization augmentation commutes with pointwise scalars. -/
theorem normalizationPullback_scalar (c : ℂ) :
    reducedSheafScalarEnd C ε hε hε1 hC hR c ≫ normalizationPullback C ε hε hε1 hC hR =
      normalizationPullback C ε hε hε1 hC hR ≫ normalizationScalarEnd C ε hε c := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact reducedPullback_scalar 𝓘(ℂ, CoordinateSpace 3) 𝓘(ℂ, CoordinateSpace 2)
    (centralSet C ε)
    ⟨componentProjection C ε hε, componentProjection_holomorphic C ε hε hε1 hC hR⟩
    (projection_componentProjection C ε hε) c

/-- Scalar compatibility of the actual positive boundary pullback. -/
theorem plusPullback_scalar (k : Fin 3) (c : ℂ) :
    normalizationScalarEnd C ε hε c ≫ plusPullback C ε hε hε1 hC hR k =
      plusPullback C ε hε hε1 hC hR k ≫ curveScalarEnd C ε hε hε1 hC hR k c := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact overBasePullback_scalar 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ)
    (normalizationMap C ε hε) (sourceCurveMap C ε hε k)
    ⟨sourcePlusLift C ε hε k, sourcePlusLift_holomorphic C ε hε hε1 hC hR k⟩
    (normalization_sourcePlusLift C ε hε k) c

/-- Scalar compatibility of the actual negative boundary pullback. -/
theorem minusPullback_scalar (k : Fin 3) (c : ℂ) :
    normalizationScalarEnd C ε hε c ≫ minusPullback C ε hε hε1 hC hR k =
      minusPullback C ε hε hε1 hC hR k ≫ curveScalarEnd C ε hε hε1 hC hR k c := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact overBasePullback_scalar 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ)
    (normalizationMap C ε hε) (sourceCurveMap C ε hε k)
    ⟨sourceMinusLift C ε hε k, sourceMinusLift_holomorphic C ε hε hε1 hC hR k⟩
    (normalization_sourceMinusLift C ε hε k) c

theorem boundaryDifference_scalar (k : Fin 3) (c : ℂ) :
    normalizationScalarEnd C ε hε c ≫ boundaryDifference C ε hε hε1 hC hR k =
      boundaryDifference C ε hε hε1 hC hR k ≫ curveScalarEnd C ε hε hε1 hC hR k c := by
  simp only [boundaryDifference, Preadditive.comp_sub, Preadditive.sub_comp,
    plusPullback_scalar, minusPullback_scalar]

/-- The actual first global sheaf differential commutes with pointwise scalars. -/
theorem deltaZero_scalar (c : ℂ) :
    normalizationScalarEnd C ε hε c ≫ deltaZero C ε hε hε1 hC hR =
      deltaZero C ε hε hε1 hC hR ≫ boundaryScalarEnd C ε hε hε1 hC hR c := by
  apply biproduct.hom_ext
  intro k
  rw [Category.assoc, Category.assoc, deltaZero_component, boundaryScalarEnd_π,
    ← Category.assoc, deltaZero_component]
  exact boundaryDifference_scalar C ε hε hε1 hC hR k c

/-- The actual curve evaluation at P or Q respects its actual scalar skyscraper action. -/
theorem curveEvaluation_scalar (k : Fin 3) (t : Fin 2) (c : ℂ) :
    curveScalarEnd C ε hε hε1 hC hR k c ≫ curveEvaluation C ε hε hε1 hC hR k t =
      curveEvaluation C ε hε hε1 hC hR k t ≫ triplePointScalarEnd C ε hε t c := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact evaluation_scalar 𝓘(ℂ) (sourceCurveMap C ε hε k)
    (curveTriplePoint C ε hε k t) (triplePoint C ε hε t)
    (sourceCurveMap_curveTriplePoint C ε hε k t) c

theorem deltaOneAt_scalar (t : Fin 2) (c : ℂ) :
    boundaryScalarEnd C ε hε hε1 hC hR c ≫ deltaOneAt C ε hε hε1 hC hR t =
      deltaOneAt C ε hε hε1 hC hR t ≫ triplePointScalarEnd C ε hε t c := by
  simp only [deltaOneAt, Preadditive.comp_add, Preadditive.comp_sub,
    Preadditive.add_comp, Preadditive.sub_comp, Category.assoc,
    boundaryScalarEnd_π_assoc, curveEvaluation_scalar]

/-- The actual signed P/Q evaluation differential commutes with pointwise scalars. -/
theorem deltaOne_scalar (c : ℂ) :
    boundaryScalarEnd C ε hε hε1 hC hR c ≫ deltaOne C ε hε hε1 hC hR =
      deltaOne C ε hε hε1 hC hR ≫ tripleScalarEnd C ε hε c := by
  apply biproduct.hom_ext
  intro t
  rw [Category.assoc, Category.assoc, deltaOne_component, tripleScalarEnd_π,
    ← Category.assoc, deltaOne_component]
  exact deltaOneAt_scalar C ε hε hε1 hC hR t c

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution
