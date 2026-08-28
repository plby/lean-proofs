import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyConstantEdgeGlobalsBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyConstantEdgeGlobalsBiproduct
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsNormalization
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsCurves
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionConstants
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionGlobalMaps

/-!
# The actual constant and holomorphic global complexes are isomorphic

Compactness and connectedness of the actual normalization and source-ordered
curves make the original constants inclusions isomorphisms on their genuine
global sections. The terminal comparison is the identity. Thus this is an
isomorphism of the literal global complexes, with their original differentials.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge

open SheafResolution SheafCohomologyResolution SheafCohomologyGlobalSections
open CuspQuotient ToricCharts ToricSpace NormalizationCurves

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual constants inclusion on normalization global sections is an isomorphism. -/
theorem normalizationConstantsGlobal_isIso :
    IsIso ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
      (normalizationConstantsMap C ε hε)) :=
  pushforwardConstantsGlobal_isIso 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)
    (normalizationMap C ε hε)

/-- The actual constants inclusion on each actual source curve's direct-image
global sections is an isomorphism. -/
theorem curveConstantsGlobal_isIso (k : Fin 3) :
    IsIso ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
      (curveConstantsMap C ε hε hε1 hC hR k)) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let := curve_isManifold C ε hε hε1 hC hR (sourceEdgeIndex k)
  let := sourceCurve_compact C ε hε hε1 hC hR k
  let := sourceCurve_connected C ε hε hε1 hC hR k
  exact pushforwardConstantsGlobal_isIso 𝓘(ℂ) (sourceDoubleCurve C ε hε k)
    (sourceCurveMap C ε hε k)

/-- The actual finite-sum constants map is an isomorphism on genuine global sections. -/
theorem boundaryConstantsGlobal_isIso :
    IsIso ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
      (boundaryConstantsMap C ε hε hε1 hC hR)) := by
  let G := globalSectionsFunctor (TopCat.of (CentralSpace C ε))
  have : ∀ k, IsIso (G.map (curveConstantsMap C ε hε hε1 hC hR k)) :=
    curveConstantsGlobal_isIso C ε hε hε1 hC hR
  change IsIso (G.map (biproduct.map (curveConstantsMap C ε hε hε1 hC hR)))
  exact mapBiproduct_isIso G (curveConstantSheaf C ε hε)
    (curveSheaf C ε hε hε1 hC hR) (curveConstantsMap C ε hε hε1 hC hR)

/-- The original constants comparison is an isomorphism of the actual Γ complexes. -/
theorem constantsGlobalMap_isIso :
    IsIso (constantsAugmentedResolutionComparison C ε hε hε1 hC hR).globalMap := by
  let φ := constantsAugmentedResolutionComparison C ε hε hε1 hC hR
  have : IsIso φ.globalMap.τ₁ := normalizationConstantsGlobal_isIso C ε hε
  have : IsIso φ.globalMap.τ₂ := boundaryConstantsGlobal_isIso C ε hε hε1 hC hR
  have : IsIso φ.globalMap.τ₃ := by
    change IsIso ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
      (𝟙 (tripleSheaf C ε hε)))
    infer_instance
  exact ShortComplex.isIso_of_isIso φ.globalMap

/-- The induced map is the genuine cokernel map of the actual Γ differentials. -/
theorem constantsGlobalCokernelMap_isIso :
    IsIso (constantsAugmentedResolutionComparison C ε hε hε1 hC hR).globalCokernelMap := by
  let φ := constantsAugmentedResolutionComparison C ε hε hε1 hC hR
  have : IsIso φ.globalMap := constantsGlobalMap_isIso C ε hε hε1 hC hR
  change IsIso (cokernel.map _ _ φ.globalMap.τ₂ φ.globalMap.τ₃ φ.globalMap.comm₂₃.symm)
  infer_instance

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge
