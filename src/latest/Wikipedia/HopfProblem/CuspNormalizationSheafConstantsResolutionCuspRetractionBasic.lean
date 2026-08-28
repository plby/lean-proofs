import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionStalkRetractionNaturality
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionSums
import Wikipedia.HopfProblem.CuspNormalizationSheafCurveStalkBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafBiproduct

/-!
# Actual constant-stalk retractions on the cusp normalization and curves

These maps specialize the proved finite-fibre scalar-evaluation
retraction to the actual normalization and source-ordered double curves.
Closedness, finite fibres and Hausdorff source spaces come from the
constructed geometry.  The inclusions they retract are the actual
termwise constant-to-holomorphic maps of the normalization sequence.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace NormalizationCurves

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The actual closed source-curve inclusion has finite fibres. -/
theorem sourceCurveMap_fibre_finite (k : Fin 3) (x : CentralSpace C ε) :
    (sourceCurveMap C ε hε k ⁻¹' {x}).Finite :=
  Set.Finite.preimage (SheafCurveStalk.sourceCurveMap_injective C ε hε k).injOn
    (Set.finite_singleton x)

variable (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- Scalar evaluation on the actual finite normalization fibre,
returned to the actual constant pushforward stalk. -/
def normalizationStalkConstantRetraction (x : CentralSpace C ε) :
    (normalizationSheaf C ε hε).presheaf.stalk x →+
      (normalizationConstantSheaf C ε hε).presheaf.stalk x :=
  SheafConstants.holomorphicStalkConstantRetraction 𝓘(ℂ, CoordinateSpace 2)
    (normalizationMap C ε hε) (normalization_isClosedMap C ε hε) x
    (normalization_fibre_finite C ε hε hε1 hC hR x)

/-- The normalization retraction as a genuine additive stalk morphism. -/
def normalizationStalkConstantRetractionHom (x : CentralSpace C ε) :
    (normalizationSheaf C ε hε).presheaf.stalk x ⟶
      (normalizationConstantSheaf C ε hε).presheaf.stalk x :=
  AddCommGrpCat.ofHom (normalizationStalkConstantRetraction C ε hε hε1 hC hR x)

/-- The actual normalization constant inclusion is retracted on each stalk. -/
theorem normalizationStalkConstantRetraction_leftInverse (x : CentralSpace C ε) :
    Function.LeftInverse (normalizationStalkConstantRetraction C ε hε hε1 hC hR x)
      ((SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
        (normalizationConstantsMap C ε hε)) :=
  SheafConstants.holomorphicStalkConstantRetraction_leftInverse 𝓘(ℂ, CoordinateSpace 2)
    (normalizationMap C ε hε) (normalization_isClosedMap C ε hε) x
    (normalization_fibre_finite C ε hε hε1 hC hR x)

/-- Inclusion followed by the actual normalization stalk retraction is identity. -/
theorem normalizationStalkConstantRetraction_comp (x : CentralSpace C ε) :
    (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
        (normalizationConstantsMap C ε hε) ≫
      normalizationStalkConstantRetractionHom C ε hε hε1 hC hR x =
        𝟙 ((normalizationConstantSheaf C ε hε).presheaf.stalk x) := by
  ext s
  exact normalizationStalkConstantRetraction_leftInverse C ε hε hε1 hC hR x s

/-- Scalar evaluation on the actual source curve, in its prescribed
holomorphic charts, returned to its actual constant pushforward stalk. -/
def curveStalkConstantRetraction (k : Fin 3) (x : CentralSpace C ε) :
    (curveSheaf C ε hε hε1 hC hR k).presheaf.stalk x →+
      (curveConstantSheaf C ε hε k).presheaf.stalk x := by
  letI := quotient_t2Space C ε hε hε1 hC hR
  letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact SheafConstants.holomorphicStalkConstantRetraction 𝓘(ℂ, ℂ)
    (sourceCurveMap C ε hε k) (SheafCurveStalk.sourceCurveMap_isClosedMap C ε hε k) x
    (sourceCurveMap_fibre_finite C ε hε k x)

/-- The curve retraction as a genuine additive stalk morphism. -/
def curveStalkConstantRetractionHom (k : Fin 3) (x : CentralSpace C ε) :
    (curveSheaf C ε hε hε1 hC hR k).presheaf.stalk x ⟶
      (curveConstantSheaf C ε hε k).presheaf.stalk x :=
  AddCommGrpCat.ofHom (curveStalkConstantRetraction C ε hε hε1 hC hR k x)

/-- The actual curve constant inclusion is retracted on each stalk. -/
theorem curveStalkConstantRetraction_leftInverse (k : Fin 3) (x : CentralSpace C ε) :
    Function.LeftInverse (curveStalkConstantRetraction C ε hε hε1 hC hR k x)
      ((SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
        (curveConstantsMap C ε hε hε1 hC hR k)) := by
  let _ := quotient_t2Space C ε hε hε1 hC hR
  let _ := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact SheafConstants.holomorphicStalkConstantRetraction_leftInverse 𝓘(ℂ, ℂ)
    (sourceCurveMap C ε hε k) (SheafCurveStalk.sourceCurveMap_isClosedMap C ε hε k) x
    (sourceCurveMap_fibre_finite C ε hε k x)

/-- Inclusion followed by the actual curve stalk retraction is identity. -/
theorem curveStalkConstantRetraction_comp (k : Fin 3) (x : CentralSpace C ε) :
    (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
        (curveConstantsMap C ε hε hε1 hC hR k) ≫
      curveStalkConstantRetractionHom C ε hε hε1 hC hR k x =
        𝟙 ((curveConstantSheaf C ε hε k).presheaf.stalk x) := by
  ext s
  exact curveStalkConstantRetraction_leftInverse C ε hε hε1 hC hR k x s

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
