import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionCuspRetractionBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionReducedRetractionPullback

/-!
# The actual reduced constant-stalk retraction on the cusp central fibre

The scalar value of a genuine reduced holomorphic germ determines an
actual constant germ.  The construction uses the quotient charts that
define the reduced sheaf.  Its compatibility with normalization is the
specialization of literal reduced-function pullback compatibility; the
closedness and finite fibres are properties of the constructed map.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- Scalar evaluation of an actual reduced germ, returned to the genuine
constant stalk on the central fibre. -/
def reducedStalkConstantRetraction (x : CentralSpace C ε) :
    (reducedSheaf C ε hε hε1 hC hR).presheaf.stalk x →+
      (constantSheaf C ε).presheaf.stalk x := by
  letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact SheafConstants.reducedStalkConstantRetraction
    𝓘(ℂ, CoordinateSpace 3) (centralSet C ε) x

/-- The reduced retraction as a genuine additive stalk morphism. -/
def reducedStalkConstantRetractionHom (x : CentralSpace C ε) :
    (reducedSheaf C ε hε hε1 hC hR).presheaf.stalk x ⟶
      (constantSheaf C ε).presheaf.stalk x :=
  AddCommGrpCat.ofHom (reducedStalkConstantRetraction C ε hε hε1 hC hR x)

/-- The actual reduced constant inclusion is retracted on each stalk. -/
theorem reducedStalkConstantRetraction_leftInverse (x : CentralSpace C ε) :
    Function.LeftInverse (reducedStalkConstantRetraction C ε hε hε1 hC hR x)
      ((SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
        (reducedConstantsMap C ε hε hε1 hC hR)) := by
  let _ := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact SheafConstants.reducedStalkConstantRetraction_leftInverse
    𝓘(ℂ, CoordinateSpace 3) (centralSet C ε) x

/-- Inclusion followed by the actual reduced stalk retraction is identity. -/
theorem reducedStalkConstantRetraction_comp (x : CentralSpace C ε) :
    (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
        (reducedConstantsMap C ε hε hε1 hC hR) ≫
      reducedStalkConstantRetractionHom C ε hε hε1 hC hR x =
        𝟙 ((constantSheaf C ε).presheaf.stalk x) := by
  ext s
  exact reducedStalkConstantRetraction_leftInverse C ε hε hε1 hC hR x s

/-- The actual first-arrow square of constant-stalk retractions commutes
for the constructed normalization map. -/
theorem normalization_stalkConstantRetraction_naturality (x : CentralSpace C ε) :
    reducedStalkConstantRetractionHom C ε hε hε1 hC hR x ≫
        (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
          (normalizationConstantPullback C ε hε) =
      (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
          (normalizationPullback C ε hε hε1 hC hR) ≫
        normalizationStalkConstantRetractionHom C ε hε hε1 hC hR x := by
  let _ := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let g : ContMDiffMap 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, CoordinateSpace 3)
      (rayDivisor 0) (QuotientSpace C ε) ω :=
    ⟨componentProjection C ε hε, componentProjection_holomorphic C ε hε hε1 hC hR⟩
  exact (SheafConstants.reducedStalkConstantRetraction_pullback_hom
    𝓘(ℂ, CoordinateSpace 3) 𝓘(ℂ, CoordinateSpace 2) (centralSet C ε) g
    (projection_componentProjection C ε hε) (normalization_isClosedMap C ε hε) x
    (normalization_fibre_finite C ε hε hε1 hC hR x)).symm

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
