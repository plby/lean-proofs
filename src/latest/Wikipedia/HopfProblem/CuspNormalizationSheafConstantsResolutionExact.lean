import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionComplex
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionRetract
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionCuspReducedRetraction
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionCuspLastRetraction
import Wikipedia.HopfProblem.CuspNormalizationSheafExactHolomorphic

/-!
# Exactness of the actual constant normalization resolution

The constant sequence is the independently constructed sequence of actual
constant sheaves and actual direct images. Its stalks are retracted from
the holomorphic sequence by evaluating genuine analytic germs on the
actual finite normalization fibres. The actual reverse chain squares
therefore transfer exactness, and the actual last retraction transfers
surjectivity onto the two scalar skyscrapers.

No cohomology comparison or higher-cohomology acyclicity is used.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace
open SheafConstants.ResolutionRetract

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual constant normalization stalk complex is exact: lift a
cycle through the actual constants inclusion, use analytic exactness,
and evaluate its actual analytic preimage. -/
theorem constantNormalizationComplex_stalk_exact (x : CentralSpace C ε) :
    ((constantNormalizationComplex C ε hε hε1 hC hR).map
      (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x)).Exact := by
  let K := SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x
  let i := K.mapShortComplex.map
    (constantNormalizationComplexComparison C ε hε hε1 hC hR)
  exact ab_exact_of_middle_retract_components i.τ₂ i.τ₃
    (reducedStalkConstantRetractionHom C ε hε hε1 hC hR x)
    (normalizationStalkConstantRetractionHom C ε hε hε1 hC hR x)
    i.comm₂₃ (normalization_stalkConstantRetraction_naturality C ε hε hε1 hC hR x)
    (normalizationStalkConstantRetraction_comp C ε hε hε1 hC hR x)
    ((TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
      (normalizationComplex C ε hε hε1 hC hR)).mp
        (normalizationComplex_exact C ε hε hε1 hC hR) x)

/-- Exactness at the genuine normalization constant direct image. -/
theorem constantNormalizationComplex_exact :
    (constantNormalizationComplex C ε hε hε1 hC hR).Exact :=
  (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
    (constantNormalizationComplex C ε hε hε1 hC hR)).mpr
      (constantNormalizationComplex_stalk_exact C ε hε hε1 hC hR)

/-- The actual constant double-curve stalk complex is exact, using the
actual finite-fibre retractions and the actual signed difference map. -/
theorem constantBoundaryComplex_stalk_exact (x : CentralSpace C ε) :
    ((constantBoundaryComplex C ε hε hε1 hC hR).map
      (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x)).Exact := by
  let K := SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x
  let i := K.mapShortComplex.map
    (constantBoundaryComplexComparison C ε hε hε1 hC hR)
  exact ab_exact_of_middle_retract_components i.τ₂ i.τ₃
    (normalizationStalkConstantRetractionHom C ε hε hε1 hC hR x)
    (boundaryStalkConstantRetractionHom C ε hε hε1 hC hR x)
    i.comm₂₃ (deltaZero_stalkConstantRetraction_naturality C ε hε hε1 hC hR x)
    (boundaryStalkConstantRetraction_comp C ε hε hε1 hC hR x)
    ((TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
      (boundaryComplex C ε hε hε1 hC hR)).mp
        (boundaryComplex_exact C ε hε hε1 hC hR) x)

/-- Exactness at the genuine sum of the three constant curve direct images. -/
theorem constantBoundaryComplex_exact :
    (constantBoundaryComplex C ε hε hε1 hC hR).Exact :=
  (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
    (constantBoundaryComplex C ε hε hε1 hC hR)).mpr
      (constantBoundaryComplex_stalk_exact C ε hε hε1 hC hR)

include hε1 hC hR

/-- The actual last constant differential is surjective on every stalk.
The endpoint values of an analytic lift are unchanged by the constructed
boundary stalk retraction. -/
theorem constantDeltaOne_stalk_surjective (x : CentralSpace C ε) :
    Function.Surjective
      ((SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
        (constantDeltaOne C ε hε)) := by
  intro v
  obtain ⟨β, hβ⟩ := deltaOne_stalk_surjective C ε hε hε1 hC hR x v
  refine ⟨boundaryStalkConstantRetractionHom C ε hε hε1 hC hR x β, ?_⟩
  exact (ConcreteCategory.congr_hom
    (deltaOne_stalkConstantRetraction_naturality C ε hε hε1 hC hR x) β).trans hβ

/-- Exactness at the actual two-point scalar skyscraper term. -/
theorem constantTerminalComplex_exact : (constantTerminalComplex C ε hε).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
    (constantTerminalComplex C ε hε)).mpr
  intro x
  let K := SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x
  have hz : ((constantTerminalComplex C ε hε).map K).g = 0 := K.map_zero _ _
  apply (((constantTerminalComplex C ε hε).map K).exact_iff_epi hz).mpr
  exact ConcreteCategory.epi_of_surjective _
    (constantDeltaOne_stalk_surjective C ε hε hε1 hC hR x)

/-- The actual constant endpoint differential is an epimorphism of sheaves. -/
theorem constantDeltaOne_epi : Epi (constantDeltaOne C ε hε) :=
  ((constantTerminalComplex C ε hε).exact_iff_epi rfl).mp
    (constantTerminalComplex_exact C ε hε hε1 hC hR)

/-- The genuine constant analogue of the normalization resolution is exact,
with both zero endpoints, the three actual curves, the two actual triple
points, and the literal source signs. -/
theorem constantResolution_exact : (constantResolution C ε hε hε1 hC hR).Exact where
  toIsComplex := constantResolution_isComplex C ε hε hε1 hC hR
  exact i hi := by
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact constantInitialComplex_exact C ε hε
    · exact constantNormalizationComplex_exact C ε hε hε1 hC hR
    · exact constantBoundaryComplex_exact C ε hε hε1 hC hR
    · exact constantTerminalComplex_exact C ε hε hε1 hC hR

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
