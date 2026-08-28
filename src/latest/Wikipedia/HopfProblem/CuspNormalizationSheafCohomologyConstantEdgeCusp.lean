import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyConstantEdgeNaturality
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyConstantEdgeAcyclic
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyConstantEdgeGlobals
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyDimensions

/-!
# The actual constant-to-holomorphic H¹ and edge H² comparisons

These are unconditional statements for the actual cusp and its actual
normalization. In degree two the domain is the literal kernel of the map
to the constant normalization term; that term is not assumed H²-acyclic.
All cohomology here is Mathlib's genuine sheaf Ext cohomology. No singular
cohomology identification or cup-product calculation is asserted.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge

open SheafResolution SheafCohomologyResolution CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The genuine H² map of the actual constant normalization pullback. -/
def constantH2EdgeMap :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 2) ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (normalizationConstantSheaf C ε hε) 2) :=
  (CategoryTheory.Sheaf.functorH _ 2).map (normalizationConstantPullback C ε hε)

/-- The literal categorical kernel of the actual normalization H² map. -/
abbrev constantH2EdgeKernel : AddCommGrpCat := kernel (constantH2EdgeMap C ε hε)

/-- Only the proved actual H¹ vanishings are used to identify this edge kernel. -/
def constantH2EdgeCokernelIso : constantH2EdgeKernel C ε hε ≅
    cokernel (constantAugmentedResolution C ε hε hε1 hC hR).globalComplex.g := by
  let R := constantAugmentedResolution C ε hε hε1 hC hR
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1) :=
    normalizationConstant_h1_subsingleton C ε hε hε1 hC hR
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1) :=
    boundaryConstant_h1_subsingleton C ε hε hε1 hC hR
  exact h2EdgeIso R

/-- The original coefficients map on H² restricted by the original kernel inclusion. -/
def constantsH2OnEdge : constantH2EdgeKernel C ε hε ⟶
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 2) :=
  kernel.ι (constantH2EdgeMap C ε hε) ≫
    (CategoryTheory.Sheaf.functorH _ 2).map (reducedConstantsMap C ε hε hε1 hC hR)

/-- The actual constants H² map is an isomorphism on the literal edge kernel. -/
theorem constantsH2OnEdge_isIso : IsIso (constantsH2OnEdge C ε hε hε1 hC hR) := by
  let R := constantAugmentedResolution C ε hε hε1 hC hR
  let S := normalizationAugmentedResolution C ε hε hε1 hC hR
  let φ := constantsAugmentedResolutionComparison C ε hε hε1 hC hR
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1) :=
    normalizationConstant_h1_subsingleton C ε hε hε1 hC hR
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1) :=
    boundaryConstant_h1_subsingleton C ε hε hε1 hC hR
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 1) :=
    SheafCohomology.normalizationSheaf_higher_subsingleton C ε hε hε1 hC hR 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 2) :=
    SheafCohomology.normalizationSheaf_higher_subsingleton C ε hε hε1 hC hR 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₂ 1) :=
    boundarySheaf_higher_subsingleton C ε hε hε1 hC hR 0
  let : IsIso φ.globalCokernelMap := constantsGlobalCokernelMap_isIso C ε hε hε1 hC hR
  change IsIso (h2EdgeToCohomology φ)
  exact h2EdgeToCohomology_isIso φ

/-- This isomorphism's forward map is the original coefficient map on the actual kernel. -/
def constantsH2EdgeIso : constantH2EdgeKernel C ε hε ≅
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 2) := by
  let := constantsH2OnEdge_isIso C ε hε hε1 hC hR
  exact asIso (constantsH2OnEdge C ε hε hε1 hC hR)

@[simp] theorem constantsH2EdgeIso_hom :
    (constantsH2EdgeIso C ε hε hε1 hC hR).hom =
      kernel.ι (constantH2EdgeMap C ε hε) ≫
        (CategoryTheory.Sheaf.functorH _ 2).map (reducedConstantsMap C ε hε hε1 hC hR) := rfl

/-- The genuine degree-one coefficient map, without choosing resolution coordinates. -/
def constantsH1Map : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1) ⟶
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 1) :=
  (CategoryTheory.Sheaf.functorH _ 1).map (reducedConstantsMap C ε hε hε1 hC hR)

/-- The original constants inclusion induces an unconditional native H¹ isomorphism. -/
theorem constantsH1Map_isIso : IsIso (constantsH1Map C ε hε hε1 hC hR) := by
  let R := constantAugmentedResolution C ε hε hε1 hC hR
  let S := normalizationAugmentedResolution C ε hε hε1 hC hR
  let φ := constantsAugmentedResolutionComparison C ε hε hε1 hC hR
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1) :=
    normalizationConstant_h1_subsingleton C ε hε hε1 hC hR
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 1) :=
    SheafCohomology.normalizationSheaf_higher_subsingleton C ε hε hε1 hC hR 0
  let : IsIso φ.globalMap := constantsGlobalMap_isIso C ε hε hε1 hC hR
  exact h1Map_isIso_of_globalMap φ

/-- The degree-one isomorphism retains the original coefficient map as its forward map. -/
def constantsH1Iso : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1) ≅
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 1) := by
  let := constantsH1Map_isIso C ε hε hε1 hC hR
  exact asIso (constantsH1Map C ε hε hε1 hC hR)

@[simp] theorem constantsH1Iso_hom :
    (constantsH1Iso C ε hε hε1 hC hR).hom =
      (CategoryTheory.Sheaf.functorH _ 1).map (reducedConstantsMap C ε hε hε1 hC hR) := rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge
