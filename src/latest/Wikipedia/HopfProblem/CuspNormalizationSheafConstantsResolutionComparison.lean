import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionDifferentials
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspDifferentials

/-!
# The actual endpoint comparison and constant complex identity

The actual constants inclusions commute with each independent endpoint
evaluation and hence with their actual alternating sum. Since the
target skyscraper term is the same, the proved holomorphic complex
identity then proves the actual constant complex identity as well.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff ZeroObject

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual alternating endpoint comparison at one triple point. -/
theorem deltaOneAt_constants_naturality (t : Fin 2) :
    boundaryConstantsMap C ε hε hε1 hC hR ≫ deltaOneAt C ε hε hε1 hC hR t =
      constantDeltaOneAt C ε hε t := by
  have h (k : Fin 3) :
      boundaryConstantsMap C ε hε hε1 hC hR ≫
          (biproduct.π (curveSheaf C ε hε hε1 hC hR) k ≫
            curveEvaluation C ε hε hε1 hC hR k t) =
        biproduct.π (curveConstantSheaf C ε hε) k ≫ curveConstantEvaluation C ε hε k t := by
    rw [← Category.assoc, boundaryConstantsMap_component, Category.assoc,
      curveEvaluation_constants_naturality]
  simp only [deltaOneAt, constantDeltaOneAt, Preadditive.comp_add,
    Preadditive.comp_sub, h]

/-- The final actual comparison square has identity on the two genuine
scalar skyscraper summands. -/
theorem deltaOne_constants_naturality :
    boundaryConstantsMap C ε hε hε1 hC hR ≫ deltaOne C ε hε hε1 hC hR =
      constantDeltaOne C ε hε := by
  apply biproduct.hom_ext
  intro t
  rw [Category.assoc, deltaOne_component, constantDeltaOne_component]
  exact deltaOneAt_constants_naturality C ε hε hε1 hC hR t

/-- The actual constant boundary and endpoint differentials compose to
zero, proved from the actual holomorphic identity and comparison squares. -/
theorem constantDeltaZero_constantDeltaOne :
    constantDeltaZero C ε hε hε1 hC hR ≫ constantDeltaOne C ε hε = 0 := by
  rw [← deltaOne_constants_naturality C ε hε hε1 hC hR, ← Category.assoc,
    ← deltaZero_constants_naturality C ε hε hε1 hC hR, Category.assoc,
    deltaZero_deltaOne, comp_zero]

/-- The two actual nonzero constant differentials as a genuine short complex. -/
def constantBoundaryComplex :
    ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε))) where
  X₁ := normalizationConstantSheaf C ε hε
  X₂ := boundaryConstantSheaf C ε hε
  X₃ := tripleSheaf C ε hε
  f := constantDeltaZero C ε hε hε1 hC hR
  g := constantDeltaOne C ε hε
  zero := constantDeltaZero_constantDeltaOne C ε hε hε1 hC hR

/-- The actual final zero endpoint of the constant normalization sequence. -/
def constantTerminalComplex :
    ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε))) where
  X₁ := boundaryConstantSheaf C ε hε
  X₂ := tripleSheaf C ε hε
  X₃ := 0
  f := constantDeltaOne C ε hε
  g := 0
  zero := comp_zero

/-- Actual termwise inclusion is a morphism of the middle short complexes. -/
def constantBoundaryComplexComparison :
    constantBoundaryComplex C ε hε hε1 hC hR ⟶ boundaryComplex C ε hε hε1 hC hR where
  τ₁ := normalizationConstantsMap C ε hε
  τ₂ := boundaryConstantsMap C ε hε hε1 hC hR
  τ₃ := 𝟙 _
  comm₁₂ := deltaZero_constants_naturality C ε hε hε1 hC hR
  comm₂₃ := (deltaOne_constants_naturality C ε hε hε1 hC hR).trans
    (Category.comp_id (constantDeltaOne C ε hε)).symm

/-- The actual endpoint comparison is identity on the skyscraper and
zero-object terms. -/
def constantTerminalComplexComparison :
    constantTerminalComplex C ε hε ⟶ terminalComplex C ε hε hε1 hC hR where
  τ₁ := boundaryConstantsMap C ε hε hε1 hC hR
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := (deltaOne_constants_naturality C ε hε hε1 hC hR).trans
    (Category.comp_id (constantDeltaOne C ε hε)).symm
  comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
