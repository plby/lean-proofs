import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionSums
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationPullbackInjective

/-!
# The actual initial constant normalization complex

The normalization map is genuinely surjective, so its actual constant
pullback is a monomorphism without any analytic hypotheses. Together
with the already proved first zero-composite identity, this gives the
initial short complexes and their actual termwise maps to the
holomorphic normalization complexes.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff ZeroObject

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The actual first constant arrow is injective because the actual
normalization map is surjective. No complex-atlas assumptions are needed. -/
instance normalizationConstantPullback_mono : Mono (normalizationConstantPullback C ε hε) :=
  SheafConstants.additivePullbackMap_mono_of_surjective (normalizationMap C ε hε)
    (normalization_surjective C ε hε)

/-- The initial zero endpoint and the actual first constant arrow. -/
def constantInitialComplex :
    ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε))) where
  X₁ := 0
  X₂ := constantSheaf C ε
  X₃ := normalizationConstantSheaf C ε hε
  f := 0
  g := normalizationConstantPullback C ε hε
  zero := zero_comp

/-- Actual injectivity gives exactness at the first constant-sheaf term. -/
theorem constantInitialComplex_exact : (constantInitialComplex C ε hε).Exact :=
  ((constantInitialComplex C ε hε).exact_iff_mono rfl).mpr
    (normalizationConstantPullback_mono C ε hε)

variable (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The first two actual nonzero arrows form a genuine short complex. -/
def constantNormalizationComplex :
    ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε))) where
  X₁ := constantSheaf C ε
  X₂ := normalizationConstantSheaf C ε hε
  X₃ := boundaryConstantSheaf C ε hε
  f := normalizationConstantPullback C ε hε
  g := constantDeltaZero C ε hε hε1 hC hR
  zero := normalizationConstantPullback_constantDeltaZero C ε hε hε1 hC hR

/-- The actual inclusions give a morphism of the initial short complexes. -/
def constantInitialComplexComparison :
    constantInitialComplex C ε hε ⟶ initialComplex C ε hε hε1 hC hR where
  τ₁ := 𝟙 _
  τ₂ := reducedConstantsMap C ε hε hε1 hC hR
  τ₃ := normalizationConstantsMap C ε hε
  comm₁₂ := (Category.id_comp _).trans zero_comp.symm
  comm₂₃ := normalization_constants_naturality C ε hε hε1 hC hR

/-- The actual termwise inclusions give a morphism of the first two
nonzero arrows, with the independently constructed constant differential. -/
def constantNormalizationComplexComparison :
    constantNormalizationComplex C ε hε hε1 hC hR ⟶ normalizationComplex C ε hε hε1 hC hR where
  τ₁ := reducedConstantsMap C ε hε hε1 hC hR
  τ₂ := normalizationConstantsMap C ε hε
  τ₃ := boundaryConstantsMap C ε hε hε1 hC hR
  comm₁₂ := normalization_constants_naturality C ε hε hε1 hC hR
  comm₂₃ := deltaZero_constants_naturality C ε hε hε1 hC hR

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
