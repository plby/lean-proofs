import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsCusp
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspSums

/-!
# Actual finite direct sums in the constant normalization sequence

The boundary term is the categorical direct sum of the actual constant
pushforwards from the three double curves. Its differential and its
comparison to the holomorphic boundary term use the proved actual
source-oriented restriction maps, with no assumption of exactness.
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

/-- The genuine direct sum of the actual constant double-curve pushforwards. -/
abbrev boundaryConstantSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)) :=
  ⨁ curveConstantSheaf C ε hε

/-- The actual signed restrictions on constants, assembled as a genuine
map to the finite categorical direct sum. -/
def constantDeltaZero : normalizationConstantSheaf C ε hε ⟶ boundaryConstantSheaf C ε hε :=
  biproduct.lift (constantBoundaryDifference C ε hε hε1 hC hR)

@[reassoc (attr := simp)] theorem constantDeltaZero_component (k : Fin 3) :
    constantDeltaZero C ε hε hε1 hC hR ≫ biproduct.π (curveConstantSheaf C ε hε) k =
      constantBoundaryDifference C ε hε hε1 hC hR k :=
  biproduct.lift_π _ _

/-- The actual termwise constants inclusion on the boundary direct sums. -/
def boundaryConstantsMap :
    boundaryConstantSheaf C ε hε ⟶ boundarySheaf C ε hε hε1 hC hR :=
  biproduct.map (curveConstantsMap C ε hε hε1 hC hR)

@[reassoc (attr := simp)] theorem boundaryConstantsMap_component (k : Fin 3) :
    boundaryConstantsMap C ε hε hε1 hC hR ≫
        biproduct.π (curveSheaf C ε hε hε1 hC hR) k =
      biproduct.π (curveConstantSheaf C ε hε) k ≫ curveConstantsMap C ε hε hε1 hC hR k :=
  biproduct.map_π _ _

/-- Each actual component inclusion is injective, so the finite direct-sum
comparison is a monomorphism in the actual sheaf category. -/
instance boundaryConstantsMap_mono : Mono (boundaryConstantsMap C ε hε hε1 hC hR) :=
  biproduct.map_mono (curveConstantsMap C ε hε hε1 hC hR)

/-- The assembled middle square commutes in genuine additive sheaves. -/
theorem deltaZero_constants_naturality :
    normalizationConstantsMap C ε hε ≫ deltaZero C ε hε hε1 hC hR =
      constantDeltaZero C ε hε hε1 hC hR ≫ boundaryConstantsMap C ε hε hε1 hC hR := by
  apply biproduct.hom_ext
  intro k
  rw [Category.assoc, deltaZero_component, Category.assoc,
    boundaryConstantsMap_component, ← Category.assoc, constantDeltaZero_component]
  exact boundary_constants_naturality C ε hε hε1 hC hR k

/-- The first two actual constant arrows compose to zero. This follows
from the proved holomorphic complex identity and the injective actual
termwise comparison, not from an assumed constant complex. -/
theorem normalizationConstantPullback_constantDeltaZero :
    normalizationConstantPullback C ε hε ≫ constantDeltaZero C ε hε hε1 hC hR = 0 := by
  apply (cancel_mono (boundaryConstantsMap C ε hε hε1 hC hR)).mp
  rw [zero_comp, Category.assoc, ← deltaZero_constants_naturality,
    ← Category.assoc, ← normalization_constants_naturality C ε hε hε1 hC hR, Category.assoc,
    normalizationPullback_deltaZero, comp_zero]

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
