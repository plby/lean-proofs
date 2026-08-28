import Wikipedia.HopfProblem.CuspNormalizationSheafCuspInitial
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Actual finite direct sums in the cusp normalization complex

The curve term is the categorical direct sum of the three genuine curve
pushforwards. The last term is the direct sum of the two genuine Mathlib
skyscraper sheaves at the actual distinct triple points.
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

/-- The actual direct sum of the three double-curve direct images. -/
abbrev boundarySheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)) :=
  ⨁ curveSheaf C ε hε hε1 hC hR

/-- The three actual signed restriction differences as a single sheaf map. -/
def deltaZero : normalizationSheaf C ε hε ⟶ boundarySheaf C ε hε hε1 hC hR :=
  biproduct.lift (boundaryDifference C ε hε hε1 hC hR)

/-- Each coordinate is the literal signed difference along the actual two lifts. -/
@[reassoc (attr := simp)] theorem deltaZero_component (k : Fin 3) :
    deltaZero C ε hε hε1 hC hR ≫ biproduct.π (curveSheaf C ε hε hε1 hC hR) k =
      boundaryDifference C ε hε hε1 hC hR k :=
  biproduct.lift_π _ _

theorem normalizationPullback_deltaZero :
    normalizationPullback C ε hε hε1 hC hR ≫ deltaZero C ε hε hε1 hC hR = 0 := by
  apply biproduct.hom_ext
  intro k
  change (normalizationPullback C ε hε hε1 hC hR ≫ deltaZero C ε hε hε1 hC hR) ≫
      biproduct.π (curveSheaf C ε hε hε1 hC hR) k = _
  rw [Category.assoc, deltaZero_component, normalizationPullback_boundaryDifference, zero_comp]

/-- The actual two-point list, in the source's order `P,Q`. -/
def triplePoint (t : Fin 2) : CentralSpace C ε := ![pointP C ε hε, pointQ C ε hε] t

@[simp] theorem triplePoint_zero : triplePoint C ε hε 0 = pointP C ε hε := rfl

@[simp] theorem triplePoint_one : triplePoint C ε hε 1 = pointQ C ε hε := rfl

theorem triplePoint_injective : Function.Injective (triplePoint C ε hε) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim ((pointP_ne_pointQ C ε hε) hij)
  · exact False.elim ((pointP_ne_pointQ C ε hε) hij.symm)
  · rfl

/-- An actual complex-valued skyscraper sheaf at either actual triple point. -/
def triplePointSheaf (t : Fin 2) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)) := by
  classical
  exact skyscraperSheaf (triplePoint C ε hε t) (AddCommGrpCat.of ℂ)

/-- The actual last term `ℂ_P ⊕ ℂ_Q`. -/
abbrev tripleSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)) :=
  ⨁ triplePointSheaf C ε hε

/-- The actual initial segment with its zero endpoint. -/
def initialComplex : ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε))) where
  X₁ := 0
  X₂ := reducedSheaf C ε hε hε1 hC hR
  X₃ := normalizationSheaf C ε hε
  f := 0
  g := normalizationPullback C ε hε hε1 hC hR
  zero := zero_comp

/-- Injectivity has already been proved on the actual section functions. -/
theorem initialComplex_exact : (initialComplex C ε hε hε1 hC hR).Exact :=
  ((initialComplex C ε hε hε1 hC hR).exact_iff_mono rfl).mpr
    (normalizationPullback_mono C ε hε hε1 hC hR)

/-- The first two nonzero arrows of the actual sheaf complex. -/
def normalizationComplex :
    ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε))) where
  X₁ := reducedSheaf C ε hε hε1 hC hR
  X₂ := normalizationSheaf C ε hε
  X₃ := boundarySheaf C ε hε hε1 hC hR
  f := normalizationPullback C ε hε hε1 hC hR
  g := deltaZero C ε hε hε1 hC hR
  zero := normalizationPullback_deltaZero C ε hε hε1 hC hR

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
