import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionPullbacks
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionBiproduct
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspDifferentials

/-!
# Pointwise complex scalars on every actual normalization resolution term

The fixed cusp and curve atlases are supplied explicitly in data
definitions. All actions are on the original actual sheaves.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution

open SheafResolution CuspQuotient ToricCharts ToricSpace
open CuspQuotient.NormalizationCurves

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- Actual reduced sections for the fixed cusp atlas. -/
abbrev ReducedSections (U : Opens (CentralSpace C ε)) : Type :=
  @SheafReduced.Section (CoordinateSpace 3) (CoordinateSpace 3) _ _ _
    (QuotientSpace C ε) _ (CuspQuotient.chartedSpace C ε hε hε1 hC hR)
    𝓘(ℂ, CoordinateSpace 3) (centralSet C ε) U

/-- The original pointwise module on actual reduced holomorphic sections. -/
instance reducedSection_module (U : Opens (CentralSpace C ε)) :
    Module ℂ ((reducedSheaf C ε hε hε1 hC hR).presheaf.obj (op U)) :=
  inferInstanceAs (Module ℂ (ReducedSections C ε hε hε1 hC hR U))

/-- The actual reduced structure sheaf's pointwise scalar action. -/
def reducedSheafScalarEnd : ℂ →+* End (reducedSheaf C ε hε hε1 hC hR) :=
  @reducedScalarEnd (CoordinateSpace 3) (CoordinateSpace 3) _ _ _
    (QuotientSpace C ε) _ (CuspQuotient.chartedSpace C ε hε hε1 hC hR)
    𝓘(ℂ, CoordinateSpace 3) (centralSet C ε)

@[simp] theorem reducedSheafScalarEnd_apply (c : ℂ) (U : Opens (CentralSpace C ε))
    (s : (reducedSheaf C ε hε hε1 hC hR).presheaf.obj (op U)) :
    (reducedSheafScalarEnd C ε hε hε1 hC hR c).hom.app (op U) s = c • s := rfl

/-- Pointwise scalars on the genuine normalization direct image. -/
def normalizationScalarEnd : ℂ →+* End (normalizationSheaf C ε hε) :=
  pushedScalarEnd 𝓘(ℂ, CoordinateSpace 2) (normalizationMap C ε hε)

/-- Pointwise scalars on the genuine source-ordered curve direct images. -/
def curveScalarEnd (k : Fin 3) : ℂ →+* End (curveSheaf C ε hε hε1 hC hR k) :=
  @pushedScalarEnd ℂ ℂ _ _ _ 𝓘(ℂ) (sourceDoubleCurve C ε hε k) _
    (curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k))
    (CentralSpace C ε) _ (sourceCurveMap C ε hε k)

/-- The componentwise action on the actual three-curve direct sum. -/
def boundaryScalarEnd : ℂ →+* End (boundarySheaf C ε hε hε1 hC hR) :=
  biproductScalarEnd (curveSheaf C ε hε hε1 hC hR) (curveScalarEnd C ε hε hε1 hC hR)

@[reassoc] theorem boundaryScalarEnd_π (c : ℂ) (k : Fin 3) :
    boundaryScalarEnd C ε hε hε1 hC hR c ≫
        biproduct.π (curveSheaf C ε hε hε1 hC hR) k =
      biproduct.π (curveSheaf C ε hε hε1 hC hR) k ≫ curveScalarEnd C ε hε hε1 hC hR k c :=
  biproductScalarEnd_π _ _ _ _

/-- Literal complex multiplication on the actual P or Q skyscraper. -/
def triplePointScalarEnd (t : Fin 2) : ℂ →+* End (triplePointSheaf C ε hε t) :=
  skyscraperScalarEnd (X := TopCat.of (CentralSpace C ε)) (triplePoint C ε hε t)

/-- The componentwise action on the two actual triple-point skyscrapers. -/
def tripleScalarEnd : ℂ →+* End (tripleSheaf C ε hε) :=
  biproductScalarEnd (triplePointSheaf C ε hε) (triplePointScalarEnd C ε hε)

@[reassoc] theorem tripleScalarEnd_π (c : ℂ) (t : Fin 2) :
    tripleScalarEnd C ε hε c ≫ biproduct.π (triplePointSheaf C ε hε) t =
      biproduct.π (triplePointSheaf C ε hε) t ≫ triplePointScalarEnd C ε hε t c :=
  biproductScalarEnd_π _ _ _ _

/-- The additive group is the existing group on the genuine Ext cohomology. -/
instance reducedCohomology_addCommGroup (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The genuine degree-`n` Ext cohomology inherits the actual sheaf scalar action. -/
instance reducedCohomology_module (n : ℕ) :
    Module ℂ (CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) n) :=
  SheafCohomology.cohomologyModule (reducedSheaf C ε hε hε1 hC hR)
    (reducedSheafScalarEnd C ε hε hε1 hC hR) n

/-- This scalar action is induced by the original pointwise sheaf endomorphism. -/
theorem reducedCohomology_smul (n : ℕ) (c : ℂ)
    (a : CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) n) :
    c • a = CategoryTheory.Sheaf.H.map (reducedSheafScalarEnd C ε hε hε1 hC hR c) n a := rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution
