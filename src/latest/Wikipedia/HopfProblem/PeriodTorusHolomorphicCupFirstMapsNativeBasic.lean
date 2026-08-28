import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupFirstMapsSheaf
import Wikipedia.HopfProblem.SheafCupProductFunctions
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalNativeMapsComposition

/-!
# Naturality of the original native holomorphic cohomology comparison

The actual first-column resolution map induces the identity on the
original holomorphic sheaf. Genuine partial-resolution naturality and
the proved injectivity of the original terms therefore identify its
global homology maps with the original Ext comparison maps.
-/

noncomputable section

open CategoryTheory
open scoped Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstMaps

open SheafCupProduct

variable (p : PeriodDomain)

/-- The original scalar endomorphisms of the actual holomorphic sheaf. -/
abbrev sourceScalarEnd := CuspNormalization.SheafCohomology.holomorphicScalarEnd
  (modelWithCornersSelf ℂ ComplexPlane₂) p.Torus

local instance source_I0_injective :
    Injective (GodementExact.partialResolution (Derivation.holomorphicRingSheaf p)).I₀ :=
  GodementRing.godement_injective_of_scalarEnd _ (sourceScalarEnd p)

local instance source_I1_injective :
    Injective (GodementExact.partialResolution (Derivation.holomorphicRingSheaf p)).I₁ :=
  GodementRing.doubleGodement_injective_of_scalarEnd _ (sourceScalarEnd p)

local instance total_I0_injective : Injective (totalPartialResolution p).I₀ :=
  (totalOperators p).I0_injective

local instance total_I1_injective : Injective (totalPartialResolution p).I₁ :=
  (totalOperators p).I1_injective

theorem first_one_homology :
    (GodementExact.partialResolution (Derivation.holomorphicRingSheaf p)).h1Iso.hom ≫
        ShortComplex.homologyMap (firstToTotal p).globalOneMap =
      (totalPartialResolution p).h1Iso.hom := by
  have h := (firstToTotal p).h1Iso_naturality
  exact h.symm.trans (SheafSingularCupComparison.TotalNativeMaps.map_identity_comp
    (CategoryTheory.Sheaf.functorH _ 1) (PeriodTorusHolomorphicCohomology.holomorphicSheaf p)
    (totalPartialResolution p).h1Iso.hom)

theorem first_two_homology :
    (GodementExact.partialResolution (Derivation.holomorphicRingSheaf p)).h2Iso.hom ≫
        ShortComplex.homologyMap (firstToTotal p).globalTwoMap =
      (totalPartialResolution p).h2Iso.hom := by
  have h := (firstToTotal p).h2Iso_naturality
  exact h.symm.trans (SheafSingularCupComparison.TotalNativeMaps.map_identity_comp
    (CategoryTheory.Sheaf.functorH _ 2) (PeriodTorusHolomorphicCohomology.holomorphicSheaf p)
    (totalPartialResolution p).h2Iso.hom)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstMaps
