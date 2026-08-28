import Wikipedia.HopfProblem.SheafCupProductScalarsResolution
import Wikipedia.HopfProblem.SheafCupProductGodementInjective
import Wikipedia.HopfProblem.SheafCupProductResolutionNaturality

/-!
# Scalar compatibility of the genuine H¹ and H² comparisons

The original scalar sheaf endomorphism and its literal multiplications
on Godement terms form the proved partial-resolution map. Actual
injectivity follows from the scalar action. Naturality of the genuine
Ext comparison therefore proves the following compatibility, without
transporting a scalar structure through a desired cohomology quotient.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafCupProduct.Scalars

open GodementRing GodementExact
open CuspNormalization.SheafCohomology

variable {X : TopCat.{0}} {F : RingSheaf X}

/-- The actual first comparison commutes with original scalar endomorphisms. -/
theorem h1Iso_scalar (c : Coefficients F) (z : ℂ) :
    letI : Injective (partialResolution F).I₀ :=
      godement_injective_of_scalarEnd F (scalarEnd c)
    (CategoryTheory.Sheaf.functorH _ 1).map (scalarEnd c z).asHom ≫
        (partialResolution F).h1Iso.hom =
      (partialResolution F).h1Iso.hom ≫
        ShortComplex.homologyMap (scalarPartialResolutionMap c z).globalOneMap := by
  let : Injective (partialResolution F).I₀ :=
    godement_injective_of_scalarEnd F (scalarEnd c)
  exact (scalarPartialResolutionMap c z).h1Iso_naturality

/-- The actual degree-two comparison has the same scalar compatibility. -/
theorem h2Iso_scalar (c : Coefficients F) (z : ℂ) :
    letI : Injective (partialResolution F).I₀ :=
      godement_injective_of_scalarEnd F (scalarEnd c)
    letI : Injective (partialResolution F).I₁ :=
      doubleGodement_injective_of_scalarEnd F (scalarEnd c)
    (CategoryTheory.Sheaf.functorH _ 2).map (scalarEnd c z).asHom ≫
        (partialResolution F).h2Iso.hom =
      (partialResolution F).h2Iso.hom ≫
        ShortComplex.homologyMap (scalarPartialResolutionMap c z).globalTwoMap := by
  let : Injective (partialResolution F).I₀ :=
    godement_injective_of_scalarEnd F (scalarEnd c)
  let : Injective (partialResolution F).I₁ :=
    doubleGodement_injective_of_scalarEnd F (scalarEnd c)
  exact (scalarPartialResolutionMap c z).h2Iso_naturality

end Wikipedia.HopfProblem.SheafCupProduct.Scalars
