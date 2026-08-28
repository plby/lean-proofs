import Wikipedia.HopfProblem.SheafHigherDirectImageExt
import Wikipedia.HopfProblem.SheafHigherDirectImageSections
import Wikipedia.HopfProblem.SheafHigherDirectImagePresheaf

/-!
# Resolution cohomology and the genuine sheaf-cohomology presheaf

Mathlib's Ext comparison for an injective resolution identifies Hom-
complex cohomology with the actual Ext groups.  The free sheaf on an
open represents sections on that open, naturally under restriction.
Combining the two comparisons identifies presheaves, retaining the
actual cohomological restriction maps.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafHigherDirectImage

open HolomorphicSheafCohomology.OpenRestriction

variable {X Y : TopCat.{0}} {F : AbelianSheaf X}

/-- The represented Hom-complex homology is the actual homology
presheaf, not just a pointwise family of isomorphic groups. -/
def representedHomologyPresheafIso (K : CochainComplex (AbelianSheaf X) ℕ) (n : ℕ) :
    (Sections.freeOpenFunctor X).op ⋙ ExtBridge.coyonedaHomologyFunctor K n ≅
      homologyPresheaf K n :=
  NatIso.ofComponents (fun U => Sections.homSectionsHomologyIso K U.unop n)
    (fun i => Sections.homSectionsHomologyIso_hom_naturality_open K i.unop n)

/-- The cohomology presheaf of an actual injective resolution is the
native Ext-defined sheaf-cohomology presheaf, naturally in the open set. -/
def resolutionCohomologyPresheafIso (I : InjectiveResolution F) (n : ℕ) :
    CategoryTheory.Sheaf.cohomologyPresheaf F n ≅ homologyPresheaf I.cocomplex n :=
  Functor.isoWhiskerLeft (Sections.freeOpenFunctor X).op (ExtBridge.extHomologyNatIso I n) ≪≫
    representedHomologyPresheafIso I.cocomplex n

/-- The pushed-forward resolution computes the actual source
cohomology presheaf on inverse-image opens. -/
def pushedResolutionCohomologyPresheafIso (f : X ⟶ Y)
    (I : InjectiveResolution F) (n : ℕ) :
    resolutionPresheaf f I n ≅
      (Opens.map f).op ⋙ CategoryTheory.Sheaf.cohomologyPresheaf F n :=
  resolutionPresheafPushforwardIso f I n ≪≫
    Functor.isoWhiskerLeft (Opens.map f).op (resolutionCohomologyPresheafIso I n).symm

end Wikipedia.HopfProblem.SheafHigherDirectImage
