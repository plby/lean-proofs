import Wikipedia.HopfProblem.SheafHigherDirectImageCohomology

/-!
# Components of the native cohomology-presheaf comparison

These formulas expose the actual resolution comparison and the actual
coefficient map at a single open set. They permit rewriting their
components without unfolding a complete naturality square at once.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkNaturality

open SheafHigherDirectImage HolomorphicSheafCohomology.OpenRestriction

variable {X : TopCat.{0}} {F G : AbelianSheaf X}

/-- At an open set, the original resolution comparison is the genuine
Ext-to-homology comparison followed by the section homology comparison. -/
theorem resolutionCohomologyPresheafIso_hom_app
    (I : InjectiveResolution F) (n : ℕ) (U : Opens X) :
    (resolutionCohomologyPresheafIso I n).hom.app (op U) =
      (ExtBridge.extHomologyIso I (freeOpen U) n).hom ≫
        (Sections.homSectionsHomologyIso I.cocomplex U n).hom := rfl

/-- The original coefficient map at an open is the actual Ext-functor
map from the free sheaf representing that open. -/
theorem cohomologyPresheafFunctor_map_app (g : F ⟶ G) (n : ℕ) (U : Opens X) :
    ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map g).app (op U) =
      ((extFunctor n).obj (op (freeOpen U))).map g := rfl

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkNaturality
