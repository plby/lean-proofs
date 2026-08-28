import Wikipedia.HopfProblem.SheafLerayLowDegreesSequenceElementNaturality

/-!
# Coefficient naturality of the genuine low-degree Leray sequence

The maps of the unconditional native sequence commute with every
morphism of the actual coefficient sheaf.  In the edge term the map
is induced by the genuine first right-derived pushforward functor.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees

open SheafHigherDirectImage

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {F G : AbelianSheaf X} (g : F ⟶ G)

/-- Inflation commutes with every actual coefficient morphism. -/
@[reassoc] theorem firstComplex_f_naturality :
    AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map ((pushforward f).map g) 1) ≫
        (firstComplex f G).f =
      (firstComplex f F).f ≫ AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map g 1) := by
  apply AddCommGrpCat.ext
  intro x
  change inflation f G (CategoryTheory.Sheaf.H.map ((pushforward f).map g) 1 x) =
    CategoryTheory.Sheaf.H.map g 1 (inflation f F x)
  exact inflation_naturality f g x

/-- The edge map commutes with the actual first right-derived coefficient map. -/
@[reassoc] theorem firstComplex_g_naturality :
    AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map g 1) ≫ (firstComplex f G).g =
      (firstComplex f F).g ≫
        AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map ((functor f 1).map g) 0) := by
  apply AddCommGrpCat.ext
  intro x
  change edge f G (CategoryTheory.Sheaf.H.map g 1 x) =
    CategoryTheory.Sheaf.H.map ((functor f 1).map g) 0 (edge f F x)
  exact edge_naturality f g x

/-- The transgression commutes with actual coefficient morphisms. -/
@[reassoc] theorem secondComplex_g_naturality :
    AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map ((functor f 1).map g) 0) ≫
        (secondComplex f G).g =
      (secondComplex f F).g ≫
        AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map ((pushforward f).map g) 2) := by
  apply AddCommGrpCat.ext
  intro x
  change transgression f G (CategoryTheory.Sheaf.H.map ((functor f 1).map g) 0 x) =
    CategoryTheory.Sheaf.H.map ((pushforward f).map g) 2 (transgression f F x)
  exact transgression_naturality f g x

end Wikipedia.HopfProblem.SheafLerayLowDegrees
