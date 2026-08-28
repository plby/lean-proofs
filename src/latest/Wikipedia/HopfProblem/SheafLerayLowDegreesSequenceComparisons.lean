import Wikipedia.HopfProblem.SheafLerayLowDegreesSequence
import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractNaturality
import Wikipedia.HopfProblem.SheafLerayLowDegreesCoefficientMaps

/-!
# Element formulas for the genuine low-degree Leray maps

The formulas retain the actual resolution comparisons and abstract
connecting maps.  They also expose the inverse comparison squares
needed for coefficient naturality, without expanding the constructions
of native homology and Ext groups.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees

open SheafHigherDirectImage
open CuspNormalization.SheafCohomologyFinitePushforward (integerSheaf)

attribute [local instance] canonicalPushedInjectiveZero
attribute [local irreducible] Abstract.firstMap

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {F G : AbelianSheaf X}

/-- Inflation is the native Ext injection under the actual term comparisons. -/
theorem inflation_apply (x : CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) 1) :
    inflation f F x = (sourceCohomologyIso f F (injectiveResolution F) 1).inv
      (Abstract.firstMap (integerSheaf Y) (pushedResolution f (injectiveResolution F))
        ((homologyZeroCohomologyIso f (injectiveResolution F) 1).inv x)) := by
  dsimp only [inflation, firstComplex, transportComplex, Abstract.firstComplex,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
    AddCommGrpCat.Hom.hom, Iso.symm]
  apply congrArg ((sourceCohomologyIso f F (injectiveResolution F) 1).inv.hom)
  apply congrArg ((Abstract.firstMap (integerSheaf Y)
    (pushedResolution f (injectiveResolution F))).hom)
  rfl

/-- The edge map uses the original source and derived-image comparisons. -/
theorem edge_apply (x : CategoryTheory.Sheaf.H.{0} F 1) :
    edge f F x = (homologyOneExtZeroIso f (injectiveResolution F)).inv
      (Abstract.edgeMap (integerSheaf Y) (pushedResolution f (injectiveResolution F))
        ((sourceCohomologyIso f F (injectiveResolution F) 1).hom x)) := rfl

/-- The transgression uses the actual pair of Ext connecting morphisms. -/
theorem transgression_apply (x : CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 0) :
    transgression f F x = (homologyZeroCohomologyIso f (injectiveResolution F) 2).hom
      (Abstract.transgression (integerSheaf Y) (pushedResolution f (injectiveResolution F))
        ((homologyOneExtZeroIso f (injectiveResolution F)).hom x)) := rfl

variable (g : F ⟶ G)

/-- The inverse degree-zero comparison commutes with actual coefficient maps. -/
@[reassoc] theorem coefficient_homologyZeroCohomologyIso_inv_naturality (n : ℕ) :
    AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map ((pushforward f).map g) n) ≫
        (homologyZeroCohomologyIso f (injectiveResolution G) n).inv =
      (homologyZeroCohomologyIso f (injectiveResolution F) n).inv ≫
        (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) n).map
          (HomologicalComplex.homologyMap (coefficientResolutionMap f g) 0) :=
  inverse_naturality
    (homologyZeroCohomologyIso f (injectiveResolution F) n)
    (homologyZeroCohomologyIso f (injectiveResolution G) n) _ _
    (coefficient_homologyZeroCohomologyIso_naturality f g n)

/-- The forward source comparison commutes with actual coefficient maps. -/
@[reassoc] theorem coefficient_sourceCohomologyIso_hom_naturality (n : ℕ) :
    AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map g n) ≫
        (sourceCohomologyIso f G (injectiveResolution G) n).hom =
      (sourceCohomologyIso f F (injectiveResolution F) n).hom ≫
        HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (op (integerSheaf Y))).mapHomologicalComplex _).map
            (coefficientResolutionMap f g)) n :=
  inverse_naturality
    (sourceCohomologyIso f F (injectiveResolution F) n).symm
    (sourceCohomologyIso f G (injectiveResolution G) n).symm _ _
    (coefficient_sourceCohomologyIso_inv_naturality f g n)

/-- The forward derived-image comparison commutes with actual coefficient maps. -/
@[reassoc] theorem coefficient_homologyOneExtZeroIso_hom_naturality :
    AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map ((functor f 1).map g) 0) ≫
        (homologyOneExtZeroIso f (injectiveResolution G)).hom =
      (homologyOneExtZeroIso f (injectiveResolution F)).hom ≫
        (preadditiveCoyoneda.obj (op (integerSheaf Y))).map
          (HomologicalComplex.homologyMap (coefficientResolutionMap f g) 1) :=
  inverse_naturality
    (homologyOneExtZeroIso f (injectiveResolution F)).symm
    (homologyOneExtZeroIso f (injectiveResolution G)).symm _ _
    (coefficient_homologyOneExtZeroIso_inv_naturality f g)

end Wikipedia.HopfProblem.SheafLerayLowDegrees
