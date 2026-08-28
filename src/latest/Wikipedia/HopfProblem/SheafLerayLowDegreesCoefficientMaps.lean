import Wikipedia.HopfProblem.SheafLerayLowDegreesBasicNaturality
import Wikipedia.HopfProblem.SheafLerayLowDegreesPushforwardNaturality
import Wikipedia.HopfProblem.SheafLerayLowDegreesTransportNaturality

/-!
# Actual coefficient maps in the Leray term comparisons

Every morphism of coefficient sheaves has the native comparison map
between their chosen injective resolutions.  Pushing that map forward
gives the genuine maps on resolution homology.  The three canonical
term isomorphisms intertwine these with the actual sheaf-cohomology
maps, including the right-derived coefficient map in the edge term.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees

open SheafHigherDirectImage
open CuspNormalization.SheafCohomologyFinitePushforward (integerSheaf)

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {F G : AbelianSheaf X} (g : F ⟶ G)

/-- Pushforward of the native lift of an actual coefficient morphism. -/
def coefficientResolutionMap :
    pushedResolution f (injectiveResolution F) ⟶
      pushedResolution f (injectiveResolution G) :=
  ((pushforward f).mapHomologicalComplex _).map
    (InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F))

/-- The degree-zero homology comparison intertwines actual coefficient maps. -/
@[reassoc] theorem coefficient_homologyZeroCohomologyIso_naturality (n : ℕ) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) n).map
        (HomologicalComplex.homologyMap (coefficientResolutionMap f g) 0) ≫
      (homologyZeroCohomologyIso f (injectiveResolution G) n).hom =
    (homologyZeroCohomologyIso f (injectiveResolution F) n).hom ≫
      AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map ((pushforward f).map g) n) :=
  homologyZeroCohomologyIso_hom_naturality f g
    (injectiveResolution F) (injectiveResolution G)
    (InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F))
    (InjectiveResolution.desc_commutes_zero g (injectiveResolution G) (injectiveResolution F)) n

/-- The inverse source comparison is natural for genuine coefficient maps. -/
@[reassoc] theorem coefficient_sourceCohomologyIso_inv_naturality (n : ℕ) :
    HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op (integerSheaf Y))).mapHomologicalComplex _).map
          (coefficientResolutionMap f g)) n ≫
      (sourceCohomologyIso f G (injectiveResolution G) n).inv =
    (sourceCohomologyIso f F (injectiveResolution F) n).inv ≫
      AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map g n) :=
  inverse_naturality
    (sourceCohomologyIso f F (injectiveResolution F) n)
    (sourceCohomologyIso f G (injectiveResolution G) n) _ _
    (sourceCohomologyIso_hom_naturality f (injectiveResolution F) (injectiveResolution G) g
      (InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F))
      (InjectiveResolution.desc_commutes_zero g (injectiveResolution G)
        (injectiveResolution F)) n)

/-- The inverse edge-term comparison is natural for the actual first
right-derived coefficient map. -/
@[reassoc] theorem coefficient_homologyOneExtZeroIso_inv_naturality :
    (preadditiveCoyoneda.obj (op (integerSheaf Y))).map
        (HomologicalComplex.homologyMap (coefficientResolutionMap f g) 1) ≫
      (homologyOneExtZeroIso f (injectiveResolution G)).inv =
    (homologyOneExtZeroIso f (injectiveResolution F)).inv ≫
      AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map ((functor f 1).map g) 0) :=
  inverse_naturality
    (homologyOneExtZeroIso f (injectiveResolution F))
    (homologyOneExtZeroIso f (injectiveResolution G)) _ _
    (homologyOneExtZeroIso_hom_naturality f g (injectiveResolution F) (injectiveResolution G)
      (InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F))
      (InjectiveResolution.desc_commutes_zero g (injectiveResolution G)
        (injectiveResolution F)))

end Wikipedia.HopfProblem.SheafLerayLowDegrees
