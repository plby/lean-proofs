import Wikipedia.HopfProblem.SheafLerayLowDegreesSequenceComparisons

/-!
# Naturality on the actual elements of the Leray sequence

Each equality follows the three original comparison squares separately.
This keeps native resolution and homology morphisms intact throughout
the proof.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees

open SheafHigherDirectImage
open CuspNormalization.SheafCohomologyFinitePushforward (integerSheaf)

attribute [local instance] canonicalPushedInjectiveZero
attribute [local irreducible] Abstract.firstMap

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {F G : AbelianSheaf X} (g : F ⟶ G)

/-- Naturality on the actual elements of degree-one cohomology. -/
theorem inflation_naturality (x : CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) 1) :
    inflation f G (CategoryTheory.Sheaf.H.map ((pushforward f).map g) 1 x) =
      CategoryTheory.Sheaf.H.map g 1 (inflation f F x) := by
  rw [inflation_apply, inflation_apply]
  let a := (homologyZeroCohomologyIso f (injectiveResolution F) 1).inv x
  have h₀ := ConcreteCategory.congr_hom
    (coefficient_homologyZeroCohomologyIso_inv_naturality f g 1) x
  have h₁ := ConcreteCategory.congr_hom
    (Abstract.firstMap_naturality (integerSheaf Y) (coefficientResolutionMap f g)) a
  have h₂ := ConcreteCategory.congr_hom
    (coefficient_sourceCohomologyIso_inv_naturality f g 1)
    (Abstract.firstMap (integerSheaf Y) (pushedResolution f (injectiveResolution F)) a)
  exact (congrArg (fun b => (sourceCohomologyIso f G (injectiveResolution G) 1).inv
    (Abstract.firstMap (integerSheaf Y) (pushedResolution f (injectiveResolution G)) b)) h₀).trans
      ((congrArg (sourceCohomologyIso f G (injectiveResolution G) 1).inv h₁).trans h₂)

/-- Naturality on actual cohomology classes for the genuine Leray edge map. -/
theorem edge_naturality (x : CategoryTheory.Sheaf.H.{0} F 1) :
    edge f G (CategoryTheory.Sheaf.H.map g 1 x) =
      CategoryTheory.Sheaf.H.map ((functor f 1).map g) 0 (edge f F x) := by
  rw [edge_apply, edge_apply]
  let a := (sourceCohomologyIso f F (injectiveResolution F) 1).hom x
  have h₀ := ConcreteCategory.congr_hom
    (coefficient_sourceCohomologyIso_hom_naturality f g 1) x
  have h₁ := ConcreteCategory.congr_hom
    (Abstract.edgeMap_naturality (integerSheaf Y) (coefficientResolutionMap f g)) a
  have h₂ := ConcreteCategory.congr_hom
    (coefficient_homologyOneExtZeroIso_inv_naturality f g)
    (Abstract.edgeMap (integerSheaf Y) (pushedResolution f (injectiveResolution F)) a)
  exact (congrArg (fun b => (homologyOneExtZeroIso f (injectiveResolution G)).inv
    (Abstract.edgeMap (integerSheaf Y) (pushedResolution f (injectiveResolution G)) b)) h₀).trans
      ((congrArg (homologyOneExtZeroIso f (injectiveResolution G)).inv h₁).trans h₂)

/-- Naturality on actual global sections of the first higher direct image. -/
theorem transgression_naturality (x : CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 0) :
    transgression f G (CategoryTheory.Sheaf.H.map ((functor f 1).map g) 0 x) =
      CategoryTheory.Sheaf.H.map ((pushforward f).map g) 2 (transgression f F x) := by
  rw [transgression_apply, transgression_apply]
  let a := (homologyOneExtZeroIso f (injectiveResolution F)).hom x
  have h₀ := ConcreteCategory.congr_hom
    (coefficient_homologyOneExtZeroIso_hom_naturality f g) x
  have h₁ := ConcreteCategory.congr_hom
    (Abstract.transgression_naturality (integerSheaf Y) (coefficientResolutionMap f g)) a
  have h₂ := ConcreteCategory.congr_hom
    (coefficient_homologyZeroCohomologyIso_naturality f g 2)
    (Abstract.transgression (integerSheaf Y) (pushedResolution f (injectiveResolution F)) a)
  exact (congrArg (fun b => (homologyZeroCohomologyIso f (injectiveResolution G) 2).hom
    (Abstract.transgression (integerSheaf Y)
      (pushedResolution f (injectiveResolution G)) b)) h₀).trans
      ((congrArg (homologyZeroCohomologyIso f (injectiveResolution G) 2).hom h₁).trans h₂)

end Wikipedia.HopfProblem.SheafLerayLowDegrees
