import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyGodement
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# The actual additive Godement and cokernel functors

Morphisms act on each actual stalk and then on the corresponding actual
skyscraper. This makes the product-of-stalks construction additive and
its germ inclusion natural. Taking the actual categorical cokernel gives
an additive successor functor, which retains the actual scalar and
partition-of-unity endomorphisms needed in the acyclicity argument.
-/

noncomputable section

open TopCat CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.Godement

attribute [local instance] Classical.propDecidable

variable {X : TopCat.{0}}

/-- The actual skyscraper functor is additive, as follows from its
proved preservation of products and the zero object. -/
instance skyscraperFunctor_additive (x : X) :
    (skyscraperSheafFunctor (C := AddCommGrpCat.{0}) x).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- A morphism acts on the actual stalk and its actual skyscraper. -/
def pointMap {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G) (x : X) :
    pointTerm F x ⟶ pointTerm G x :=
  (skyscraperSheafFunctor (C := AddCommGrpCat.{0}) x).map
    ((CuspNormalization.SheafBiproduct.stalkFunctor X x).map f)

/-- The actual product map on the Godement terms. -/
def map {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G) : sheaf F ⟶ sheaf G :=
  Pi.lift fun x => Pi.π (pointTerm F) x ≫ pointMap f x

@[reassoc] theorem map_component {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : F ⟶ G) (x : X) :
    map f ≫ Pi.π (pointTerm G) x = Pi.π (pointTerm F) x ≫ pointMap f x :=
  Pi.lift_π _ _

@[simp] theorem pointMap_id (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : X) :
    pointMap (𝟙 F) x = 𝟙 (pointTerm F x) := by
  let K := CuspNormalization.SheafBiproduct.stalkFunctor X x
  let S := skyscraperSheafFunctor (C := AddCommGrpCat.{0}) x
  exact (congrArg S.map (K.map_id F)).trans (S.map_id (K.obj F))

theorem pointMap_comp {F G H : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : F ⟶ G) (g : G ⟶ H) (x : X) :
    pointMap (f ≫ g) x = pointMap f x ≫ pointMap g x := by
  let K := CuspNormalization.SheafBiproduct.stalkFunctor X x
  let S := skyscraperSheafFunctor (C := AddCommGrpCat.{0}) x
  exact (congrArg S.map (K.map_comp f g)).trans (S.map_comp (K.map f) (K.map g))

@[simp] theorem map_id (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    map (𝟙 F) = 𝟙 (sheaf F) := by
  apply Pi.hom_ext
  intro x
  rw [map_component, pointMap_id, Category.comp_id, Category.id_comp]

theorem map_comp {F G H : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : F ⟶ G) (g : G ⟶ H) : map (f ≫ g) = map f ≫ map g := by
  apply Pi.hom_ext
  intro x
  simp only [map_component, map_component_assoc, pointMap_comp, Category.assoc]

/-- The genuine product-of-stalks construction is a functor. -/
def functor : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X where
  obj := sheaf
  map := map
  map_id := map_id
  map_comp := map_comp

/-- The pointwise skyscraper map is additive. -/
theorem pointMap_add {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f g : F ⟶ G) (x : X) : pointMap (f + g) x = pointMap f x + pointMap g x := by
  let K := CuspNormalization.SheafBiproduct.stalkFunctor X x
  let S := skyscraperSheafFunctor (C := AddCommGrpCat.{0}) x
  have hK : K.map (f + g) = K.map f + K.map g := K.map_add
  exact (congrArg S.map hK).trans S.map_add

theorem map_add {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f g : F ⟶ G) : map (f + g) = map f + map g := by
  apply Pi.hom_ext
  intro x
  rw [map_component, Preadditive.add_comp, map_component, map_component,
    pointMap_add, Preadditive.comp_add]

instance functor_additive : (functor (X := X)).Additive where
  map_add := map_add _ _

/-- The actual germ inclusion commutes with every actual sheaf morphism. -/
theorem inclusion_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G) :
    inclusion F ≫ map f = f ≫ inclusion G := by
  apply Pi.hom_ext
  intro x
  rw [Category.assoc, map_component, ← Category.assoc, inclusion_component,
    Category.assoc, inclusion_component]
  exact ((stalkSkyscraperSheafAdjunction x).unit.naturality f).symm

/-- The actual first Godement cokernel. -/
abbrev successor (F : TopCat.Sheaf AddCommGrpCat.{0} X) := cokernel (inclusion F)

/-- The morphism induced on the actual cokernels. -/
def successorMap {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G) :
    successor F ⟶ successor G :=
  cokernel.map (inclusion F) (inclusion G) f (map f) (inclusion_naturality f)

@[reassoc] theorem successorMap_π {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : F ⟶ G) :
    cokernel.π (inclusion F) ≫ successorMap f = map f ≫ cokernel.π (inclusion G) :=
  cokernel.π_desc _ _ _

@[simp] theorem successorMap_id (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    successorMap (𝟙 F) = 𝟙 (successor F) := by
  apply (cancel_epi (cokernel.π (inclusion F))).mp
  rw [successorMap_π, map_id, Category.id_comp, Category.comp_id]

theorem successorMap_comp {F G H : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : F ⟶ G) (g : G ⟶ H) :
    successorMap (f ≫ g) = successorMap f ≫ successorMap g := by
  apply (cancel_epi (cokernel.π (inclusion F))).mp
  simp only [successorMap_π, successorMap_π_assoc, map_comp, Category.assoc]

/-- The genuine cokernel construction is functorial. -/
def successorFunctor : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X where
  obj := successor
  map := successorMap
  map_id := successorMap_id
  map_comp := successorMap_comp

theorem successorMap_add {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f g : F ⟶ G) :
    successorMap (f + g) = successorMap f + successorMap g := by
  apply (cancel_epi (cokernel.π (inclusion F))).mp
  rw [successorMap_π, map_add, Preadditive.comp_add, successorMap_π, successorMap_π,
    Preadditive.add_comp]

instance successorFunctor_additive : (successorFunctor (X := X)).Additive where
  map_add := successorMap_add _ _

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.Godement
