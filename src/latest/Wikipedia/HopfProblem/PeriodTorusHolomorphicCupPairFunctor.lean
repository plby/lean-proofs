import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupPairSheaf

/-!
# Functoriality of the actual coefficient-pair sheaf

The additive functor and its product comparison are induced by the
literal two coefficient maps, without changing any section values.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Pairs

variable {X : TopCat.{0}}

@[simp] theorem map_id (F : AbSheaf X) : map (𝟙 F) = 𝟙 (sheaf F) := by
  apply hom_ext
  · simp
  · simp

@[simp] theorem map_comp {F G H : AbSheaf X} (f : F ⟶ G) (g : G ⟶ H) :
    map (f ≫ g) = map f ≫ map g := by
  apply hom_ext
  · simp
  · simp

@[simp] theorem map_zero (F G : AbSheaf X) : map (0 : F ⟶ G) = 0 := by
  apply hom_ext
  · simp
  · simp

@[simp] theorem map_add {F G : AbSheaf X} (f g : F ⟶ G) :
    map (f + g) = map f + map g := by
  apply hom_ext
  · simp [Preadditive.comp_add, Preadditive.add_comp]
  · simp [Preadditive.comp_add, Preadditive.add_comp]

/-- The genuine additive functor of coefficient pairs. -/
def functor (X : TopCat.{0}) : AbSheaf X ⥤ AbSheaf X where
  obj := sheaf
  map := map
  map_id := map_id
  map_comp := map_comp

instance functor_additive (X : TopCat.{0}) : (functor X).Additive where
  map_add {_ _ f g} := map_add f g

/-- The original pair and categorical biproduct comparisons commute with every actual map. -/
@[reassoc] theorem biprodIso_map {F G : AbSheaf X} (f : F ⟶ G) :
    map f ≫ (biprodIso G).hom = (biprodIso F).hom ≫ biprod.map f f := by
  apply biprod.hom_ext
  · simp
  · simp

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Pairs
