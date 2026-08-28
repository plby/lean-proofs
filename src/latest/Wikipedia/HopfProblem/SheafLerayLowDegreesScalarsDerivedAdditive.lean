import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Additivity of the native right-derived functor

The sum of two resolution lifts lifts the sum of the coefficient maps.
Uniqueness up to homotopy therefore proves additivity of the actual
injective-resolution functor. The native right-derived functor is a
composition of this functor with additive functors.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees.Scalars

universe u v u' v'

variable (C : Type u) [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]

/-- The actual functor of injective resolutions is additive because
any two lifts of the same coefficient map are homotopic. -/
theorem injectiveResolutions_additive : (injectiveResolutions C).Additive where
  map_add {X Y} a b := by
    change (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc (a + b) (injectiveResolution Y) (injectiveResolution X)) =
      (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc a (injectiveResolution Y) (injectiveResolution X)) +
        (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc b (injectiveResolution Y) (injectiveResolution X))
    rw [← Functor.map_add]
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descHomotopy (a + b)
    · exact InjectiveResolution.desc_commutes _ _ _
    · simp only [Preadditive.comp_add, InjectiveResolution.desc_commutes,
        Functor.map_add, Preadditive.add_comp]

variable {C} {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Additivity of the genuine native right-derived functor. -/
instance rightDerived_additive (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.rightDerived n).Additive := by
  let := injectiveResolutions_additive C
  change ((injectiveResolutions C ⋙ F.mapHomotopyCategory (ComplexShape.up ℕ)) ⋙
    HomotopyCategory.homologyFunctor D (ComplexShape.up ℕ) n).Additive
  infer_instance

end Wikipedia.HopfProblem.SheafLerayLowDegrees.Scalars
