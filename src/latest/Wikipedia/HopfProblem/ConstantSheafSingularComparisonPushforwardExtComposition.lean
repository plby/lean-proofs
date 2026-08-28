import Mathlib.CategoryTheory.Functor.Basic

/-!
# Composing the native pushforward and truncation squares
-/

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt

theorem remove_functor_map_id {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) (X : C) {Z : D} {a b : G.obj X ⟶ Z}
    (h : G.map (𝟙 X) ≫ a = b) : a = b :=
  (Category.id_comp a).symm.trans
    ((congrArg (fun k => k ≫ a) (G.map_id X).symm).trans h)

theorem comparison_of_truncation {C : Type*} [Category C]
    {A B D A' B' : C} (x : A ⟶ A') (a : A ⟶ B) (b : B ⟶ D)
    (m : A' ⟶ B) (a' : A' ⟶ B') (b' : B' ⟶ D) (t : B ⟶ B')
    (hx : x ≫ m = a) (ha : a' = m ≫ t) (hb : t ≫ b' = b) :
    x ≫ (a' ≫ b') = a ≫ b := by
  rw [ha, Category.assoc, ← Category.assoc, hx, hb]

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt
