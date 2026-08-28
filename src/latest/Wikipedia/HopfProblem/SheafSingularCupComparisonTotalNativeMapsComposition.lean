import Mathlib.Algebra.Category.Grp.Basic

/-!
# Composition of the actual native and quotient comparison squares
-/

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalNativeMaps

/-- The literal image of an identity has the original identity action on a comparison map. -/
theorem map_identity_comp {C : Type*} [Category C] (G : C ⥤ AddCommGrpCat.{0})
    (A : C) {B : AddCommGrpCat.{0}} (f : G.obj A ⟶ B) :
    G.map (𝟙 A) ≫ f = f :=
  (congrArg (fun g => g ≫ f) (G.map_id A)).trans (Category.id_comp f)

/-- A native comparison followed by a compatible quotient map is the target comparison. -/
theorem postcompose_comparison {A B C D E : AddCommGrpCat.{0}}
    (a : A ⟶ B) (b : A ⟶ C) (e : B ⟶ D) (f : C ⟶ E)
    (u : B ⟶ C) (v : D ⟶ E) (ha : a ≫ u = b) (he : e ≫ v = u ≫ f) :
    (a ≫ e) ≫ v = b ≫ f := by
  rw [Category.assoc, he, ← Category.assoc, ha]

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalNativeMaps
