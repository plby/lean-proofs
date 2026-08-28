import Mathlib.Algebra.Category.Grp.Basic

/-!
# A categorical cancellation used by the actual comparison diagrams
-/

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RowGlobal

/-- Two proved comparison squares retain the original map after cancellation of an isomorphism. -/
theorem comparison_of_unit_and_iso {A B C D E : AddCommGrpCat.{0}}
    (s : A ⟶ B) (g : B ⟶ C) (e : D ≅ C) (r : A ⟶ D) (q : D ⟶ E) (u : B ⟶ E)
    (hu : g ≫ e.inv ≫ q = u) (hs : s ≫ g = r ≫ e.hom) : s ≫ u = r ≫ q := by
  rw [← hu, ← Category.assoc, hs, Category.assoc, Iso.hom_inv_id_assoc]

end Wikipedia.HopfProblem.SheafSingularCupComparison.RowGlobal
