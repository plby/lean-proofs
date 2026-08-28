import Wikipedia.HopfProblem.SheafSingularCupComparisonRingDifferentialBasic

/-!
# The ring-coface complex is the original additive singular complex

These comparisons use the original native sheafification functors and
the original additive singular differential. No exactness or product
comparison is supplied as a hypothesis.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains

open ConstantSheafSingularComparison
open CuspNormalization.SheafForgetStalk (forgetToAdd)

variable (X : TopCat.{0})

private theorem differentialComparison {n m : ℕ}
    (d : (forgetSheaf X).obj (sheaf X n) ⟶ (forgetSheaf X).obj (sheaf X m))
    (p : presheaf X n ⋙ forgetToAdd ⟶ presheaf X m ⋙ forgetToAdd)
    (q : cochainPresheaf X (AddCommGrpCat.of ℂ) n ⟶
      cochainPresheaf X (AddCommGrpCat.of ℂ) m)
    (h : d ≫ (forgetSheafificationIso X (presheaf X m)).hom =
      (forgetSheafificationIso X (presheaf X n)).hom ≫ (additiveSheafification X).map p)
    (hq : p ≫ (presheafAddIso X m).hom = (presheafAddIso X n).hom ≫ q) :
    d ≫ (forgetSheafIso X m).hom =
      (forgetSheafIso X n).hom ≫ (additiveSheafification X).map q := by
  change d ≫ ((forgetSheafificationIso X (presheaf X m)).hom ≫
      (additiveSheafification X).map (presheafAddIso X m).hom) =
    ((forgetSheafificationIso X (presheaf X n)).hom ≫
      (additiveSheafification X).map (presheafAddIso X n).hom) ≫
        (additiveSheafification X).map q
  rw [← Category.assoc, h, Category.assoc, ← (additiveSheafification X).map_comp,
    hq, (additiveSheafification X).map_comp, Category.assoc]

/-- The first actual alternating coface differential is the original singular differential. -/
@[reassoc] theorem d0_additive :
    d0 X ≫ (forgetSheafIso X 1).hom =
      (forgetSheafIso X 0).hom ≫ sheafDifferential X (AddCommGrpCat.of ℂ) 0 1 := by
  apply differentialComparison X (d0 X) (presheafD0 X)
      (presheafDifferential X (AddCommGrpCat.of ℂ) 0 1) _ (presheafD0_additive X)
  simp only [d0, coface, Preadditive.sub_comp, forgetSheafificationIso_naturality,
    presheafD0, (additiveSheafification X).map_sub, Preadditive.comp_sub]

/-- The second actual alternating coface differential is the original singular differential. -/
@[reassoc] theorem d1_additive :
    d1 X ≫ (forgetSheafIso X 2).hom =
      (forgetSheafIso X 1).hom ≫ sheafDifferential X (AddCommGrpCat.of ℂ) 1 2 := by
  apply differentialComparison X (d1 X) (presheafD1 X)
      (presheafDifferential X (AddCommGrpCat.of ℂ) 1 2) _ (presheafD1_additive X)
  simp only [d1, coface, Preadditive.add_comp, Preadditive.sub_comp,
    forgetSheafificationIso_naturality, presheafD1, (additiveSheafification X).map_add,
    (additiveSheafification X).map_sub, Preadditive.comp_add, Preadditive.comp_sub]

/-- The third actual alternating coface differential is the original singular differential. -/
@[reassoc] theorem d2_additive :
    d2 X ≫ (forgetSheafIso X 3).hom =
      (forgetSheafIso X 2).hom ≫ sheafDifferential X (AddCommGrpCat.of ℂ) 2 3 := by
  apply differentialComparison X (d2 X) (presheafD2 X)
      (presheafDifferential X (AddCommGrpCat.of ℂ) 2 3) _ (presheafD2_additive X)
  simp only [d2, coface, Preadditive.add_comp, Preadditive.sub_comp,
    forgetSheafificationIso_naturality, presheafD2, (additiveSheafification X).map_add,
    (additiveSheafification X).map_sub, Preadditive.comp_add, Preadditive.comp_sub]

end Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains
