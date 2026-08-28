import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryMap

/-!
# Actual additive-functor coordinates of first and last injections

The coordinates use the canonical biproduct comparison and the images
of the original projections. They do not identify or redefine any
cohomology group.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : C}
  (D : TotalCategory.Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)
  (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] {A : C}

theorem oneEquiv_first (a : A ⟶ R10) (s : F.obj A) :
    D.oneEquiv F (F.map (a ≫ biprod.inl) s) = (F.map a s, 0) := by
  simp only [TotalCategory.Data.oneEquiv_apply, ← AddCommGrpCat.comp_apply, ← F.map_comp]
  simp [Category.assoc]

theorem twoEquiv_first (a : A ⟶ R20) (s : F.obj A) :
    D.twoEquiv F (F.map (a ≫ biprod.inl) s) = (F.map a s, 0, 0) := by
  simp only [TotalCategory.Data.twoEquiv_apply, ← AddCommGrpCat.comp_apply, ← F.map_comp]
  simp [Category.assoc]

theorem threeEquiv_first (a : A ⟶ R30) (s : F.obj A) :
    D.threeEquiv F (F.map (a ≫ biprod.inl) s) = (F.map a s, 0, 0, 0) := by
  simp only [TotalCategory.Data.threeEquiv_apply, ← AddCommGrpCat.comp_apply, ← F.map_comp]
  simp [Category.assoc]

theorem oneEquiv_last (a : A ⟶ R01) (s : F.obj A) :
    D.oneEquiv F (F.map (a ≫ biprod.inr) s) = (0, F.map a s) := by
  simp only [TotalCategory.Data.oneEquiv_apply, ← AddCommGrpCat.comp_apply, ← F.map_comp]
  simp [Category.assoc]

theorem twoEquiv_last (a : A ⟶ R02) (s : F.obj A) :
    D.twoEquiv F (F.map (a ≫ biprod.inr ≫ biprod.inr) s) = (0, 0, F.map a s) := by
  simp only [TotalCategory.Data.twoEquiv_apply, ← AddCommGrpCat.comp_apply, ← F.map_comp]
  simp [Category.assoc]

theorem threeEquiv_last (a : A ⟶ R03) (s : F.obj A) :
    D.threeEquiv F (F.map (a ≫ biprod.inr ≫ biprod.inr ≫ biprod.inr) s) =
      (0, 0, 0, F.map a s) := by
  simp only [TotalCategory.Data.threeEquiv_apply, ← AddCommGrpCat.comp_apply, ← F.map_comp]
  simp [Category.assoc]

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps
