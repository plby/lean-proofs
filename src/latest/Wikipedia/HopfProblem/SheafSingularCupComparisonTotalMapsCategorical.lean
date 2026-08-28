import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryComplex

/-!
# Actual first and last injections into a categorical total complex

These are the component calculations for the original signed
biproduct differential. They are later applied to the genuine
Godement maps and the genuine column units.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : C}
  (D : TotalCategory.Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)
  {A B : C}

theorem first_square0 (a : A ⟶ R00) (b : B ⟶ R10) (d : A ⟶ B)
    (hv : a ≫ D.v00 = d ≫ b) (hh : a ≫ D.h00 = 0) :
    a ≫ D.d0 = d ≫ b ≫ biprod.inl := by
  apply biprod.hom_ext
  · simpa [Category.assoc] using hv
  · simp [Category.assoc, hh]

theorem first_square1 (a : A ⟶ R10) (b : B ⟶ R20) (d : A ⟶ B)
    (hv : a ≫ D.v10 = d ≫ b) (hh : a ≫ D.h10 = 0) :
    (a ≫ biprod.inl) ≫ D.d1 = d ≫ b ≫ biprod.inl := by
  apply biprod.hom_ext
  · simpa [Category.assoc] using hv
  · apply biprod.hom_ext
    · simp [Category.assoc, hh]
    · simp [Category.assoc]

theorem first_square2 (a : A ⟶ R20) (b : B ⟶ R30) (d : A ⟶ B)
    (hv : a ≫ D.v20 = d ≫ b) (hh : a ≫ D.h20 = 0) :
    (a ≫ biprod.inl) ≫ D.d2 = d ≫ b ≫ biprod.inl := by
  apply biprod.hom_ext
  · simpa [Category.assoc] using hv
  · apply biprod.hom_ext
    · simp [Category.assoc, hh]
    · apply biprod.hom_ext
      · simp [Category.assoc]
      · simp [Category.assoc]

theorem last_square0 (a : A ⟶ R00) (b : B ⟶ R01) (d : A ⟶ B)
    (hv : a ≫ D.v00 = 0) (hh : a ≫ D.h00 = d ≫ b) :
    a ≫ D.d0 = d ≫ b ≫ biprod.inr := by
  apply biprod.hom_ext
  · simp [Category.assoc, hv]
  · simpa [Category.assoc] using hh

theorem last_square1 (a : A ⟶ R01) (b : B ⟶ R02) (d : A ⟶ B)
    (hv : a ≫ D.v01 = 0) (hh : a ≫ D.h01 = d ≫ b) :
    (a ≫ biprod.inr) ≫ D.d1 = d ≫ b ≫ biprod.inr ≫ biprod.inr := by
  apply biprod.hom_ext
  · simp [Category.assoc]
  · apply biprod.hom_ext
    · simp [Category.assoc, hv]
    · simpa [Category.assoc] using hh

theorem last_square2 (a : A ⟶ R02) (b : B ⟶ R03) (d : A ⟶ B)
    (hv : a ≫ D.v02 = 0) (hh : a ≫ D.h02 = d ≫ b) :
    (a ≫ biprod.inr ≫ biprod.inr) ≫ D.d2 =
      d ≫ b ≫ biprod.inr ≫ biprod.inr ≫ biprod.inr := by
  apply biprod.hom_ext
  · simp [Category.assoc]
  · apply biprod.hom_ext
    · simp [Category.assoc]
    · apply biprod.hom_ext
      · simp [Category.assoc, hv]
      · simpa [Category.assoc] using hh

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps
