import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryBasic
import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# Square-zero for the categorical signed total differential

These are identities between the original biproduct morphisms, obtained
from the supplied horizontal, vertical, and mixed identities.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalCategory.Data

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : C}
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)

theorem d0_d1 : D.d0 ≫ D.d1 = 0 := by
  apply biprod.hom_ext
  · simp [Category.assoc, D.vertical00]
  · apply biprod.hom_ext
    · simp [Category.assoc, Preadditive.comp_add, Preadditive.comp_neg,
        D.mixed00]
    · simp [Category.assoc, D.horizontal00]

theorem d1_d2 : D.d1 ≫ D.d2 = 0 := by
  apply biprod.hom_ext
  · simp [Category.assoc, D.vertical10]
  · apply biprod.hom_ext
    · simp [Category.assoc, Preadditive.comp_add, Preadditive.add_comp,
        Preadditive.neg_comp, D.vertical01, D.mixed10]
    · apply biprod.hom_ext
      · simp [Category.assoc, Preadditive.comp_add, Preadditive.add_comp,
          Preadditive.comp_neg, Preadditive.neg_comp, D.horizontal10, D.mixed01]
      · simp [Category.assoc, D.horizontal01]

/-- The actual degree-one short complex of categorical total terms. -/
def oneComplex : ShortComplex C := ShortComplex.mk D.d0 D.d1 D.d0_d1

/-- The actual degree-two short complex of categorical total terms. -/
def twoComplex : ShortComplex C := ShortComplex.mk D.d1 D.d2 D.d1_d2

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalCategory.Data
