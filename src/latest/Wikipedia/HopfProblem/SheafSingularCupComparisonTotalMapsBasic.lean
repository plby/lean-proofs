import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalSheafColumnsBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonRingAugmentation

/-!
# The original first-column and last-row maps into the actual total complex

The first map applies each genuine Godement iterate to the original
constant-to-singular-cochain augmentation, then takes the first
biproduct injection. The second map is the original column unit,
followed by the last injection. Horizontal vanishing for the first map
comes from the equality of the two actual endpoint restrictions of a
constant cochain.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps

open SheafCupProduct CuspNormalization

variable (X : TopCat.{0})

def first0 : GodementExact.I0 (SheafConstants.complexSheaf X) ⟶
    (TotalSheaf.categoryData X).zeroTerm :=
  GodementExact.I0Map (RingCochains.augmentation X)

def first1 : GodementExact.I1 (SheafConstants.complexSheaf X) ⟶
    (TotalSheaf.categoryData X).oneTerm :=
  GodementExact.I1Map (RingCochains.augmentation X) ≫ biprod.inl

def first2 : GodementExact.I2 (SheafConstants.complexSheaf X) ⟶
    (TotalSheaf.categoryData X).twoTerm :=
  GodementExact.I2Map (RingCochains.augmentation X) ≫ biprod.inl

def first3 : GodementExact.I3 (SheafConstants.complexSheaf X) ⟶
    (TotalSheaf.categoryData X).threeTerm :=
  GodementExact.I3Map (RingCochains.augmentation X) ≫ biprod.inl

def last0 : (RingCochains.forgetSheaf X).obj (RingCochains.sheaf X 0) ⟶
    (TotalSheaf.categoryData X).zeroTerm :=
  TotalSheaf.columnUnit X 0

def last1 : (RingCochains.forgetSheaf X).obj (RingCochains.sheaf X 1) ⟶
    (TotalSheaf.categoryData X).oneTerm :=
  TotalSheaf.columnUnit X 1 ≫ biprod.inr

def last2 : (RingCochains.forgetSheaf X).obj (RingCochains.sheaf X 2) ⟶
    (TotalSheaf.categoryData X).twoTerm :=
  TotalSheaf.columnUnit X 2 ≫ biprod.inr ≫ biprod.inr

def last3 : (RingCochains.forgetSheaf X).obj (RingCochains.sheaf X 3) ⟶
    (TotalSheaf.categoryData X).threeTerm :=
  TotalSheaf.columnUnit X 3 ≫ biprod.inr ≫ biprod.inr ≫ biprod.inr

private theorem forget_comp_difference_eq_zero
    {A B E : GodementRing.RingSheaf X} (a : A ⟶ B) (b c : B ⟶ E)
    (h : a ≫ b = a ≫ c) :
    (GodementRing.forgetSheaf X).map a ≫
        ((GodementRing.forgetSheaf X).map b - (GodementRing.forgetSheaf X).map c) = 0 := by
  rw [Preadditive.comp_sub, ← (GodementRing.forgetSheaf X).map_comp,
    ← (GodementRing.forgetSheaf X).map_comp, h, sub_self]

/-- The first Godement image of the actual augmentation has zero horizontal differential. -/
theorem first0_horizontal :
    first0 X ≫ (TotalSheaf.categoryData X).h00 = 0 :=
  forget_comp_difference_eq_zero X
    (GodementRing.term0Map (RingCochains.augmentation X))
    (GodementRing.term0Map (RingCochains.coface X 0 0))
    (GodementRing.term0Map (RingCochains.coface X 0 1))
    (GodementRing.map_composition_eq _ _ _ _ (RingCochains.augmentation_coface X))

/-- The same vanishing after the actual second Godement iterate. -/
theorem first1_horizontal :
    GodementExact.I1Map (RingCochains.augmentation X) ≫
      (TotalSheaf.categoryData X).h10 = 0 :=
  forget_comp_difference_eq_zero X
    (GodementRing.term1Map (RingCochains.augmentation X))
    (GodementRing.term1Map (RingCochains.coface X 0 0))
    (GodementRing.term1Map (RingCochains.coface X 0 1))
    (GodementRing.map_composition_eq _ _ _ _
      (GodementRing.map_composition_eq _ _ _ _ (RingCochains.augmentation_coface X)))

/-- The same vanishing after the actual third Godement iterate. -/
theorem first2_horizontal :
    GodementExact.I2Map (RingCochains.augmentation X) ≫
      (TotalSheaf.categoryData X).h20 = 0 :=
  forget_comp_difference_eq_zero X
    (GodementRing.term2Map (RingCochains.augmentation X))
    (GodementRing.term2Map (RingCochains.coface X 0 0))
    (GodementRing.term2Map (RingCochains.coface X 0 1))
    (GodementRing.map_composition_eq _ _ _ _
      (GodementRing.map_composition_eq _ _ _ _
        (GodementRing.map_composition_eq _ _ _ _ (RingCochains.augmentation_coface X))))

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps
