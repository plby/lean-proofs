import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupPairFunctor
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupZero
import Wikipedia.HopfProblem.SheafCupProductGodementExactBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryComplex

/-!
# The actual categorical Godement--Dolbeault total diagram

Its vertical maps are the original Godement differentials. Literal pair
sheaves carry the two coordinate derivatives and their alternating top
derivative. The final coefficient sheaf is genuinely zero. The signed
total construction is the already proved categorical biproduct complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total

open SheafCupProduct SheafSingularCupComparison

variable {X : TopCat.{0}}

/-- Actual additive coordinate operators on the original Godement terms. -/
structure Operators (F : GodementRing.RingSheaf X) where
  deriv0 : Fin 2 → End (GodementExact.I0 F)
  deriv1 : Fin 2 → End (GodementExact.I1 F)
  deriv2 : Fin 2 → End (GodementExact.I2 F)
  commute0 : deriv0 1 ≫ deriv0 0 = deriv0 0 ≫ deriv0 1
  commute1 : deriv1 1 ≫ deriv1 0 = deriv1 0 ≫ deriv1 1
  vertical0 : ∀ i, deriv0 i ≫ GodementExact.d0 F = GodementExact.d0 F ≫ deriv1 i
  vertical1 : ∀ i, deriv1 i ≫ GodementExact.d1 F = GodementExact.d1 F ≫ deriv2 i

namespace Operators

variable {F : GodementRing.RingSheaf X} (D : Operators F)

/-- The two original degree-zero derivative coefficients. -/
def df0 : GodementExact.I0 F ⟶ Pairs.sheaf (GodementExact.I0 F) :=
  Pairs.lift (D.deriv0 0) (D.deriv0 1)

def df1 : GodementExact.I1 F ⟶ Pairs.sheaf (GodementExact.I1 F) :=
  Pairs.lift (D.deriv1 0) (D.deriv1 1)

def df2 : GodementExact.I2 F ⟶ Pairs.sheaf (GodementExact.I2 F) :=
  Pairs.lift (D.deriv2 0) (D.deriv2 1)

/-- The original order `∂bar₀ a₁ - ∂bar₁ a₀` on coefficient pairs. -/
def top0 : Pairs.sheaf (GodementExact.I0 F) ⟶ GodementExact.I0 F :=
  Pairs.snd _ ≫ D.deriv0 0 - Pairs.fst _ ≫ D.deriv0 1

def top1 : Pairs.sheaf (GodementExact.I1 F) ⟶ GodementExact.I1 F :=
  Pairs.snd _ ≫ D.deriv1 0 - Pairs.fst _ ≫ D.deriv1 1

theorem df0_top0 : D.df0 ≫ D.top0 = 0 := by
  simp only [df0, top0, Preadditive.comp_sub, Pairs.lift_snd_assoc,
    Pairs.lift_fst_assoc, D.commute0, sub_self]

theorem df1_top1 : D.df1 ≫ D.top1 = 0 := by
  simp only [df1, top1, Preadditive.comp_sub, Pairs.lift_snd_assoc,
    Pairs.lift_fst_assoc, D.commute1, sub_self]

theorem df0_vertical :
    D.df0 ≫ Pairs.map (GodementExact.d0 F) = GodementExact.d0 F ≫ D.df1 := by
  apply Pairs.hom_ext
  · simp [df0, df1, Category.assoc, D.vertical0]
  · simp [df0, df1, Category.assoc, D.vertical0]

theorem df1_vertical :
    D.df1 ≫ Pairs.map (GodementExact.d1 F) = GodementExact.d1 F ≫ D.df2 := by
  apply Pairs.hom_ext
  · simp [df1, df2, Category.assoc, D.vertical1]
  · simp [df1, df2, Category.assoc, D.vertical1]

theorem top0_vertical :
    D.top0 ≫ GodementExact.d0 F = Pairs.map (GodementExact.d0 F) ≫ D.top1 := by
  simp only [top0, top1, Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
    Pairs.map_snd_assoc, Pairs.map_fst_assoc, D.vertical0]

/-- The literal triangular portion of the genuine double complex. -/
def categoryData : TotalCategory.Data
    (GodementExact.I0 F) (GodementExact.I1 F) (Pairs.sheaf (GodementExact.I0 F))
    (GodementExact.I2 F) (Pairs.sheaf (GodementExact.I1 F)) (GodementExact.I0 F)
    (GodementExact.I3 F) (Pairs.sheaf (GodementExact.I2 F)) (GodementExact.I1 F)
    (zeroSheaf X) where
  v00 := GodementExact.d0 F
  h00 := D.df0
  v10 := GodementExact.d1 F
  h10 := D.df1
  v01 := Pairs.map (GodementExact.d0 F)
  h01 := D.top0
  v20 := GodementExact.d2 F
  h20 := D.df2
  v11 := Pairs.map (GodementExact.d1 F)
  h11 := D.top1
  v02 := GodementExact.d0 F
  h02 := 0
  vertical00 := GodementExact.d0_d1 F
  vertical10 := GodementExact.d1_d2 F
  vertical01 := by rw [← Pairs.map_comp, GodementExact.d0_d1, Pairs.map_zero]
  horizontal00 := D.df0_top0
  horizontal01 := by simp
  horizontal10 := D.df1_top1
  mixed00 := D.df0_vertical
  mixed10 := D.df1_vertical
  mixed01 := D.top0_vertical

end Operators

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total
