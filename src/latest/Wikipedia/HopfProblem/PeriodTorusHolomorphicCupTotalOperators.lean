import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupTotalCategory
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupDerivationBasic

/-!
# Actual derivations and original ring cofaces in the total diagram

The sectionwise Leibniz data come from genuine sheaf derivations. Their
coface squares imply commutation with the original alternating
Godement differentials, so they supply the categorical total operators.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total

open SheafCupProduct

variable {X : TopCat.{0}}

/-- Genuine derivations of the original ring-Godement terms. -/
structure RingOperators (F : GodementRing.RingSheaf X) where
  deriv0 : Fin 2 → Derivation.SheafDerivation (GodementRing.term0 F)
  deriv1 : Fin 2 → Derivation.SheafDerivation (GodementRing.term1 F)
  deriv2 : Fin 2 → Derivation.SheafDerivation (GodementRing.term2 F)
  commute0 : (deriv0 1).map ≫ (deriv0 0).map = (deriv0 0).map ≫ (deriv0 1).map
  commute1 : (deriv1 1).map ≫ (deriv1 0).map = (deriv1 0).map ≫ (deriv1 1).map
  coface0 : ∀ i j, (deriv0 i).map ≫
      (GodementRing.forgetSheaf X).map (GodementRing.face0 F j) =
    (GodementRing.forgetSheaf X).map (GodementRing.face0 F j) ≫ (deriv1 i).map
  coface1 : ∀ i j, (deriv1 i).map ≫
      (GodementRing.forgetSheaf X).map (GodementRing.face1 F j) =
    (GodementRing.forgetSheaf X).map (GodementRing.face1 F j) ≫ (deriv2 i).map

namespace RingOperators

variable {F : GodementRing.RingSheaf X} (D : RingOperators F)

/-- The actual coface squares give the original alternating-differential squares. -/
def operators : Operators F where
  deriv0 i := (D.deriv0 i).map
  deriv1 i := (D.deriv1 i).map
  deriv2 i := (D.deriv2 i).map
  commute0 := D.commute0
  commute1 := D.commute1
  vertical0 i := by
    change (D.deriv0 i).map ≫
      ((GodementRing.forgetSheaf X).map (GodementRing.face0 F 0) -
        (GodementRing.forgetSheaf X).map (GodementRing.face0 F 1)) =
      ((GodementRing.forgetSheaf X).map (GodementRing.face0 F 0) -
        (GodementRing.forgetSheaf X).map (GodementRing.face0 F 1)) ≫ (D.deriv1 i).map
    rw [Preadditive.comp_sub, Preadditive.sub_comp, D.coface0, D.coface0]
  vertical1 i := by
    change (D.deriv1 i).map ≫
      ((GodementRing.forgetSheaf X).map (GodementRing.face1 F 0) -
        (GodementRing.forgetSheaf X).map (GodementRing.face1 F 1) +
        (GodementRing.forgetSheaf X).map (GodementRing.face1 F 2)) =
      ((GodementRing.forgetSheaf X).map (GodementRing.face1 F 0) -
        (GodementRing.forgetSheaf X).map (GodementRing.face1 F 1) +
        (GodementRing.forgetSheaf X).map (GodementRing.face1 F 2)) ≫ (D.deriv2 i).map
    simp only [Preadditive.comp_add, Preadditive.comp_sub, Preadditive.add_comp,
      Preadditive.sub_comp, D.coface1]

/-- The categorical diagram of the actual ring-coface/derivation data. -/
abbrev categoryData := D.operators.categoryData

end RingOperators

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total
