import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupDerivationNative
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupDerivationCofaces
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupTotalOperators

/-!
# The actual native derivative operators for the torus total complex

The two original Dolbeault derivations are prolonged through the actual
ring-valued Godement terms. Their genuine commutation and original
coface squares supply the total operators without an extension or
compatibility hypothesis. The original holomorphic inclusion is killed
in each of the first three terms.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation

open SheafCupProduct

variable {X : TopCat.{0}} {F : GodementRing.RingSheaf X}

/-- Two actual commuting derivations supply the genuine ring-Godement operators. -/
def operatorsOfDerivations (D : Fin 2 → SheafDerivation F)
    (h : (D 1).map ≫ (D 0).map = (D 0).map ≫ (D 1).map) : Total.RingOperators F where
  deriv0 i := term0Derivation (D i)
  deriv1 i := term1Derivation (D i)
  deriv2 i := term2Derivation (D i)
  commute0 := term0Derivation_commute (D 1) (D 0) h
  commute1 := term1Derivation_commute (D 1) (D 0) h
  coface0 i := term0Derivation_coface (D i)
  coface1 i := term1Derivation_coface (D i)

/-- The original smooth torus sheaf has these actual, unconditionally prolonged operators. -/
def nativeOperators (p : PeriodDomain) : Total.RingOperators (smoothRingSheaf p) :=
  operatorsOfDerivations (nativeDerivation p) (derivativeMap_commute p).symm

/-- Naturality of the original smooth augmentation with the actual native derivative. -/
theorem native_augmentation_derivative (p : PeriodDomain) (i : Fin 2) :
    derivativeMap p i ≫ (GodementRing.forgetSheaf (TopCat.of p.Torus)).map
        (GodementRing.inclusion (smoothRingSheaf p)) =
      (GodementRing.forgetSheaf (TopCat.of p.Torus)).map
        (GodementRing.inclusion (smoothRingSheaf p)) ≫ ((nativeOperators p).deriv0 i).map :=
  (liftMap_inclusion (derivativeMap p i)).symm

/-- The original first holomorphic Godement image is annihilated by either derivative. -/
theorem native_inclusion_derivative0 (p : PeriodDomain) (i : Fin 2) :
    (GodementRing.forgetSheaf (TopCat.of p.Torus)).map
        (GodementRing.term0Map (inclusionRing p)) ≫ ((nativeOperators p).deriv0 i).map = 0 :=
  lifted_ring_annihilate (inclusionRing p) (nativeDerivation p i) (inclusion_derivativeMap p i)

/-- The same actual annihilation after two Godement steps. -/
theorem native_inclusion_derivative1 (p : PeriodDomain) (i : Fin 2) :
    (GodementRing.forgetSheaf (TopCat.of p.Torus)).map
        (GodementRing.term1Map (inclusionRing p)) ≫ ((nativeOperators p).deriv1 i).map = 0 :=
  lifted_ring_annihilate (GodementRing.term0Map (inclusionRing p))
    (term0Derivation (nativeDerivation p i)) (native_inclusion_derivative0 p i)

/-- The same actual annihilation after three Godement steps. -/
theorem native_inclusion_derivative2 (p : PeriodDomain) (i : Fin 2) :
    (GodementRing.forgetSheaf (TopCat.of p.Torus)).map
        (GodementRing.term2Map (inclusionRing p)) ≫ ((nativeOperators p).deriv2 i).map = 0 :=
  lifted_ring_annihilate (GodementRing.term1Map (inclusionRing p))
    (term1Derivation (nativeDerivation p i)) (native_inclusion_derivative1 p i)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation
