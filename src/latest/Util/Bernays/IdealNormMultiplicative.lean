import Util.Bernays.InvertibleIdeal
import Mathlib.RingTheory.Artinian.Ring

/-!
# Multiplicativity of the index for invertible ideals in an order

Reduction modulo any nonzero ideal gives a finite ring. Its Picard group is
trivial, so an invertible module has one generator after reduction. This
extends the maximal-ideal index calculation to arbitrary nonzero ideals.
-/

open scoped nonZeroDivisors
open TensorProduct

namespace Bernays

theorem relIndex_invertible_mul {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] (P J : Ideal R) (hP : P ≠ ⊥)
    [Module.Invertible R J] :
    (P * J).toAddSubgroup.relIndex J.toAddSubgroup = P.cardQuot := by
  classical
  by_cases htop : P = ⊤
  · subst P
    simp
  let A := R ⧸ P
  let T := A ⊗[R] J
  letI : Nontrivial A := (Ideal.Quotient.nontrivial_iff (R := R) (I := P)).mpr htop
  letI : Finite A := Ring.HasFiniteQuotients.finiteQuotient hP
  letI : IsArtinianRing A := isArtinian_of_finite
  letI : Module.Invertible A T := inferInstance
  letI : Module.Free A T := inferInstance
  let L : Submodule R J := Submodule.comap (J : Submodule R R).subtype (P • (J : Submodule R R))
  change Nat.card (J ⧸ L) = Nat.card A
  let e : (J ⧸ L) ≃ₗ[R] T :=
    Submodule.quotEquivOfEq _ (P • (⊤ : Submodule R J))
      (Submodule.map_injective_of_injective J.injective_subtype
        (by simp [L, Ideal.mul_le_right])) ≪≫ₗ
      (quotTensorEquivQuotSMul J P).symm
  let e' : T ≃ₗ[A] A := (Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free A T)).some
  exact Nat.card_congr (e.toEquiv.trans e'.toEquiv)

theorem cardQuot_mul_invertible {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] (P J : Ideal R) (hP : P ≠ ⊥)
    (hJ : IsUnit (J : FractionalIdeal R⁰ (FractionRing R))) :
    (P * J).cardQuot = P.cardQuot * J.cardQuot := by
  letI : Module.Invertible R J := Erdos1081.moduleInvertibleIdealOfIsUnit J hJ
  calc
    (P * J).cardQuot =
        (P * J).toAddSubgroup.relIndex J.toAddSubgroup * J.toAddSubgroup.index :=
      (AddSubgroup.relIndex_mul_index (show (P * J).toAddSubgroup ≤ J.toAddSubgroup
        from Ideal.mul_le_right)).symm
    _ = P.cardQuot * J.cardQuot := by rw [relIndex_invertible_mul P J hP]; rfl

namespace InvertibleIdeal

theorem cardQuot_mul {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] (I J : InvertibleIdeal R) :
    ((I * J : InvertibleIdeal R) : Ideal R).cardQuot =
      (I : Ideal R).cardQuot * (J : Ideal R).cardQuot :=
  cardQuot_mul_invertible _ _ I.ne_bot J.2

end InvertibleIdeal

end Bernays
