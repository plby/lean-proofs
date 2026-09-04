import Util.Bernays.QuadraticClassBalls
import Util.Bernays.AssociateFibers

/-!
# Passing from a family of lattice points to distinct integral ideals
-/

namespace Bernays

def RestrictedIdealClassBall (R : Type*) [CommRing R] [IsDomain R]
    (C : ClassGroup R) (N : ℕ) (A : InvertibleIdeal R → Prop) :=
  {I : IdealClassBall R C N // A I.1}

theorem lattice_family_class_count {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {X : Type*} [Finite X] :
    letI := quadraticOrderIsDomain hD
    ∀ (I : InvertibleIdeal (QuadraticAlgebra ℤ d b)) (N : ℕ)
      (A : InvertibleIdeal (QuadraticAlgebra ℤ d b) → Prop)
      (z : X → QuadraticAlgebra ℤ d b),
      Function.Injective z →
      (∀ x, z x ≠ 0) →
      (∀ x, z x ∈ (I : Ideal (QuadraticAlgebra ℤ d b))) →
      (∀ x, (z x).norm.natAbs ≤ N) →
      (∀ x, ∀ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (I : Ideal (QuadraticAlgebra ℤ d b)) * J = Ideal.span {z x} → A J) →
      Nat.card X ≤ Nat.card (QuadraticAlgebra ℤ d b)ˣ *
        Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) I.idealClass⁻¹ N A) := by
  let := quadraticOrderIsDomain hD
  intro I N A z hinj hz₀ hzI hzN hA
  let O := QuadraticAlgebra ℤ d b
  let Y := RestrictedIdealClassBall O I.idealClass⁻¹ N A
  have hex (x : X) : ∃ J : InvertibleIdeal O, I * J = InvertibleIdeal.principal (z x) (hz₀ x) :=
    InvertibleIdeal.exists_mul_eq_of_le I (InvertibleIdeal.principal (z x) (hz₀ x))
      ((Ideal.span_singleton_le_iff_mem _).mpr (hzI x))
  let J : X → InvertibleIdeal O := fun x => (hex x).choose
  have hJ (x : X) : I * J x = InvertibleIdeal.principal (z x) (hz₀ x) := (hex x).choose_spec
  have hJideal (x : X) : (I : Ideal O) * (J x : Ideal O) = Ideal.span {z x} :=
    congrArg (fun K : InvertibleIdeal O => (K : Ideal O)) (hJ x)
  have hclass (x : X) : (J x).idealClass = I.idealClass⁻¹ := by
    have hc := congrArg InvertibleIdeal.idealClass (hJ x)
    rw [InvertibleIdeal.idealClass_mul, InvertibleIdeal.idealClass_principal] at hc
    calc
      _ = I.idealClass⁻¹ * (I.idealClass * (J x).idealClass) := by simp
      _ = _ := by rw [hc, mul_one]
  have hnorm (x : X) : (J x : Ideal O).cardQuot ≤ N := by
    have hm := InvertibleIdeal.cardQuot_mul I (J x)
    rw [hJ x, InvertibleIdeal.coe_principal,
      Erdos1081.cardQuot_span_singleton_eq_norm_natAbs, algebraNorm_quadraticOrder] at hm
    calc
      (J x : Ideal O).cardQuot ≤ (I : Ideal O).cardQuot * (J x : Ideal O).cardQuot :=
        Nat.le_mul_of_pos_left _ I.cardQuot_pos
      _ = (z x).norm.natAbs := hm.symm
      _ ≤ N := hzN x
  let f : X → Y := fun x => ⟨⟨J x, hclass x, hnorm x⟩, hA x (J x) (hJideal x)⟩
  have hassoc (x y : X) (h : f x = f y) : Associated (z x) (z y) := by
    have heq : J x = J y := congrArg (fun t : Y => t.1.1) h
    apply Ideal.span_singleton_eq_span_singleton.mp
    rw [← hJideal x, ← hJideal y, heq]
  let := finite_quadraticOrder_units hD
  let := finite_idealClassBall hD I.idealClass⁻¹ N
  let : Finite Y := by
    dsimp only [Y, RestrictedIdealClassBall]
    infer_instance
  exact natCard_le_units_mul_of_associate_fibers z hinj f hassoc

end Bernays
