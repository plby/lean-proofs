import Util.Bernays.LatticeClassCounting

/-!
# Exact ideal-class counts from principal generators
-/

namespace Bernays

def IdealGeneratorBall {d b : ℤ} [IsDomain (QuadraticAlgebra ℤ d b)]
    (I : InvertibleIdeal (QuadraticAlgebra ℤ d b)) (N : ℕ)
    (A : InvertibleIdeal (QuadraticAlgebra ℤ d b) → Prop) :=
  {z : QuadraticAlgebra ℤ d b // ∃ hz : z ≠ 0,
    ∃ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      I * J = InvertibleIdeal.principal z hz ∧
        (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ≤ N ∧ A J}

theorem generator_norm_of_product {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
    ∀ z : QuadraticAlgebra ℤ d b, ∀ hz : z ≠ 0,
    I * J = InvertibleIdeal.principal z hz →
      z.norm.natAbs = (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot *
        (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot := by
  let := quadraticOrderIsDomain hD
  intro I J z hz hprod
  have h := InvertibleIdeal.cardQuot_mul I J
  rwa [hprod, InvertibleIdeal.coe_principal,
    Erdos1081.cardQuot_span_singleton_eq_norm_natAbs, algebraNorm_quadraticOrder] at h

theorem idealGeneratorBall_card {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (I : InvertibleIdeal (QuadraticAlgebra ℤ d b)) (N : ℕ)
      (A : InvertibleIdeal (QuadraticAlgebra ℤ d b) → Prop),
      Nat.card (IdealGeneratorBall I N A) = Nat.card (QuadraticAlgebra ℤ d b)ˣ *
        Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) I.idealClass⁻¹ N A) := by
  classical
  let := quadraticOrderIsDomain hD
  intro I N A
  let O := QuadraticAlgebra ℤ d b
  let X := IdealGeneratorBall I N A
  let Y := RestrictedIdealClassBall O I.idealClass⁻¹ N A
  have hz (x : X) : (x.1 : O) ≠ 0 := x.2.choose
  have hex (x : X) : ∃ J : InvertibleIdeal O, I * J = InvertibleIdeal.principal (x.1 : O) (hz x) ∧
      (J : Ideal O).cardQuot ≤ N ∧ A J := x.2.choose_spec
  let J (x : X) := (hex x).choose
  have hJ (x : X) : I * J x = InvertibleIdeal.principal (x.1 : O) (hz x) ∧
      (J x : Ideal O).cardQuot ≤ N ∧ A (J x) := (hex x).choose_spec
  have hclass (x : X) : (J x).idealClass = I.idealClass⁻¹ := by
    have h := congrArg InvertibleIdeal.idealClass (hJ x).1
    rw [InvertibleIdeal.idealClass_mul, InvertibleIdeal.idealClass_principal] at h
    exact (eq_inv_iff_mul_eq_one).mpr (by simpa only [mul_comm] using h)
  let f : X → Y := fun x => ⟨⟨J x, hclass x, (hJ x).2.1⟩, (hJ x).2.2⟩
  have hnorm (x : X) : (x.1 : O).norm.natAbs ≤ (I : Ideal O).cardQuot * N := by
    rw [generator_norm_of_product hD I (J x) x.1 (hz x) (hJ x).1]
    exact Nat.mul_le_mul_left _ (hJ x).2.1
  let := finite_quadraticNormBall hD ((I : Ideal O).cardQuot * N)
  let e : X → QuadraticNormBall d b ((I : Ideal O).cardQuot * N) := fun x => ⟨x.1, hnorm x⟩
  let : Finite X := Finite.of_injective e (fun x y h =>
    Subtype.ext (congrArg (fun t : QuadraticNormBall d b ((I : Ideal O).cardQuot * N) => t.1) h))
  let := finite_idealClassBall hD I.idealClass⁻¹ N
  let : Finite Y := by dsimp only [Y, RestrictedIdealClassBall]; infer_instance
  let := finite_quadraticOrder_units hD
  have hcancel (x : X) (K : InvertibleIdeal O)
      (hK : I * K = InvertibleIdeal.principal (x.1 : O) (hz x)) : J x = K :=
    InvertibleIdeal.mul_right_cancel _ _ I (by simpa only [mul_comm] using (hJ x).1.trans hK.symm)
  apply natCard_eq_units_mul_of_associate_fibers (fun x : X => (x.1 : O))
    Subtype.val_injective hz f
  · intro y
    obtain ⟨z, hz₀, hprod, _⟩ := exists_principal_generator_norm hD I y.1.1
      (by rw [y.1.2.1, mul_inv_cancel])
    let x : X := ⟨z, hz₀, y.1.1, hprod, y.1.2.2, y.2⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hcancel x y.1.1 hprod
  · intro x y hxy
    have hJJ : J x = J y := congrArg (fun t : Y => t.1.1) hxy
    apply Ideal.span_singleton_eq_span_singleton.mp
    have hprod : InvertibleIdeal.principal (x.1 : O) (hz x) =
        InvertibleIdeal.principal (y.1 : O) (hz y) := (hJ x).1.symm.trans (hJJ ▸ (hJ y).1)
    exact congrArg (fun K : InvertibleIdeal O => (K : Ideal O)) hprod
  · intro x u
    have hu : (x.1 : O) * (u : O) ≠ 0 := mul_ne_zero (hz x) (Units.ne_zero u)
    have hprincipal : InvertibleIdeal.principal ((x.1 : O) * u) hu =
        InvertibleIdeal.principal (x.1 : O) (hz x) := by
      apply InvertibleIdeal.ext
      exact Ideal.span_singleton_eq_span_singleton.mpr (Associated.symm ⟨u, rfl⟩)
    let w : X := ⟨(x.1 : O) * u, hu, J x, (hJ x).1.trans hprincipal.symm, (hJ x).2⟩
    refine ⟨w, rfl, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hcancel w (J x) ((hJ x).1.trans hprincipal.symm)

end Bernays
