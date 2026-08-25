import Util.Bernays.QuadraticClassBalls

/-!
# Counting ideals divisible by a specified invertible ideal
-/

namespace Bernays

def DivisibleIdealClassBall (R : Type*) [CommRing R] [IsDomain R]
    (C : ClassGroup R) (N : ℕ) (P : InvertibleIdeal R) :=
  {I : IdealClassBall R C N // (I.1 : Ideal R) ≤ (P : Ideal R)}

noncomputable def divisibleClassBallEmbedding {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] (C : ClassGroup R) (N : ℕ) (P : InvertibleIdeal R) :
    DivisibleIdealClassBall R C N P ↪
      IdealClassBall R (P.idealClass⁻¹ * C) (N / (P : Ideal R).cardQuot) := by
  let B := DivisibleIdealClassBall R C N P
  have hex (I : B) : ∃ J : InvertibleIdeal R, P * J = I.1.1 :=
    InvertibleIdeal.exists_mul_eq_of_le P I.1.1 I.2
  let J : B → InvertibleIdeal R := fun I => (hex I).choose
  have hmul (I : B) : P * J I = I.1.1 := (hex I).choose_spec
  have hclass (I : B) : (J I).idealClass = P.idealClass⁻¹ * C := by
    have hc := congrArg InvertibleIdeal.idealClass (hmul I)
    rw [InvertibleIdeal.idealClass_mul, I.1.2.1] at hc
    calc
      (J I).idealClass = P.idealClass⁻¹ * (P.idealClass * (J I).idealClass) := by simp
      _ = P.idealClass⁻¹ * C := by rw [hc]
  have hnorm (I : B) : (J I : Ideal R).cardQuot ≤ N / (P : Ideal R).cardQuot := by
    have h := InvertibleIdeal.cardQuot_mul P (J I)
    rw [hmul I] at h
    apply (Nat.le_div_iff_mul_le P.cardQuot_pos).mpr
    rw [Nat.mul_comm, ← h]
    exact I.1.2.2
  refine ⟨fun I => ⟨J I, hclass I, hnorm I⟩, ?_⟩
  intro I K h
  have hJ : J I = J K := congrArg Subtype.val h
  apply Subtype.ext
  apply Subtype.ext
  calc
    I.1.1 = P * J I := (hmul I).symm
    _ = P * J K := congrArg (P * ·) hJ
    _ = K.1.1 := hmul K

theorem natCard_divisibleIdealClassBall_le {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ B : ℕ,
      (∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∀ N : ℕ,
        Nat.card (IdealClassBall (QuadraticAlgebra ℤ d b) C N) ≤ B * N) →
      ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∀ N : ℕ,
        ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
          Nat.card (DivisibleIdealClassBall (QuadraticAlgebra ℤ d b) C N P) ≤
            B * (N / (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot) := by
  letI := quadraticOrderIsDomain hD
  intro B hB C N P
  letI := finite_idealClassBall hD (P.idealClass⁻¹ * C)
    (N / (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot)
  exact (Nat.card_le_card_of_injective (divisibleClassBallEmbedding C N P)
    (divisibleClassBallEmbedding C N P).injective).trans (hB _ _)

end Bernays
