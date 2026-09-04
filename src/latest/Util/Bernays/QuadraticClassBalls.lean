import Util.Bernays.QuadraticNormBalls
import Util.Bernays.IdealNormMultiplicative

/-!
# Linear upper bounds for ideals in each quadratic ideal class
-/

open scoped nonZeroDivisors

namespace Bernays

def IdealClassBall (R : Type*) [CommRing R] [IsDomain R] (C : ClassGroup R) (N : ℕ) :=
  {I : InvertibleIdeal R // I.idealClass = C ∧ (I : Ideal R).cardQuot ≤ N}

theorem natCard_idealClassBall_zero {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] (C : ClassGroup R) : Nat.card (IdealClassBall R C 0) = 0 := by
  have : IsEmpty (IdealClassBall R C 0) := ⟨fun I => (not_le_of_gt I.1.cardQuot_pos) I.2.2⟩
  simp

theorem exists_principal_generator_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I J : InvertibleIdeal (QuadraticAlgebra ℤ d b), I.idealClass * J.idealClass = 1 →
      ∃ z : QuadraticAlgebra ℤ d b, ∃ hz : z ≠ 0, I * J = InvertibleIdeal.principal z hz ∧
        z.norm.natAbs = (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot *
          (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot := by
  let := quadraticOrderIsDomain hD
  intro I J hc
  have hclass : (I * J).idealClass = 1 := by rwa [InvertibleIdeal.idealClass_mul]
  obtain ⟨z, hz, heq⟩ := (InvertibleIdeal.idealClass_eq_one_iff (I * J)).mp hclass
  refine ⟨z, hz, heq, ?_⟩
  have hnorm := InvertibleIdeal.cardQuot_mul I J
  rw [heq, InvertibleIdeal.coe_principal,
    Erdos1081.cardQuot_span_singleton_eq_norm_natAbs, algebraNorm_quadraticOrder] at hnorm
  exact hnorm

theorem exists_classBall_embedding_normBall {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∃ m : ℕ, 0 < m ∧
      ∀ N : ℕ, Nonempty (IdealClassBall (QuadraticAlgebra ℤ d b) C N ↪ QuadraticNormBall d b (m * N)) := by
  let := quadraticOrderIsDomain hD
  intro C
  obtain ⟨J, hJ⟩ := InvertibleIdeal.idealClass_surjective C⁻¹
  let m := (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot
  refine ⟨m, J.cardQuot_pos, ?_⟩
  intro N
  let B := IdealClassBall (QuadraticAlgebra ℤ d b) C N
  have hex (I : B) : ∃ z : QuadraticAlgebra ℤ d b, ∃ hz : z ≠ 0,
      J * I.1 = InvertibleIdeal.principal z hz ∧ z.norm.natAbs ≤ m * N := by
    have hc : J.idealClass * I.1.idealClass = 1 := by rw [hJ, I.2.1, inv_mul_cancel]
    obtain ⟨z, hz, heq, hnorm⟩ := exists_principal_generator_norm hD J I.1 hc
    exact ⟨z, hz, heq, hnorm ▸ Nat.mul_le_mul_left m I.2.2⟩
  let z : B → QuadraticAlgebra ℤ d b := fun I => (hex I).choose
  have hz (I : B) : z I ≠ 0 := (hex I).choose_spec.choose
  have heq (I : B) : J * I.1 = InvertibleIdeal.principal (z I) (hz I) :=
    (hex I).choose_spec.choose_spec.1
  have hbound (I : B) : (z I).norm.natAbs ≤ m * N := (hex I).choose_spec.choose_spec.2
  refine ⟨⟨fun I => ⟨z I, hbound I⟩, ?_⟩⟩
  intro I K h
  have hzero : z I = z K := congrArg Subtype.val h
  have hprod : J * I.1 = J * K.1 := by
    rw [heq I, heq K]
    apply InvertibleIdeal.ext
    simp only [InvertibleIdeal.coe_principal, hzero]
  apply Subtype.ext
  exact InvertibleIdeal.mul_right_cancel I.1 K.1 J (by simpa only [mul_comm] using hprod)

theorem finite_idealClassBall {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∀ N : ℕ,
      Finite (IdealClassBall (QuadraticAlgebra ℤ d b) C N) := by
  let := quadraticOrderIsDomain hD
  intro C N
  obtain ⟨m, _, hm⟩ := exists_classBall_embedding_normBall hD C
  let := finite_quadraticNormBall hD (m * N)
  obtain ⟨e⟩ := hm N
  exact Finite.of_injective e e.injective

theorem exists_natCard_idealClassBall_le {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∃ B : ℕ, 0 < B ∧ ∀ N : ℕ, 0 < N →
      Nat.card (IdealClassBall (QuadraticAlgebra ℤ d b) C N) ≤ B * N := by
  let := quadraticOrderIsDomain hD
  intro C
  obtain ⟨m, _, hm⟩ := exists_classBall_embedding_normBall hD C
  refine ⟨36 * (m + 1), by positivity, ?_⟩
  intro N hN
  let := finite_quadraticNormBall hD (m * N)
  obtain ⟨e⟩ := hm N
  have hcard := (Nat.card_le_card_of_injective e e.injective).trans (natCard_quadraticNormBall_le hD (m * N))
  exact hcard.trans (by nlinarith)

theorem exists_uniform_natCard_idealClassBall_le {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∃ B : ℕ, 0 < B ∧ ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∀ N : ℕ,
      Nat.card (IdealClassBall (QuadraticAlgebra ℤ d b) C N) ≤ B * N := by
  classical
  let := quadraticOrderIsDomain hD
  let := quadraticOrderClassGroupFintype hD
  choose B hBpos hB using exists_natCard_idealClassBall_le hD
  refine ⟨∑ C, B C, ?_, ?_⟩
  · exact (hBpos 1).trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 1))
  · intro C N
    by_cases hN : N = 0
    · simp [hN, natCard_idealClassBall_zero]
    · exact (hB C N (Nat.pos_of_ne_zero hN)).trans (Nat.mul_le_mul_right N
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ C)))

end Bernays
