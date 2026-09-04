import Util.Bernays.IdealGeneratorCounting
import Util.Bernays.CoprimeIdealResidues
import Util.Bernays.QuadraticCosetCounts

/-!
# Coprime ideal classes as counts of unit-residue generators
-/

namespace Bernays

def CoprimeQuadraticBall {d b : ℤ} (I F : Ideal (QuadraticAlgebra ℤ d b)) (T : ℕ) :=
  {z : QuadraticAlgebra ℤ d b // z ∈ I ∧ z.norm.natAbs ≤ T ∧ IsUnit (Ideal.Quotient.mk F z)}

theorem exists_good_factor_iff {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (I : InvertibleIdeal (QuadraticAlgebra ℤ d b))
      (F : Ideal (QuadraticAlgebra ℤ d b)), F ≠ ⊤ → IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) F →
    ∀ z : QuadraticAlgebra ℤ d b, ∀ N : ℕ,
      (∃ hz : z ≠ 0, ∃ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        I * J = InvertibleIdeal.principal z hz ∧
          (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ≤ N ∧
          IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F) ↔
      z ∈ (I : Ideal (QuadraticAlgebra ℤ d b)) ∧
        z.norm.natAbs ≤ (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot * N ∧
        IsUnit (Ideal.Quotient.mk F z) := by
  let := quadraticOrderIsDomain hD
  intro I F hF hIF z N
  let O := QuadraticAlgebra ℤ d b
  let : Nontrivial (O ⧸ F) := Ideal.Quotient.nontrivial_iff.mpr hF
  constructor
  · rintro ⟨hz, J, hprod, hJN, hJF⟩
    have hspan : (I : Ideal O) * (J : Ideal O) = Ideal.span {z} :=
      congrArg (fun K : InvertibleIdeal O => (K : Ideal O)) hprod
    have hzI : z ∈ (I : Ideal O) := Ideal.mul_le_left
      (hspan ▸ Ideal.mem_span_singleton_self z)
    refine ⟨hzI, ?_, (isCoprime_principal_iff_isUnit_quotient F z).mp ?_⟩
    · rw [generator_norm_of_product hD I J z hz hprod]
      exact Nat.mul_le_mul_left _ hJN
    · rw [← hspan]
      exact hIF.mul_left hJF
  · rintro ⟨hzI, hzN, hzunit⟩
    have hz : z ≠ 0 := by
      intro hzero
      have h := hzunit.ne_zero
      exact h (by rw [hzero, map_zero])
    obtain ⟨J, hprod⟩ := InvertibleIdeal.exists_mul_eq_of_le I (InvertibleIdeal.principal z hz)
      ((Ideal.span_singleton_le_iff_mem _).mpr hzI)
    refine ⟨hz, J, hprod, ?_, ?_⟩
    · rw [generator_norm_of_product hD I J z hz hprod] at hzN
      exact (mul_le_mul_iff_right₀ I.cardQuot_pos).mp (by simpa only [Nat.mul_comm] using hzN)
    · have hc := (isCoprime_principal_iff_isUnit_quotient F z).mpr hzunit
      have hspan : (I : Ideal O) * (J : Ideal O) = Ideal.span {z} :=
        congrArg (fun K : InvertibleIdeal O => (K : Ideal O)) hprod
      rw [← hspan] at hc
      exact hc.of_mul_left_right

theorem coprimeQuadraticBall_card {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (I : InvertibleIdeal (QuadraticAlgebra ℤ d b))
      (F : Ideal (QuadraticAlgebra ℤ d b)), F ≠ ⊤ → IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) F →
    ∀ N : ℕ,
      Nat.card (CoprimeQuadraticBall (I : Ideal (QuadraticAlgebra ℤ d b)) F
        ((I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot * N)) =
      Nat.card (QuadraticAlgebra ℤ d b)ˣ *
        Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) I.idealClass⁻¹ N
          (fun J => IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F)) := by
  let := quadraticOrderIsDomain hD
  intro I F hF hIF N
  rw [← idealGeneratorBall_card hD]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun z => (exists_good_factor_iff hD I F hF hIF z N).symm)

end Bernays
