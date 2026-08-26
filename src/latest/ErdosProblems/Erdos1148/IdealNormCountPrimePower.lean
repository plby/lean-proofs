import ErdosProblems.Erdos1148.IdealNormCountProduct
import ErdosProblems.Erdos1148.QuadraticRootArithmetic

/-! # Lower bounds for ideal counts at split prime powers and squares -/

namespace Erdos1148.DukeArithmetic

open NumberField Ideal UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

lemma normalizedFactors_count_prime_mul_pow {P Q : Ideal (𝓞 K)}
    (hP : Prime P) (hQ : Prime Q) (hne : P ≠ Q) (i j : ℕ) :
    (normalizedFactors (P ^ i * Q ^ j)).count P = i := by
  classical
  rw [normalizedFactors_mul (pow_ne_zero _ hP.ne_zero) (pow_ne_zero _ hQ.ne_zero),
    normalizedFactors_pow, normalizedFactors_pow, normalizedFactors_irreducible hP.irreducible,
    normalizedFactors_irreducible hQ.irreducible]
  simp [normalize_eq, hne]

theorem ideal_norm_count_prime_pow_lower {P Q : Ideal (𝓞 K)}
    (hP : Prime P) (hQ : Prime Q) (hne : P ≠ Q) {p : ℕ}
    (hnP : absNorm P = p) (hnQ : absNorm Q = p) (k : ℕ) :
    k + 1 ≤ Nat.card {I : Ideal (𝓞 K) // absNorm I = p ^ k} := by
  let f : Fin (k + 1) → {I : Ideal (𝓞 K) // absNorm I = p ^ k} :=
    fun i => ⟨P ^ i.val * Q ^ (k - i.val), by
      rw [map_mul, map_pow, map_pow, hnP, hnQ, ← pow_add,
        Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]⟩
  have hf : Function.Injective f := by
    intro i j h
    have hi := congrArg
      (fun I : Ideal (𝓞 K) => (normalizedFactors I).count P) (congrArg Subtype.val h)
    dsimp only [f] at hi
    rw [normalizedFactors_count_prime_mul_pow hP hQ hne,
      normalizedFactors_count_prime_mul_pow hP hQ hne] at hi
    exact Fin.ext hi
  have : Finite {I : Ideal (𝓞 K) // absNorm I = p ^ k} := finite_setOfPred_absNorm_eq _
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

theorem quadratic_ideal_norm_count_square_lower (d : ℤ) [Fact (¬IsSquare d)] (n : ℕ) :
    1 ≤ Nat.card {I : Ideal (𝓞 (QuadraticDiscrAlgebra d)) // absNorm I = n ^ 2} := by
  have hnorm : absNorm (Ideal.span {(n : 𝓞 (QuadraticDiscrAlgebra d))}) = n ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, quadraticDiscrAlgebra_finrank]
  have : Nonempty {I : Ideal (𝓞 (QuadraticDiscrAlgebra d)) // absNorm I = n ^ 2} :=
    ⟨⟨Ideal.span {(n : 𝓞 (QuadraticDiscrAlgebra d))}, hnorm⟩⟩
  have : Finite {I : Ideal (𝓞 (QuadraticDiscrAlgebra d)) // absNorm I = n ^ 2} :=
    finite_setOfPred_absNorm_eq _
  exact Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'

end Erdos1148.DukeArithmetic
