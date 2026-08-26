import ErdosProblems.Erdos380.PrimeProducts
import BoundedGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.CharacterLargeSieve

/-!
# Even moments of prime character sums

The ordinary primitive-character large sieve, applied to coefficients of
ordered prime products, gives every fixed even moment. The coefficient
energy is proved by unique factorization in `PrimeProducts`.
-/

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos380

noncomputable section

lemma dirichletCharacter_sum_pow (s : Finset ℕ) (k q : ℕ)
    (χ : DirichletCharacter ℂ q) :
    (∑ p ∈ s, χ p) ^ k =
      ∑ n ∈ primeProductSupport s k, (productMultiplicity s k n : ℂ) * χ n := by
  let χ' : ℕ →* ℂ := χ.toMonoidHom.comp (Nat.castRingHom (ZMod q)).toMonoidHom
  exact sum_monoidHom_pow s k χ'

lemma productMultiplicity_energy_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (k : ℕ) :
    ∑ n ∈ primeProductSupport s k, ‖(productMultiplicity s k n : ℂ)‖ ^ 2 ≤
      (k.factorial : ℝ) * (s.card : ℝ) ^ k := by
  simp only [Complex.norm_natCast]
  exact_mod_cast sum_productMultiplicity_sq_le hs k

/-- The `2k`-th moment of prime sums over all primitive characters. -/
theorem prime_character_even_moment_le (s : Finset ℕ) (Q P k : ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hP : ∀ p ∈ s, p ≤ P) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (Nat.totient q : ℝ) *
        ∑ χ : primitiveCharacters q, ‖∑ p ∈ s, χ.val p‖ ^ (2 * k)) ≤
      ((P : ℝ) ^ k + (Q : ℝ) ^ 2) *
        ((k.factorial : ℝ) * (s.card : ℝ) ^ k) := by
  classical
  have hls := sum_weighted_norm_sq_primitiveTwists_subset_Ioc_le
    Q 0 (P ^ k) (primeProductSupport s k)
    (by simpa using primeProductSupport_subset_Ioc hs hP)
    (fun n => (productMultiplicity s k n : ℂ))
  have hnorm (q : ℕ) (χ : primitiveCharacters q) :
      ‖∑ n ∈ primeProductSupport s k, (productMultiplicity s k n : ℂ) * χ.val n‖ ^ 2 =
        ‖∑ p ∈ s, χ.val p‖ ^ (2 * k) := by
    rw [← dirichletCharacter_sum_pow s k q χ.val, norm_pow, ← pow_mul, Nat.mul_comm k 2]
  simp_rw [hnorm] at hls
  rw [Nat.cast_pow] at hls
  exact hls.trans (mul_le_mul_of_nonneg_left (productMultiplicity_energy_le hs k)
    (by positivity))

/-- The tenth moment used for products of ten independently chosen primes. -/
theorem prime_character_tenth_moment_le (s : Finset ℕ) (Q P : ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hP : ∀ p ∈ s, p ≤ P) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (Nat.totient q : ℝ) *
        ∑ χ : primitiveCharacters q, ‖∑ p ∈ s, χ.val p‖ ^ 10) ≤
      ((P : ℝ) ^ 5 + (Q : ℝ) ^ 2) * (120 * (s.card : ℝ) ^ 5) := by
  convert prime_character_even_moment_le s Q P 5 hs hP using 1
  norm_num

/-- Uniform average of a character over a finite prime set. -/
def primeCharacterMean {q : ℕ} (s : Finset ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ p ∈ s, χ p) / (s.card : ℂ)

theorem normalized_prime_character_even_moment_le (s : Finset ℕ) (Q P k : ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hP : ∀ p ∈ s, p ≤ P) (hne : s.Nonempty) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (Nat.totient q : ℝ) *
        ∑ χ : primitiveCharacters q, ‖primeCharacterMean s χ.val‖ ^ (2 * k)) ≤
      (((P : ℝ) ^ k + (Q : ℝ) ^ 2) * (k.factorial : ℝ)) / (s.card : ℝ) ^ k := by
  classical
  have hM : 0 < (s.card : ℝ) := by exact_mod_cast hne.card_pos
  simp only [primeCharacterMean, norm_div, Complex.norm_natCast, div_pow]
  simp_rw [← Finset.sum_div, ← mul_div_assoc, ← Finset.sum_div]
  have h := div_le_div_of_nonneg_right (prime_character_even_moment_le s Q P k hs hP)
    (le_of_lt (pow_pos hM (2 * k)))
  refine h.trans_eq ?_
  rw [show 2 * k = k + k by omega, pow_add]
  field_simp

/-- Removing the sieve weights costs nothing because `phi(q) ≤ q`. -/
theorem normalized_prime_character_even_moment_unweighted_le
    (s : Finset ℕ) (Q P k : ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hP : ∀ p ∈ s, p ≤ P) (hne : s.Nonempty) :
    (∑ q ∈ Finset.Ioc 0 Q,
      ∑ χ : primitiveCharacters q, ‖primeCharacterMean s χ.val‖ ^ (2 * k)) ≤
      (((P : ℝ) ^ k + (Q : ℝ) ^ 2) * (k.factorial : ℝ)) / (s.card : ℝ) ^ k := by
  classical
  refine le_trans (Finset.sum_le_sum ?_)
    (normalized_prime_character_even_moment_le s Q P k hs hP hne)
  intro q hq
  have hqpos := (Finset.mem_Ioc.mp hq).1
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hqpos
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hweight : 1 ≤ (q : ℝ) / (q.totient : ℝ) :=
    (le_div_iff₀ hφ).mpr (by simpa using hφq)
  exact le_mul_of_one_le_left (Finset.sum_nonneg fun χ _ => by positivity) hweight

end

end Erdos380
