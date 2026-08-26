import ErdosProblems.Erdos1148.CoprimeZetaConvolution
import ErdosProblems.Erdos1148.QuadraticSplitPrimes
import ErdosProblems.Erdos1148.IdealNormCountPrimePower

/-! # A quadratic-character convolution is bounded by quadratic ideal counts -/

namespace Erdos1148.DukeArithmetic

open NumberField Ideal ArithmeticFunction Finset

lemma good_prime_not_dvd_twice_radicand {a p : ℕ} (hp : p.Prime)
    (hgood : p.Coprime (4 * a)) : ¬(p : ℤ) ∣ 2 * (a : ℤ) := by
  intro h
  have hnat : p ∣ 2 * a := by exact_mod_cast h
  apply (hp.coprime_iff_not_dvd.mp hgood)
  rw [show 4 * a = 2 * (2 * a) by ring]
  exact dvd_mul_of_dvd_right hnat 2

lemma quadraticDirichletCharacter_good_prime (a : ℕ) [NeZero a] {p : ℕ} [Fact p.Prime]
    (hp : p.Prime)
    (hgood : p.Coprime (4 * a)) :
    quadraticDirichletCharacter a p = (legendreSym p (a : ℤ) : ℝ) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h
    apply hp.coprime_iff_not_dvd.mp hgood
    rw [h]
    exact ⟨2 * a, by ring⟩
  rw [quadraticDirichletCharacter_apply_nat, quadraticCharacterValue,
    if_pos (hp.odd_of_ne_two hp2), jacobiSym.legendreSym.to_jacobiSym]

theorem quadratic_convolution_prime_pow_le_ideal_count (a : ℕ) [NeZero a]
    [Fact (¬IsSquare (a : ℤ))] {t : ℤ × ℤ × ℤ} (ht : discr t = (a : ℤ))
    {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) :
    realCoprimeZetaConvolution (quadraticDirichletCharacter a) (p ^ k) ≤
      (Nat.card {I : Ideal (𝓞 (QuadraticDiscrAlgebra (a : ℤ))) // absNorm I = p ^ k} : ℝ) := by
  let : Fact p.Prime := ⟨hp⟩
  rw [realCoprimeZetaConvolution_apply _ (pow_ne_zero k hp.ne_zero), Nat.cast_pow, map_pow]
  by_cases hgood : p.Coprime (4 * a)
  · rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime p (4 * a)).mpr hgood), one_pow, one_mul,
      realZetaConvolution_prime_pow _ hp, quadraticDirichletCharacter_good_prime a hp hgood]
    have hnot := good_prime_not_dvd_twice_radicand hp hgood
    have ha0 : ((a : ℤ) : ZMod p) ≠ 0 := by
      intro h
      exact hnot (dvd_mul_of_dvd_right
        ((ZMod.intCast_zmod_eq_zero_iff_dvd (a : ℤ) p).mp h) 2)
    rcases legendreSym.eq_one_or_neg_one p ha0 with hpos | hneg
    · rw [hpos]
      simp only [Int.cast_one, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
      obtain ⟨P, Q, hP, hQ, hne, hnP, hnQ⟩ := exists_two_primeIdeals_of_legendre_one ht hnot hpos
      exact_mod_cast ideal_norm_count_prime_pow_lower hP hQ hne hnP hnQ k
    · rw [hneg]
      simp only [Int.cast_neg, Int.cast_one, neg_one_geom_sum]
      by_cases he : Even (k + 1)
      · rw [if_pos he]
        exact Nat.cast_nonneg _
      · rw [if_neg he]
        have hkEven : Even k := by simpa only [Nat.even_add_one, not_not] using he
        obtain ⟨j, hj⟩ := hkEven
        have hsq : p ^ k = (p ^ j) ^ 2 := by rw [hj, pow_add, pow_two]
        rw [hsq]
        exact_mod_cast quadratic_ideal_norm_count_square_lower (a : ℤ) (p ^ j)
  · rw [MulChar.map_nonunit _ (fun h => hgood ((ZMod.isUnit_iff_coprime p (4 * a)).mp h)),
      zero_pow hk.ne', zero_mul]
    exact Nat.cast_nonneg _

theorem quadratic_convolution_le_ideal_count (a : ℕ) [NeZero a]
    [Fact (¬IsSquare (a : ℤ))] {t : ℤ × ℤ × ℤ} (ht : discr t = (a : ℤ)) (n : ℕ) :
    realCoprimeZetaConvolution (quadraticDirichletCharacter a) n ≤
      (Nat.card {I : Ideal (𝓞 (QuadraticDiscrAlgebra (a : ℤ))) // absNorm I = n} : ℝ) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    exact quadratic_convolution_prime_pow_le_ideal_count a ht hp hk
  | zero =>
    rw [ArithmeticFunction.map_zero]
    exact Nat.cast_nonneg _
  | one =>
    rw [(isMultiplicative_realCoprimeZetaConvolution _).map_one]
    simp only [absNorm_eq_one_iff, Nat.card_unique, Nat.cast_one, le_refl]
  | coprime m n hm hn hmn hmBound hnBound =>
    rw [(isMultiplicative_realCoprimeZetaConvolution _).map_mul_of_coprime hmn]
    apply (mul_le_mul hmBound hnBound (realCoprimeZetaConvolution_nonneg _ n)
      (Nat.cast_nonneg _)).trans
    exact_mod_cast ideal_norm_count_mul_le (K := QuadraticDiscrAlgebra (a : ℤ)) hmn

end Erdos1148.DukeArithmetic
