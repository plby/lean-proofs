import ErdosProblems.Erdos941.AllRootCoefficient
import ErdosProblems.Erdos941.RealNegativeCharacter
import ErdosProblems.Erdos941.SquareIndicator
import ErdosProblems.Erdos941.CoprimeZetaConvolution

/-! # The local convolution identity for quadratic roots -/

namespace Erdos941

open ArithmeticFunction Finset Analytic

theorem coprime_four_mul_iff (a n : ℕ) : a.Coprime (4 * n) ↔ a.Coprime (2 * n) := by
  rw [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
  rw [show 4 = 2 ^ 2 by norm_num, Nat.coprime_pow_right_iff (by decide : 0 < 2)]

noncomputable def restrictedLiouville (n : ℕ) : ArithmeticFunction ℝ :=
  (realCharacterArithmetic (1 : DirichletCharacter ℝ (4 * n))).pmul
    (liouville : ArithmeticFunction ℝ)

theorem restrictedLiouville_multiplicative (n : ℕ) :
    (restrictedLiouville n).IsMultiplicative :=
  (1 : DirichletCharacter ℝ (4 * n)).isMultiplicative_toArithmeticFunction.pmul
    isMultiplicative_liouville.intCast

theorem real_liouville_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (liouville : ArithmeticFunction ℝ) (p ^ k) = (-1 : ℝ) ^ k := by
  rw [intCoe_apply, liouville_apply (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp]
  push_cast
  rfl

theorem restrictedLiouville_prime_pow {n p : ℕ} (hp : p.Prime)
    (hcop : p.Coprime (2 * n)) (k : ℕ) :
    restrictedLiouville n (p ^ k) = (-1 : ℝ) ^ k := by
  rw [restrictedLiouville, pmul_apply, realCharacterArithmetic_prime_pow _ hp,
    MulChar.one_apply ((ZMod.isUnit_iff_coprime p (4 * n)).mpr
      ((coprime_four_mul_iff p n).mpr hcop)), one_pow, one_mul,
    real_liouville_prime_pow hp]

theorem allRootCoefficient_prime_pow_real {n p : ℕ} [NeZero n] [hp : Fact p.Prime]
    (hcop : p.Coprime (2 * n)) (k : ℕ) :
    (allRootCoefficient n (p ^ (k + 1)) : ℝ) =
      1 + realNegativeQuadraticCharacter n p := by
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    have hh := hcop.of_dvd_right (dvd_mul_right 2 n)
    norm_num at hh
  rw [realNegativeQuadraticCharacter_prime n hp2]
  have h := allRootCoefficient_prime_pow n hcop k
  exact_mod_cast h.trans (add_comm _ _)

theorem convolution_prime_pow_sum {R : Type*} [Semiring R]
    (f g : ArithmeticFunction R) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ i ∈ range (k + 1), f (p ^ (k - i)) * g (p ^ i) := by
  rw [mul_apply, ← Nat.map_div_left_divisors, sum_map, Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro i hi
  change f (p ^ k / p ^ i) * g (p ^ i) = f (p ^ (k - i)) * g (p ^ i)
  rw [Nat.pow_div (by have hh := mem_range.mp hi; omega) hp.pos]

theorem realNegativeQuadraticCharacter_good_prime {n p : ℕ} [NeZero n]
    [Fact p.Prime] (hcop : p.Coprime (2 * n)) :
    realNegativeQuadraticCharacter n p = 1 ∨ realNegativeQuadraticCharacter n p = -1 := by
  have hu : IsUnit (p : ZMod (4 * n)) := (ZMod.isUnit_iff_coprime p (4 * n)).mpr
    ((coprime_four_mul_iff p n).mpr hcop)
  have h := (realNegativeQuadraticCharacter n).unit_norm_eq_one hu.unit
  rw [hu.unit_spec, Real.norm_eq_abs] at h
  exact (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h

theorem root_liouville_good_prime_pow {n p : ℕ} [NeZero n] [hp : Fact p.Prime]
    (hcop : p.Coprime (2 * n)) (k : ℕ) :
    ((allRootCoefficient n : ArithmeticFunction ℝ) * restrictedLiouville n) (p ^ k) =
      realCharacterArithmetic (realNegativeQuadraticCharacter n) (p ^ k) := by
  rw [convolution_prime_pow_sum _ _ hp.out k,
    realCharacterArithmetic_prime_pow _ hp.out k]
  have hs : (∑ i ∈ range k,
      (allRootCoefficient n : ArithmeticFunction ℝ) (p ^ (k - i)) *
        restrictedLiouville n (p ^ i)) =
      (1 + realNegativeQuadraticCharacter n p) * ∑ i ∈ range k, (-1 : ℝ) ^ i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have hki : 0 < k - i := by have hh := mem_range.mp hi; omega
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hki.ne'
    rw [natCoe_apply, hj, allRootCoefficient_prime_pow_real hcop j,
      restrictedLiouville_prime_pow hp.out hcop i]
  rw [sum_range_succ, hs, Nat.sub_self, pow_zero,
    (allRootCoefficient_multiplicative n).natCast.map_one, one_mul,
    restrictedLiouville_prime_pow hp.out hcop k, neg_one_geom_sum]
  rcases realNegativeQuadraticCharacter_good_prime hcop with h | h
  · rw [h, one_pow]
    by_cases hk : Even k
    · rw [if_pos hk, hk.neg_one_pow]; ring
    · rw [if_neg hk, (Nat.not_even_iff_odd.mp hk).neg_one_pow]; ring
  · rw [h]
    ring

theorem root_liouville_bad_prime_pow {n p : ℕ} [NeZero n] [hp : Fact p.Prime]
    (hcop : ¬p.Coprime (2 * n)) (k : ℕ) :
    ((allRootCoefficient n : ArithmeticFunction ℝ) * restrictedLiouville n) (p ^ k) =
      realCharacterArithmetic (realNegativeQuadraticCharacter n) (p ^ k) := by
  have hu : ¬IsUnit (p : ZMod (4 * n)) := by
    rwa [ZMod.isUnit_iff_coprime, coprime_four_mul_iff]
  have hroot (j : ℕ) : (allRootCoefficient n : ArithmeticFunction ℝ) (p ^ j) =
      (1 : ArithmeticFunction ℝ) (p ^ j) := by
    cases j with
    | zero => simp [(allRootCoefficient_multiplicative n).map_one]
    | succ j =>
      rw [natCoe_apply, allRootCoefficient_bad_prime_pow n hcop j,
        arithmetic_one_prime_pow hp.out, Nat.cast_zero, zero_pow (Nat.succ_ne_zero j)]
  have hliou (j : ℕ) : restrictedLiouville n (p ^ j) =
      (1 : ArithmeticFunction ℝ) (p ^ j) := by
    cases j with
    | zero => simp [(restrictedLiouville_multiplicative n).map_one]
    | succ j =>
      rw [restrictedLiouville, pmul_apply, realCharacterArithmetic_prime_pow _ hp.out,
        MulChar.map_nonunit _ hu, zero_pow (Nat.succ_ne_zero j), zero_mul,
        arithmetic_one_prime_pow hp.out, zero_pow (Nat.succ_ne_zero j)]
  rw [convolution_prime_power_congr hp.out hroot hliou, mul_one,
    arithmetic_one_prime_pow hp.out, realCharacterArithmetic_prime_pow _ hp.out,
    MulChar.map_nonunit _ hu]

theorem root_liouville_convolution (n : ℕ) [NeZero n] :
    (allRootCoefficient n : ArithmeticFunction ℝ) * restrictedLiouville n =
      realCharacterArithmetic (realNegativeQuadraticCharacter n) := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((allRootCoefficient_multiplicative n).natCast.mul (restrictedLiouville_multiplicative n)) _
    (realNegativeQuadraticCharacter n).isMultiplicative_toArithmeticFunction).mpr
  intro p k hp
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hcop : p.Coprime (2 * n)
  · exact root_liouville_good_prime_pow hcop k
  · exact root_liouville_bad_prime_pow hcop k

theorem character_twist_zeta_convolution {q : ℕ} (χ : DirichletCharacter ℝ q)
    (f : ArithmeticFunction ℝ) :
    ((realCharacterArithmetic χ).pmul f) * realCharacterArithmetic χ =
      (realCharacterArithmetic χ).pmul (f * (zeta : ArithmeticFunction ℝ)) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [mul_apply, pmul_apply, mul_apply, mul_sum]
  apply sum_congr rfl
  intro u hu
  have he := (Nat.mem_divisorsAntidiagonal.mp hu).1
  have hn0 : u.1 * u.2 ≠ 0 := he ▸ hn
  have h1 := left_ne_zero_of_mul hn0
  have h2 := right_ne_zero_of_mul hn0
  simp only [pmul_apply, realCharacterArithmetic,
    ← DirichletCharacter.apply_eq_toArithmeticFunction_apply _ h1,
    ← DirichletCharacter.apply_eq_toArithmeticFunction_apply _ h2,
    ← DirichletCharacter.apply_eq_toArithmeticFunction_apply _ hn,
    natCoe_apply, zeta_apply, h2, if_false, Nat.cast_one, mul_one]
  rw [← he, Nat.cast_mul, map_mul]
  ring

theorem coprime_convolution_eq_root_square (n : ℕ) [NeZero n] :
    realCoprimeZetaConvolution (realNegativeQuadraticCharacter n) =
      (allRootCoefficient n : ArithmeticFunction ℝ) *
        (realCharacterArithmetic (1 : DirichletCharacter ℝ (4 * n))).pmul
          (squareIndicator : ArithmeticFunction ℝ) := by
  have hs : (realCharacterArithmetic (1 : DirichletCharacter ℝ (4 * n))).pmul
      (squareIndicator : ArithmeticFunction ℝ) =
      restrictedLiouville n * realCharacterArithmetic (1 : DirichletCharacter ℝ (4 * n)) := by
    rw [restrictedLiouville, character_twist_zeta_convolution, squareIndicator, intCoe_mul]
    congr 1
    rw [mul_comm]
    rfl
  rw [hs, ← mul_assoc, root_liouville_convolution, realCoprimeZetaConvolution, mul_comm]

theorem coprime_convolution_le_root_square (n : ℕ) [NeZero n] (a : ℕ) :
    realCoprimeZetaConvolution (realNegativeQuadraticCharacter n) a ≤
      ((allRootCoefficient n : ArithmeticFunction ℝ) *
        (squareIndicator : ArithmeticFunction ℝ)) a := by
  rw [coprime_convolution_eq_root_square, mul_apply, mul_apply]
  apply sum_le_sum
  intro u hu
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [pmul_apply]
  have hS : 0 ≤ (squareIndicator : ArithmeticFunction ℝ) u.2 := by
    rw [intCoe_apply]
    exact_mod_cast squareIndicator_nonneg u.2
  have hP : realCharacterArithmetic (1 : DirichletCharacter ℝ (4 * n)) u.2 ≤ 1 := by
    rcases eq_or_ne u.2 0 with hz | hz
    · simp [hz]
    rw [realCharacterArithmetic, ← DirichletCharacter.apply_eq_toArithmeticFunction_apply _ hz]
    by_cases hunit : IsUnit (u.2 : ZMod (4 * n))
    · rw [MulChar.one_apply hunit]
    · rw [MulChar.map_nonunit _ hunit]; norm_num
  exact (mul_le_mul_of_nonneg_right hP hS).trans_eq (one_mul _)

end Erdos941
