import ErdosProblems.Erdos67.MRGSA10GlobalSecondary

/-!
# The actual high-factor generalized Mangoldt coefficient

For the completely multiplicative coefficients used by the E69 source
specialization, the generalized Mangoldt coefficient of the high-prime
factor is exactly the ordinary von Mangoldt function times that factor.
This gives both the sharp norm majorant and the support above the splitting
point required by the two Shiu secondary sums.
-/

open scoped BigOperators ArithmeticFunction

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Prime-band restriction preserves complete multiplicativity on positive
integers. -/
theorem primeBandCoefficient_isCompletelyMultiplicativeOnPositive
    {f : ℕ → ℂ} (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (P : ℕ → Prop) [DecidablePred P] :
    IsCompletelyMultiplicativeOnPositive (primeBandCoefficient f P) := by
  refine ⟨?_, ?_⟩
  · simp [primeBandCoefficient, primeSupported_one P, hcomp.1]
  · intro m n hm hn
    have hiff := primeSupported_mul_iff P hm.ne' hn.ne'
    by_cases hmP : PrimeSupported P m
    · by_cases hnP : PrimeSupported P n
      · rw [primeBandCoefficient_eq_of_supported f P (hiff.mpr ⟨hmP, hnP⟩),
            primeBandCoefficient_eq_of_supported f P hmP,
            primeBandCoefficient_eq_of_supported f P hnP]
        exact hcomp.2 m n hm hn
      · have hmnP : ¬ PrimeSupported P (m * n) :=
          fun h ↦ hnP (hiff.mp h).2
        simp [primeBandCoefficient, hmP, hnP, hmnP]
    · have hmnP : ¬ PrimeSupported P (m * n) :=
        fun h ↦ hmP (hiff.mp h).1
      simp [primeBandCoefficient, hmP, hmnP]

/-- The high-prime arithmetic function inherits complete multiplicativity. -/
theorem gsA9HighArithmetic_isCompletelyMultiplicativeOnPositive
    {f : ℕ → ℂ} (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (y : ℕ) :
    IsCompletelyMultiplicativeOnPositive (gsA9HighArithmetic f y) := by
  have hhigh := primeBandCoefficient_isCompletelyMultiplicativeOnPositive
    hcomp (fun p ↦ ¬ p ≤ y)
  refine ⟨?_, ?_⟩
  · simpa [gsA9HighArithmetic_one
      hcomp.isMultiplicativeOnPositiveNat y] using hhigh.1
  · intro m n hm hn
    rw [gsA9HighArithmetic_apply_of_ne_zero f y
          (Nat.mul_ne_zero hm.ne' hn.ne'),
      gsA9HighArithmetic_apply_of_ne_zero f y hm.ne',
      gsA9HighArithmetic_apply_of_ne_zero f y hn.ne']
    exact hhigh.2 m n hm hn

/-- The coefficient `a(n) Λ(n)` bundled as a complex arithmetic function. -/
def completelyMultiplicativeMangoldt
    (a : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ a n * (ArithmeticFunction.vonMangoldt n : ℂ), by simp⟩

@[simp] theorem completelyMultiplicativeMangoldt_apply
    (a : ArithmeticFunction ℂ) (n : ℕ) :
    completelyMultiplicativeMangoldt a n =
      a n * (ArithmeticFunction.vonMangoldt n : ℂ) := rfl

/-- For a completely multiplicative arithmetic function, convolution with
`a(n) Λ(n)` inserts the logarithmic weight. -/
theorem completelyMultiplicativeMangoldt_mul_self
    (a : ArithmeticFunction ℂ)
    (hcomp : IsCompletelyMultiplicativeOnPositive a) :
    completelyMultiplicativeMangoldt a * a = gsLogWeighted a := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  rw [ArithmeticFunction.mul_apply, gsLogWeighted_apply]
  calc
    (∑ xy ∈ n.divisorsAntidiagonal,
        completelyMultiplicativeMangoldt a xy.1 * a xy.2) =
        ∑ xy ∈ n.divisorsAntidiagonal,
          a n * (ArithmeticFunction.vonMangoldt xy.1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro xy hxy
      have hprod := (Nat.mem_divisorsAntidiagonal.mp hxy).1
      have hx : 0 < xy.1 := Nat.pos_of_ne_zero
        (Nat.ne_zero_of_mem_divisorsAntidiagonal hxy).1
      have hy : 0 < xy.2 := Nat.pos_of_ne_zero
        (Nat.ne_zero_of_mem_divisorsAntidiagonal hxy).2
      rw [completelyMultiplicativeMangoldt_apply]
      calc
        a xy.1 * (ArithmeticFunction.vonMangoldt xy.1 : ℂ) * a xy.2 =
            (a xy.1 * a xy.2) *
              (ArithmeticFunction.vonMangoldt xy.1 : ℂ) := by ring
        _ = a n * (ArithmeticFunction.vonMangoldt xy.1 : ℂ) := by
          rw [← hcomp.2 xy.1 xy.2 hx hy, hprod]
    _ = a n * ∑ xy ∈ n.divisorsAntidiagonal,
          (ArithmeticFunction.vonMangoldt xy.1 : ℂ) := by
      rw [Finset.mul_sum]
    _ = a n * (Real.log n : ℂ) := by
      rw [Nat.sum_divisorsAntidiagonal
        (fun d _q ↦ (ArithmeticFunction.vonMangoldt d : ℂ))]
      rw [← Complex.ofReal_sum, ArithmeticFunction.vonMangoldt_sum]

/-- Algebraic identification of the generalized and ordinary Mangoldt
coefficients in the completely multiplicative case. -/
theorem gsGeneralizedMangoldt_eq_completelyMultiplicativeMangoldt
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (hcomp : IsCompletelyMultiplicativeOnPositive a) :
    gsGeneralizedMangoldt a ha = completelyMultiplicativeMangoldt a := by
  have hconv := completelyMultiplicativeMangoldt_mul_self a hcomp
  calc
    gsGeneralizedMangoldt a ha =
        gsLogWeighted a * ArithmeticFunction.dirichletInverse a ha := rfl
    _ = (completelyMultiplicativeMangoldt a * a) *
          ArithmeticFunction.dirichletInverse a ha := by rw [hconv]
    _ = completelyMultiplicativeMangoldt a *
          (a * ArithmeticFunction.dirichletInverse a ha) := by
      rw [mul_assoc]
    _ = completelyMultiplicativeMangoldt a := by
      rw [ArithmeticFunction.self_mul_dirichletInverse, mul_one]

/-- Exact formula for the actual high-prime generalized Mangoldt factor. -/
theorem gsA9HighGeneralizedMangoldt_eq_completelyMultiplicativeMangoldt
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f) (y : ℕ) :
    gsA9HighGeneralizedMangoldt hmul y =
      completelyMultiplicativeMangoldt (gsA9HighArithmetic f y) := by
  exact gsGeneralizedMangoldt_eq_completelyMultiplicativeMangoldt
    (gsA9HighArithmetic f y) (gsA9HighArithmeticInvertible hmul y)
    (gsA9HighArithmetic_isCompletelyMultiplicativeOnPositive hcomp y)

/-- Pointwise form of the actual-high-factor identity. -/
theorem gsA9HighGeneralizedMangoldt_apply
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f) (y n : ℕ) :
    gsA9HighGeneralizedMangoldt hmul y n =
      gsA9HighArithmetic f y n *
        (ArithmeticFunction.vonMangoldt n : ℂ) := by
  rw [gsA9HighGeneralizedMangoldt_eq_completelyMultiplicativeMangoldt
    hmul hcomp y]
  rfl

/-- The actual generalized Mangoldt coefficient has the ordinary von
Mangoldt function as a sharp pointwise norm majorant. -/
theorem norm_gsA9HighGeneralizedMangoldt_le_vonMangoldt
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (y n : ℕ) :
    ‖gsA9HighGeneralizedMangoldt hmul y n‖ ≤
      ArithmeticFunction.vonMangoldt n := by
  rw [gsA9HighGeneralizedMangoldt_apply hmul hcomp y n, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  by_cases hn : n = 0
  · subst n
    simp
  have hhigh : ‖gsA9HighArithmetic f y n‖ ≤ 1 := by
    rw [gsA9HighArithmetic_apply_of_ne_zero f y hn]
    exact norm_primeBandCoefficient_le_one hbound _ (Nat.pos_of_ne_zero hn)
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg hhigh

/-- The high-prime coefficient is zero on nontrivial integers below the
splitting point. -/
theorem gsA9HighArithmetic_eq_zero_of_two_le_of_le
    (f : ℕ → ℂ) (y : ℕ) {n : ℕ}
    (hn : 2 ≤ n) (hny : n ≤ y) :
    gsA9HighArithmetic f y n = 0 := by
  rw [gsA9HighArithmetic_apply_of_ne_zero f y (by omega)]
  unfold gsA9High primeBandCoefficient
  split_ifs with hsupp
  · obtain ⟨p, hpPrime, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    have hpMem : p ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpPrime, hpdvd, by omega⟩
    have hpHigh := hsupp.2 p hpMem
    have hpn : p ≤ n := Nat.le_of_dvd (by omega) hpdvd
    exact (hpHigh (hpn.trans hny)).elim
  · rfl

/-- Consequently the actual generalized Mangoldt factor is supported
strictly above `y`. -/
theorem gsA9HighGeneralizedMangoldt_eq_zero_of_le_of_completelyMultiplicative
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (y : ℕ) {n : ℕ} (hny : n ≤ y) :
    gsA9HighGeneralizedMangoldt hmul y n = 0 := by
  rcases n with (_ | _ | n)
  · simp
  · exact gsGeneralizedMangoldt_one _ _
  · rw [gsA9HighGeneralizedMangoldt_apply hmul hcomp y (n + 2),
      gsA9HighArithmetic_eq_zero_of_two_le_of_le f y (by omega) hny,
      zero_mul]

end

end Erdos67.MRHalaszBands
