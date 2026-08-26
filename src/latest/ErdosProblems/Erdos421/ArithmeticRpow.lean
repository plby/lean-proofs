import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Real powers as multiplicative arithmetic functions -/

namespace Erdos421

noncomputable def arithmeticRpow (α : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 0 then 0 else (n : ℝ) ^ α, by simp⟩

theorem arithmeticRpow_apply {n : ℕ} (hn : n ≠ 0) (α : ℝ) :
    arithmeticRpow α n = (n : ℝ) ^ α := by
  simp only [arithmeticRpow, ArithmeticFunction.coe_mk, if_neg hn]

theorem arithmeticRpow_isMultiplicative (α : ℝ) :
    (arithmeticRpow α).IsMultiplicative := by
  constructor
  · simp [arithmeticRpow]
  · intro m n hcop
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    rw [arithmeticRpow_apply (mul_ne_zero hm hn), arithmeticRpow_apply hm,
      arithmeticRpow_apply hn, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

theorem sum_divisors_multiplicative_rpow (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    {P : ℕ} (hP : Squarefree P) (α : ℝ) :
    (∑ d ∈ P.divisors, f d * (d : ℝ) ^ α) =
      ∏ p ∈ P.primeFactors, (1 + f p * (p : ℝ) ^ α) := by
  have hm := (hf.pmul (arithmeticRpow_isMultiplicative α)).prodPrimeFactors_one_add_of_squarefree hP
  have hs : (∑ d ∈ P.divisors, (f.pmul (arithmeticRpow α)) d) =
      ∑ d ∈ P.divisors, f d * (d : ℝ) ^ α := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [ArithmeticFunction.pmul_apply, arithmeticRpow_apply (Nat.pos_of_mem_divisors hd).ne']
  have hp : (∏ p ∈ P.primeFactors, (1 + (f.pmul (arithmeticRpow α)) p)) =
      ∏ p ∈ P.primeFactors, (1 + f p * (p : ℝ) ^ α) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [ArithmeticFunction.pmul_apply,
      arithmeticRpow_apply (Nat.prime_of_mem_primeFactors hp).ne_zero]
  rw [hs, hp] at hm
  exact hm.symm

end Erdos421
