import ErdosProblems.Erdos964.ScalarHarmonicMean
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Cumulative identities for harmonic Dirichlet convolutions
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem abelCumulative_arithmeticFunction (f : ArithmeticFunction ℝ) (x : ℝ) :
    abelCumulative f x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n := by
  unfold abelCumulative
  have hinterval (Q : ℕ) : Finset.Icc 0 Q = insert 0 (Finset.Ioc 0 Q) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hinterval, Finset.sum_insert (by simp)]
  simp only [ArithmeticFunction.map_zero, zero_add]

theorem abelCumulative_convolution (f g : ArithmeticFunction ℝ) (x : ℝ) :
    abelCumulative (f * g : ArithmeticFunction ℝ) x =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n * abelCumulative g (x / n) := by
  rw [abelCumulative_arithmeticFunction, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [abelCumulative_arithmeticFunction, Nat.floor_div_natCast]

theorem coprimeHarmonicAF_nonneg (M n : ℕ) : 0 ≤ coprimeHarmonicAF M n := by
  rw [coprimeHarmonicAF_apply]
  split_ifs <;> positivity

theorem arithmeticFunction_convolution_nonneg (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f * g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg (fun d _ => mul_nonneg (hf d.1) (hg d.2))

theorem coprimeHarmonicAF_pow_nonneg (M k n : ℕ) : 0 ≤ (coprimeHarmonicAF M ^ k) n := by
  induction k generalizing n with
  | zero => simp only [pow_zero, ArithmeticFunction.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
      rw [pow_succ]
      exact arithmeticFunction_convolution_nonneg _ _ ih (coprimeHarmonicAF_nonneg M) n

theorem coprimeHarmonicAF_pow_cumulative_succ (M k : ℕ) (x : ℝ) :
    abelCumulative (coprimeHarmonicAF M ^ (k + 1) : ArithmeticFunction ℝ) x =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, coprimeHarmonicAF M n *
        abelCumulative (coprimeHarmonicAF M ^ k : ArithmeticFunction ℝ) (x / n) := by
  rw [pow_succ', abelCumulative_convolution]

end Erdos964
