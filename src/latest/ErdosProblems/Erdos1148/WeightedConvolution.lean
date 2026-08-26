import ErdosProblems.Erdos1148.DirichletHyperbola
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Power weights and finite Dirichlet convolution -/

namespace Erdos1148.DukeArithmetic

open Finset ArithmeticFunction

noncomputable def arithmeticRpowTwist (s : ℝ) (f : ArithmeticFunction ℝ) :
    ArithmeticFunction ℝ where
  toFun n := (n : ℝ) ^ (-s) * f n
  map_zero' := by simp

@[simp] lemma arithmeticRpowTwist_apply (s : ℝ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    arithmeticRpowTwist s f n = (n : ℝ) ^ (-s) * f n := rfl

theorem arithmeticRpowTwist_mul (s : ℝ) (f g : ArithmeticFunction ℝ) :
    arithmeticRpowTwist s (f * g) = arithmeticRpowTwist s f * arithmeticRpowTwist s g := by
  ext n
  simp only [arithmeticRpowTwist_apply, mul_apply, mul_sum]
  refine sum_congr rfl (fun p hp => ?_)
  rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

noncomputable def weightedArithmeticPartialSum (f : ArithmeticFunction ℝ) (s : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) * f n

theorem weighted_convolution_hyperbola (f g : ArithmeticFunction ℝ) (s : ℝ)
    {A B X : ℕ} (hAX : A ≤ X) (hBX : B ≤ X) (hAB : A * B ≤ X)
    (hX : X < (A + 1) * (B + 1)) :
    weightedArithmeticPartialSum (f * g) s X =
      (∑ m ∈ Ioc 0 A, (m : ℝ) ^ (-s) * f m * weightedArithmeticPartialSum g s (X / m)) +
      (∑ n ∈ Ioc 0 B, (n : ℝ) ^ (-s) * g n * weightedArithmeticPartialSum f s (X / n)) -
      weightedArithmeticPartialSum f s A * weightedArithmeticPartialSum g s B := by
  have h := sum_convolution_hyperbola (arithmeticRpowTwist s f) (arithmeticRpowTwist s g)
    hAX hBX hAB hX
  rw [← arithmeticRpowTwist_mul] at h
  simpa only [weightedArithmeticPartialSum, arithmeticRpowTwist_apply] using h

lemma weightedArithmeticPartialSum_eq_sum_range (f : ArithmeticFunction ℝ) (s : ℝ) (N : ℕ) :
    weightedArithmeticPartialSum f s N =
      ∑ n ∈ range N, ((n + 1 : ℕ) : ℝ) ^ (-s) * f (n + 1) := by
  unfold weightedArithmeticPartialSum
  rw [← Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, zero_add, add_comm 1]

end Erdos1148.DukeArithmetic
