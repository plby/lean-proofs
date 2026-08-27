/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTHarmonicConvolution
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Absolute sums of real arithmetic convolutions

This specializes the fiberwise argument used by Mathlib's L-series
convolution theorem to unweighted real arithmetic functions. In particular
the infinite fiber above zero is handled using the defining zero values,
not by identifying it with the empty divisor antidiagonal.
-/

namespace Erdos4b.FGKMT

noncomputable section

open ArithmeticFunction
open scoped BigOperators

theorem arithmetic_mul_eq_tsum_fiber (f g : ArithmeticFunction ℝ) (n : ℕ) :
    (f * g) n = ∑' p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n}, f p.val.1 * g p.val.2 := by
  by_cases hn : n = 0
  · subst n
    rw [ArithmeticFunction.map_zero]
    have hzero : ∀ p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}, f p.val.1 * g p.val.2 = 0 := by
      rintro ⟨⟨a, b⟩, hab⟩
      have hab0 : a * b = 0 := hab
      rcases Nat.mul_eq_zero.mp hab0 with ha | hb
      · simp [ha]
      · simp [hb]
    simp only [hzero, tsum_zero]
  · have hset : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n} =
        (n.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
      ext p
      simp [hn]
    rw [hset, Finset.tsum_subtype' n.divisorsAntidiagonal
      (fun p => f p.1 * g p.2), ArithmeticFunction.mul_apply]

theorem arithmetic_mul_hasSum (f g : ArithmeticFunction ℝ)
    (hf : Summable (fun n => |f n|)) (hg : Summable (fun n => |g n|)) :
    HasSum (fun n => (f * g) n) ((∑' n, f n) * ∑' n, g n) := by
  have hfn : Summable (fun n => ‖f n‖) := by simpa only [Real.norm_eq_abs] using hf
  have hgn : Summable (fun n => ‖g n‖) := by simpa only [Real.norm_eq_abs] using hg
  have hprod := hfn.of_norm.hasSum.mul hgn.of_norm.hasSum
    (summable_mul_of_summable_norm hfn hgn)
  simpa only [← arithmetic_mul_eq_tsum_fiber] using
    hprod.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)

def absArithmetic (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => |f n|, by simp⟩

@[simp] theorem absArithmetic_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    absArithmetic f n = |f n| := rfl

theorem abs_arithmetic_mul_le (f g : ArithmeticFunction ℝ) (n : ℕ) :
    |(f * g) n| ≤ (absArithmetic f * absArithmetic g) n := by
  simp only [ArithmeticFunction.mul_apply, absArithmetic_apply, ← abs_mul]
  exact Finset.abs_sum_le_sum_abs _ _

theorem arithmetic_mul_abs_summable_and_tsum_le (f g : ArithmeticFunction ℝ)
    (hf : Summable (fun n => |f n|)) (hg : Summable (fun n => |g n|)) :
    Summable (fun n => |(f * g) n|) ∧
      (∑' n, |(f * g) n|) ≤ (∑' n, |f n|) * ∑' n, |g n| := by
  have hmajor := arithmetic_mul_hasSum (absArithmetic f) (absArithmetic g)
    (by simpa only [absArithmetic_apply, abs_abs] using hf)
    (by simpa only [absArithmetic_apply, abs_abs] using hg)
  have hs := Summable.of_nonneg_of_le (fun n => abs_nonneg ((f * g) n))
    (abs_arithmetic_mul_le f g) hmajor.summable
  refine ⟨hs, ?_⟩
  exact (Summable.tsum_le_tsum (abs_arithmetic_mul_le f g) hs hmajor.summable).trans_eq
    hmajor.tsum_eq

def logWeightedArithmetic (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n * Real.log n, by simp⟩

@[simp] theorem logWeightedArithmetic_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    logWeightedArithmetic f n = f n * Real.log n := rfl

theorem abs_logWeightedArithmetic (f : ArithmeticFunction ℝ) (n : ℕ) :
    |logWeightedArithmetic f n| = |f n| * Real.log n := by
  rw [logWeightedArithmetic_apply, abs_mul, abs_of_nonneg (Real.log_natCast_nonneg n)]

/-- Logarithmic weighting is a derivation for divisor convolution. -/
theorem logWeightedArithmetic_mul (f g : ArithmeticFunction ℝ) :
    logWeightedArithmetic (f * g) = logWeightedArithmetic f * g + f * logWeightedArithmetic g := by
  ext n
  simp only [logWeightedArithmetic_apply, ArithmeticFunction.add_apply,
    ArithmeticFunction.mul_apply, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [← hprod, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hp1) (by exact_mod_cast hp2)]
  ring

theorem arithmetic_mul_log_summable_and_tsum_le (f g : ArithmeticFunction ℝ)
    (hf : Summable (fun n => |f n|)) (hg : Summable (fun n => |g n|))
    (hfLog : Summable (fun n => |f n| * Real.log n))
    (hgLog : Summable (fun n => |g n| * Real.log n)) :
    Summable (fun n => |(f * g) n| * Real.log n) ∧
      (∑' n, |(f * g) n| * Real.log n) ≤
        (∑' n, |f n| * Real.log n) * (∑' n, |g n|) +
          (∑' n, |f n|) * (∑' n, |g n| * Real.log n) := by
  obtain ⟨hs1, hsum1⟩ := arithmetic_mul_abs_summable_and_tsum_le (logWeightedArithmetic f) g
    (by simpa only [abs_logWeightedArithmetic] using hfLog) hg
  obtain ⟨hs2, hsum2⟩ := arithmetic_mul_abs_summable_and_tsum_le f (logWeightedArithmetic g)
    hf (by simpa only [abs_logWeightedArithmetic] using hgLog)
  have hpoint : ∀ n, |(f * g) n| * Real.log n ≤
      |(logWeightedArithmetic f * g) n| + |(f * logWeightedArithmetic g) n| := by
    intro n
    rw [← abs_logWeightedArithmetic, logWeightedArithmetic_mul, ArithmeticFunction.add_apply]
    exact abs_add_le _ _
  have hs := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg ((f * g) n)) (Real.log_natCast_nonneg n))
    hpoint (hs1.add hs2)
  refine ⟨hs, ?_⟩
  have hsum := (Summable.tsum_le_tsum hpoint hs (hs1.add hs2)).trans_eq (hs1.tsum_add hs2)
  exact hsum.trans (by simpa only [abs_logWeightedArithmetic] using add_le_add hsum1 hsum2)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.arithmetic_mul_abs_summable_and_tsum_le
#print axioms Erdos4b.FGKMT.arithmetic_mul_log_summable_and_tsum_le
