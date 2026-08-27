/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTHarmonicConvolution
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Uniform harmonic convolution mean bounds

The floor in the harmonic kernel is retained exactly. Its error is at most
one, uniformly in both integers. This gives the quantitative cumulative
estimate used before smooth partial summation; no qualitative limiting
statement is substituted for that estimate.
-/

namespace Erdos4b.FGKMT

noncomputable section

open ArithmeticFunction
open scoped BigOperators

theorem harmonic_natDiv_log_bounds {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    0 ≤ (harmonic (N / d) : ℝ) - Real.log ((N : ℝ) / d) ∧
      (harmonic (N / d) : ℝ) - Real.log ((N : ℝ) / d) ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hratio : (1 : ℝ) ≤ (N : ℝ) / d :=
    (one_le_div hdR).2 (by exact_mod_cast hdN)
  have hlower : Real.log ((N : ℝ) / d) ≤ (harmonic (N / d) : ℝ) := by
    simpa only [Nat.floor_div_eq_div] using
      log_le_harmonic_floor ((N : ℝ) / d) (zero_le_one.trans hratio)
  have hupper : (harmonic (N / d) : ℝ) ≤ 1 + Real.log ((N : ℝ) / d) := by
    simpa only [Nat.floor_div_eq_div] using
      harmonic_floor_le_one_add_log ((N : ℝ) / d) hratio
  constructor <;> linarith

theorem harmonic_natDiv_log_abs_le {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    |(harmonic (N / d) : ℝ) - Real.log ((N : ℝ) / d)| ≤ 1 := by
  obtain ⟨h0, h1⟩ := harmonic_natDiv_log_bounds hd hdN
  rwa [abs_of_nonneg h0]

theorem sum_reciprocal_Ioc_eq_harmonic (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, 1 / (n : ℝ)) = harmonic N := by
  have hinterval : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp
    omega
  rw [hinterval, harmonic_eq_sum_Icc]
  simp

theorem sum_eq_harmonicCorrection_harmonic (f : ArithmeticFunction ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, f n) =
      ∑ d ∈ Finset.Ioc 0 N, harmonicCorrection f d * (harmonic (N / d) : ℝ) := by
  conv_lhs => rw [← harmonicCorrection_mul_harmonicArithmetic f]
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  simp only [harmonicArithmetic_apply, sum_reciprocal_Ioc_eq_harmonic]

theorem sum_harmonicCorrection_log_error_le (f : ArithmeticFunction ℝ) (N : ℕ) :
    |(∑ n ∈ Finset.Ioc 0 N, f n) -
      ∑ d ∈ Finset.Ioc 0 N, harmonicCorrection f d * Real.log ((N : ℝ) / d)| ≤
        ∑ d ∈ Finset.Ioc 0 N, |harmonicCorrection f d| := by
  rw [sum_eq_harmonicCorrection_harmonic, ← Finset.sum_sub_distrib]
  calc
    |∑ d ∈ Finset.Ioc 0 N,
        (harmonicCorrection f d * (harmonic (N / d) : ℝ) -
          harmonicCorrection f d * Real.log ((N : ℝ) / d))| ≤
        ∑ d ∈ Finset.Ioc 0 N,
          |harmonicCorrection f d * (harmonic (N / d) : ℝ) -
            harmonicCorrection f d * Real.log ((N : ℝ) / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, |harmonicCorrection f d| := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hd0, hdN⟩ := Finset.mem_Ioc.mp hd
      rw [← mul_sub, abs_mul]
      exact (mul_le_mul_of_nonneg_left (harmonic_natDiv_log_abs_le hd0 hdN)
        (abs_nonneg _)).trans_eq (mul_one _)

/-- Pointwise majorant for replacing a truncated harmonic kernel by
the full logarithmic main term. -/
theorem harmonic_truncated_log_error_le {N n : ℕ} (hN : 1 ≤ N) (hn : 0 < n) :
    |(if n ∈ Finset.Ioc 0 N then (harmonic (N / n) : ℝ) else 0) - Real.log N| ≤
      1 + Real.log n := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  by_cases hnN : n ≤ N
  · rw [if_pos (Finset.mem_Ioc.mpr ⟨hn, hnN⟩)]
    have herr := harmonic_natDiv_log_abs_le hn hnN
    rw [Real.log_div hN0.ne' hn0.ne'] at herr
    have hsplit : (harmonic (N / n) : ℝ) - Real.log N =
        ((harmonic (N / n) : ℝ) - (Real.log N - Real.log n)) - Real.log n := by ring
    rw [hsplit]
    obtain ⟨herrlo, herrhi⟩ := abs_le.mp herr
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [if_neg (by simpa [Finset.mem_Ioc, hn] using hnN), zero_sub, abs_neg,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hN))]
    have hlogle : Real.log (N : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hN0 (by exact_mod_cast (by omega : N ≤ n))
    linarith

/-- Absolute and logarithmic moments of the correction give a uniform
error bound for every cumulative sum, including the full infinite main
constant rather than its truncation. -/
theorem sum_sub_harmonicCorrection_tsum_log_le (f : ArithmeticFunction ℝ)
    (hs : Summable (fun n => |harmonicCorrection f n|))
    (hsLog : Summable (fun n => |harmonicCorrection f n| * Real.log n))
    {N : ℕ} (hN : 1 ≤ N) :
    |(∑ n ∈ Finset.Ioc 0 N, f n) - (∑' n, harmonicCorrection f n) * Real.log N| ≤
      (∑' n, |harmonicCorrection f n|) +
        ∑' n, |harmonicCorrection f n| * Real.log n := by
  let h := harmonicCorrection f
  let v : ℕ → ℝ := fun n =>
    if n ∈ Finset.Ioc 0 N then h n * (harmonic (N / n) : ℝ) else 0
  let e : ℕ → ℝ := fun n => v n - h n * Real.log N
  have hv : Summable v := by
    apply summable_of_ne_finset_zero (s := Finset.Ioc 0 N)
    intro n hn
    simp only [v, if_neg hn]
  have hh : Summable (fun n => h n) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using hs
  have heBound : ∀ n, |e n| ≤ |h n| + |h n| * Real.log n := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [e, v, h]
    · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      have hfactor : e n = h n *
          ((if n ∈ Finset.Ioc 0 N then (harmonic (N / n) : ℝ) else 0) - Real.log N) := by
        dsimp [e, v]
        split_ifs <;> ring
      rw [hfactor, abs_mul]
      calc
        _ ≤ |h n| * (1 + Real.log n) :=
          mul_le_mul_of_nonneg_left (harmonic_truncated_log_error_le hN hn0) (abs_nonneg _)
        _ = _ := by ring
  have hmajor : Summable (fun n => |h n| + |h n| * Real.log n) := hs.add hsLog
  have heAbs : Summable (fun n => |e n|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg (e n)) heBound hmajor
  have hvsum : ∑' n, v n = ∑ n ∈ Finset.Ioc 0 N, f n := by
    rw [tsum_eq_sum (s := Finset.Ioc 0 N) (fun n hn => by simp only [v, if_neg hn]),
      sum_eq_harmonicCorrection_harmonic]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [v, if_pos hn, h]
  have hesum : ∑' n, e n =
      (∑ n ∈ Finset.Ioc 0 N, f n) - (∑' n, h n) * Real.log N := by
    rw [show (fun n => e n) = (fun n => v n - h n * Real.log N) from rfl,
      hv.tsum_sub (hh.mul_right (Real.log N)), hvsum, tsum_mul_right]
  rw [← hesum]
  calc
    |∑' n, e n| ≤ ∑' n, |e n| := by
      simpa only [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (f := e) (by simpa only [Real.norm_eq_abs] using heAbs)
    _ ≤ ∑' n, (|h n| + |h n| * Real.log n) :=
      Summable.tsum_le_tsum heBound heAbs hmajor
    _ = _ := hs.tsum_add hsLog

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sum_harmonicCorrection_log_error_le
#print axioms Erdos4b.FGKMT.sum_sub_harmonicCorrection_tsum_log_le
