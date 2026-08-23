/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerCoprimeOuterEstimate
import Mathlib.Data.Nat.Choose.Sum

/-!
# Factorial cancellation for the coprime-node Hermite basis

Deleting the multiples of the auxiliary prime does not introduce an
`R log R` loss.  Ratios of the full integer-node factorials are binomial
coefficients, and the corresponding ratio for the deleted `q`-multiples is
another binomial coefficient.  The two estimates below isolate that
arithmetic cancellation.
-/

noncomputable section

namespace Erdos240.BakerCoprimeFactorialCancellation

theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      calc
        n + 1 ≤ 2 ^ n + 2 ^ n := Nat.add_le_add ih Nat.one_le_two_pow
        _ = 2 ^ n * 2 := by ring

/-- Ratios of the two factorial pieces attached to integer nodes are bounded
by one row sum of Pascal's triangle. -/
theorem factorial_pair_div_factorial_pair_le_two_pow
    {R l r : ℕ} (hl : 1 ≤ l) (hlR : l ≤ R)
    (hr : 1 ≤ r) (hrR : r ≤ R) :
    (((l - 1).factorial : ℝ) * (R - l).factorial) /
        (((r - 1).factorial : ℝ) * (R - r).factorial) ≤
      (2 : ℝ) ^ R := by
  have hlidx : l - 1 ≤ R - 1 := by omega
  have hridx : r - 1 ≤ R - 1 := by omega
  have hlchoose : 1 ≤ (R - 1).choose (l - 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.choose_ne_zero hlidx)
  have hrchoose : (R - 1).choose (r - 1) ≤ 2 ^ (R - 1) :=
    Nat.choose_le_two_pow (R - 1) (r - 1)
  have hlfac := Nat.choose_mul_factorial_mul_factorial hlidx
  have hrfac := Nat.choose_mul_factorial_mul_factorial hridx
  have hlsub : (R - 1) - (l - 1) = R - l := by omega
  have hrsub : (R - 1) - (r - 1) = R - r := by omega
  rw [hlsub] at hlfac
  rw [hrsub] at hrfac
  have hden : (0 : ℝ) < ((r - 1).factorial : ℝ) * (R - r).factorial := by
    positivity
  rw [div_le_iff₀ hden]
  have hcast_l :
      ((R - 1).factorial : ℝ) =
        ((R - 1).choose (l - 1) : ℕ) *
          (((l - 1).factorial : ℝ) * (R - l).factorial) := by
    norm_cast
    simpa [mul_assoc] using hlfac.symm
  have hcast_r :
      ((R - 1).factorial : ℝ) =
        ((R - 1).choose (r - 1) : ℕ) *
          (((r - 1).factorial : ℝ) * (R - r).factorial) := by
    norm_cast
    simpa [mul_assoc] using hrfac.symm
  let A : ℝ := ((l - 1).factorial : ℝ) * (R - l).factorial
  let B : ℝ := ((r - 1).factorial : ℝ) * (R - r).factorial
  let CL : ℝ := (R - 1).choose (l - 1)
  let CR : ℝ := (R - 1).choose (r - 1)
  have hCL : 1 ≤ CL := by
    dsimp only [CL]
    exact_mod_cast hlchoose
  have hCR : CR ≤ (2 : ℝ) ^ (R - 1) := by
    dsimp only [CR]
    exact_mod_cast hrchoose
  have hAB : CL * A = CR * B := by
    dsimp only [A, B, CL, CR]
    linarith [hcast_l, hcast_r]
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hstep : A ≤ (2 : ℝ) ^ (R - 1) * B := by
    calc
      A ≤ CL * A := by nlinarith
      _ = CR * B := hAB
      _ ≤ (2 : ℝ) ^ (R - 1) * B := by gcongr
  calc
    A ≤ (2 : ℝ) ^ (R - 1) * B := hstep
    _ ≤ (2 : ℝ) ^ R * B := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)) hB

/-- The factorial ratio belonging to the deleted multiples is also merely
exponential.  The extra factor `M` is absorbed by `M ≤ 2^M`. -/
theorem deleted_factorial_pair_div_le_two_pow
    {M s t : ℕ} (hs : s ≤ M) (ht : 1 ≤ t) (htM : t ≤ M) :
    ((s.factorial : ℝ) * (M - s).factorial) /
        (((t - 1).factorial : ℝ) * (M - t).factorial) ≤
      (2 : ℝ) ^ (2 * M) := by
  have htidx : t - 1 ≤ M - 1 := by omega
  have hschoose : 1 ≤ M.choose s :=
    Nat.one_le_iff_ne_zero.mpr (Nat.choose_ne_zero hs)
  have htchoose : (M - 1).choose (t - 1) ≤ 2 ^ (M - 1) :=
    Nat.choose_le_two_pow (M - 1) (t - 1)
  have hsfac := Nat.choose_mul_factorial_mul_factorial hs
  have htfac := Nat.choose_mul_factorial_mul_factorial htidx
  have htsub : (M - 1) - (t - 1) = M - t := by omega
  rw [htsub] at htfac
  have hM : 0 < M := by omega
  have hMfac : M.factorial = M * (M - 1).factorial := by
    exact (Nat.mul_factorial_pred hM.ne').symm
  have hden : (0 : ℝ) < ((t - 1).factorial : ℝ) * (M - t).factorial := by
    positivity
  rw [div_le_iff₀ hden]
  let A : ℝ := (s.factorial : ℝ) * (M - s).factorial
  let B : ℝ := ((t - 1).factorial : ℝ) * (M - t).factorial
  let CS : ℝ := M.choose s
  let CT : ℝ := (M - 1).choose (t - 1)
  have hCS : 1 ≤ CS := by
    dsimp only [CS]
    exact_mod_cast hschoose
  have hCT : CT ≤ (2 : ℝ) ^ (M - 1) := by
    dsimp only [CT]
    exact_mod_cast htchoose
  have hsCast : (M.factorial : ℝ) = CS * A := by
    dsimp only [A, CS]
    norm_cast
    simpa [mul_assoc] using hsfac.symm
  have htCast : ((M - 1).factorial : ℝ) = CT * B := by
    dsimp only [B, CT]
    norm_cast
    simpa [mul_assoc] using htfac.symm
  have hrelation : CS * A = (M : ℝ) * CT * B := by
    calc
      CS * A = (M.factorial : ℝ) := hsCast.symm
      _ = (M : ℝ) * ((M - 1).factorial : ℝ) := by exact_mod_cast hMfac
      _ = (M : ℝ) * (CT * B) := by rw [htCast]
      _ = (M : ℝ) * CT * B := by ring
  have hMpow : (M : ℝ) ≤ (2 : ℝ) ^ M := by
    exact_mod_cast nat_le_two_pow M
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  calc
    A ≤ CS * A := by nlinarith
    _ = (M : ℝ) * CT * B := hrelation
    _ ≤ ((2 : ℝ) ^ M * (2 : ℝ) ^ (M - 1)) * B := by gcongr
    _ ≤ (2 : ℝ) ^ (2 * M) * B := by
      gcongr
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)

end Erdos240.BakerCoprimeFactorialCancellation

#print axioms Erdos240.BakerCoprimeFactorialCancellation.factorial_pair_div_factorial_pair_le_two_pow
#print axioms Erdos240.BakerCoprimeFactorialCancellation.deleted_factorial_pair_div_le_two_pow
