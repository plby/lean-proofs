import ErdosProblems.Erdos520.HarperEconomicalTruncation
import ErdosProblems.Erdos520.HarperExplicitPrefixWindows
import ErdosProblems.Erdos520.HarperWeightedAssembly

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos
namespace Problem520

/-!
# Entropy loss at the economical starts

The prefix mesh used by the positive-log recursion has a completely explicit
entropy base.  This file discharges the elementary growth bookkeeping needed
when that recursion is applied to the vertical decomposition.

For the noncentral unit shell `shell`, the height parameter is `shell + 1`
and the economical start is shifted by `clog 2 (shell + 2)`.  The resulting
entropy base is bounded by a constant depending only on the fixed analytic
start `J`, times the pre-existing local moment loss `(shell + 1)^(1/6)`.

For the central dyadic band of depth `depth`, the height parameter can be
taken to be one.  At the economical start `J + depth`, the entropy base is
exactly affine in `depth`, and hence is bounded by a fixed constant times
`depth + 1`.
-/

/-- Fixed entropy constant for the noncentral shell decomposition. -/
noncomputable def harperShellEntropyLossConstant (J : ℕ) : ℝ :=
  Real.log 4 + Real.log 4097 / 2 +
    (J : ℝ) * Real.log 2 / 2 + Real.log 2 + 6

/-- The noncentral shell entropy constant is nonnegative. -/
theorem harperShellEntropyLossConstant_nonneg (J : ℕ) :
    0 ≤ harperShellEntropyLossConstant J := by
  unfold harperShellEntropyLossConstant
  positivity

/-- The dyadic ceiling contributes no more than one extra factor of two.
This logarithmic form avoids introducing any reciprocal of `log 2`. -/
private theorem natCast_clog_two_mul_log_two_le (n : ℕ) (hn : 2 ≤ n) :
    (Nat.clog 2 n : ℝ) * Real.log 2 ≤
      Real.log 2 + Real.log (n : ℝ) := by
  have hclog : 0 < Nat.clog 2 n :=
    Nat.clog_pos (by norm_num) (by omega)
  have hpred : 2 ^ (Nat.clog 2 n).pred < n :=
    Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hpowNat : 2 ^ Nat.clog 2 n ≤ 2 * n := by
    rw [← Nat.succ_pred_eq_of_pos hclog, pow_succ]
    omega
  have hpowReal :
      (2 : ℝ) ^ Nat.clog 2 n ≤ 2 * (n : ℝ) := by
    exact_mod_cast hpowNat
  have hlog := Real.log_le_log
    (by positivity : 0 < (2 : ℝ) ^ Nat.clog 2 n) hpowReal
  rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at hlog
  exact hlog

/-- The height coefficient for shell `shell` is at most `4097 (shell+1)`. -/
private theorem harperExplicitPrefixEntropyCoefficient_shell_le
    (shell : ℕ) :
    harperExplicitPrefixEntropyCoefficient (shell + 1) ≤
      4097 * (shell + 1) := by
  unfold harperExplicitPrefixEntropyCoefficient
  omega

/-- The logarithm of the shell coefficient splits into a fixed constant and
one copy of `log (shell+1)`. -/
private theorem log_harperExplicitPrefixEntropyCoefficient_shell_le
    (shell : ℕ) :
    Real.log (harperExplicitPrefixEntropyCoefficient (shell + 1) : ℝ) ≤
      Real.log 4097 + Real.log ((shell + 1 : ℕ) : ℝ) := by
  have hcoefPos :
      0 < (harperExplicitPrefixEntropyCoefficient (shell + 1) : ℝ) := by
    exact_mod_cast (show 0 < harperExplicitPrefixEntropyCoefficient
      (shell + 1) by
        unfold harperExplicitPrefixEntropyCoefficient
        omega)
  have hcoef :
      (harperExplicitPrefixEntropyCoefficient (shell + 1) : ℝ) ≤
        4097 * (((shell + 1 : ℕ) : ℝ)) := by
    exact_mod_cast harperExplicitPrefixEntropyCoefficient_shell_le shell
  calc
    Real.log (harperExplicitPrefixEntropyCoefficient (shell + 1) : ℝ) ≤
        Real.log (4097 * (((shell + 1 : ℕ) : ℝ))) :=
      Real.log_le_log hcoefPos hcoef
    _ = Real.log 4097 + Real.log ((shell + 1 : ℕ) : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity)]

/-- The logarithmic start shift is controlled by the same single shell
logarithm, with two harmless factors of two. -/
private theorem economicalShellStart_log_shift_le (shell : ℕ) :
    (Nat.clog 2 (shell + 2) : ℝ) * Real.log 2 ≤
      2 * Real.log 2 + Real.log ((shell + 1 : ℕ) : ℝ) := by
  have hclog := natCast_clog_two_mul_log_two_le (shell + 2) (by omega)
  have hcast :
      (((shell + 2 : ℕ) : ℝ)) ≤
        2 * (((shell + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show shell + 2 ≤ 2 * (shell + 1) by omega)
  have hlog :
      Real.log (((shell + 2 : ℕ) : ℝ)) ≤
        Real.log (2 * (((shell + 1 : ℕ) : ℝ))) :=
    Real.log_le_log (by positivity) hcast
  rw [Real.log_mul (by norm_num) (by positivity)] at hlog
  linarith

/-- A single shell logarithm is absorbed by the local sixth-root moment
loss already present in the weighted assembly. -/
private theorem log_shellScale_le_six_mul_localMomentLoss (shell : ℕ) :
    Real.log ((shell + 1 : ℕ) : ℝ) ≤
      6 * harperLocalMomentLoss shell := by
  have h := Real.log_natCast_le_rpow_div (shell + 1)
    (show (0 : ℝ) < 1 / 6 by norm_num)
  change Real.log ((shell + 1 : ℕ) : ℝ) ≤
    (((shell + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 6) / ((1 : ℝ) / 6) at h
  unfold harperLocalMomentLoss harperShellScale
  calc
    Real.log ((shell + 1 : ℕ) : ℝ) ≤
        (((shell + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 6) / ((1 : ℝ) / 6) := h
    _ = 6 * (((shell + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 6) := by ring

/-- The local sixth-root loss is at least one. -/
private theorem one_le_harperLocalMomentLoss (shell : ℕ) :
    1 ≤ harperLocalMomentLoss shell := by
  unfold harperLocalMomentLoss harperShellScale
  exact Real.one_le_rpow (by norm_num) (by norm_num)

/-- At the economical start of a noncentral unit shell, the complete
explicit-prefix entropy base is absorbed by the shell's existing local
moment loss.  In particular, the prefix union bound introduces no new
growth class in the vertical weighted assembly. -/
theorem
    harperExplicitPrefixEntropyBase_economicalShellStart_le_localMomentLoss
    (J shell : ℕ) :
    harperExplicitPrefixEntropyBase
        (harperEconomicalShellStart J shell) (shell + 1) ≤
      harperShellEntropyLossConstant J * harperLocalMomentLoss shell := by
  have hcoef :=
    log_harperExplicitPrefixEntropyCoefficient_shell_le shell
  have hshift := economicalShellStart_log_shift_le shell
  have hlog := log_shellScale_le_six_mul_localMomentLoss shell
  have hloss := one_le_harperLocalMomentLoss shell
  push_cast at hcoef hshift hlog
  let A : ℝ := Real.log 4 + Real.log 4097 / 2 +
    (J : ℝ) * Real.log 2 / 2 + Real.log 2
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  calc
    harperExplicitPrefixEntropyBase
        (harperEconomicalShellStart J shell) (shell + 1) ≤
        A + Real.log ((shell : ℝ) + 1) := by
      unfold harperExplicitPrefixEntropyBase harperEconomicalShellStart
        harperEconomicalStart
      push_cast
      dsimp [A]
      linear_combination (1 / 2 : ℝ) * hcoef + (1 / 2 : ℝ) * hshift
    _ ≤ A + 6 * harperLocalMomentLoss shell := by
      linarith
    _ ≤ (A + 6) * harperLocalMomentLoss shell := by
      nlinarith [mul_nonneg hA (sub_nonneg.mpr hloss)]
    _ = harperShellEntropyLossConstant J *
        harperLocalMomentLoss shell := by
      unfold harperShellEntropyLossConstant
      dsimp [A]

/-- Fixed affine intercept for the central dyadic-band entropy. -/
noncomputable def harperCentralEntropyLinearConstant (J : ℕ) : ℝ :=
  Real.log 4 + Real.log 4097 / 2 +
    (J : ℝ) * Real.log 2 / 2

theorem harperCentralEntropyLinearConstant_nonneg (J : ℕ) :
    0 ≤ harperCentralEntropyLinearConstant J := by
  unfold harperCentralEntropyLinearConstant
  positivity

/-- With height cutoff one, the central-band prefix entropy at the economical
start is exactly affine in the dyadic depth. -/
theorem harperExplicitPrefixEntropyBase_economicalCentralStart_eq_linear
    (J depth : ℕ) :
    harperExplicitPrefixEntropyBase
        (harperEconomicalCentralStart J depth) 1 =
      harperCentralEntropyLinearConstant J +
        (depth : ℝ) * Real.log 2 / 2 := by
  unfold harperExplicitPrefixEntropyBase harperEconomicalCentralStart
    harperEconomicalStart harperCentralEntropyLinearConstant
    harperExplicitPrefixEntropyCoefficient
  push_cast
  ring

/-- A convenient polynomial envelope for summing the shrinking central
bands.  The growth is in fact only linear. -/
theorem harperExplicitPrefixEntropyBase_economicalCentralStart_le_depth
    (J depth : ℕ) :
    harperExplicitPrefixEntropyBase
        (harperEconomicalCentralStart J depth) 1 ≤
      (harperCentralEntropyLinearConstant J + Real.log 2 / 2) *
        ((depth : ℝ) + 1) := by
  rw [harperExplicitPrefixEntropyBase_economicalCentralStart_eq_linear]
  have hC := harperCentralEntropyLinearConstant_nonneg J
  have hlog : 0 ≤ Real.log 2 / 2 := by positivity
  have hdepth : 0 ≤ (depth : ℝ) := by positivity
  nlinarith [mul_nonneg hC hdepth]

end Problem520
end Erdos
