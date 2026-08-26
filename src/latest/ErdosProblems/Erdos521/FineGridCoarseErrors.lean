/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform fourth-power probability bounds for the original fine-grid errors.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.FineGridRootError
import ErdosProblems.Erdos521.FineErrorPowers

namespace Erdos521

open MeasureTheory Filter

theorem eventually_fineGrid_root_error_four :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j,
      sequenceLaw.real {ε | intervalRootCount ε (2 ^ j) (dyadicPoint k) (dyadicPoint (k + 1)) ≠
        gridSignChanges ε (2 ^ j) (dyadicFineGrid j k) (fineGridLength j)} ≤
        (3 * fineGridSmallBallConstant + 97) * (j : ℝ) ^ (-4 : ℝ) := by
  filter_upwards [eventually_fineGrid_root_disagreement, eventually_dyadic_inverse_le_four, eventually_ge_atTop 1]
    with j hj hdegree hj₁
  intro k hk
  have hj₀ : 0 < j := by omega
  have h := hj k hk
  have heq : (3 * fineGridSmallBallConstant + 96) * (fineGridLength j : ℝ) * fineGridThreshold j =
      (3 * fineGridSmallBallConstant + 96) * (j : ℝ) ^ (-6 : ℝ) := by
    rw [mul_assoc, fineGrid_length_mul_threshold hj₀]
  rw [heq] at h
  have hp : (j : ℝ) ^ (-6 : ℝ) ≤ (j : ℝ) ^ (-4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj₁) (by norm_num)
  have hK : 0 ≤ 3 * fineGridSmallBallConstant + 96 := by have := fineGridSmallBallConstant_pos; positivity
  have hmul := mul_le_mul_of_nonneg_left hp hK
  nlinarith

theorem eventually_mainBin_zero_error_four :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j, ∀ x ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1)),
      sequenceLaw.real {ε | powerSum ε (2 ^ j + 1) x = 0} ≤
        fineGridSmallBallConstant * (j : ℝ) ^ (-4 : ℝ) := by
  filter_upwards [eventually_mainBin_fine_zero_probability, eventually_ge_atTop 1] with j hj hj₁
  intro k hk x hx
  exact (hj k hk x hx).trans (mul_le_mul_of_nonneg_left (fineGridThreshold_le_four hj₁)
    fineGridSmallBallConstant_pos.le)

end Erdos521
