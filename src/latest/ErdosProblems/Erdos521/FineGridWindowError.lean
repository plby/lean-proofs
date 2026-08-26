/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The original and truncated fine sign grids differ with a summable per-bin probability.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.MainWindowValueError
import ErdosProblems.Erdos521.FineGridSmallBall
import ErdosProblems.Erdos521.FineErrorPowers
import ErdosProblems.Erdos521.SignPerturbation
import ErdosProblems.Erdos521.WindowGrid

namespace Erdos521

open MeasureTheory Filter
open scoped BigOperators

theorem eventually_fineGrid_window_disagreement :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j,
      sequenceLaw.real {ε | gridSignChanges ε (2 ^ j) (dyadicFineGrid j k) (fineGridLength j) ≠
        windowGridSignChanges ε (dyadicCoefficientWindow (2 ^ j) k (windowWidthScale j))
          (dyadicFineGrid j k) (fineGridLength j)} ≤
        (2 * fineGridSmallBallConstant + 16) * (j : ℝ) ^ (-4 : ℝ) := by
  filter_upwards [eventually_mainBin_fine_smallBall, eventually_mainBin_window_value_error, eventually_ge_atTop 1]
    with j hsmall hwindow hj₁
  intro k hk
  have hj₀ : 0 < j := by omega
  let f := fun (ε : ℕ → ℝ) i ↦ powerSum ε (2 ^ j + 1) (dyadicFineGrid j k i)
  let w := fun (ε : ℕ → ℝ) i ↦ windowPowerSum ε
    (dyadicCoefficientWindow (2 ^ j) k (windowWidthScale j)) (dyadicFineGrid j k i)
  let t := fun i ↦ fineGridThreshold j * Real.sqrt (geometricVariance (dyadicFineGrid j k i) (2 ^ j + 1))
  have ht (i : ℕ) : 0 ≤ t i := mul_nonneg (fineGridThreshold_pos hj₀).le (Real.sqrt_nonneg _)
  have h := sign_grid_perturbation_probability sequenceLaw f w (fineGridLength j) t ht
  have hpoint (i : ℕ) (hi : i ∈ Finset.range (fineGridLength j + 1)) :
      sequenceLaw.real {ε | |f ε i| ≤ t i} + sequenceLaw.real {ε | t i ≤ |f ε i - w ε i|} ≤
        fineGridSmallBallConstant * fineGridThreshold j + 8 * (j : ℝ) ^ (-32 : ℝ) := by
    have hmem := dyadicFineGrid_mem hj₀ k (i := i) (by have := Finset.mem_range.mp hi; omega)
    exact add_le_add (hsmall k hk _ hmem) (hwindow k hk _ hmem)
  have hsum : (∑ i ∈ Finset.range (fineGridLength j + 1),
      (sequenceLaw.real {ε | |f ε i| ≤ t i} + sequenceLaw.real {ε | t i ≤ |f ε i - w ε i|})) ≤
      ((fineGridLength j : ℝ) + 1) * (fineGridSmallBallConstant * fineGridThreshold j + 8 * (j : ℝ) ^ (-32 : ℝ)) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using
      Finset.sum_le_sum hpoint
  have hfinal := h.trans (hsum.trans (fine_grid_error_sum_bound hj₁ fineGridSmallBallConstant_pos.le))
  simpa only [gridSignChanges, polynomial_eval, windowGridSignChanges, f, w] using hfinal

end Erdos521
