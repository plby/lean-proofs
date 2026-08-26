/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Expected root-count error of a finite sign grid.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.NatComparisonError
import ErdosProblems.Erdos521.SignGridExpectation
import ErdosProblems.Erdos521.IntervalMoments

namespace Erdos521

open MeasureTheory

theorem root_grid_expectation_error (n N : ℕ) (g : ℕ → ℝ) (hg : Monotone g) {R : ℝ} (hR : 0 < R) :
    0 ≤ (∫ ε, (intervalRootCount ε n (g 0) (g N) : ℝ) ∂sequenceLaw) -
      (∫ ε, (gridSignChanges ε n g N : ℝ) ∂sequenceLaw) ∧
    (∫ ε, (intervalRootCount ε n (g 0) (g N) : ℝ) ∂sequenceLaw) -
      (∫ ε, (gridSignChanges ε n g N : ℝ) ∂sequenceLaw) ≤
        R * sequenceLaw.real {ε | intervalRootCount ε n (g 0) (g N) ≠ gridSignChanges ε n g N} +
          (∫ ε, (intervalRootCount ε n (g 0) (g N) : ℝ) ^ 8 ∂sequenceLaw) / R ^ 7 := by
  apply integral_nat_comparison_error sequenceLaw
    (intervalRootCount_aemeasurable n (g 0) (g N)) (gridSignChanges_aemeasurable n g N) n N
    (fun ε ↦ intervalRootCount_le ε n (g 0) (g N)) (fun ε ↦ gridSignChanges_le ε n g N) _ hR
  filter_upwards [ae_sequence_signs] with ε hε
  have hε₀ : ε 0 ≠ 0 := by rcases hε 0 with h | h <;> simp [h]
  exact gridSignChanges_le_intervalRootCount ε n hε₀ g hg N

end Erdos521
