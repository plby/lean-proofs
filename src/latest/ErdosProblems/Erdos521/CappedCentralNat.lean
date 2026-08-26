/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The natural-valued capped statistic and its deterministic bounds.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.CappedCentralSum
import ErdosProblems.Erdos521.WindowCapBounds

namespace Erdos521

open MeasureTheory
open scoped BigOperators

noncomputable def cappedCentralNatSum (ε : ℕ → ℝ) (j : ℕ) (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) : ℕ :=
  ∑ k ∈ mainBinSet j, min (windowGridSignChanges ε
    (dyadicCoefficientWindow (2 ^ j) k (windowWidthScale j)) (g k) (N k)) (windowCapScale j)

theorem measurable_cappedCentralNatSum (j : ℕ) (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) :
    Measurable (fun ε ↦ cappedCentralNatSum ε j g N) := by
  unfold cappedCentralNatSum
  exact Finset.measurable_sum _ (fun k _ ↦
    (measurable_windowGridSignChanges (dyadicCoefficientWindow (2 ^ j) k (windowWidthScale j)) (g k) (N k)).min
      measurable_const)

theorem cappedCentralNatSum_le (ε : ℕ → ℝ) (j : ℕ) (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) :
    cappedCentralNatSum ε j g N ≤ j * windowCapScale j := by
  unfold cappedCentralNatSum
  calc
    _ ≤ ∑ _k ∈ mainBinSet j, windowCapScale j := Finset.sum_le_sum (fun _ _ ↦ min_le_right _ _)
    _ = (mainBinSet j).card * windowCapScale j := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (mainBinSet_card_le j)

theorem cappedCentralNatSum_cast (ε : ℕ → ℝ) (j : ℕ) (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) :
    (cappedCentralNatSum ε j g N : ℝ) = cappedCentralSum ε j g N := by
  simp only [cappedCentralNatSum, cappedCentralSum, cappedWindowStatistic, Nat.cast_sum, Nat.cast_min]

theorem cappedCentralNatSum_pow_integrable (j p : ℕ) (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) :
    Integrable (fun ε ↦ (cappedCentralNatSum ε j g N : ℝ) ^ p) sequenceLaw :=
  bounded_nat_pow_integrable sequenceLaw (measurable_cappedCentralNatSum j g N).aemeasurable
    (j * windowCapScale j) p (fun ε ↦ cappedCentralNatSum_le ε j g N)

theorem cappedCentralNatSum_real_le {j : ℕ} (hj : 1 ≤ j) (ε : ℕ → ℝ) (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) :
    (cappedCentralNatSum ε j g N : ℝ) ≤ 2 * (j : ℝ) ^ 2 := by
  have hT : (windowCapScale j : ℝ) ≤ 2 * (j : ℝ) := by exact_mod_cast windowCapScale_le_twice_index hj
  calc
    _ ≤ (j : ℝ) * (windowCapScale j : ℝ) := by exact_mod_cast cappedCentralNatSum_le ε j g N
    _ ≤ (j : ℝ) * (2 * (j : ℝ)) := mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg j)
    _ = _ := by ring

theorem integral_cappedCentralNatSum_pow_le {j : ℕ} (hj : 1 ≤ j) (p : ℕ)
    (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) :
    (∫ ε, (cappedCentralNatSum ε j g N : ℝ) ^ p ∂sequenceLaw) ≤ (2 * (j : ℝ) ^ 2) ^ p := by
  have h := integral_mono (cappedCentralNatSum_pow_integrable j p g N)
    (integrable_const ((2 * (j : ℝ) ^ 2) ^ p))
    (fun ε ↦ pow_le_pow_left₀ (Nat.cast_nonneg _) (cappedCentralNatSum_real_le hj ε g N) p)
  simpa using h

end Erdos521
