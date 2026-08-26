/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The measurable capped-window statistic on the central dyadic bins.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.ColoredConcentration
import ErdosProblems.Erdos521.WindowScales
import ErdosProblems.Erdos521.MainBins

namespace Erdos521

open MeasureTheory
open scoped BigOperators

noncomputable def cappedWindowStatistic (ε : ℕ → ℝ) (n k q T : ℕ) (g : ℕ → ℝ) (N : ℕ) : ℝ :=
  min (windowGridSignChanges ε (dyadicCoefficientWindow n k q) g N : ℝ) (T : ℝ)

theorem measurable_cappedWindowStatistic (n k q T : ℕ) (g : ℕ → ℝ) (N : ℕ) :
    Measurable (fun ε ↦ cappedWindowStatistic ε n k q T g N) :=
  ((measurable_of_countable (fun m : ℕ ↦ (m : ℝ))).comp
    (measurable_windowGridSignChanges (dyadicCoefficientWindow n k q) g N)).min measurable_const

theorem cappedWindowStatistic_bounds (ε : ℕ → ℝ) (n k q T : ℕ) (g : ℕ → ℝ) (N : ℕ) :
    0 ≤ cappedWindowStatistic ε n k q T g N ∧ cappedWindowStatistic ε n k q T g N ≤ T :=
  ⟨le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _), min_le_right _ _⟩

theorem integrable_cappedWindowStatistic (n k q T : ℕ) (g : ℕ → ℝ) (N : ℕ) :
    Integrable (fun ε ↦ cappedWindowStatistic ε n k q T g N) sequenceLaw := by
  have hLp : MemLp (fun ε ↦ cappedWindowStatistic ε n k q T g N) 1 sequenceLaw := by
    apply MemLp.of_bound (measurable_cappedWindowStatistic n k q T g N).aestronglyMeasurable (T : ℝ)
    filter_upwards [] with ε
    have h := cappedWindowStatistic_bounds ε n k q T g N
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  exact hLp.integrable le_rfl

noncomputable def cappedCentralSum (ε : ℕ → ℝ) (j : ℕ) (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) : ℝ :=
  ∑ k ∈ mainBinSet j, cappedWindowStatistic ε (2 ^ j) k (windowWidthScale j) (windowCapScale j) (g k) (N k)

theorem measurable_cappedCentralSum (j : ℕ) (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) :
    Measurable (fun ε ↦ cappedCentralSum ε j g N) :=
  Finset.measurable_sum _ (fun _k _ ↦ measurable_cappedWindowStatistic _ _ _ _ _ _)

theorem integrable_cappedCentralSum (j : ℕ) (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) :
    Integrable (fun ε ↦ cappedCentralSum ε j g N) sequenceLaw :=
  integrable_finsetSum _ (fun _k _ ↦ integrable_cappedWindowStatistic _ _ _ _ _ _)

theorem cappedCentralSum_centering (ε : ℕ → ℝ) (j : ℕ) (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) :
    (∑ k ∈ mainBinSet j,
      (cappedWindowStatistic ε (2 ^ j) k (windowWidthScale j) (windowCapScale j) (g k) (N k) -
        ∫ ζ, cappedWindowStatistic ζ (2 ^ j) k (windowWidthScale j) (windowCapScale j) (g k) (N k) ∂sequenceLaw)) =
      cappedCentralSum ε j g N - ∫ ζ, cappedCentralSum ζ j g N ∂sequenceLaw := by
  unfold cappedCentralSum
  rw [integral_finsetSum _ (fun k _ ↦ integrable_cappedWindowStatistic _ _ _ _ _ _), Finset.sum_sub_distrib]

theorem cappedCentralSum_concentration (j : ℕ) (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) {t : ℝ} (ht : 0 ≤ t) :
    sequenceLaw.real {ε | t ≤ |cappedCentralSum ε j g N - ∫ ζ, cappedCentralSum ζ j g N ∂sequenceLaw|} ≤
      2 * Real.exp (-t ^ 2 / (2 * ((2 * windowWidthScale j + 1 : ℕ) : ℝ) ^ 2 *
        ((mainBinSet j).card : ℝ) * ((windowCapScale j : ℝ) / 2) ^ 2)) := by
  have h := colored_window_grid_concentration (2 ^ j) (windowWidthScale j) (windowCapScale j) g N (mainBinSet j) ht
  change sequenceLaw.real {ε | t ≤ |∑ k ∈ mainBinSet j,
    (cappedWindowStatistic ε (2 ^ j) k (windowWidthScale j) (windowCapScale j) (g k) (N k) -
      ∫ ζ, cappedWindowStatistic ζ (2 ^ j) k (windowWidthScale j) (windowCapScale j) (g k) (N k) ∂sequenceLaw)|} ≤ _ at h
  simpa only [cappedCentralSum_centering] using h

end Erdos521
