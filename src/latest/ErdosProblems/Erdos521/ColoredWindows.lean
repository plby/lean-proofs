/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Independence within a residue class of dyadic coefficient windows.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.DyadicWindows
import ErdosProblems.Erdos521.WindowGridIndependence

namespace Erdos521

open MeasureTheory ProbabilityTheory

def coloredCoefficientWindow (n q c k : ℕ) : Finset ℕ :=
  if k % (2 * q + 1) = c then dyadicCoefficientWindow n k q else ∅

theorem coloredCoefficientWindow_pairwise_disjoint (n q c : ℕ) :
    Pairwise (fun i j ↦ Disjoint (coloredCoefficientWindow n q c i) (coloredCoefficientWindow n q c j)) := by
  intro i j hij
  by_cases hi : i % (2 * q + 1) = c
  · by_cases hj : j % (2 * q + 1) = c
    · simp only [coloredCoefficientWindow, if_pos hi, if_pos hj]
      exact dyadicCoefficientWindow_disjoint_same_color n q hij (hi.trans hj.symm)
    · simp [coloredCoefficientWindow, hi, hj]
  · simp [coloredCoefficientWindow, hi]

theorem windowGridSignChanges_empty (ε : ℕ → ℝ) (g : ℕ → ℝ) (N : ℕ) :
    windowGridSignChanges ε ∅ g N = 0 := by
  simp [windowGridSignChanges, windowPowerSum, signChange]

theorem independent_colored_window_counts (n q c T : ℕ) (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) :
    iIndepFun (fun k (ε : ℕ → ℝ) ↦ if k % (2 * q + 1) = c then
      (min (windowGridSignChanges ε (dyadicCoefficientWindow n k q) (g k) (N k)) T : ℝ) else 0)
      sequenceLaw := by
  have h := independent_capped_window_grid (coloredCoefficientWindow n q c)
    (coloredCoefficientWindow_pairwise_disjoint n q c) g N (fun _ ↦ T)
  convert h using 1
  funext k ε
  by_cases hk : k % (2 * q + 1) = c
  · simp only [coloredCoefficientWindow, if_pos hk]
  · simp only [coloredCoefficientWindow, if_neg hk, windowGridSignChanges_empty, Nat.cast_zero,
      min_eq_left (Nat.cast_nonneg T)]

end Erdos521
