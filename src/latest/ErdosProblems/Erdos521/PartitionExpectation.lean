/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Expected root counts under a finite interval partition.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.IntervalPartition

namespace Erdos521

open MeasureTheory
open scoped BigOperators

theorem intervalRootCount_integrable (n : ℕ) (a b : ℝ) :
    Integrable (fun ε ↦ (intervalRootCount ε n a b : ℝ)) sequenceLaw := by
  simpa only [pow_one] using intervalRootCount_pow_integrable n 1 a b

theorem integral_intervalRootCount_grid_identity (n N : ℕ) (g : ℕ → ℝ) (hg : Monotone g) :
    (∑ i ∈ Finset.range N, ∫ ε, (intervalRootCount ε n (g i) (g (i + 1)) : ℝ) ∂sequenceLaw) +
        sequenceLaw.real {ε | powerSum ε (n + 1) (g 0) = 0} =
      (∫ ε, (intervalRootCount ε n (g 0) (g N) : ℝ) ∂sequenceLaw) +
        ∑ i ∈ Finset.range N, sequenceLaw.real {ε | powerSum ε (n + 1) (g i) = 0} := by
  have hpoint : (fun ε ↦ (∑ i ∈ Finset.range N, (intervalRootCount ε n (g i) (g (i + 1)) : ℝ)) +
      (intervalRootCount ε n (g 0) (g 0) : ℝ)) =
      (fun ε ↦ (intervalRootCount ε n (g 0) (g N) : ℝ) +
        ∑ i ∈ Finset.range N, (intervalRootCount ε n (g i) (g i) : ℝ)) := by
    funext ε
    exact_mod_cast intervalRootCount_grid_identity ε n g hg N
  have h := congrArg (fun f : (ℕ → ℝ) → ℝ ↦ ∫ ε, f ε ∂sequenceLaw) hpoint
  rw [integral_add (integrable_finsetSum _ (fun i _ ↦ intervalRootCount_integrable n _ _))
      (intervalRootCount_integrable n _ _),
    integral_add (intervalRootCount_integrable n _ _)
      (integrable_finsetSum _ (fun i _ ↦ intervalRootCount_integrable n _ _)),
    integral_finsetSum _ (fun i _ ↦ intervalRootCount_integrable n _ _),
    integral_finsetSum _ (fun i _ ↦ intervalRootCount_integrable n _ _)] at h
  simpa only [integral_intervalRootCount_singleton] using h

end Erdos521
