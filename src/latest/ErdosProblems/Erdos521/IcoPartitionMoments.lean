/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Root-count moment bounds for a finite interval of grid indices.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.PartitionMoments

namespace Erdos521

open MeasureTheory
open scoped BigOperators

theorem integral_intervalRootCount_Ico_pow_le (n a b p : ℕ) (hab : a < b) (hp : 1 ≤ p)
    (g : ℕ → ℝ) (hg : Monotone g) {B : ℝ}
    (hB : ∀ i ∈ Finset.Ico a b,
      (∫ ε, (intervalRootCount ε n (g i) (g (i + 1)) : ℝ) ^ p ∂sequenceLaw) ≤ B) :
    (∫ ε, (intervalRootCount ε n (g a) (g b) : ℝ) ^ p ∂sequenceLaw) ≤ ((b - a : ℕ) : ℝ) ^ p * B := by
  have hcell (i : ℕ) (hi : i ∈ Finset.range (b - a)) :
      (∫ ε, (intervalRootCount ε n (g (a + i)) (g (a + (i + 1))) : ℝ) ^ p ∂sequenceLaw) ≤ B := by
    have hi' : a + i ∈ Finset.Ico a b := by
      have h := Finset.mem_range.mp hi
      simp only [Finset.mem_Ico]
      omega
    simpa only [Nat.add_assoc] using hB (a + i) hi'
  have h := integral_intervalRootCount_partition_pow_le n (b - a) p (by omega) hp
    (fun i ↦ g (a + i)) (fun i j hij ↦ hg (Nat.add_le_add_left hij a)) hcell
  simpa only [Nat.add_zero, Nat.add_sub_of_le hab.le] using h

end Erdos521
