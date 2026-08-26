/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Exact distinct-root partitions when the shared grid points are not roots.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.IntervalPartition

namespace Erdos521

open scoped BigOperators

theorem intervalRootCount_Ico_identity (ε : ℕ → ℝ) (n a b : ℕ) (hab : a ≤ b)
    (g : ℕ → ℝ) (hg : Monotone g) :
    (∑ i ∈ Finset.Ico a b, intervalRootCount ε n (g i) (g (i + 1))) + intervalRootCount ε n (g a) (g a) =
      intervalRootCount ε n (g a) (g b) + ∑ i ∈ Finset.Ico a b, intervalRootCount ε n (g i) (g i) := by
  have h := intervalRootCount_grid_identity ε n (fun i ↦ g (a + i))
    (fun i j hij ↦ hg (Nat.add_le_add_left hij a)) (b - a)
  simpa only [Finset.sum_Ico_eq_sum_range, Nat.add_zero, Nat.add_sub_of_le hab, Nat.add_assoc] using h

theorem intervalRootCount_Ico_eq_sum_of_nonzero_grid (ε : ℕ → ℝ) (n : ℕ) (hε₀ : ε 0 ≠ 0)
    (a b : ℕ) (hab : a < b) (g : ℕ → ℝ) (hg : Monotone g)
    (hzero : ∀ i ∈ Finset.Ico a b, powerSum ε (n + 1) (g i) ≠ 0) :
    intervalRootCount ε n (g a) (g b) = ∑ i ∈ Finset.Ico a b, intervalRootCount ε n (g i) (g (i + 1)) := by
  have hsingle (i : ℕ) (hi : i ∈ Finset.Ico a b) : intervalRootCount ε n (g i) (g i) = 0 := by
    rw [intervalRootCount_singleton ε n hε₀, if_neg (hzero i hi)]
  have hstart := hsingle a (Finset.mem_Ico.mpr ⟨le_rfl, hab⟩)
  have hsum : (∑ i ∈ Finset.Ico a b, intervalRootCount ε n (g i) (g i)) = 0 := Finset.sum_eq_zero hsingle
  have h := intervalRootCount_Ico_identity ε n a b hab.le g hg
  rw [hstart, hsum, add_zero, add_zero] at h
  exact h.symm

end Erdos521
