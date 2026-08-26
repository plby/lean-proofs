import Mathlib

/-!
# A common-endpoint shortcut does not prove discrepancy

For each fixed endpoint `X`, color the first half negatively and the second half
positively. Every homogeneous progression stopped at that same endpoint has sum
zero or one. The coloring depends on `X`; this is not a counterexample to the
Erdős discrepancy theorem.
-/

open scoped BigOperators
open Finset

namespace Erdos67.CommonEndpointCounterexample

def cutoffSign (X n : ℕ) : ℤ := if 2 * n ≤ X then -1 else 1

theorem cutoffSign_values (X n : ℕ) : cutoffSign X n = -1 ∨ cutoffSign X n = 1 := by
  unfold cutoffSign
  split_ifs <;> simp

theorem half_block_sum (m : ℕ) :
    (∑ k ∈ range m, if 2 * (k + 1) ≤ m then (-1 : ℤ) else 1) = (m % 2 : ℕ) := by
  have hhalf : m / 2 ≤ m := Nat.div_le_self m 2
  have hsplit := Finset.sum_range_add
    (fun k ↦ if 2 * (k + 1) ≤ m then (-1 : ℤ) else 1) (m / 2) (m - m / 2)
  rw [Nat.add_sub_of_le hhalf] at hsplit
  have hfirst : (∑ k ∈ range (m / 2), if 2 * (k + 1) ≤ m then (-1 : ℤ) else 1) =
      -(m / 2 : ℕ) := by
    calc
      (∑ k ∈ range (m / 2), if 2 * (k + 1) ≤ m then (-1 : ℤ) else 1) =
          ∑ _ ∈ range (m / 2), (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        rw [if_pos (by omega)]
      _ = -(m / 2 : ℕ) := by simp
  have hsecond :
      (∑ k ∈ range (m - m / 2), if 2 * (m / 2 + k + 1) ≤ m then (-1 : ℤ) else 1) =
        (m - m / 2 : ℕ) := by
    calc
      (∑ k ∈ range (m - m / 2), if 2 * (m / 2 + k + 1) ≤ m then (-1 : ℤ) else 1) =
          ∑ _ ∈ range (m - m / 2), (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [if_neg (by omega)]
      _ = (m - m / 2 : ℕ) := by simp
  rw [hsplit, hfirst, hsecond, Nat.cast_sub hhalf]
  have hmod : ((m % 2 : ℕ) : ℤ) + 2 * ((m / 2 : ℕ) : ℤ) = (m : ℤ) := by
    exact_mod_cast Nat.mod_add_div m 2
  linarith

/-- Every progression stopped at one prescribed endpoint has sum zero or one. -/
theorem common_endpoint_sum (X d : ℕ) (hd : 0 < d) :
    (∑ k ∈ range (X / d), cutoffSign X ((k + 1) * d)) = ((X / d) % 2 : ℕ) := by
  have heq (k : ℕ) : 2 * ((k + 1) * d) ≤ X ↔ 2 * (k + 1) ≤ X / d := by
    rw [Nat.le_div_iff_mul_le hd, Nat.mul_assoc]
  simp only [cutoffSign, heq]
  exact half_block_sum (X / d)

theorem abs_common_endpoint_sum_le_one (X d : ℕ) (hd : 0 < d) :
    |∑ k ∈ range (X / d), cutoffSign X ((k + 1) * d)| ≤ 1 := by
  rw [common_endpoint_sum X d hd, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (by omega : (X / d) % 2 ≤ 1)

/-- Quantifiers matter: the coloring can depend on the common endpoint. -/
theorem common_endpoint_counterexample (X : ℕ) :
    ∃ f : ℕ → ℤ, (∀ n, f n = -1 ∨ f n = 1) ∧
      ∀ d, 0 < d → |∑ k ∈ range (X / d), f ((k + 1) * d)| ≤ 1 :=
  ⟨cutoffSign X, cutoffSign_values X, abs_common_endpoint_sum_le_one X⟩

end Erdos67.CommonEndpointCounterexample
