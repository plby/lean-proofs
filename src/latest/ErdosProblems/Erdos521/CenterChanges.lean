/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Simultaneous control of polynomial values as the degree varies.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.Maximal

namespace Erdos521

open MeasureTheory
open scoped BigOperators

def tailWeight (x : ℝ) (n i : ℕ) : ℝ := if n < i then x ^ i else 0

theorem sum_range_tail {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n N : ℕ) :
    (∑ i ∈ Finset.range N, if n < i then f i else 0) =
      ∑ i ∈ Finset.Ico (n + 1) N, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

theorem weightedPartialSum_tailWeight (x : ℝ) (n m : ℕ) (hnm : n ≤ m) (ε : ℕ → ℝ) :
    weightedPartialSum (tailWeight x n) m ε =
      powerSum ε (m + 1) x - powerSum ε (n + 1) x := by
  simp only [weightedPartialSum, weightedIncrement, tailWeight, ite_mul, zero_mul]
  rw [sum_range_tail, powerSum, powerSum,
    ← Finset.sum_Ico_eq_sub (fun i ↦ ε i * x ^ i) (Nat.add_le_add_right hnm 1)]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem sum_tailWeight_sq (x : ℝ) (n N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), (tailWeight x n i) ^ 2) =
      x ^ (2 * (n + 1)) * geometricVariance x (N - n) := by
  simp only [tailWeight, ite_pow, zero_pow (by norm_num : 2 ≠ 0)]
  rw [sum_range_tail]
  have h := sum_tail_square x 1 (n + 1) (N + 1)
  simpa only [one_mul, ← pow_mul, Nat.mul_comm, Nat.add_sub_add_right] using h

theorem powerSum_changes_probability (n N : ℕ) (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    sequenceLaw.real {ε | ∃ m, n ≤ m ∧ m ≤ N ∧
      δ ≤ |powerSum ε (m + 1) x - powerSum ε (n + 1) x|} ≤
      x ^ (2 * (n + 1)) * geometricVariance x (N - n) / δ ^ 2 := by
  have hsub : {ε | ∃ m, n ≤ m ∧ m ≤ N ∧
      δ ≤ |powerSum ε (m + 1) x - powerSum ε (n + 1) x|} ⊆
      {ε | δ ^ 2 ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ (weightedPartialSum (tailWeight x n) k ε) ^ 2)} := by
    intro ε hε
    obtain ⟨m, hnm, hmN, hdiff⟩ := hε
    have hsq : δ ^ 2 ≤ (weightedPartialSum (tailWeight x n) m ε) ^ 2 := by
      rw [weightedPartialSum_tailWeight x n m hnm ε]
      simpa only [sq_abs] using pow_le_pow_left₀ hδ.le hdiff 2
    exact hsq.trans (Finset.le_sup' (s := Finset.range (N + 1))
      (fun k ↦ (weightedPartialSum (tailWeight x n) k ε) ^ 2)
      (Finset.mem_range.mpr (by omega)))
  apply (measureReal_mono hsub).trans
  simpa only [sum_tailWeight_sq] using weightedPartialSum_maximal (tailWeight x n) N hδ

end Erdos521
