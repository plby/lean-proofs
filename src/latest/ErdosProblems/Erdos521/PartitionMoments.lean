/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Moment bounds for root counts assembled from a finite interval partition.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.PartitionExpectation
import Mathlib.Analysis.MeanInequalities

namespace Erdos521

open MeasureTheory
open scoped BigOperators

theorem intervalRootCount_grid_le_sum (ε : ℕ → ℝ) (n : ℕ) (g : ℕ → ℝ) (hg : Monotone g)
    (N : ℕ) (hN : 1 ≤ N) :
    intervalRootCount ε n (g 0) (g N) ≤
      ∑ i ∈ Finset.range N, intervalRootCount ε n (g i) (g (i + 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  induction k with
  | zero => simp
  | succ k ih =>
    have h := intervalRootCount_split ε n (hg (Nat.zero_le (k + 1))) (hg (Nat.le_succ (k + 1)))
    simp only [Nat.succ_eq_add_one, Finset.sum_range_succ] at ih h ⊢
    omega

theorem nat_pow_sum_le_card (S : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ i ∈ S, 0 ≤ f i)
    (p : ℕ) (hp : 1 ≤ p) :
    (∑ i ∈ S, f i) ^ p ≤ (S.card : ℝ) ^ (p - 1) * ∑ i ∈ S, (f i) ^ p := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S (f := f)
    (show (1 : ℝ) ≤ (p : ℝ) by exact_mod_cast hp) hf
  have hcast : (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hp]; norm_num
  simpa only [hcast, Real.rpow_natCast] using h

theorem integral_intervalRootCount_partition_pow_le (n N p : ℕ) (hN : 1 ≤ N) (hp : 1 ≤ p)
    (g : ℕ → ℝ) (hg : Monotone g) {B : ℝ}
    (hB : ∀ i ∈ Finset.range N,
      (∫ ε, (intervalRootCount ε n (g i) (g (i + 1)) : ℝ) ^ p ∂sequenceLaw) ≤ B) :
    (∫ ε, (intervalRootCount ε n (g 0) (g N) : ℝ) ^ p ∂sequenceLaw) ≤ (N : ℝ) ^ p * B := by
  have hpoint (ε : ℕ → ℝ) : (intervalRootCount ε n (g 0) (g N) : ℝ) ^ p ≤
      (N : ℝ) ^ (p - 1) * ∑ i ∈ Finset.range N, (intervalRootCount ε n (g i) (g (i + 1)) : ℝ) ^ p := by
    apply le_trans (pow_le_pow_left₀ (Nat.cast_nonneg _)
      (show (intervalRootCount ε n (g 0) (g N) : ℝ) ≤
        ∑ i ∈ Finset.range N, (intervalRootCount ε n (g i) (g (i + 1)) : ℝ) by
        exact_mod_cast intervalRootCount_grid_le_sum ε n g hg N hN) p)
    simpa only [Finset.card_range] using nat_pow_sum_le_card (Finset.range N)
      (fun i ↦ (intervalRootCount ε n (g i) (g (i + 1)) : ℝ)) (fun _ _ ↦ Nat.cast_nonneg _) p hp
  have h := integral_mono (intervalRootCount_pow_integrable n p _ _)
    ((integrable_finsetSum _ (fun i _ ↦ intervalRootCount_pow_integrable n p _ _)).const_mul
      ((N : ℝ) ^ (p - 1))) hpoint
  rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦ intervalRootCount_pow_integrable n p _ _)] at h
  apply h.trans
  calc
    (N : ℝ) ^ (p - 1) * (∑ i ∈ Finset.range N,
        ∫ ε, (intervalRootCount ε n (g i) (g (i + 1)) : ℝ) ^ p ∂sequenceLaw) ≤
        (N : ℝ) ^ (p - 1) * (N * B) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using Finset.sum_le_sum hB
    _ = (N : ℝ) ^ p * B := by rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp]

end Erdos521
