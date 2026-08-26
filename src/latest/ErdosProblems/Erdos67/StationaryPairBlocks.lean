import ErdosProblems.Erdos67.StationaryAbelComparison

/-! # Pairing consecutive indices in harmonic sums -/

open scoped BigOperators
open Finset

namespace Erdos67.StationaryModel

def pairBlock (a : ℕ → ℝ) (n : ℕ) : ℝ := a (2 * n + 1) + a (2 * n + 2)

theorem pairBlock_prefix (a : ℕ → ℝ) (ha0 : a 0 = 0) (N : ℕ) :
    (∑ n ∈ range N, pairBlock a n) = ∑ p ∈ range (2 * N + 1), a p := by
  induction N with
  | zero => simp [ha0]
  | succ N ih =>
    conv_rhs =>
      rw [show 2 * (N + 1) + 1 = (2 * N + 1) + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Finset.sum_range_succ, ih]
    simp only [pairBlock]
    ring

theorem pairBlock_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    0 ≤ pairBlock a n := add_nonneg (ha _) (ha _)

theorem summable_pairBlock_harmonic (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ a n / (n : ℝ))) :
    Summable (fun n ↦ pairBlock a n / (n + 1 : ℕ)) := by
  have hodd := hs.comp_injective (i := fun n : ℕ ↦ 2 * n + 1)
    (by intro m n h; change 2 * m + 1 = 2 * n + 1 at h; omega)
  have heven := hs.comp_injective (i := fun n : ℕ ↦ 2 * n + 2)
    (by intro m n h; change 2 * m + 2 = 2 * n + 2 at h; omega)
  apply ((hodd.add heven).mul_left 2).of_nonneg_of_le
    (fun n ↦ div_nonneg (pairBlock_nonneg a ha n) (Nat.cast_nonneg _))
  intro n
  simp only [Function.comp_apply, pairBlock, add_div, mul_add]
  apply add_le_add
  · rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    push_cast
    nlinarith [ha (2 * n + 1)]
  · rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    push_cast
    nlinarith

theorem summable_harmonic_of_pairBlock (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ pairBlock a n / (n + 1 : ℕ))) :
    Summable (fun n ↦ a n / (n : ℝ)) := by
  apply summable_of_sum_range_le (fun n ↦ div_nonneg (ha n) (Nat.cast_nonneg _))
    (c := ∑' n, pairBlock a n / (n + 1 : ℕ))
  intro N
  calc
    (∑ n ∈ range N, a n / (n : ℝ)) ≤ ∑ n ∈ range (2 * N + 1), a n / (n : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
        (fun n _ _ ↦ div_nonneg (ha n) (Nat.cast_nonneg _))
    _ = ∑ n ∈ range N, pairBlock (fun p ↦ a p / (p : ℝ)) n :=
      (pairBlock_prefix _ (by simp) N).symm
    _ ≤ ∑ n ∈ range N, pairBlock a n / (n + 1 : ℕ) := by
      apply sum_le_sum
      intro n _
      simp only [pairBlock, add_div]
      apply add_le_add
      · exact div_le_div_of_nonneg_left (ha _) (by positivity) (by push_cast; linarith)
      · exact div_le_div_of_nonneg_left (ha _) (by positivity) (by push_cast; linarith)
    _ ≤ _ := hs.sum_le_tsum _ (fun n _ ↦ div_nonneg (pairBlock_nonneg a ha n) (Nat.cast_nonneg _))

end Erdos67.StationaryModel
