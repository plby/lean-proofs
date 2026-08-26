import Mathlib

/-!
# Reciprocal-square tails from a linear prefix mean

A finite dyadic decomposition turns a uniform nonnegative prefix bound
into an inverse-length tail estimate. No convergence assumption is used.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

/-- One doubling block, using only the upper prefix mean. -/
theorem sum_Ico_div_sq_le_double_prefix
    {a : ℕ → ℝ} {C : ℝ} (ha : ∀ n, 0 ≤ a n)
    (hmean : ∀ N, (∑ n ∈ Finset.Icc 1 N, a n) ≤ C * N)
    {X : ℕ} (hX : 0 < X) :
    (∑ n ∈ Finset.Ico X (2 * X), a n / (n : ℝ) ^ 2) ≤ 2 * C / X := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hmass : (∑ n ∈ Finset.Ico X (2 * X), a n) ≤ C * (2 * X) := by
    have hm := hmean (2 * X)
    push_cast at hm
    apply le_trans ?_ hm
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hn
      exact Finset.mem_Icc.mpr ⟨hX.trans_le hlo, hhi.le⟩
    · intro n _ _
      exact ha n
  calc
    _ ≤ ∑ n ∈ Finset.Ico X (2 * X), a n / (X : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply div_le_div_of_nonneg_left (ha n) (sq_pos_of_pos hXr)
      have hnX : (X : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
      exact pow_le_pow_left₀ hXr.le hnX 2
    _ = (∑ n ∈ Finset.Ico X (2 * X), a n) / (X : ℝ) ^ 2 :=
      (Finset.sum_div _ _ _).symm
    _ ≤ (C * (2 * X)) / (X : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hmass (sq_nonneg _)
    _ = 2 * C / X := by field_simp

/-- Finitely many dyadic blocks retain the full geometric saving. -/
theorem sum_Ico_div_sq_le_dyadic_geometric
    {a : ℕ → ℝ} {C : ℝ} (ha : ∀ n, 0 ≤ a n)
    (hmean : ∀ N, (∑ n ∈ Finset.Icc 1 N, a n) ≤ C * N)
    {X : ℕ} (hX : 0 < X) (k : ℕ) :
    (∑ n ∈ Finset.Ico X (2 ^ k * X), a n / (n : ℝ) ^ 2) ≤
      (2 * C / X) * ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    have hmid : X ≤ 2 ^ k * X := by nlinarith
    have hpos : 0 < 2 ^ k * X := by positivity
    have hstep := sum_Ico_div_sq_le_double_prefix ha hmean hpos
    have hlast : 2 ^ (k + 1) * X = 2 * (2 ^ k * X) := by rw [pow_succ]; ring
    rw [hlast, ← Finset.sum_Ico_consecutive
      (fun n : ℕ ↦ a n / (n : ℝ) ^ 2) hmid (by omega)]
    have hgeo : 2 * C / ((2 ^ k * X : ℕ) : ℝ) =
        (2 * C / X) * (1 / 2 : ℝ) ^ k := by
      push_cast
      rw [div_pow]
      simp only [one_pow]
      ring
    rw [hgeo] at hstep
    rw [Finset.sum_range_succ, mul_add]
    exact add_le_add ih hstep

/-- Every finite reciprocal-square tail has an inverse lower-endpoint
bound under a uniform linear prefix mean. -/
theorem sum_Icc_div_sq_le_four_of_prefix
    {a : ℕ → ℝ} {C : ℝ} (ha : ∀ n, 0 ≤ a n) (hC : 0 ≤ C)
    (hmean : ∀ N, (∑ n ∈ Finset.Icc 1 N, a n) ≤ C * N)
    {X : ℕ} (hX : 0 < X) (N : ℕ) :
    (∑ n ∈ Finset.Icc X N, a n / (n : ℝ) ^ 2) ≤ 4 * C / X := by
  have hNpow : N < 2 ^ N := Nat.lt_two_pow_self
  have hpowmul : 2 ^ N ≤ 2 ^ N * X := by nlinarith
  have hsubset : Finset.Icc X N ⊆ Finset.Ico X (2 ^ N * X) := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Ico.mpr ⟨hlo, hhi.trans_lt (hNpow.trans_le hpowmul)⟩
  have hgeom : (∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j) ≤ 2 := by
    have hs := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    have hb := Summable.sum_le_tsum (s := Finset.range N)
      (fun j _ ↦ by positivity : ∀ j ∉ Finset.range N, 0 ≤ (1 / 2 : ℝ) ^ j) hs.summable
    rw [hs.tsum_eq] at hb
    norm_num at hb ⊢
    exact hb
  calc
    _ ≤ ∑ n ∈ Finset.Ico X (2 ^ N * X), a n / (n : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _ ↦ div_nonneg (ha n) (sq_nonneg _))
    _ ≤ (2 * C / X) * ∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j :=
      sum_Ico_div_sq_le_dyadic_geometric ha hmean hX N
    _ ≤ (2 * C / X) * 2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 4 * C / X := by ring

end Erdos67b
