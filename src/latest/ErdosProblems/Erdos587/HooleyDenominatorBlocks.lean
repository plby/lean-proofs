import ErdosProblems.Erdos587.HooleyDyadicShell
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Denominator blocks and their finite geometric costs -/

open scoped BigOperators

namespace Erdos587

lemma exists_delta_dyadic_scale {K : ℝ} (hK : 1 ≤ K) :
    ∃ D : ℕ, K ≤ 2 ^ D ∧ (2 : ℝ) ^ D ≤ 2 * K := by
  obtain ⟨d, hlo, hupp⟩ := exists_nat_pow_near hK (by norm_num : (1 : ℝ) < 2)
  refine ⟨d + 1, hupp.le, ?_⟩
  rw [pow_succ]
  linarith

lemma delta_dyadic_denominator_bounds {b : ℕ} (hb : 0 < b) :
    (2 : ℝ) ^ Nat.clog 2 b / 2 < b ∧ (b : ℝ) ≤ 2 ^ Nat.clog 2 b := by
  refine ⟨?_, by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) b⟩
  by_cases hb1 : b = 1
  · subst b
    norm_num
  · have hb2 : 1 < b := by omega
    have hc : 0 < Nat.clog 2 b := Nat.clog_pos (by norm_num) hb2
    have h := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hb2
    have heq : Nat.clog 2 b = Nat.clog 2 b - 1 + 1 := by omega
    rw [heq, pow_succ]
    have hR : (2 : ℝ) ^ (Nat.clog 2 b - 1) < b := by exact_mod_cast h
    nlinarith

lemma delta_dyadic_denominator_index_le {b D : ℕ} (hb : (b : ℝ) ≤ 2 ^ D) :
    Nat.clog 2 b ≤ D := by
  apply Nat.clog_le_of_le_pow
  exact_mod_cast hb

lemma delta_dyadic_error_scale {K u : ℝ} {D j b : ℕ}
    (hu : 0 ≤ u) (hK : K ≤ 2 ^ D) (hj : j ≤ D)
    (hb : (2 : ℝ) ^ j ≤ 2 * b) (hub : u * b ≤ 2 * K) :
    u ≤ 2 ^ (D - j + 2) := by
  have hpow : (2 : ℝ) ^ (D - j + 2) * 2 ^ j = 4 * 2 ^ D := by
    rw [← pow_add, show D - j + 2 + j = D + 2 by omega, pow_add]
    norm_num
    ring
  apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2 ^ j)).mp
  nlinarith [mul_le_mul_of_nonneg_left hb hu]

lemma delta_sum_dyadic_mass_below (J : ℕ) {M H : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H) :
    (∑ j ∈ (Finset.range (J + 1)).filter (fun j => M * 2 ^ j ≤ H), M * 2 ^ j) ≤
      2 * H := by
  classical
  let I := (Finset.range (J + 1)).filter (fun j => M * 2 ^ j ≤ H)
  by_cases hI : I.Nonempty
  · let k := I.max' hI
    have hk : k ∈ I := Finset.max'_mem I hI
    have hIk : I ⊆ Finset.range (k + 1) := by
      intro j hj
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' I j hj))
    have hbound : M * 2 ^ k ≤ H := (Finset.mem_filter.mp hk).2
    calc
      _ ≤ ∑ j ∈ Finset.range (k + 1), M * 2 ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hIk (fun j hj hnot => by positivity)
      _ = M * (2 ^ (k + 1) - 1) := by rw [← Finset.mul_sum, delta_sum_two_pow]
      _ ≤ 2 * H := by rw [pow_succ]; nlinarith
  · have hempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    change (∑ j ∈ I, M * 2 ^ j) ≤ 2 * H
    rw [hempty, Finset.sum_empty]
    positivity

lemma delta_sum_dyadic_small_cost (J : ℕ) {M H q : ℝ}
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hq : 0 ≤ q) :
    (∑ j ∈ (Finset.range (J + 1)).filter (fun j => M * 2 ^ j ≤ H),
      (M * 2 ^ j + q) * ((J - j : ℕ) + 3)) ≤
      (2 * H + q * (J + 1)) * (J + 3) := by
  classical
  let I := (Finset.range (J + 1)).filter (fun j => M * 2 ^ j ≤ H)
  have hcost (j : ℕ) (_hj : j ∈ I) :
      (M * 2 ^ j + q) * ((J - j : ℕ) + 3) ≤ (M * 2 ^ j + q) * (J + 3) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hsub : ((J - j : ℕ) : ℝ) ≤ J := by exact_mod_cast Nat.sub_le J j
    linarith
  have hcard : (I.card : ℝ) ≤ J + 1 := by
    exact_mod_cast (Finset.card_filter_le (Finset.range (J + 1)) _).trans_eq
      (Finset.card_range (J + 1))
  calc
    _ ≤ ∑ j ∈ I, (M * 2 ^ j + q) * (J + 3) := Finset.sum_le_sum hcost
    _ = ((∑ j ∈ I, M * 2 ^ j) + I.card * q) * (J + 3) := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib]
      simp
    _ ≤ (2 * H + (J + 1) * q) * (J + 3) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact add_le_add (delta_sum_dyadic_mass_below J hM hH)
        (mul_le_mul_of_nonneg_right hcard hq)
    _ = _ := by ring

end Erdos587
