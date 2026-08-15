import ErdosProblems.Erdos888.CoreEstimate

/-!
# Elementary series estimates for Erdős Problem 888

This file supplies the two unconditional finite-sum estimates used as the
`hseries` and `htail` inputs of `CoreEstimate.squarefreeCorePairSum_le`.
-/

open scoped BigOperators

namespace Erdos888
namespace CoreSeries

noncomputable section

/-- The logarithmic numerator divided by a square is summable.  We spell out
the elementary comparison with `n ^ (-3/2)` so that this result has no
number-theoretic dependency. -/
lemma summable_log_div_sq :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := by
  have h_log_le_n_eps : ∀ (ε : ℝ), ε > 0 → ∃ C > 0, ∀ n : ℕ, n ≥ 2 →
      Real.log n / (n : ℝ) ^ (2 : ℝ) ≤ C * (n : ℝ) ^ (ε - 2) := by
    intro ε hε_pos
    obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, ∀ n : ℕ, n ≥ 2 →
        Real.log n ≤ C * (n : ℝ) ^ ε := by
      refine ⟨1 / ε, by positivity, fun n hn ↦ ?_⟩
      have h := Real.log_le_sub_one_of_pos
        (by positivity : 0 < (n : ℝ) ^ ε)
      rw [Real.log_rpow (by positivity)] at h
      nlinarith [Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)) ε,
        mul_div_cancel₀ 1 hε_pos.ne']
    refine ⟨C, hC_pos, fun n hn ↦ ?_⟩
    rw [Real.rpow_sub (by positivity)]
    exact le_trans
      (div_le_div_of_nonneg_right (hC n hn) (by positivity))
      (by rw [div_eq_mul_inv]; ring_nf; norm_num)
  obtain ⟨C, _, hC⟩ : ∃ C > 0, ∀ n : ℕ, n ≥ 2 →
      Real.log n / (n : ℝ) ^ (2 : ℝ) ≤
        C * (n : ℝ) ^ (((2 : ℝ) - 1) / 2 - 2) :=
    h_log_le_n_eps (((2 : ℝ) - 1) / 2) (by norm_num)
  have hrpow : Summable (fun n : ℕ =>
      Real.log n / (n : ℝ) ^ (2 : ℝ)) := by
    rw [← summable_nat_add_iff 2]
    exact Summable.of_nonneg_of_le
      (fun n ↦ div_nonneg (Real.log_nonneg (by norm_cast; omega))
        (Real.rpow_nonneg (by positivity) _))
      (fun n ↦ hC _ (by omega))
      (Summable.mul_left C <| by
        simpa using summable_nat_add_iff 2 |>.2 <|
          Real.summable_nat_rpow.2 (by norm_num))
  refine hrpow.congr ?_
  intro n
  rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]

/-- Every term in the core series is nonnegative. -/
lemma coreSeriesTerm_nonneg (r : ℕ) :
    0 ≤ CoreEstimate.coreSeriesTerm r := by
  by_cases hr : r = 0
  · subst r
    simp [CoreEstimate.coreSeriesTerm, CoreEstimate.logWeight, lambda]
  · rw [CoreEstimate.coreSeriesTerm, CoreEstimate.logWeight,
      lambda_eq_one_add_log (Nat.cast_ne_zero.mpr hr)]
    exact div_nonneg (by
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr)
      linarith [Real.log_nonneg hr1]) (sq_nonneg _)

/-- The complete core series is summable. -/
theorem summable_coreSeriesTerm :
    Summable CoreEstimate.coreSeriesTerm := by
  have hone : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  have hadd := hone.add summable_log_div_sq
  refine hadd.congr ?_
  intro n
  by_cases hn : n = 0
  · subst n
    simp [CoreEstimate.coreSeriesTerm, CoreEstimate.logWeight, lambda]
  · rw [CoreEstimate.coreSeriesTerm, CoreEstimate.logWeight,
      lambda_eq_one_add_log (Nat.cast_ne_zero.mpr hn)]
    ring

/-- A fixed, finite bound for all initial core-series sums. -/
def coreSeriesBound : ℝ :=
  ∑' r : ℕ, CoreEstimate.coreSeriesTerm r

lemma coreSeriesBound_nonneg : 0 ≤ coreSeriesBound := by
  exact tsum_nonneg coreSeriesTerm_nonneg

/-- Uniform boundedness of the finite series used in Lemma 7.2. -/
theorem sum_coreSeriesTerm_Ico_le (R : ℕ) :
    (∑ r ∈ Finset.Ico 2 R, CoreEstimate.coreSeriesTerm r) ≤
      coreSeriesBound := by
  exact summable_coreSeriesTerm.sum_le_tsum _
    (fun r _ ↦ coreSeriesTerm_nonneg r)

/-- The elementary telescoping inequality
`1/n² ≤ 1/(n-1) - 1/n`. -/
lemma inv_sq_le_inv_pred_sub_inv {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) ^ 2)⁻¹ ≤ ((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpredR : (0 : ℝ) < (n - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < n - 1)
  have hnsub : (n : ℝ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (by omega : n ≠ 1)
  have heq : ((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ =
      ((n : ℝ) * (n - 1 : ℕ))⁻¹ := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    field_simp [hnR.ne', hpredR.ne', hnsub]
    ring
  rw [heq]
  refine (inv_le_inv₀ (sq_pos_of_pos hnR) (mul_pos hnR hpredR)).2 ?_
  nlinarith [show ((n - 1 : ℕ) : ℝ) ≤ n by
    exact_mod_cast (by omega : n - 1 ≤ n)]

/-- The reciprocal-square tail strictly above `L` is at most `1/L`. -/
lemma sum_Icc_succ_inv_sq_le_inv (L N : ℕ) (hL : 1 ≤ L) :
    (∑ r ∈ Finset.Icc (L + 1) N, 1 / (r : ℝ) ^ 2) ≤ 1 / (L : ℝ) := by
  by_cases hLN : L < N
  · have hrewrite :
        (∑ r ∈ Finset.Icc (L + 1) N, 1 / (r : ℝ) ^ 2) =
          ∑ i ∈ Finset.range (N - L),
            1 / ((L + i + 1 : ℕ) : ℝ) ^ 2 := by
      have hsets : Finset.Icc (L + 1) N = Finset.Ico (L + 1) (N + 1) := by
        ext r
        simp
      rw [hsets, Finset.sum_Ico_eq_sum_range]
      have hlen : N + 1 - (L + 1) = N - L := by omega
      rw [hlen]
      apply Finset.sum_congr rfl
      intro i hi
      congr 3
      omega
    rw [hrewrite]
    calc
      (∑ i ∈ Finset.range (N - L),
          1 / ((L + i + 1 : ℕ) : ℝ) ^ 2) ≤
          ∑ i ∈ Finset.range (N - L),
            (1 / ((L + i : ℕ) : ℝ) -
              1 / ((L + i + 1 : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hpred : L + i + 1 - 1 = L + i := by omega
        simpa only [one_div, hpred] using
          (inv_sq_le_inv_pred_sub_inv (n := L + i + 1) (by omega))
      _ = 1 / (L : ℝ) - 1 / (N : ℝ) := by
        change (Finset.range (N - L)).sum (fun i ↦
          (fun j : ℕ ↦ 1 / ((L + j : ℕ) : ℝ)) i -
            (fun j : ℕ ↦ 1 / ((L + j : ℕ) : ℝ)) (i + 1)) = _
        rw [Finset.sum_range_sub']
        simp [Nat.add_sub_of_le hLN.le]
      _ ≤ 1 / (L : ℝ) := sub_le_self _ (by positivity)
  · have hempty : Finset.Icc (L + 1) N = ∅ := by
      rw [Finset.Icc_eq_empty]
      omega
    simp [hempty]

/-- Explicit reciprocal-square tail bound in exactly the form required by
`CoreEstimate.squarefreeCorePairSum_le`.  The absolute constant is `D = 2`.
-/
theorem sum_Icc_inv_sq_le_two_div (R N : ℕ) (hR : 2 ≤ R) :
    (∑ r ∈ Finset.Icc R N, 1 / (r : ℝ) ^ 2) ≤ 2 / (R : ℝ) := by
  have hRm1 : 1 ≤ R - 1 := by omega
  have hstart : R - 1 + 1 = R := by omega
  calc
    (∑ r ∈ Finset.Icc R N, 1 / (r : ℝ) ^ 2) =
        ∑ r ∈ Finset.Icc ((R - 1) + 1) N, 1 / (r : ℝ) ^ 2 := by
          rw [hstart]
    _ ≤ 1 / ((R - 1 : ℕ) : ℝ) :=
      sum_Icc_succ_inv_sq_le_inv (R - 1) N hRm1
    _ ≤ 2 / (R : ℝ) := by
      have hRpos : (0 : ℝ) < R := by positivity
      have hRm1pos : (0 : ℝ) < (R - 1 : ℕ) := by positivity
      rw [div_le_div_iff₀ hRm1pos hRpos]
      norm_num
      have hsubcast : ((R - 1 : ℕ) : ℝ) = (R : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ R)]
        norm_num
      rw [hsubcast]
      have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR
      linarith

end
end CoreSeries
end Erdos888
