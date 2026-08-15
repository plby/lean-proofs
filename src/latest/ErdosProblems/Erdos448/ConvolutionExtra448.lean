import ErdosProblems.Erdos448.LogConvolution448

open scoped BigOperators
open Set

namespace ConvolutionExtra448

open LogConvolution448

/-- The finite `3/4` power sum needed at the middle-range endpoint. -/
lemma sum_Ioo_rpow_neg_three_quarters_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.Ioo 0 N, (j : ℝ) ^ (-(3 / 4 : ℝ))) ≤
      4 * (N : ℝ) ^ (1 / 4 : ℝ) := by
  have hsub : Finset.Ioo 0 N ⊆ Finset.Icc 1 N := by
    intro j hj
    simp only [Finset.mem_Ioo, Finset.mem_Icc] at hj ⊢
    omega
  calc
    (∑ j ∈ Finset.Ioo 0 N, (j : ℝ) ^ (-(3 / 4 : ℝ))) ≤
        ∑ j ∈ Finset.Icc 1 N, (j : ℝ) ^ (-(3 / 4 : ℝ)) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ ↦ Real.rpow_nonneg (by positivity) _)
    _ = ∑ j ∈ Finset.range N,
          ((j + 1 : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) := by
      rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      congr 2
      ring
    _ ≤ 1 + ((N : ℝ) ^ (1 - (3 / 4 : ℝ)) - 1) /
          (1 - (3 / 4 : ℝ)) :=
      sum_range_succ_rpow_neg_le (3 / 4 : ℝ) (by norm_num)
        (by norm_num) N hN
    _ ≤ 4 * (N : ℝ) ^ (1 / 4 : ℝ) := by
      have hp : 0 ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
        Real.rpow_nonneg (by positivity) _
      norm_num at hp ⊢
      linarith

/-- The dyadic-shell convolution in the middle regime.  The coarse constant
is intentional: only the exponent `N⁻¹/⁴` is used downstream. -/
lemma convolution_three_quarters_half_le_twelve (N : ℕ) (hN : 2 ≤ N) :
    (∑ j ∈ Finset.Ioo 0 N,
        (j : ℝ) ^ (-(3 / 4 : ℝ)) *
          ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      12 * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
  classical
  let S := Finset.Ioo 0 N
  let low : Finset ℕ := S.filter (fun j ↦ 2 * j ≤ N)
  let high : Finset ℕ := S.filter (fun j ↦ ¬ 2 * j ≤ N)
  have hNR : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hhalf : (0 : ℝ) < (N : ℝ) / 2 := by positivity
  have hsplit :
      (∑ j ∈ S,
          (j : ℝ) ^ (-(3 / 4 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
        (∑ j ∈ low,
          (j : ℝ) ^ (-(3 / 4 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) +
        ∑ j ∈ high,
          (j : ℝ) ^ (-(3 / 4 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    exact (Finset.sum_filter_add_sum_filter_not S (fun j ↦ 2 * j ≤ N)
      (fun j ↦ (j : ℝ) ^ (-(3 / 4 : ℝ)) *
        ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))).symm
  have hlow :
      (∑ j ∈ low,
          (j : ℝ) ^ (-(3 / 4 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        8 * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ low, (j : ℝ) ^ (-(3 / 4 : ℝ)) *
            ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjS := (Finset.mem_filter.mp hj).1
        have hjlow := (Finset.mem_filter.mp hj).2
        have hbase : (N : ℝ) / 2 ≤ ((N - j : ℕ) : ℝ) := by
          have hNat : N ≤ 2 * (N - j) := by
            have hjlt := (Finset.mem_Ioo.mp hjS).2
            omega
          apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
          exact_mod_cast (by simpa [mul_comm] using hNat)
        have hpow := Real.rpow_le_rpow_of_nonpos hhalf hbase
          (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
        exact mul_le_mul_of_nonneg_left hpow
          (Real.rpow_nonneg (by positivity) _)
      _ = ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            ∑ j ∈ low, (j : ℝ) ^ (-(3 / 4 : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            ∑ j ∈ S, (j : ℝ) ^ (-(3 / 4 : ℝ)) := by
        gcongr
        simpa [low] using Finset.filter_subset (fun j ↦ 2 * j ≤ N) S
      _ ≤ ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            (4 * (N : ℝ) ^ (1 / 4 : ℝ)) := by
        gcongr
        exact sum_Ioo_rpow_neg_three_quarters_le N (by omega)
      _ ≤ (2 * (N : ℝ) ^ (-(1 / 2 : ℝ))) *
            (4 * (N : ℝ) ^ (1 / 4 : ℝ)) := by
        gcongr
        exact half_rpow_neg_le_two_mul (N : ℝ) (1 / 2 : ℝ) hNR
          (by norm_num) (by norm_num)
      _ = 8 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) *
            (N : ℝ) ^ (1 / 4 : ℝ)) := by ring
      _ = 8 * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
        rw [← Real.rpow_add hNR]
        norm_num
  have hhigh :
      (∑ j ∈ high,
          (j : ℝ) ^ (-(3 / 4 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        4 * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ high, ((N : ℝ) / 2) ^ (-(3 / 4 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjS := (Finset.mem_filter.mp hj).1
        have hjhigh := (Finset.mem_filter.mp hj).2
        have hbase : (N : ℝ) / 2 ≤ (j : ℝ) := by
          have hNat : N ≤ 2 * j := by omega
          apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
          exact_mod_cast (by simpa [mul_comm] using hNat)
        have hpow := Real.rpow_le_rpow_of_nonpos hhalf hbase
          (by norm_num : (-(3 / 4 : ℝ)) ≤ 0)
        exact mul_le_mul_of_nonneg_right hpow
          (Real.rpow_nonneg (by positivity) _)
      _ = ((N : ℝ) / 2) ^ (-(3 / 4 : ℝ)) *
            ∑ j ∈ high, ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ ((N : ℝ) / 2) ^ (-(3 / 4 : ℝ)) *
            ∑ j ∈ S, ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        gcongr
        simpa [high] using Finset.filter_subset (fun j ↦ ¬ 2 * j ≤ N) S
      _ = ((N : ℝ) / 2) ^ (-(3 / 4 : ℝ)) *
            ∑ j ∈ S, (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
        apply congrArg (fun z : ℝ ↦ ((N : ℝ) / 2) ^ (-(3 / 4 : ℝ)) * z)
        exact sum_Ioo_reflect (fun j ↦ (j : ℝ) ^ (-(1 / 2 : ℝ))) N
      _ ≤ ((N : ℝ) / 2) ^ (-(3 / 4 : ℝ)) *
            (2 * (N : ℝ) ^ (1 / 2 : ℝ)) := by
        gcongr
        exact sum_Ioo_rpow_neg_half_le N (by omega)
      _ ≤ (2 * (N : ℝ) ^ (-(3 / 4 : ℝ))) *
            (2 * (N : ℝ) ^ (1 / 2 : ℝ)) := by
        gcongr
        exact half_rpow_neg_le_two_mul (N : ℝ) (3 / 4 : ℝ) hNR
          (by norm_num) (by norm_num)
      _ = 4 * ((N : ℝ) ^ (-(3 / 4 : ℝ)) *
            (N : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ = 4 * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
        rw [← Real.rpow_add hNR]
        norm_num
  rw [show (∑ j ∈ Finset.Ioo 0 N,
      (j : ℝ) ^ (-(3 / 4 : ℝ)) *
        ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (∑ j ∈ S, (j : ℝ) ^ (-(3 / 4 : ℝ)) *
        ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) by rfl, hsplit]
  linarith

/-- The long-range endpoint convolution is uniformly bounded. -/
lemma convolution_half_half_le_eight (N : ℕ) (hN : 2 ≤ N) :
    (∑ j ∈ Finset.Ioo 0 N,
        (j : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 8 := by
  classical
  let S := Finset.Ioo 0 N
  let low : Finset ℕ := S.filter (fun j ↦ 2 * j ≤ N)
  let high : Finset ℕ := S.filter (fun j ↦ ¬ 2 * j ≤ N)
  have hNR : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hhalf : (0 : ℝ) < (N : ℝ) / 2 := by positivity
  have hsplit :
      (∑ j ∈ S,
          (j : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
        (∑ j ∈ low,
          (j : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) +
        ∑ j ∈ high,
          (j : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    exact (Finset.sum_filter_add_sum_filter_not S (fun j ↦ 2 * j ≤ N)
      (fun j ↦ (j : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))).symm
  have hlow :
      (∑ j ∈ low,
          (j : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 4 := by
    calc
      _ ≤ ∑ j ∈ low, (j : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjS := (Finset.mem_filter.mp hj).1
        have hjlow := (Finset.mem_filter.mp hj).2
        have hbase : (N : ℝ) / 2 ≤ ((N - j : ℕ) : ℝ) := by
          have hNat : N ≤ 2 * (N - j) := by
            have hjlt := (Finset.mem_Ioo.mp hjS).2
            omega
          apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
          exact_mod_cast (by simpa [mul_comm] using hNat)
        have hpow := Real.rpow_le_rpow_of_nonpos hhalf hbase
          (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
        exact mul_le_mul_of_nonneg_left hpow
          (Real.rpow_nonneg (by positivity) _)
      _ = ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            ∑ j ∈ low, (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            ∑ j ∈ S, (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
        gcongr
        simpa [low] using Finset.filter_subset (fun j ↦ 2 * j ≤ N) S
      _ ≤ ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            (2 * (N : ℝ) ^ (1 / 2 : ℝ)) := by
        gcongr
        exact sum_Ioo_rpow_neg_half_le N (by omega)
      _ ≤ (2 * (N : ℝ) ^ (-(1 / 2 : ℝ))) *
            (2 * (N : ℝ) ^ (1 / 2 : ℝ)) := by
        gcongr
        exact half_rpow_neg_le_two_mul (N : ℝ) (1 / 2 : ℝ) hNR
          (by norm_num) (by norm_num)
      _ = 4 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) *
            (N : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ = 4 := by
        rw [← Real.rpow_add hNR]
        norm_num
  have hhigh :
      (∑ j ∈ high,
          (j : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 4 := by
    calc
      _ ≤ ∑ j ∈ high, ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjhigh := (Finset.mem_filter.mp hj).2
        have hbase : (N : ℝ) / 2 ≤ (j : ℝ) := by
          have hNat : N ≤ 2 * j := by omega
          apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
          exact_mod_cast (by simpa [mul_comm] using hNat)
        have hpow := Real.rpow_le_rpow_of_nonpos hhalf hbase
          (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
        exact mul_le_mul_of_nonneg_right hpow
          (Real.rpow_nonneg (by positivity) _)
      _ = ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            ∑ j ∈ high, ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            ∑ j ∈ S, ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        gcongr
        simpa [high] using Finset.filter_subset (fun j ↦ ¬ 2 * j ≤ N) S
      _ = ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            ∑ j ∈ S, (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
        apply congrArg (fun z : ℝ ↦ ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) * z)
        exact sum_Ioo_reflect (fun j ↦ (j : ℝ) ^ (-(1 / 2 : ℝ))) N
      _ ≤ ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            (2 * (N : ℝ) ^ (1 / 2 : ℝ)) := by
        gcongr
        exact sum_Ioo_rpow_neg_half_le N (by omega)
      _ ≤ (2 * (N : ℝ) ^ (-(1 / 2 : ℝ))) *
            (2 * (N : ℝ) ^ (1 / 2 : ℝ)) := by
        gcongr
        exact half_rpow_neg_le_two_mul (N : ℝ) (1 / 2 : ℝ) hNR
          (by norm_num) (by norm_num)
      _ = 4 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) *
            (N : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ = 4 := by
        rw [← Real.rpow_add hNR]
        norm_num
  rw [show (∑ j ∈ Finset.Ioo 0 N,
      (j : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (∑ j ∈ S, (j : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) by rfl, hsplit]
  linarith

end ConvolutionExtra448
