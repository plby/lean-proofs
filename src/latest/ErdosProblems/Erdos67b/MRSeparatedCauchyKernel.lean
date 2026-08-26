import ErdosProblems.Erdos67b.MRSparseIntegerMean
import Mathlib.Analysis.PSeries

/-! # Uniform Cauchy-kernel rows on separated finite frequency sets -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrSum_inv_sq_separated_positive_le {ι : Type*} (S : Finset ι) (d : ι → ℝ)
    (hlo : ∀ i ∈ S, 1 ≤ d i)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |d i - d j|) :
    (∑ i ∈ S, 1 / (d i) ^ 2) ≤ 2 := by
  classical
  let q : ι → ℕ := fun i ↦ ⌊d i⌋₊
  have hinj : ∀ i ∈ S, ∀ j ∈ S, q i = q j → i = j := by
    intro i hi j hj heq
    by_contra hne
    have hgap := hsep i hi j hj hne
    have hil : (q i : ℝ) ≤ d i := Nat.floor_le (by linarith [hlo i hi])
    have hjl : (q j : ℝ) ≤ d j := Nat.floor_le (by linarith [hlo j hj])
    have hiu : d i < (q i : ℝ) + 1 := Nat.lt_floor_add_one _
    have hju : d j < (q j : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [heq] at hil hiu
    have hh : |d i - d j| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
    linarith
  have hsub : S.image q ⊆ Finset.Ioo 0 (S.sup q + 1) := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hn
    exact Finset.mem_Ioo.2 ⟨Nat.floor_pos.2 (hlo i hi), Nat.lt_succ_of_le (Finset.le_sup hi)⟩
  calc
    _ ≤ ∑ i ∈ S, 1 / (q i : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hq : (0 : ℝ) < q i := by exact_mod_cast Nat.floor_pos.2 (hlo i hi)
      apply one_div_le_one_div_of_le (sq_pos_of_pos hq)
      exact pow_le_pow_left₀ hq.le (Nat.floor_le (by linarith [hlo i hi])) _
    _ = ∑ n ∈ S.image q, 1 / (n : ℝ) ^ 2 :=
      (Finset.sum_image (f := fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) hinj).symm
    _ ≤ ∑ n ∈ Finset.Ioo 0 (S.sup q + 1), 1 / (n : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
    _ ≤ 2 := by simpa only [one_div, Nat.cast_zero, zero_add, div_one] using
        (sum_Ioo_inv_sq_le (α := ℝ) 0 (S.sup q + 1))

theorem mrSeparated_inv_sq_gap_sum_le (S : Finset ℝ)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    {s : ℝ} (hs : s ∈ S) :
    (∑ t ∈ S.erase s, 1 / |t - s| ^ 2) ≤ 4 := by
  classical
  let A := (S.erase s).filter (fun t ↦ s < t)
  let B := (S.erase s).filter (fun t ↦ ¬s < t)
  have hApos (t : ℝ) (ht : t ∈ A) : s < t := (Finset.mem_filter.1 ht).2
  have hBneg (t : ℝ) (ht : t ∈ B) : t < s := by
    obtain ⟨herase, hle⟩ := Finset.mem_filter.1 ht
    exact lt_of_le_of_ne (le_of_not_gt hle) (Finset.mem_erase.1 herase).1
  have hmem (t : ℝ) (ht : t ∈ S.erase s) : t ∈ S := (Finset.mem_erase.1 ht).2
  have hgap (t : ℝ) (ht : t ∈ S.erase s) : 1 ≤ |t - s| :=
    hsep t (hmem t ht) s hs (Finset.mem_erase.1 ht).1
  have hA := mrSum_inv_sq_separated_positive_le A (fun t ↦ t - s)
    (fun t ht ↦ by
      simpa only [abs_of_pos (sub_pos.2 (hApos t ht))] using hgap t (Finset.mem_filter.1 ht).1)
    (fun t ht u hu hne ↦ by
      have hh := hsep t (hmem t (Finset.mem_filter.1 ht).1)
        u (hmem u (Finset.mem_filter.1 hu).1) hne
      simpa only [sub_sub_sub_cancel_right] using hh)
  have hB := mrSum_inv_sq_separated_positive_le B (fun t ↦ s - t)
    (fun t ht ↦ by
      have hh := hgap t (Finset.mem_filter.1 ht).1
      rw [abs_of_neg (sub_neg.2 (hBneg t ht))] at hh
      linarith)
    (fun t ht u hu hne ↦ by
      have hh := hsep u (hmem u (Finset.mem_filter.1 hu).1)
        t (hmem t (Finset.mem_filter.1 ht).1) hne.symm
      simpa only [sub_sub_sub_cancel_left] using hh)
  have hsplit : (∑ t ∈ S.erase s, 1 / |t - s| ^ 2) =
      (∑ t ∈ A, 1 / (t - s) ^ 2) + ∑ t ∈ B, 1 / (s - t) ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (S.erase s) (fun t ↦ s < t)]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro t ht
      rw [abs_of_pos (sub_pos.2 (hApos t ht))]
    · apply Finset.sum_congr rfl
      intro t ht
      rw [abs_of_neg (sub_neg.2 (hBneg t ht)), neg_sub]
  rw [hsplit]
  linarith

theorem mrSeparated_cauchy_kernel_sum_le (S : Finset ℝ)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    {s : ℝ} (hs : s ∈ S) :
    (∑ t ∈ S, 1 / (1 + (t - s) ^ 2)) ≤ 5 := by
  classical
  have hgap := mrSeparated_inv_sq_gap_sum_le S hsep hs
  have hterm : (∑ t ∈ S.erase s, 1 / (1 + (t - s) ^ 2)) ≤
      ∑ t ∈ S.erase s, 1 / |t - s| ^ 2 := by
    apply Finset.sum_le_sum
    intro t ht
    have hts := hsep t (Finset.mem_erase.1 ht).2 s hs (Finset.mem_erase.1 ht).1
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq_abs]
    linarith
  rw [← Finset.sum_erase_add _ _ hs]
  simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, div_one]
  linarith

end

end Erdos67b
