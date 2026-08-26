import ErdosProblems.Erdos421.IntegerReciprocalSquares

/-! # Uniform reciprocal-square tails for integer Fourier modes -/

namespace Erdos421

def integerTailShift (H : ℕ) (n : ℤ) : ℤ := if 0 < n then n - H else n + H

theorem integerTailShift_properties {H : ℕ} {n : ℤ} (hn : (H : ℤ) < |n|) :
    integerTailShift H n ≠ 0 ∧ |n| = H + |integerTailShift H n| := by
  by_cases hpos : 0 < n
  · rw [integerTailShift, if_pos hpos, abs_of_pos hpos] at *
    have hs : 0 < n - (H : ℤ) := by omega
    rw [abs_of_pos hs]
    exact ⟨hs.ne', by ring⟩
  · have hneg : n < 0 := by
      rw [abs_of_nonpos (by omega)] at hn
      omega
    rw [integerTailShift, if_neg hpos, abs_of_neg hneg] at *
    have hs : n + (H : ℤ) < 0 := by omega
    rw [abs_of_neg hs]
    exact ⟨hs.ne, by ring⟩

theorem integerTailShift_injective (H : ℕ) :
    Set.InjOn (integerTailShift H) {n : ℤ | (H : ℤ) < |n|} := by
  intro n hn m hm he
  change (H : ℤ) < |n| at hn
  change (H : ℤ) < |m| at hm
  by_cases hnpos : 0 < n <;> by_cases hmpos : 0 < m
  · simp only [integerTailShift, if_pos hnpos, if_pos hmpos] at he
    omega
  · simp only [integerTailShift, if_pos hnpos, if_neg hmpos] at he
    rw [abs_of_pos hnpos] at hn
    rw [abs_of_nonpos (by omega)] at hm
    omega
  · simp only [integerTailShift, if_neg hnpos, if_pos hmpos] at he
    rw [abs_of_nonpos (by omega)] at hn
    rw [abs_of_pos hmpos] at hm
    omega
  · simp only [integerTailShift, if_neg hnpos, if_neg hmpos] at he
    omega

theorem sum_integer_inverse_square_tail (S : Finset ℤ) {H : ℕ} (hH : 0 < H)
    (hS : ∀ n ∈ S, (H : ℤ) < |n|) :
    (∑ n ∈ S, 1 / (n : ℝ) ^ 2) ≤ 2 / (H : ℝ) := by
  classical
  have hinj : Set.InjOn (integerTailShift H) (↑S : Set ℤ) :=
    (integerTailShift_injective H).mono hS
  have hT : ∀ n ∈ S.image (integerTailShift H), n ≠ 0 := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    exact (integerTailShift_properties (hS m hm)).1
  have he (n : ℤ) (hn : n ∈ S) : |(n : ℝ)| = (H : ℝ) + |(integerTailShift H n : ℝ)| := by
    exact_mod_cast (integerTailShift_properties (hS n hn)).2
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hb := sum_integer_arithmetic_inverse_squares_le (S.image (integerTailShift H))
    hT hHR (by norm_num : (0 : ℝ) < 1)
  rw [Finset.sum_image hinj] at hb
  simp only [one_mul] at hb
  calc
    _ = ∑ n ∈ S, 1 / ((H : ℝ) + |(integerTailShift H n : ℝ)|) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← he n hn, sq_abs]
    _ ≤ _ := hb

theorem tsum_integer_inverse_square_tail {H : ℕ} (hH : 0 < H) :
    (∑' n : ℤ, if (H : ℤ) < |n| then 1 / (n : ℝ) ^ 2 else 0) ≤ 2 / (H : ℝ) := by
  apply Real.tsum_le_of_sum_le (fun _ ↦ by split_ifs <;> positivity)
  intro S
  rw [← Finset.sum_filter]
  exact sum_integer_inverse_square_tail _ hH (fun n hn ↦ (Finset.mem_filter.mp hn).2)

theorem integer_tail_series_norm_le (f : ℤ → ℂ) (hf : Summable f) {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ n : ℤ, n ≠ 0 → ‖f n‖ ≤ D / (n : ℝ) ^ 2)
    {H : ℕ} (hH : 0 < H) :
    ‖∑' n : {n : ℤ // (H : ℤ) < |n|}, f n‖ ≤ 2 * D / H := by
  have hs := hf.subtype (fun n : ℤ ↦ (H : ℤ) < |n|)
  apply le_of_tendsto hs.hasSum.norm
  apply Filter.Eventually.of_forall
  intro S
  have hS : ∀ n ∈ S.image Subtype.val, (H : ℤ) < |n| := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    exact m.property
  have hinj : Set.InjOn Subtype.val (↑S : Set {n : ℤ // (H : ℤ) < |n|}) :=
    Subtype.val_injective.injOn
  have hb := sum_integer_inverse_square_tail (S.image Subtype.val) hH hS
  rw [Finset.sum_image hinj] at hb
  calc
    _ ≤ ∑ n ∈ S, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, D / (n.val : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply hbound
      intro he
      have h := n.property
      rw [he, abs_zero] at h
      omega
    _ = D * ∑ n ∈ S, 1 / (n.val : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ D * (2 / (H : ℝ)) := mul_le_mul_of_nonneg_left hb hD
    _ = _ := by ring

end Erdos421
