import Mathlib

/-! # Square-summable arithmetic progressions for divisor Fourier coefficients -/

namespace Erdos421

theorem arithmetic_inverse_square_step {d Y : ℝ} (hd : 0 < d) (hY : 0 < Y) (n : ℕ) :
    1 / (d + Y * ((n : ℝ) + 1)) ^ 2 ≤
      1 / (Y * (d + Y * n)) - 1 / (Y * (d + Y * ((n : ℝ) + 1))) := by
  have h0 : 0 < d + Y * n := by positivity
  have h1 : 0 < d + Y * ((n : ℝ) + 1) := by positivity
  have he : 1 / (Y * (d + Y * n)) - 1 / (Y * (d + Y * ((n : ℝ) + 1))) =
      1 / ((d + Y * n) * (d + Y * ((n : ℝ) + 1))) := by field_simp; ring
  rw [he]
  apply one_div_le_one_div_of_le (mul_pos h0 h1)
  nlinarith

theorem sum_arithmetic_inverse_squares_le {d Y : ℝ} (hd : 0 < d) (hY : 0 < Y)
    (N : ℕ) : (∑ n ∈ Finset.range N, 1 / (d + Y * ((n : ℝ) + 1)) ^ 2) ≤
      1 / (Y * d) := by
  have hstrong : ∀ N : ℕ, (∑ n ∈ Finset.range N,
      1 / (d + Y * ((n : ℝ) + 1)) ^ 2) ≤ 1 / (Y * d) - 1 / (Y * (d + Y * N)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      push_cast
      linarith [arithmetic_inverse_square_step hd hY N]
  exact (hstrong N).trans (sub_le_self _ (by positivity))

theorem sum_positive_arithmetic_inverse_squares_le (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) {d Y : ℝ} (hd : 0 < d) (hY : 0 < Y) :
    (∑ n ∈ S, 1 / (d + Y * n) ^ 2) ≤ 1 / (Y * d) := by
  classical
  let N := S.sup id
  have hsub : S ⊆ Finset.Icc 1 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨hS n hn, Finset.le_sup (f := id) hn⟩
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, 1 / (d + Y * n) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
    _ = ∑ n ∈ Finset.range N, 1 / (d + Y * ((n : ℝ) + 1)) ^ 2 := by
      symm
      apply Finset.sum_bij (fun n _ ↦ n + 1)
      · intro n hn
        have hn' := Finset.mem_range.mp hn
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro n hn m hm he
        omega
      · intro n hn
        obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
        exact ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
      · intro n hn
        simp only [Nat.cast_add, Nat.cast_one]
    _ ≤ _ := sum_arithmetic_inverse_squares_le hd hY N

end Erdos421
