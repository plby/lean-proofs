import ErdosProblems.Erdos421.ShortShiftAverage

/-! # Short-shift moments indexed by the positive integers -/

namespace Erdos421

theorem norm_sum_le_positive_shift_add_two (u : ℕ → ℂ) (N : ℕ)
    (hu : ∀ n < N + 1, ‖u n‖ ≤ 1) :
    ‖∑ n ∈ Finset.range N, u n‖ ≤ ‖∑ n ∈ Finset.range N, u (n + 1)‖ + 2 := by
  have h := norm_forward_shift_error_le u N 1 hu
  norm_num only [Nat.cast_one, mul_one] at h
  calc
    _ = ‖(∑ n ∈ Finset.range N, u (n + 1)) -
        ((∑ n ∈ Finset.range N, u (n + 1)) - ∑ n ∈ Finset.range N, u n)‖ := by
      congr 1
      abel
    _ ≤ ‖∑ n ∈ Finset.range N, u (n + 1)‖ +
        ‖(∑ n ∈ Finset.range N, u (n + 1)) - ∑ n ∈ Finset.range N, u n‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add le_rfl h

theorem positive_short_shift_moment_bound (u : ℕ → ℂ) (N : ℕ) {M p : ℕ}
    (hM : 0 < M) (hp : 0 < p) (hu : ∀ n < N + M + 1, ‖u n‖ ≤ 1) :
    ‖∑ n ∈ Finset.range N, u n‖ ≤
      ((N : ℝ) ^ (p - 1) *
        ∑ n ∈ Finset.range N, ‖∑ h ∈ Finset.range M, u (n + h + 1)‖ ^ p) ^ ((p : ℝ)⁻¹) / M +
          4 * M := by
  have hshift := norm_sum_le_positive_shift_add_two u N (fun n hn ↦ hu n (by omega))
  have h := short_shift_moment_bound (fun n ↦ u (n + 1)) N hM hp
    (fun n hn ↦ hu (n + 1) (by omega))
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  exact hshift.trans ((add_le_add h le_rfl).trans (by linarith))

end Erdos421
