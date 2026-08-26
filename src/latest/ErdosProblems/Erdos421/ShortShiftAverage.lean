import ErdosProblems.Erdos421.FiniteNormPower

/-! # Averaging short forward shifts with explicit endpoint errors -/

namespace Erdos421

theorem sum_range_forward_shift_sub (u : ℕ → ℂ) (N h : ℕ) :
    (∑ n ∈ Finset.range N, u (n + h)) - (∑ n ∈ Finset.range N, u n) =
      (∑ n ∈ Finset.range h, u (N + n)) - (∑ n ∈ Finset.range h, u n) := by
  have hleft := Finset.sum_range_add u h N
  have hright := Finset.sum_range_add u N h
  have hshift : (∑ n ∈ Finset.range N, u (n + h)) =
      ∑ n ∈ Finset.range N, u (h + n) := by simp only [Nat.add_comm]
  rw [hshift]
  rw [Nat.add_comm h N] at hleft
  rw [hright] at hleft
  linear_combination -hleft

theorem norm_forward_shift_error_le (u : ℕ → ℂ) (N h : ℕ)
    (hu : ∀ n < N + h, ‖u n‖ ≤ 1) :
    ‖(∑ n ∈ Finset.range N, u (n + h)) - (∑ n ∈ Finset.range N, u n)‖ ≤ 2 * (h : ℝ) := by
  have htail : ‖∑ n ∈ Finset.range h, u (N + n)‖ ≤ (h : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Finset.range h, ‖u (N + n)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range h, (1 : ℝ) :=
        Finset.sum_le_sum (fun n hn ↦ hu (N + n) (Nat.add_lt_add_left (Finset.mem_range.mp hn) N))
      _ = _ := by simp
  have hhead : ‖∑ n ∈ Finset.range h, u n‖ ≤ (h : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Finset.range h, ‖u n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range h, (1 : ℝ) :=
        Finset.sum_le_sum (fun n hn ↦ hu n (by have := Finset.mem_range.mp hn; omega))
      _ = _ := by simp
  rw [sum_range_forward_shift_sub]
  exact (norm_sub_le _ _).trans ((add_le_add htail hhead).trans_eq (two_mul _).symm)

theorem short_shift_average_mul_bound (u : ℕ → ℂ) (N M : ℕ)
    (hu : ∀ n < N + M, ‖u n‖ ≤ 1) :
    (M : ℝ) * ‖∑ n ∈ Finset.range N, u n‖ ≤
      (∑ n ∈ Finset.range N, ‖∑ h ∈ Finset.range M, u (n + h)‖) + 2 * (M : ℝ) ^ 2 := by
  let A := ∑ n ∈ Finset.range N, u n
  let B := ∑ n ∈ Finset.range N, ∑ h ∈ Finset.range M, u (n + h)
  have hid : (M : ℂ) * A - B =
      ∑ h ∈ Finset.range M, (A - ∑ n ∈ Finset.range N, u (n + h)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    dsimp only [B]
    rw [Finset.sum_comm]
  have herr : ‖(M : ℂ) * A - B‖ ≤ 2 * (M : ℝ) ^ 2 := by
    rw [hid]
    calc
      _ ≤ ∑ h ∈ Finset.range M, ‖A - ∑ n ∈ Finset.range N, u (n + h)‖ := norm_sum_le _ _
      _ ≤ ∑ _h ∈ Finset.range M, 2 * (M : ℝ) := by
        apply Finset.sum_le_sum
        intro h hh
        have hhM : h < M := Finset.mem_range.mp hh
        rw [norm_sub_rev]
        exact (norm_forward_shift_error_le u N h
          (fun n hn ↦ hu n (by omega))).trans (by exact_mod_cast Nat.mul_le_mul_left 2 hhM.le)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hB : ‖B‖ ≤ ∑ n ∈ Finset.range N, ‖∑ h ∈ Finset.range M, u (n + h)‖ := norm_sum_le _ _
  calc
    _ = ‖(M : ℂ) * A‖ := by rw [norm_mul, Complex.norm_natCast]
    _ = ‖B + ((M : ℂ) * A - B)‖ := by congr 1; ring
    _ ≤ ‖B‖ + ‖(M : ℂ) * A - B‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hB herr

theorem short_shift_average_bound (u : ℕ → ℂ) (N : ℕ) {M : ℕ} (hM : 0 < M)
    (hu : ∀ n < N + M, ‖u n‖ ≤ 1) :
    ‖∑ n ∈ Finset.range N, u n‖ ≤
      (∑ n ∈ Finset.range N, ‖∑ h ∈ Finset.range M, u (n + h)‖) / M + 2 * M := by
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have h := short_shift_average_mul_bound u N M hu
  calc
    _ ≤ ((∑ n ∈ Finset.range N, ‖∑ h ∈ Finset.range M, u (n + h)‖) +
        2 * (M : ℝ) ^ 2) / M :=
      (le_div_iff₀ hMR).mpr (by simpa only [mul_comm] using h)
    _ = _ := by
      field_simp

theorem sum_norm_le_moment_root {X : Type*} (S : Finset X) (f : X → ℂ)
    {p : ℕ} (hp : 0 < p) :
    (∑ x ∈ S, ‖f x‖) ≤
      ((S.card : ℝ) ^ (p - 1) * ∑ x ∈ S, ‖f x‖ ^ p) ^ ((p : ℝ)⁻¹) := by
  have hsum : 0 ≤ ∑ x ∈ S, ‖f x‖ := Finset.sum_nonneg (fun x _ ↦ norm_nonneg _)
  have h := norm_sum_natPower_le S (fun x ↦ (‖f x‖ : ℂ)) hp
  have hpow : (∑ x ∈ S, ‖f x‖) ^ p ≤
      (S.card : ℝ) ^ (p - 1) * ∑ x ∈ S, ‖f x‖ ^ p := by
    simpa only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hsum, abs_of_nonneg (norm_nonneg _)] using h
  apply (pow_le_pow_iff_left₀ hsum (Real.rpow_nonneg (by positivity) _) hp.ne').mp
  rw [Real.rpow_inv_natCast_pow (by positivity) hp.ne']
  exact hpow

theorem short_shift_moment_bound (u : ℕ → ℂ) (N : ℕ) {M p : ℕ}
    (hM : 0 < M) (hp : 0 < p) (hu : ∀ n < N + M, ‖u n‖ ≤ 1) :
    ‖∑ n ∈ Finset.range N, u n‖ ≤
      ((N : ℝ) ^ (p - 1) *
        ∑ n ∈ Finset.range N, ‖∑ h ∈ Finset.range M, u (n + h)‖ ^ p) ^ ((p : ℝ)⁻¹) / M +
          2 * M := by
  have h := sum_norm_le_moment_root (Finset.range N)
    (fun n ↦ ∑ h ∈ Finset.range M, u (n + h)) hp
  rw [Finset.card_range] at h
  exact (short_shift_average_bound u N hM hu).trans
    (add_le_add (div_le_div_of_nonneg_right h (Nat.cast_nonneg M)) le_rfl)

end Erdos421
