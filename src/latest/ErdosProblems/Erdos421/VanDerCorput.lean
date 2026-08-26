import ErdosProblems.Erdos421.ShiftVectors

/-! # Finite van der Corput differencing with uniform correlation bounds -/

namespace Erdos421

noncomputable def finiteCorrelation (u : ℕ → ℂ) (N h : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N - h), inner ℂ (u (n + h)) (u n)

theorem shiftedVector_off_diagonal_bound (N H : ℕ) (u : ℕ → ℂ) {B : ℝ}
    (hcorr : ∀ h, 0 < h → h < H → ‖finiteCorrelation u N h‖ ≤ B)
    {i j : ℕ} (hi : i < H) (hj : j < H) (hij : i ≠ j) :
    ‖inner ℂ (shiftedVector N H u i) (shiftedVector N H u j)‖ ≤ B := by
  rcases le_total i j with hle | hle
  · rw [shiftedVector_inner N H u hle hi.le]
    exact hcorr (j - i) (by omega) (by omega)
  · rw [← inner_conj_symm, Complex.norm_conj, shiftedVector_inner N H u hle hj.le]
    exact hcorr (i - j) (by omega) (by omega)

/-- The finite differencing inequality, with the zero-extension boundary
contribution `N+H` kept explicit. -/
theorem vanDerCorput_uniform_mul_bound (u : ℕ → ℂ) (N H : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (hu : ∀ n < N, ‖u n‖ ≤ 1)
    (hcorr : ∀ h, 0 < h → h < H → ‖finiteCorrelation u N h‖ ≤ B) :
    (H : ℝ) * ‖∑ n ∈ Finset.range N, u n‖ ^ 2 ≤
      (N + H : ℝ) * (N + H * B) := by
  let v := shiftedVector N H u
  have hrow : ∀ i ∈ Finset.range H,
      (∑ j ∈ Finset.range H, ‖inner ℂ (v i) (v j)‖) ≤ N + (H : ℝ) * B := by
    intro i hi
    calc
      _ ≤ ∑ j ∈ Finset.range H, ((if j = i then (N : ℝ) else 0) + B) := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hji : j = i
        · subst j
          rw [if_pos rfl]
          exact (shiftedVector_inner_self_bound N H u hu (Finset.mem_range.mp hi).le).trans
            (le_add_of_nonneg_right hB)
        · rw [if_neg hji, zero_add]
          exact shiftedVector_off_diagonal_bound N H u hcorr
            (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (Ne.symm hji)
      _ = _ := by simp [Finset.sum_add_distrib, hi]
  have hR : (0 : ℝ) ≤ N + H * B := by positivity
  have h := hilbert_large_values_bound (Finset.range H) v (constantVector (N + H)) hR hrow
  have heq : (∑ i ∈ Finset.range H, ‖inner ℂ (v i) (constantVector (N + H))‖ ^ 2) =
      (H : ℝ) * ‖∑ n ∈ Finset.range N, u n‖ ^ 2 := by
    calc
      _ = ∑ _i ∈ Finset.range H, ‖∑ n ∈ Finset.range N, u n‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [shiftedVector_inner_constantVector_norm N H u (Finset.mem_range.mp hi).le]
      _ = _ := by simp
  rw [heq, constantVector_norm_sq, Nat.cast_add] at h
  simpa only [mul_comm] using h

theorem vanDerCorput_uniform_bound (u : ℕ → ℂ) (N : ℕ) {H : ℕ} (hH : 0 < H) {B : ℝ}
    (hB : 0 ≤ B) (hu : ∀ n < N, ‖u n‖ ≤ 1)
    (hcorr : ∀ h, 0 < h → h < H → ‖finiteCorrelation u N h‖ ≤ B) :
    ‖∑ n ∈ Finset.range N, u n‖ ^ 2 ≤ ((N + H : ℝ) / H) * (N + H * B) := by
  have hHp : (0 : ℝ) < H := by exact_mod_cast hH
  have h := vanDerCorput_uniform_mul_bound u N H hB hu hcorr
  calc
    _ ≤ ((N + H : ℝ) * (N + H * B)) / H :=
      (le_div_iff₀ hHp).mpr (by simpa only [mul_comm] using h)
    _ = _ := by ring

theorem vanDerCorput_uniform_short_bound (u : ℕ → ℂ) {N H : ℕ} (hH : 0 < H) (hHN : H ≤ N)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ n < N, ‖u n‖ ≤ 1)
    (hcorr : ∀ h, 0 < h → h < H → ‖finiteCorrelation u N h‖ ≤ B) :
    ‖∑ n ∈ Finset.range N, u n‖ ^ 2 ≤ 2 * (N : ℝ) ^ 2 / H + 2 * N * B := by
  have hHp : (0 : ℝ) < H := by exact_mod_cast hH
  have hsize : (N + H : ℝ) ≤ 2 * N := by exact_mod_cast (show N + H ≤ 2 * N by omega)
  refine (vanDerCorput_uniform_bound u N hH hB hu hcorr).trans ?_
  calc
    _ ≤ (2 * (N : ℝ) / H) * (N + H * B) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsize hHp.le) (by positivity)
    _ = _ := by field_simp

theorem vanDerCorput_uniform_length_bound (u : ℕ → ℂ) {N H M : ℕ}
    (hH : 0 < H) (hNM : N ≤ M) (hHM : H ≤ M) {B : ℝ}
    (hB : 0 ≤ B) (hu : ∀ n < N, ‖u n‖ ≤ 1)
    (hcorr : ∀ h, 0 < h → h < H → ‖finiteCorrelation u N h‖ ≤ B) :
    ‖∑ n ∈ Finset.range N, u n‖ ^ 2 ≤ 2 * (M : ℝ) ^ 2 / H + 2 * M * B := by
  have hHp : (0 : ℝ) < H := by exact_mod_cast hH
  have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hsize : (N + H : ℝ) ≤ 2 * M := by
    exact_mod_cast (show N + H ≤ 2 * M by omega)
  refine (vanDerCorput_uniform_bound u N hH hB hu hcorr).trans ?_
  calc
    _ ≤ (2 * (M : ℝ) / H) * (M + H * B) :=
      mul_le_mul (div_le_div_of_nonneg_right hsize hHp.le)
        (add_le_add hNM' le_rfl) (by positivity) (by positivity)
    _ = _ := by field_simp

end Erdos421
