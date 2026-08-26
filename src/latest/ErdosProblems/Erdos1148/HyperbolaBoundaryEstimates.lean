import ErdosProblems.Erdos1148.HyperbolaStripEstimates

/-! # Boundary terms in the zeta-character hyperbola estimate -/

namespace Erdos1148.DukeArithmetic

lemma realDirichletValue_sub_partialSum_norm_le_nat {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 < s)
    {N : ℕ} (hN : 0 < N) :
    ‖realDirichletValue χ s - realDirichletPartialSum χ s N‖ ≤
      2 * q * (N : ℝ) ^ (-s) := by
  simpa only [Nat.floor_natCast] using realDirichletValue_sub_floor_partialSum_norm_le χ hχ hs
    (Nat.cast_pos.mpr hN : (0 : ℝ) < N)

lemma realPowerPartialSum_sub_regularized_norm_le {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ} (hN : 0 < N) :
    ‖realPowerPartialSum s N - realZetaRegularized s‖ ≤
      (N : ℝ) ^ (1 - s) / (1 - s) + 2 * (N : ℝ) ^ (-s) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h := power_sum_regularized_floor_error_le hs hs1 hN1
  simp only [Nat.floor_natCast, ← Real.norm_eq_abs] at h
  have hmain : 0 ≤ (N : ℝ) ^ (1 - s) / (1 - s) := by positivity
  calc
    _ = ‖(realPowerPartialSum s N -
        (realZetaRegularized s + (N : ℝ) ^ (1 - s) / (1 - s))) +
          (N : ℝ) ^ (1 - s) / (1 - s)‖ := by congr 1; ring
    _ ≤ ‖realPowerPartialSum s N -
        (realZetaRegularized s + (N : ℝ) ^ (1 - s) / (1 - s))‖ +
          ‖(N : ℝ) ^ (1 - s) / (1 - s)‖ := norm_add_le _ _
    _ ≤ 2 * (N : ℝ) ^ (-s) + (N : ℝ) ^ (1 - s) / (1 - s) := by
      rw [Real.norm_of_nonneg hmain]
      exact add_le_add h le_rfl
    _ = _ := add_comm _ _

theorem hyperbola_cross_error_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ} (hN : 0 < N) :
    ‖(realPowerPartialSum s N - realZetaRegularized s) *
        (realDirichletValue χ s - realDirichletPartialSum χ s N)‖ ≤
      6 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 - 2 * s) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : 0 < 1 - s := by linarith
  have hq : (q : ℝ) ≤ (q : ℝ) / (1 - s) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) q]
  have hp : (N : ℝ) ^ (-s) * (N : ℝ) ^ (-s) ≤ (N : ℝ) ^ (1 - 2 * s) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rw [norm_mul]
  calc
    _ ≤ ((N : ℝ) ^ (1 - s) / (1 - s) + 2 * (N : ℝ) ^ (-s)) *
        (2 * q * (N : ℝ) ^ (-s)) := by
      exact mul_le_mul (realPowerPartialSum_sub_regularized_norm_le hs hs1 hN)
        (realDirichletValue_sub_partialSum_norm_le_nat χ hχ hs hN) (norm_nonneg _)
        (by positivity)
    _ = 2 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 - 2 * s) +
        4 * q * ((N : ℝ) ^ (-s) * (N : ℝ) ^ (-s)) := by
      rw [← rpow_hyperbola_cross_term hN0 s]
      ring
    _ ≤ 2 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 - 2 * s) +
        4 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 - 2 * s) := by gcongr
    _ = _ := by ring

theorem hyperbola_residue_tail_error_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs1 : s < 1)
    {N : ℕ} (hN : 0 < N) :
    ‖((N * N : ℕ) : ℝ) ^ (1 - s) / (1 - s) *
        (realDirichletValue χ 1 - realDirichletPartialSum χ 1 N)‖ ≤
      2 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 - 2 * s) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : 0 < 1 - s := by linarith
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((N * N : ℕ) : ℝ) ^ (1 - s) / (1 - s) *
        (2 * q * (N : ℝ) ^ (-1 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (realDirichletValue_sub_partialSum_norm_le_nat χ hχ zero_lt_one hN) (by positivity)
    _ = _ := by
      rw [Nat.cast_mul, ← rpow_hyperbola_square_main_tail hN0 s]
      ring

end Erdos1148.DukeArithmetic
