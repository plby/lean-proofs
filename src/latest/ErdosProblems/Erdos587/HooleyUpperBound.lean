import ErdosProblems.Erdos587.HooleyFinalForcing

/-! # The unconditional fixed-exponent log-log upper bound for Erdős 587 -/

open Filter

namespace Erdos587

theorem unconditional_loglog_upper_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      (MaxNotSqSum N : ℝ) ≤ K * (N : ℝ) ^ (1 / 3 : ℝ) *
        (max 1 (Real.log (Real.log (N : ℝ)))) ^ 16 := by
  obtain ⟨J, hJ, hforce⟩ := exists_delta_finite_square_forcing
  refine ⟨(J : ℝ), by exact_mod_cast hJ, ?_⟩
  filter_upwards [hforce] with N hN
  obtain ⟨A, hA, hfree, hcard⟩ := exists_admissible_card_eq N
  let L := max 1 (Real.log (Real.log (N : ℝ)))
  have hL : 1 ≤ L := le_max_left _ _
  have hJone : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  by_contra hnot
  have hlt : (J : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) * L ^ 16 < (A.card : ℝ) := by
    rw [hcard]
    exact lt_of_not_ge hnot
  apply hN A hA _ hfree
  have hJcube : (J : ℝ) ≤ (J : ℝ) ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hJone (show 1 ≤ 3 by omega)
  have hcube : ((J : ℝ) * ((N : ℝ) ^ (1 / 3 : ℝ) * L ^ 16)) ^ 3 ≤ (A.card : ℝ) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity)
    simpa only [mul_assoc] using hlt.le
  calc
    (J : ℝ) * N * L ^ 48 ≤ (J : ℝ) ^ 3 * N * L ^ 48 := by gcongr
    _ = ((J : ℝ) * ((N : ℝ) ^ (1 / 3 : ℝ) * L ^ 16)) ^ 3 := by
      rw [mul_pow, delta_cube_root_loglog_cube]
      ring
    _ ≤ (A.card : ℝ) ^ 3 := hcube

end Erdos587
