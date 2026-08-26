import ErdosProblems.Erdos421.LogPowerCancellation

/-! # Covering polynomial frequency ranges by difference orders -/

namespace Erdos421

theorem logarithmicDifferenceConstant_pos (r : ℕ) :
    0 < logarithmicDifferenceConstant r := by
  unfold logarithmicDifferenceConstant
  positivity

theorem logarithmicDifferenceConstant_mono : Monotone logarithmicDifferenceConstant := by
  intro r R hr
  have hb : (r : ℝ) + 3 ≤ R + 3 := by exact_mod_cast Nat.add_le_add_right hr 3
  have hp : ((r : ℝ) + 3) ^ (r + 2) ≤ ((R : ℝ) + 3) ^ (R + 2) :=
    (pow_le_pow_left₀ (by positivity) hb _).trans
      (pow_le_pow_right₀ (show (1 : ℝ) ≤ (R : ℝ) + 3 by
        linarith [show (0 : ℝ) ≤ R from Nat.cast_nonneg R]) (by omega))
  have hf : (r.factorial : ℝ) ≤ R.factorial := by
    exact_mod_cast Nat.factorial_le hr
  unfold logarithmicDifferenceConstant
  have hm := mul_le_mul (show 14 + 2 * ((r : ℝ) + 3) ^ (r + 2) ≤
      14 + 2 * ((R : ℝ) + 3) ^ (R + 2) by linarith)
    (show (r.factorial : ℝ) + 3 ≤ R.factorial + 3 by linarith)
    (by positivity) (by positivity)
  linarith

/-- Consecutive choices of the difference order cover a whole frequency
range. The condition on `Q` leaves overlap between neighboring choices. -/
theorem exists_logarithmic_difference_order {M Q : ℝ}
    (R : ℕ) {τ : ℝ} (hlo : Q ^ 2 ≤ τ)
    (hhi : τ ≤ M ^ (R + 1) * Q ^ 2) :
    ∃ r ≤ R, M ^ r * Q ^ 2 ≤ τ ∧ τ ≤ M ^ (r + 1) * Q ^ 2 := by
  induction R with
  | zero =>
      exact ⟨0, le_refl _, by simpa only [pow_zero, one_mul] using hlo, hhi⟩
  | succ R ih =>
      by_cases ht : τ ≤ M ^ (R + 1) * Q ^ 2
      · obtain ⟨r, hr, hl, hu⟩ := ih ht
        exact ⟨r, by omega, hl, hu⟩
      · exact ⟨R + 1, le_refl _, (lt_of_not_ge ht).le, hhi⟩

/-- A single bound uniform over a union of polynomial frequency ranges. -/
theorem logarithmicSum_frequency_cover_bound {M N Q : ℕ}
    (hM : 0 < M) (hN : N ≤ M) (hQ : 0 < Q) (R : ℕ)
    (hscale : (Q : ℝ) ^ (2 * R + 4) ≤ M) {τ : ℝ}
    (hlo : (Q : ℝ) ^ 2 ≤ τ) (hhi : τ ≤ (M : ℝ) ^ (R + 1) * (Q : ℝ) ^ 2) :
    (‖logarithmicSum M N τ‖ / (4 * M)) ^ (2 ^ R) ≤
      logarithmicDifferenceConstant R / Q := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQp : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQM : Q ≤ M := by
    have h := (le_self_pow₀ hQ1 (by omega : 2 * R + 4 ≠ 0)).trans hscale
    exact_mod_cast h
  obtain ⟨r, hr, hl, hu⟩ := exists_logarithmic_difference_order R hlo hhi
  have hp : (Q : ℝ) ^ (2 * r + 4) ≤ M :=
    (pow_le_pow_right₀ hQ1 (by omega)).trans hscale
  have hupper : τ * (Q : ℝ) ^ (2 * r + 2) ≤ (M : ℝ) ^ (r + 2) := by
    calc
      _ ≤ ((M : ℝ) ^ (r + 1) * (Q : ℝ) ^ 2) * (Q : ℝ) ^ (2 * r + 2) :=
        mul_le_mul_of_nonneg_right hu (by positivity)
      _ = (M : ℝ) ^ (r + 1) * (Q : ℝ) ^ (2 * r + 4) := by
        rw [mul_assoc, ← pow_add]
        congr 2
        omega
      _ ≤ (M : ℝ) ^ (r + 1) * M :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by simp only [pow_succ]
  have hb := logarithmicSum_polynomial_frequency_bound hM hN hQ hQM r hl hupper
  have hnorm : ‖logarithmicSum M N τ‖ / (4 * M) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have hn : (N : ℝ) ≤ M := by exact_mod_cast hN
    have h := logarithmicSum_norm_le M N τ
    linarith
  calc
    _ ≤ (‖logarithmicSum M N τ‖ / (4 * M)) ^ (2 ^ r) :=
      pow_le_pow_of_le_one (by positivity) hnorm (Nat.pow_le_pow_right (by omega) hr)
    _ ≤ logarithmicDifferenceConstant r / Q := hb
    _ ≤ _ := div_le_div_of_nonneg_right (logarithmicDifferenceConstant_mono hr) hQp.le

end Erdos421
