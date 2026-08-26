import ErdosProblems.Erdos421.LogHigherScale

/-! # Power cancellation on explicit polynomial frequency ranges -/

namespace Erdos421

noncomputable def logarithmicDifferenceConstant (r : ℕ) : ℝ :=
  1 + (14 + 2 * ((r : ℝ) + 3) ^ (r + 2)) * (r.factorial + 3)

theorem logarithmicSum_scale_cancellation_bound {M N Q : ℕ}
    (hM : 0 < M) (hN : N ≤ M) (hQ : 0 < Q) (hQM : Q ≤ M)
    (r : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hQs : (Q : ℝ) ^ (r + 1) * s ≤ 1) (hMs : (Q : ℝ) ≤ M * s) :
    (‖logarithmicSum M N ((M : ℝ) ^ (r + 2) * s ^ 2)‖ / (4 * M)) ^ (2 ^ r) ≤
      logarithmicDifferenceConstant r / Q := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hQp : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hfirst : (Q : ℝ) ^ r * s ≤ 1 / Q := by
    apply (le_div_iff₀ hQp).mpr
    simpa only [pow_succ, mul_assoc, mul_comm s (Q : ℝ)] using hQs
  have hsecond : 3 / ((M : ℝ) * s) ≤ 3 / Q :=
    div_le_div_of_nonneg_left (by norm_num) hQp hMs
  have hcoef : 0 ≤ (14 + 2 * ((r : ℝ) + 3) ^ (r + 2)) := by positivity
  have hinside : (r.factorial : ℝ) * (Q : ℝ) ^ r * s + 3 / ((M : ℝ) * s) ≤
      (r.factorial : ℝ) * (1 / Q) + 3 / Q := by
    have hm := mul_le_mul_of_nonneg_left hfirst (Nat.cast_nonneg r.factorial)
    simp only [← mul_assoc] at hm
    linarith
  have hb := logarithmicSum_arbitrary_order_scale_bound hM hN hQ hQM r hs hs1
  calc
    _ ≤ 1 / (Q : ℝ) + (14 + 2 * ((r : ℝ) + 3) ^ (r + 2)) *
        (r.factorial * (Q : ℝ) ^ r * s + 3 / ((M : ℝ) * s)) := hb
    _ ≤ 1 / (Q : ℝ) + (14 + 2 * ((r : ℝ) + 3) ^ (r + 2)) *
        (r.factorial * (1 / Q) + 3 / Q) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hinside hcoef)
    _ = _ := by unfold logarithmicDifferenceConstant; ring

/-- A direct arbitrary-order cancellation bound on a polynomial frequency
range, without a remaining phase or correlation hypothesis. -/
theorem logarithmicSum_polynomial_frequency_bound {M N Q : ℕ}
    (hM : 0 < M) (hN : N ≤ M) (hQ : 0 < Q) (hQM : Q ≤ M)
    (r : ℕ) {τ : ℝ} (hlo : (M : ℝ) ^ r * (Q : ℝ) ^ 2 ≤ τ)
    (hhi : τ * (Q : ℝ) ^ (2 * r + 2) ≤ (M : ℝ) ^ (r + 2)) :
    (‖logarithmicSum M N τ‖ / (4 * M)) ^ (2 ^ r) ≤ logarithmicDifferenceConstant r / Q := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hQp : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hτ : 0 < τ := (mul_pos (pow_pos hMp r) (sq_pos_of_pos hQp)).trans_le hlo
  have hτM : τ ≤ (M : ℝ) ^ (r + 2) := by
    have hp : (1 : ℝ) ≤ (Q : ℝ) ^ (2 * r + 2) := one_le_pow₀ hQ1
    have hm := mul_le_mul_of_nonneg_left hp hτ.le
    simpa only [mul_one] using hm.trans hhi
  let s := Real.sqrt (τ / (M : ℝ) ^ (r + 2))
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hsq : s ^ 2 = τ / (M : ℝ) ^ (r + 2) := Real.sq_sqrt (by positivity)
  have hs1 : s ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num,
    by simpa only [one_pow] using (div_le_one (pow_pos hMp (r + 2))).mpr hτM⟩
  have hfreq : (M : ℝ) ^ (r + 2) * s ^ 2 = τ := by rw [hsq]; field_simp
  have hMs : (Q : ℝ) ≤ M * s := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, hsq]
    have heq : (M : ℝ) ^ 2 * (τ / (M : ℝ) ^ (r + 2)) = τ / (M : ℝ) ^ r := by
      rw [pow_add]
      field_simp
    rw [heq]
    exact (le_div_iff₀ (pow_pos hMp r)).mpr (by simpa only [mul_comm] using hlo)
  have hQs : (Q : ℝ) ^ (r + 1) * s ≤ 1 := by
    apply le_of_sq_le_sq _ (by norm_num : (0 : ℝ) ≤ 1)
    rw [mul_pow, hsq, ← pow_mul]
    have he : (r + 1) * 2 = 2 * r + 2 := by omega
    rw [he, one_pow]
    have heq : (Q : ℝ) ^ (2 * r + 2) * (τ / (M : ℝ) ^ (r + 2)) =
        (τ * (Q : ℝ) ^ (2 * r + 2)) / (M : ℝ) ^ (r + 2) := by ring
    rw [heq]
    exact (div_le_one (pow_pos hMp (r + 2))).mpr hhi
  have hb := logarithmicSum_scale_cancellation_bound hM hN hQ hQM r hs hs1 hQs hMs
  rwa [hfreq] at hb

end Erdos421
