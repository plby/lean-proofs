import ErdosProblems.Erdos421.IteratedDifferenceBound

/-! # Optimizing the terminal phase-band parameter at arbitrary order -/

namespace Erdos421

theorem logDifferenceLeafBound_scale {M H : ℕ} (hM : 0 < M) (hHM : H ≤ M)
    (r : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    logDifferenceLeafBound M H r ((M : ℝ) ^ (r + 2) * s ^ 2) s / M ≤
      (14 + 2 * ((r : ℝ) + 3) ^ (r + 2)) *
        (r.factorial * (H : ℝ) ^ r * s + 3 / ((M : ℝ) * s)) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hHM' : (H : ℝ) ≤ M := by exact_mod_cast hHM
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hA : (2 * M + r * H + 1 : ℝ) ≤ ((r : ℝ) + 3) * M := by
    have hm := mul_le_mul_of_nonneg_left hHM' hr0
    nlinarith
  have hpow := pow_le_pow_left₀
    (by positivity : (0 : ℝ) ≤ 2 * M + r * H + 1) hA (r + 2)
  have hpart : 2 * s * (2 * M + r * H + 1 : ℝ) ^ (r + 2) /
      ((M : ℝ) ^ (r + 2) * s ^ 2) ≤ 2 * ((r : ℝ) + 3) ^ (r + 2) / s := by
    calc
      _ ≤ 2 * s * (((r : ℝ) + 3) * M) ^ (r + 2) /
          ((M : ℝ) ^ (r + 2) * s ^ 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
      _ = _ := by rw [mul_pow]; field_simp
  have hinner : 2 + 12 / s + 2 * s * (2 * M + r * H + 1 : ℝ) ^ (r + 2) /
      ((M : ℝ) ^ (r + 2) * s ^ 2) ≤ (14 + 2 * ((r : ℝ) + 3) ^ (r + 2)) / s := by
    have htwo : (2 : ℝ) ≤ 2 / s := (le_div_iff₀ hs).mpr (by linarith)
    calc
      _ ≤ 2 / s + 12 / s + 2 * ((r : ℝ) + 3) ^ (r + 2) / s := by linarith
      _ = _ := by ring
  have houter : (M : ℝ) ^ (r + 2) * s ^ 2 * r.factorial * (H : ℝ) ^ r /
      (M : ℝ) ^ (r + 1) + 3 = (M : ℝ) * s ^ 2 * r.factorial * (H : ℝ) ^ r + 3 := by
    rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
    field_simp
  unfold logDifferenceLeafBound
  rw [houter]
  calc
    _ ≤ (((M : ℝ) * s ^ 2 * r.factorial * (H : ℝ) ^ r + 3) *
        ((14 + 2 * ((r : ℝ) + 3) ^ (r + 2)) / s)) / M :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hinner (by positivity)) hMp.le
    _ = _ := by field_simp

/-- A normalized explicit estimate after choosing the phase-band parameter.
For each fixed order, the right-hand side can be made small over a
corresponding polynomial frequency range. -/
theorem logarithmicSum_arbitrary_order_scale_bound {M N H : ℕ}
    (hM : 0 < M) (hN : N ≤ M) (hH : 0 < H) (hHM : H ≤ M)
    (r : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (‖logarithmicSum M N ((M : ℝ) ^ (r + 2) * s ^ 2)‖ / (4 * M)) ^ (2 ^ r) ≤
      1 / (H : ℝ) + (14 + 2 * ((r : ℝ) + 3) ^ (r + 2)) *
        (r.factorial * (H : ℝ) ^ r * s + 3 / ((M : ℝ) * s)) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hτ : 0 < (M : ℝ) ^ (r + 2) * s ^ 2 := by positivity
  exact (logarithmicSum_arbitrary_order_bound hM hN hH hHM r hτ hs).trans
    (add_le_add le_rfl (logDifferenceLeafBound_scale hM hHM r hs hs1))

end Erdos421
