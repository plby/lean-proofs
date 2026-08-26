import ErdosProblems.Erdos633b.NegativeCosineConjugate
import ErdosProblems.Erdos633b.RationalTilingSineSigns

/-! The second group-1 outer shape cannot be tiled with a commensurable
reference triangle: its area sign would make every cosine conjugate positive. -/

namespace Erdos633b.Tiling

theorem groupOne_second_tile_incommensurable {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    ¬ ∀ i, IsRational (d.tile.angle i / Real.pi) := by
  intro hrat
  obtain ⟨N, hN, w, a, hw, ha, hwp, hap, _, _⟩ :=
    d.common_positive_integer_angle_weights hrat
  have hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi := by
    have hh := T.angle_sum
    rw [h0, h1, h2] at hh
    linarith
  have hsmall : 3 * w 0 < N := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hθ : 0 < Real.pi / N := div_pos Real.pi_pos hNr
    have he : (N : ℝ) * (Real.pi / N) = Real.pi := by field_simp
    have hh : (3 * (w 0 : ℝ)) * (Real.pi / N) < (N : ℝ) * (Real.pi / N) := by
      rw [he]
      have hp := d.tile.angle_pos 1
      rw [hw 0] at hrel
      nlinarith
    have h := (mul_lt_mul_iff_left₀ hθ).mp hh
    exact_mod_cast h
  obtain ⟨k, hk, hcos⟩ := negative_cosine_conjugate N (w 0) (hwp 0).1 hsmall
  have hcos' : Real.cos (k * d.tile.angle 0) < 0 := by simpa only [hw] using hcos
  have hodd : Odd k := Nat.coprime_two_right.mp
    (Nat.Coprime.of_dvd_right (dvd_mul_right 2 N) hk)
  have hγ : Real.sin (k * d.tile.angle 2) =
      Real.sin (k * (d.tile.angle 0 + d.tile.angle 1)) := by
    have he : (k : ℝ) * d.tile.angle 2 =
        k * Real.pi - k * (d.tile.angle 0 + d.tile.angle 1) := by
      linear_combination (k : ℝ) * d.tile.angle_sum
    rw [he, Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, hodd.neg_one_pow]
    ring
  let P := Real.sin (k * d.tile.angle 0) * Real.sin (k * d.tile.angle 1) *
    Real.sin (k * d.tile.angle 2)
  have hout : Real.sin (k * T.angle 0) * Real.sin (k * T.angle 1) * Real.sin (k * T.angle 2) =
      2 * Real.cos (k * d.tile.angle 0) * P := by
    rw [h0, h1, h2, show (k : ℝ) * (2 * d.tile.angle 0) = 2 * (k * d.tile.angle 0) by ring,
      Real.sin_two_mul, ← hγ]
    dsimp only [P]
    ring
  have hboth := d.coprime_sine_product_positive N (by omega) w a hw ha hwp hap k hk
  rw [hout] at hboth
  change 0 < P * (2 * Real.cos (k * d.tile.angle 0) * P) at hboth
  have hn : 2 * Real.cos (k * d.tile.angle 0) * P ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg P)
  have he : P * (2 * Real.cos (k * d.tile.angle 0) * P) =
      2 * Real.cos (k * d.tile.angle 0) * P ^ 2 := by ring
  rw [he] at hboth
  linarith

end Erdos633b.Tiling
