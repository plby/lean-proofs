import ErdosProblems.Erdos633b.QuarterThirdCosine
import ErdosProblems.Erdos633b.GroupOneProductIdentity

/-! A finite primitive-order reduction for the first group-1 shape,
proved from actual geometric tilings and the coprime interval theorem. -/

namespace Erdos633b.Tiling

theorem groupOne_first_primitive_order {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi))
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 2 * d.tile.angle 1) :
    ∃ D ∈ quarterThirdExceptions, ∃ j : ℕ, 0 < j ∧ j.Coprime D ∧ 6 * j < D ∧
      d.tile.angle 0 = 2 * Real.pi * j / D := by
  obtain ⟨N, hN, w, a, hw, ha, hwp, hap, _, _⟩ :=
    d.common_positive_integer_angle_weights hrat
  have hNpos : 0 < N := by omega
  have hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi := by
    have hh := T.angle_sum
    rw [h0, h1, h2] at hh
    linarith
  have hsmall : 3 * w 0 < N := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hθ : 0 < Real.pi / N := div_pos Real.pi_pos hNr
    have he : (N : ℝ) * (Real.pi / N) = Real.pi := by field_simp
    have hh : (3 * (w 0 : ℝ)) * (Real.pi / N) < (N : ℝ) * (Real.pi / N) := by
      rw [he]
      have hp := d.tile.angle_pos 1
      rw [hw 0] at hrel
      nlinarith
    exact_mod_cast (mul_lt_mul_iff_left₀ hθ).mp hh
  have hG : 0 < (w 0).gcd (2 * N) := Nat.gcd_pos_of_pos_left _ (hwp 0).1
  obtain ⟨g, j, D, hg, hjD, hmj, hND⟩ := Nat.exists_coprime' hG
  have hj : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    rw [hz, zero_mul] at hmj
    have := (hwp 0).1
    omega
  have hmul : (6 * j) * g < D * g := by
    calc
      (6 * j) * g = 2 * (3 * w 0) := by rw [hmj]; ring
      _ < 2 * N := Nat.mul_lt_mul_of_pos_left hsmall (by decide)
      _ = D * g := hND
  have h6j : 6 * j < D := Nat.lt_of_mul_lt_mul_right hmul
  have hD : 6 < D := by omega
  have hDexc : D ∈ quarterThirdExceptions := by
    by_contra hne
    obtain ⟨k, hk, hcl, hcu⟩ := quarter_third_cosine_conjugate N (w 0) g j D
      hNpos hD hmj hND hjD hne
    have hkodd : Odd k := Nat.coprime_two_right.mp
      (Nat.Coprime.of_dvd_right (dvd_mul_right 2 N) hk)
    have hcl' : -(1 / 2 : ℝ) < Real.cos (k * d.tile.angle 0) := by
      simpa only [hw] using hcl
    have hcu' : Real.cos (k * d.tile.angle 0) < 0 := by simpa only [hw] using hcu
    have hnon := groupOne_first_sine_product_nonpos k hkodd
      (k * d.tile.angle 0) (k * d.tile.angle 1) (k * d.tile.angle 2)
      (by linear_combination (k : ℝ) * d.tile.angle_sum)
      (by linear_combination (k : ℝ) * hrel) hcu' hcl'
    have hpos := d.coprime_sine_product_positive N (by omega) w a hw ha hwp hap k hk
    have hmul (x : ℝ) : (k : ℝ) * (2 * x) = 2 * (k * x) := by ring
    rw [h0, h1, h2, hmul, hmul] at hpos
    linarith
  refine ⟨D, hDexc, j, hj, hjD, h6j, ?_⟩
  rw [hw 0]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hmj' : (w 0 : ℝ) = (j : ℝ) * g := by exact_mod_cast hmj
  have hND' : (2 : ℝ) * N = (D : ℝ) * g := by exact_mod_cast hND
  field_simp [hNr, hDr]
  linear_combination (D : ℝ) * hmj' - (j : ℝ) * hND'

end Erdos633b.Tiling
