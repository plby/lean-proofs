import ErdosProblems.Erdos633b.RationalAngleWeights
import ErdosProblems.Erdos633b.CosineLowDegree

/-! A primitive order and reduced positive numerator for a rational
reference angle below pi/3. The common angle denominator need not be minimal. -/

namespace Erdos633b.Triangle

theorem rational_small_angle_primitive_order (S : Triangle)
    (hrat : ∀ i, IsRational (S.angle i / Real.pi)) (hsmall : S.angle 0 < Real.pi / 3) :
    ∃ D j : ℕ, 6 < D ∧ 0 < j ∧ j.Coprime D ∧ 6 * j < D ∧
      S.angle 0 = 2 * Real.pi * j / D ∧
      IsPrimitiveRoot (Complex.exp ((S.angle 0 : ℂ) * Complex.I)) D := by
  obtain ⟨N, hN, w, hw, hwp, _⟩ := S.positive_integer_angle_weights hrat
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hθ : 0 < Real.pi / N := div_pos Real.pi_pos hNr
  have hsmallw : 3 * w 0 < N := by
    have he : (N : ℝ) * (Real.pi / N) = Real.pi := by field_simp
    have hh : (3 * (w 0 : ℝ)) * (Real.pi / N) < (N : ℝ) * (Real.pi / N) := by
      rw [he]
      rw [hw 0] at hsmall
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
      _ < 2 * N := Nat.mul_lt_mul_of_pos_left hsmallw (by decide)
      _ = D * g := hND
  have h6j : 6 * j < D := Nat.lt_of_mul_lt_mul_right hmul
  have hD : 6 < D := by omega
  have ha : S.angle 0 = 2 * Real.pi * j / D := by
    rw [hw 0]
    have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
    have hmj' : (w 0 : ℝ) = (j : ℝ) * g := by exact_mod_cast hmj
    have hND' : (2 : ℝ) * N = (D : ℝ) * g := by exact_mod_cast hND
    field_simp [hNr.ne', hDr]
    linear_combination (D : ℝ) * hmj' - (j : ℝ) * hND'
  refine ⟨D, j, hD, hj, hjD, h6j, ha, ?_⟩
  rw [ha]
  exact primitive_cosine_root D j (by omega) hjD

end Erdos633b.Triangle
