import ErdosProblems.Erdos633b.ReptilingTrace
import ErdosProblems.Erdos633b.ReptilingAngleArithmetic

/-! Zero diagonal for an actual ordered nonsquare reptiling whose reference
triangle is right-angled and has a commensurable unique smallest angle. -/

namespace Erdos633b

namespace Triangle

theorem right_sine_cosine_sides (T : Triangle) (h : T.angle 2 = Real.pi / 2) :
    Real.sin (T.angle 0) * T.side 2 = T.side 0 ∧
      Real.cos (T.angle 0) * T.side 2 = T.side 1 := by
  have hs := T.sine_law 0 2
  rw [h, Real.sin_pi_div_two, one_mul] at hs
  have hc := T.sine_law 1 2
  have ha : T.angle 1 = Real.pi / 2 - T.angle 0 := by linarith [T.angle_sum]
  rw [h, Real.sin_pi_div_two, one_mul, ha, Real.sin_pi_div_two_sub] at hc
  exact ⟨hs, hc⟩

end Triangle

namespace Tiling

theorem boundaryMatrix_three_equation {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h : ∀ i, d.tile.angle i = T.angle i) (i : Fin 3) :
    Real.sqrt n * d.tile.side i =
      (d.boundaryMatrix i 0 : ℝ) * d.tile.side 0 +
      (d.boundaryMatrix i 1 : ℝ) * d.tile.side 1 +
      (d.boundaryMatrix i 2 : ℝ) * d.tile.side 2 := by
  simpa only [boundaryMatrix, Int.cast_natCast] using
    (d.side_eq_sqrt_mul_of_angles h i).symm.trans (d.side_eq_three_counts i)

theorem boundaryMatrix_diagonal_zero_of_right_rational {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i)
    (hmin : ∀ j, j ≠ 0 → d.tile.angle 0 < d.tile.angle j)
    (hright : d.tile.angle 2 = Real.pi / 2)
    (hrat : IsRational (d.tile.angle 0 / Real.pi)) : ∀ i, d.boundaryMatrix i i = 0 := by
  rcases d.boundaryMatrix_corner_alternative hn h hmin with hd |
    ⟨hp, _, _, h10, h11, _, _⟩
  · exact hd
  exfalso
  obtain ⟨hsin, hcos⟩ := d.tile.right_sine_cosine_sides hright
  have hrow0 := d.boundaryMatrix_three_equation h 0
  have hrow1 := d.boundaryMatrix_three_equation h 1
  simp only [h10, h11, Int.cast_zero, zero_mul, zero_add] at hrow1
  have hfirst : Real.sqrt n * Real.cos (d.tile.angle 0) = (d.boundaryMatrix 1 2 : ℝ) := by
    apply mul_right_cancel₀ (d.tile.side_pos 2).ne'
    rw [mul_assoc, hcos]
    exact hrow1
  have hsecond : Real.sqrt n * Real.sin (d.tile.angle 0) =
      (d.boundaryMatrix 0 0 : ℝ) * Real.sin (d.tile.angle 0) +
      (d.boundaryMatrix 0 1 : ℝ) * Real.cos (d.tile.angle 0) + d.boundaryMatrix 0 2 := by
    apply mul_right_cancel₀ (d.tile.side_pos 2).ne'
    rw [add_mul, add_mul, mul_assoc, hsin, mul_assoc, hsin, mul_assoc, hcos]
    exact hrow0
  have ha4 : d.tile.angle 0 < Real.pi / 4 := by
    have h01 := hmin 1 (by decide)
    have hsum := d.tile.angle_sum
    rw [hright] at hsum
    linarith
  exact no_exceptional_rational_right (d.tile.angle_pos 0) ha4 hrat n d.positive
    (d.boundaryMatrix 0 0) (d.boundaryMatrix 0 1) (d.boundaryMatrix 0 2)
    (d.boundaryMatrix 1 2) hp (d.boundaryMatrix_nonneg 0 2) hfirst hsecond

end Tiling

end Erdos633b
