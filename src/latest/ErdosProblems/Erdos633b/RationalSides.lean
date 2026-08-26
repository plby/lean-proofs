import ErdosProblems.Erdos633b.BoundaryLength
import ErdosProblems.Erdos633b.Similarity
import ErdosProblems.Erdos633b.Trigonometry

/-! Rational side data and its propagation through actual boundary equations. -/

namespace Erdos633b

namespace IsRational

theorem mul {a b : ℝ} (ha : IsRational a) (hb : IsRational b) : IsRational (a * b) := by
  obtain ⟨q, rfl⟩ := ha
  obtain ⟨r, rfl⟩ := hb
  exact ⟨q * r, by push_cast; rfl⟩

theorem div {a b : ℝ} (ha : IsRational a) (hb : IsRational b) : IsRational (a / b) := by
  obtain ⟨q, rfl⟩ := ha
  obtain ⟨r, rfl⟩ := hb
  exact ⟨q / r, by push_cast; rfl⟩

end IsRational

namespace Triangle

/-- All ratios are taken between the actual positive Euclidean side lengths. -/
def RationalSides (S : Triangle) : Prop := ∀ i j, IsRational (S.side i / S.side j)

theorem side_ratio_eq_sine_ratio (S : Triangle) (i j : Fin 3) :
    S.side i / S.side j = Real.sin (S.angle i) / Real.sin (S.angle j) := by
  apply (div_eq_div_iff (S.side_pos j).ne'
    (Real.sin_pos_of_pos_of_lt_pi (S.angle_pos j) (S.angle_lt_pi j)).ne').mpr
  simpa only [mul_comm] using (S.sine_law i j).symm

theorem groupOne_side_ratios (S : Triangle)
    (h : 3 * S.angle 0 + 2 * S.angle 1 = Real.pi) :
    S.side 0 / S.side 2 = 2 * Real.sin (S.angle 0 / 2) ∧
      S.side 1 / S.side 2 = 1 - (2 * Real.sin (S.angle 0 / 2)) ^ 2 := by
  have hb : S.angle 1 = (Real.pi - 3 * S.angle 0) / 2 := by linarith
  have hg : S.angle 2 = (Real.pi + S.angle 0) / 2 := by linarith [S.angle_sum]
  have ha3 : S.angle 0 < Real.pi / 3 := by linarith [S.angle_pos 1]
  rw [S.side_ratio_eq_sine_ratio 0 2, S.side_ratio_eq_sine_ratio 1 2, hb, hg]
  exact groupOne_sine_ratios (S.angle 0) (S.angle_pos 0) ha3

theorem groupOne_parameter_rational (S : Triangle)
    (h : 3 * S.angle 0 + 2 * S.angle 1 = Real.pi) (hs : S.RationalSides) :
    IsRational (2 * Real.sin (S.angle 0 / 2)) := by
  rw [← (S.groupOne_side_ratios h).1]
  exact hs 0 2

end Triangle

namespace Tiling

theorem rational_outer_side_ratio {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hs : d.tile.RationalSides) (i j : Fin 3) : IsRational (T.side i / d.tile.side j) := by
  choose q hq using fun k => hs k j
  refine ⟨∑ k : Fin 3, (d.boundarySideCount i k : ℚ) * q k, ?_⟩
  push_cast
  simp_rw [hq, ← mul_div_assoc]
  rw [← Finset.sum_div, ← d.side_eq_sum_counts]

end Tiling

end Erdos633b
