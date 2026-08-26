import ErdosProblems.Erdos633b.GroupTwoNecessity
import Mathlib.NumberTheory.Real.Irrational

/-! The cosine-law conic and exact normalized side formulas for the
(2 alpha, 2 beta, alpha+beta) group-2 shape. -/

namespace Erdos633b.Triangle

theorem groupTwo_side_conic (S : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3) :
    S.side 2 ^ 2 = S.side 0 ^ 2 + S.side 0 * S.side 1 + S.side 1 ^ 2 := by
  have h := S.cosine_law 2
  change S.side 2 ^ 2 = S.side 0 ^ 2 + S.side 1 ^ 2 -
    2 * S.side 0 * S.side 1 * Real.cos (S.angle 2) at h
  rw [hg, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three] at h
  nlinarith

theorem groupTwo_normalized_conic (S : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3) :
    (S.side 0 / S.side 2) ^ 2 + (S.side 0 / S.side 2) * (S.side 1 / S.side 2) +
      (S.side 1 / S.side 2) ^ 2 = 1 := by
  field_simp [(S.side_pos 2).ne']
  nlinarith [S.groupTwo_side_conic hg]

theorem groupTwo_cosine_coordinates (S : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3) :
    2 * Real.cos (S.angle 0) = S.side 0 / S.side 2 + 2 * (S.side 1 / S.side 2) ∧
      2 * Real.cos (S.angle 1) = 2 * (S.side 0 / S.side 2) + S.side 1 / S.side 2 := by
  have hconic := S.groupTwo_side_conic hg
  have h0 := S.cosine_law 0
  have h1 := S.cosine_law 1
  change S.side 0 ^ 2 = S.side 1 ^ 2 + S.side 2 ^ 2 -
    2 * S.side 1 * S.side 2 * Real.cos (S.angle 0) at h0
  change S.side 1 ^ 2 = S.side 2 ^ 2 + S.side 0 ^ 2 -
    2 * S.side 2 * S.side 0 * Real.cos (S.angle 1) at h1
  have he0 : 2 * S.side 2 * Real.cos (S.angle 0) = S.side 0 + 2 * S.side 1 := by
    apply mul_left_cancel₀ (S.side_pos 1).ne'
    linear_combination h0 + hconic
  have he1 : 2 * S.side 2 * Real.cos (S.angle 1) = 2 * S.side 0 + S.side 1 := by
    apply mul_left_cancel₀ (S.side_pos 0).ne'
    linear_combination h1 + hconic
  constructor
  · field_simp [(S.side_pos 2).ne']
    nlinarith [he0]
  · field_simp [(S.side_pos 2).ne']
    nlinarith [he1]

theorem groupTwo_short_sides_ne (S : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3)
    (hirr : Irrational (S.angle 0 / Real.pi)) : S.side 0 ≠ S.side 1 := by
  intro he
  have hd : dist (S.points 2) (S.points 0) = dist (S.points 2) (S.points 1) := by
    change S.side 1 = dist (S.points 2) (S.points 1)
    rw [← he]
    exact dist_comm _ _
  have ha := EuclideanGeometry.angle_eq_angle_of_dist_eq hd
  have heang : S.angle 0 = S.angle 1 := by
    change EuclideanGeometry.angle (S.points 1) (S.points 0) (S.points 2) =
      EuclideanGeometry.angle (S.points 2) (S.points 1) (S.points 0)
    simpa only [EuclideanGeometry.angle_comm (S.points 2)] using ha
  have halpha : S.angle 0 = Real.pi / 6 := by linarith [S.angle_sum]
  apply hirr
  refine ⟨1 / 6, ?_⟩
  push_cast
  rw [halpha]
  field_simp

theorem groupTwoDouble_side_ratios (S T : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * S.angle 0) (h1 : T.angle 1 = 2 * S.angle 1)
    (h2 : T.angle 2 = S.angle 0 + S.angle 1) :
    T.side 0 / T.side 2 = (S.side 0 / S.side 2) *
        (S.side 0 / S.side 2 + 2 * (S.side 1 / S.side 2)) ∧
      T.side 1 / T.side 2 = (S.side 1 / S.side 2) *
        (2 * (S.side 0 / S.side 2) + S.side 1 / S.side 2) := by
  have hsum : S.angle 0 + S.angle 1 = Real.pi / 3 := by linarith [S.angle_sum]
  have hsin : Real.sin (T.angle 2) = Real.sin (S.angle 2) := by
    rw [h2, hsum, hg, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.sin_pi_sub]
  obtain ⟨hc0, hc1⟩ := S.groupTwo_cosine_coordinates hg
  constructor
  · rw [T.side_ratio_eq_sine_ratio, hsin, h0, Real.sin_two_mul, ← hc0,
      S.side_ratio_eq_sine_ratio 0 2]
    ring
  · rw [T.side_ratio_eq_sine_ratio, hsin, h1, Real.sin_two_mul, ← hc1,
      S.side_ratio_eq_sine_ratio 1 2]
    ring

theorem groupTwoDouble_normalized_sides (S T : Triangle)
    (hg : S.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * S.angle 0) (h1 : T.angle 1 = 2 * S.angle 1)
    (h2 : T.angle 2 = S.angle 0 + S.angle 1) :
    T.side 0 / S.side 2 = (T.side 2 / S.side 2) *
        ((S.side 0 / S.side 2) * (S.side 0 / S.side 2 + 2 * (S.side 1 / S.side 2))) ∧
      T.side 1 / S.side 2 = (T.side 2 / S.side 2) *
        ((S.side 1 / S.side 2) * (2 * (S.side 0 / S.side 2) + S.side 1 / S.side 2)) := by
  obtain ⟨hX, hY⟩ := S.groupTwoDouble_side_ratios T hg h0 h1 h2
  constructor
  · rw [← hX]
    field_simp [(T.side_pos 2).ne', (S.side_pos 2).ne']
  · rw [← hY]
    field_simp [(T.side_pos 2).ne', (S.side_pos 2).ne']

end Erdos633b.Triangle
