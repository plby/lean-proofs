import ErdosProblems.Erdos633b.TriangleMaps
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Equal ordered angles yield a constructed similarity and transport actual tilings. -/

namespace Erdos633b

namespace Triangle

theorem cyclic_sine_law (T : Triangle) (i : Fin 3) :
    Real.sin (T.angle i) * T.side (i + 1) = Real.sin (T.angle (i + 1)) * T.side i := by
  have h := EuclideanGeometry.law_sin (T.points (i + 1)) (T.points i) (T.points (i + 2))
  have h2 : i + 1 + 1 = i + 2 := by fin_cases i <;> rfl
  have h3 : i + 1 + 2 = i := by fin_cases i <;> rfl
  rw [dist_comm (T.points i) (T.points (i + 2)),
    dist_comm (T.points (i + 2)) (T.points (i + 1))] at h
  simpa only [angle, side, h2, h3] using h

theorem sine_law (T : Triangle) (i j : Fin 3) :
    Real.sin (T.angle i) * T.side j = Real.sin (T.angle j) * T.side i := by
  have h01 := T.cyclic_sine_law 0
  have h12 := T.cyclic_sine_law 1
  have h20 := T.cyclic_sine_law 2
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | exact h01
    | exact h01.symm
    | exact h12
    | exact h12.symm
    | exact h20
    | exact h20.symm

theorem side_ratio_of_angles (T S : Triangle) (h : ∀ i, T.angle i = S.angle i) (i : Fin 3) :
    S.side i = (S.side 0 / T.side 0) * T.side i := by
  have hsin : 0 < Real.sin (T.angle 0) := Real.sin_pos_of_pos_of_lt_pi
    (T.angle_pos 0) (T.angle_lt_pi 0)
  have hT := T.sine_law i 0
  have hS := S.sine_law i 0
  rw [← h i, ← h 0] at hS
  have hcross : S.side i * T.side 0 = S.side 0 * T.side i := by
    apply mul_left_cancel₀ hsin.ne'
    linear_combination S.side 0 * hT - T.side 0 * hS
  apply mul_right_cancel₀ (T.side_pos 0).ne'
  calc
    S.side i * T.side 0 = S.side 0 * T.side i := hcross
    _ = ((S.side 0 / T.side 0) * T.side i) * T.side 0 := by field_simp [(T.side_pos 0).ne']

theorem distances_of_sides (T S : Triangle) (h : ∀ i, T.side i = S.side i) (i j : Fin 3) :
    dist (T.points i) (T.points j) = dist (S.points i) (S.points j) := by
  have h01 : dist (T.points 0) (T.points 1) = dist (S.points 0) (S.points 1) := h 2
  have h12 : dist (T.points 1) (T.points 2) = dist (S.points 1) (S.points 2) := h 0
  have h20 : dist (T.points 2) (T.points 0) = dist (S.points 2) (S.points 0) := h 1
  fin_cases i <;> fin_cases j
  · simp
  · exact h01
  · exact (dist_comm _ _).trans (h20.trans (dist_comm _ _))
  · exact (dist_comm _ _).trans (h01.trans (dist_comm _ _))
  · simp
  · exact h12
  · exact h20
  · exact (dist_comm _ _).trans (h12.trans (dist_comm _ _))
  · simp

theorem side_dilate (T : Triangle) (r : ℝ) (hr : r ≠ 0) (i : Fin 3) :
    (T.dilate r hr).side i = |r| * T.side i := by
  simp only [side, dilate_points, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs]

theorem dilate_sides_of_angles (T S : Triangle) (h : ∀ i, T.angle i = S.angle i) (i : Fin 3) :
    (T.dilate (S.side 0 / T.side 0) (div_ne_zero (S.side_pos 0).ne' (T.side_pos 0).ne')).side i =
      S.side i := by
  have hr : 0 < S.side 0 / T.side 0 := div_pos (S.side_pos 0) (T.side_pos 0)
  rw [side_dilate, abs_of_pos hr]
  exact (side_ratio_of_angles T S h i).symm

end Triangle

namespace Tiling

/-- Construct a similarity carrying an existing tiling to any triangle with equal ordered angles. -/
noncomputable def transportAngles {T S : Triangle} {n : ℕ} (d : Tiling T n)
    (h : ∀ i, T.angle i = S.angle i) : Tiling S n := by
  let r := S.side 0 / T.side 0
  have hr : r ≠ 0 := div_ne_zero (S.side_pos 0).ne' (T.side_pos 0).ne'
  let U := T.dilate r hr
  have hside : ∀ i, U.side i = S.side i := T.dilate_sides_of_angles S h
  have hdist := U.distances_of_sides S hside
  have result := (d.dilate r hr).move (U.vertexIsometry S hdist)
  rwa [U.move_vertexIsometry S hdist] at result

end Tiling

theorem hasNonsquareTiling_of_angle_eq {T S : Triangle}
    (h : ∀ i, T.angle i = S.angle i) (hT : HasNonsquareTiling T) : HasNonsquareTiling S := by
  obtain ⟨n, hn, ⟨d⟩⟩ := hT
  exact ⟨n, hn, ⟨d.transportAngles h⟩⟩

end Erdos633b
