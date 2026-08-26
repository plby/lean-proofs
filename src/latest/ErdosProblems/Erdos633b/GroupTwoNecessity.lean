import ErdosProblems.Erdos633b.RationalSides
import ErdosProblems.Erdos633b.TriangleCosine

/-! Exact rational trigonometric consequences of commensurable tile sides. -/

namespace Erdos633b.Triangle

theorem rational_cos_of_rationalSides (S : Triangle) (hs : S.RationalSides) (i : Fin 3) :
    IsRational (Real.cos (S.angle i)) := by
  obtain ⟨q, hq⟩ := hs i (i + 2)
  obtain ⟨r, hr⟩ := hs (i + 1) (i + 2)
  refine ⟨(r ^ 2 + 1 - q ^ 2) / (2 * r), ?_⟩
  push_cast
  rw [hq, hr]
  have hb := S.side_pos (i + 1)
  have hc := S.side_pos (i + 2)
  apply (div_eq_iff (mul_ne_zero (by norm_num) (div_ne_zero hb.ne' hc.ne'))).mpr
  field_simp
  linear_combination -(S.cosine_law i)

theorem groupTwo_sqrt_sin_rational (S : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3)
    (hs : S.RationalSides) : IsRational (Real.sqrt 3 * Real.sin (S.angle 0)) := by
  obtain ⟨q, hq⟩ := hs 0 2
  refine ⟨3 * q / 2, ?_⟩
  push_cast
  rw [hq, S.side_ratio_eq_sine_ratio 0 2, hg,
    show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
    Real.sin_pi_sub, Real.sin_pi_div_three]
  have h3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

theorem groupTwo_half_parameter_rational (S : Triangle)
    (hg : S.angle 2 = 2 * Real.pi / 3) (hs : S.RationalSides) :
    IsRational (Real.sqrt 3 * Real.tan (S.angle 0 / 2)) :=
  (groupTwo_rationality_iff (S.angle 0) (S.angle_pos 0) (S.angle_lt_pi 0)).mpr
    ⟨S.groupTwo_sqrt_sin_rational hg hs, S.rational_cos_of_rationalSides hs 0⟩

theorem groupTwo_double_half_parameter_rational (S : Triangle)
    (hg : S.angle 2 = 2 * Real.pi / 3) (hs : S.RationalSides) :
    IsRational (Real.sqrt 3 * Real.tan ((2 * S.angle 0) / 2)) := by
  have ha3 : S.angle 0 < Real.pi / 3 := by linarith [S.angle_sum, S.angle_pos 1]
  obtain ⟨q, hq⟩ := S.groupTwo_sqrt_sin_rational hg hs
  obtain ⟨r, hr⟩ := S.rational_cos_of_rationalSides hs 0
  apply (groupTwo_rationality_iff (2 * S.angle 0)
    (by linarith [S.angle_pos 0]) (by linarith [Real.pi_pos])).mpr
  constructor
  · refine ⟨2 * q * r, ?_⟩
    push_cast
    rw [hq, hr, Real.sin_two_mul]
    ring
  · refine ⟨2 * r ^ 2 - 1, ?_⟩
    push_cast
    rw [hr, Real.cos_two_mul]

end Erdos633b.Triangle
