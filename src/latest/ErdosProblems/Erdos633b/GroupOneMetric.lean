import ErdosProblems.Erdos633b.TriquadraticAngles

/-! Exact reference sides and the acute angle shared by the group-1 constructions. -/

namespace Erdos633b.TriquadraticCoordinates

theorem reference_points (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1) (hd : 0 < d) :
    (reference c s d hc hs hs1 hd).points = ![0, !₂[c, 0], (c * (1 - s ^ 2)) • z s d] := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · ext j
    fin_cases j <;> simp [reference, z]

theorem reference_sides (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) (i : Fin 3) :
    (reference c s d hc hs hs1 hd).side i = ![c * s, c * (1 - s ^ 2), c] i := by
  let R := reference c s d hc hs hs1 hd
  have hz : ‖z s d‖ = 1 := by nlinarith [unit_z s d he, norm_nonneg (z s d)]
  have hb : 0 < c * (1 - s ^ 2) := mul_pos hc (parameter_denominator_pos s hs hs1).1
  fin_cases i
  · change dist (R.points 1) (R.points 2) = c * s
    rw [reference_points]
    change dist (!₂[c, 0] : Plane) ((c * (1 - s ^ 2)) • z s d) = c * s
    rw [dist_eq_norm]
    have h := reference_third_side c s d he
    nlinarith [norm_nonneg ((!₂[c, 0] : Plane) - (c * (1 - s ^ 2)) • z s d), mul_pos hc hs]
  · change dist (R.points 2) (R.points 0) = c * (1 - s ^ 2)
    rw [reference_points]
    change dist ((c * (1 - s ^ 2)) • z s d) 0 = c * (1 - s ^ 2)
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg hb.le, hz, mul_one]
  · change dist (R.points 0) (R.points 1) = c
    rw [reference_points]
    change dist (0 : Plane) !₂[c, 0] = c
    rw [dist_zero_left]
    have hv : (!₂[c, 0] : Plane) = c • (!₂[1, 0] : Plane) := by
      ext j
      fin_cases j <;> simp
    rw [hv, norm_smul, Real.norm_of_nonneg hc.le, norm_e, mul_one]

theorem reference_cos_zero (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) :
    Real.cos ((reference c s d hc hs hs1 hd).angle 0) = 1 - s ^ 2 / 2 := by
  let R := reference c s d hc hs hs1 hd
  have hz : ‖z s d‖ = 1 := by nlinarith [unit_z s d he, norm_nonneg (z s d)]
  have hb : 0 < c * (1 - s ^ 2) := mul_pos hc (parameter_denominator_pos s hs hs1).1
  have hv : (!₂[c, 0] : Plane) = c • (!₂[1, 0] : Plane) := by
    ext j
    fin_cases j <;> simp
  change Real.cos (InnerProductGeometry.angle
    (R.points 1 - R.points 0) (R.points 2 - R.points 0)) = _
  rw [reference_points]
  change Real.cos (InnerProductGeometry.angle ((!₂[c, 0] : Plane) - 0)
    ((c * (1 - s ^ 2)) • z s d - 0)) = _
  rw [sub_zero, sub_zero, hv, InnerProductGeometry.angle_smul_left_of_pos _ _ hc,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hb, InnerProductGeometry.cos_angle, norm_e, hz]
  simp [PiLp.inner_apply, Fin.sum_univ_two, z]

theorem outer_angle_zero_eq_twice_reference (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) :
    (outer c s d hc hs hs1 hd).angle 0 = 2 * (reference c s d hc hs hs1 hd).angle 0 := by
  let T := outer c s d hc hs hs1 hd
  let R := reference c s d hc hs hs1 hd
  have hrel := (outer_angle_relations c s d hc hs hs1 hd he).1
  have hhalf : T.angle 0 / 2 = Real.pi - 2 * T.angle 2 := by linarith [T.angle_sum]
  have hcos : Real.cos (T.angle 0 / 2) = Real.cos (R.angle 0) := by
    rw [hhalf, Real.cos_pi_sub, Real.cos_two_mul, outer_cos_two c s d hc hs hs1 hd he,
      reference_cos_zero c s d hc hs hs1 hd he]
    ring
  have hh := Real.injOn_cos
    ⟨by linarith [T.angle_pos 0], by linarith [T.angle_lt_pi 0, Real.pi_pos]⟩
    ⟨(R.angle_pos 0).le, (R.angle_lt_pi 0).le⟩ hcos
  linarith

end Erdos633b.TriquadraticCoordinates
