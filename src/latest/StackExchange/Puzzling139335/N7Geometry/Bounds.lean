import StackExchange.Puzzling139335.N7Geometry.Defs

namespace Puzzling139335.N7Geometry

theorem c_pos : 0 < c := by
  dsimp [c]
  positivity

theorem c_sq : c ^ 2 = 3 / 4 := by
  dsimp [c]
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem c_gt_three_quarters : (3 / 4 : ℝ) < c := by
  nlinarith only [c_sq, c_pos]

theorem c_lt_one : c < 1 := by
  nlinarith only [c_sq, c_pos]

theorem u_pos : 0 < u := by
  dsimp [u]
  linarith only [c_lt_one]

theorem u_lt_quarter : u < 1 / 4 := by
  dsimp [u]
  linarith only [c_gt_three_quarters]

theorem source_x_nonneg {p : Plane} (hp : p ∈ unitSquare) : 0 ≤ p 0 :=
  hp.1.1

theorem source_y_nonneg {p : Plane} (hp : p ∈ unitSquare) : 0 ≤ p 1 :=
  hp.2.1

/-- The right edge of the square bounds the first coordinate of the third placement. -/
theorem source_x_add_twice_c_y_le_one {p : Plane}
    (hTp : T p ∈ unitSquare) :
    p 0 + 2 * c * p 1 ≤ 1 := by
  have h := hTp.1.2
  change 1 / 2 + p 0 / 2 + c * p 1 ≤ 1 at h
  nlinarith only [h]

/-- The bottom edge bounds the second coordinate of the third placement. -/
theorem source_y_le_twice_u_add_twice_c_x {p : Plane}
    (hTp : T p ∈ unitSquare) :
    p 1 ≤ 2 * u + 2 * c * p 0 := by
  have h := hTp.2.1
  change 0 ≤ u + c * p 0 - p 1 / 2 at h
  nlinarith only [h]

/-- The source height bound follows from actual containment of the third
placement; it is not an extra geometric assumption. -/
theorem source_y_le_half {p : Plane} (hTp : T p ∈ unitSquare) :
    p 1 ≤ 1 / 2 := by
  have hfirst := source_x_add_twice_c_y_le_one hTp
  have hsecond := source_y_le_twice_u_add_twice_c_x hTp
  have hmul :=
    mul_le_mul_of_nonneg_left hfirst
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) c_pos.le)
  have hcircle_y := congrArg (fun t : ℝ => t * p 1) c_sq
  dsimp [u] at hsecond
  nlinarith only [hmul, hsecond, hcircle_y]

/-- All normalized source inequalities derived from the two actual square containments. -/
theorem source_bounds {p : Plane} (hp : p ∈ unitSquare)
    (hTp : T p ∈ unitSquare) :
    0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 0 + 2 * c * p 1 ≤ 1 ∧
      p 1 ≤ 2 * u + 2 * c * p 0 ∧ p 1 ≤ 1 / 2 :=
  ⟨source_x_nonneg hp, source_y_nonneg hp,
    source_x_add_twice_c_y_le_one hTp,
    source_y_le_twice_u_add_twice_c_x hTp, source_y_le_half hTp⟩

/-- On the left source side, containment of the third placement gives a
strictly smaller height than the left midpoint. -/
theorem left_slice_bound {p : Plane} (hTp : T p ∈ unitSquare)
    (hp0 : p 0 = 0) :
    p 1 ≤ 2 * u := by
  simpa [hp0] using source_y_le_twice_u_add_twice_c_x hTp

theorem T_x_ge_half {p : Plane} (hp : p ∈ unitSquare) :
    (1 / 2 : ℝ) ≤ (T p) 0 := by
  change 1 / 2 ≤ 1 / 2 + p 0 / 2 + c * p 1
  nlinarith only [hp.1.1, mul_nonneg c_pos.le hp.2.1]

theorem Uminus_x_ge_u {p : Plane} (hp : p ∈ unitSquare) :
    u ≤ (Uminus p) 0 := by
  change u ≤ u + c * p 0 + p 1 / 2
  nlinarith only [hp.2.1, mul_nonneg c_pos.le hp.1.1]

/-- The first singleton placement is bounded using the actual coordinates
of the third placement. -/
theorem Uplus_x_identity (p : Plane) :
    (Uplus p) 0 = u + (1 - (T p) 0) / 2 + c * (T p) 1 := by
  change 1 / 2 + p 0 / 2 - c * p 1 =
    u + (1 - (1 / 2 + p 0 / 2 + c * p 1)) / 2 +
      c * (u + c * p 0 - p 1 / 2)
  have hcircle_x := congrArg (fun t : ℝ => t * p 0) c_sq
  dsimp [u]
  nlinarith only [c_sq, hcircle_x]

theorem Uplus_x_ge_u {p : Plane} (hTp : T p ∈ unitSquare) :
    u ≤ (Uplus p) 0 := by
  rw [Uplus_x_identity]
  have hfirst : 0 ≤ 1 - (T p) 0 := sub_nonneg.mpr hTp.1.2
  have hsecond : 0 ≤ c * (T p) 1 := mul_nonneg c_pos.le hTp.2.1
  linarith only [hfirst, hsecond]

/-- The left midpoint cannot belong to a source whose third placement
is contained in the square. -/
theorem T_leftMidpoint_not_mem_unitSquare :
    T leftMidpoint ∉ unitSquare := by
  intro h
  have hbound := left_slice_bound h leftMidpoint_zero
  rw [leftMidpoint_one] at hbound
  linarith only [hbound, u_lt_quarter]

end Puzzling139335.N7Geometry
