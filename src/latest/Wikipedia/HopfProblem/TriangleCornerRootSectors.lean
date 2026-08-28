import Wikipedia.HopfProblem.RiemannBoundaryRoot

/-!
# Cubic and quartic roots in the triangle corner sectors

The actual principal roots take the closed upper half-plane to the required
linear corner sectors.  The fourth root is rotated by `-π / 4`; consequently
its fourth power is the negative of the original input.  The boundary
identities include the corner itself and do not use an argument at zero as
if it were a nonzero polar coordinate.
-/

noncomputable section

open Complex Set
open scoped Topology

namespace Wikipedia.HopfProblem.RiemannBoundary

private theorem cubic_sector_slack (w : ℂ) :
    3 * w.re - Real.sqrt 3 * w.im =
      (2 * Real.sqrt 3 * ‖w‖) * Real.sin (Real.pi / 3 - w.arg) := by
  rw [Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three]
  rw [← norm_mul_cos_arg w, ← norm_mul_sin_arg w]
  calc
    3 * (‖w‖ * Real.cos w.arg) - Real.sqrt 3 * (‖w‖ * Real.sin w.arg) =
        ‖w‖ * ((Real.sqrt 3 * Real.sqrt 3) * Real.cos w.arg -
          Real.sqrt 3 * Real.sin w.arg) := by
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    _ = _ := by ring

private theorem quartic_sector_slack (w : ℂ) :
    w.re - w.im =
      (Real.sqrt 2 * ‖w‖) * Real.sin (Real.pi / 4 - w.arg) := by
  rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
  rw [← norm_mul_cos_arg w, ← norm_mul_sin_arg w]
  calc
    ‖w‖ * Real.cos w.arg - ‖w‖ * Real.sin w.arg =
        (‖w‖ / 2) * ((Real.sqrt 2 * Real.sqrt 2) * Real.cos w.arg -
          (Real.sqrt 2 * Real.sqrt 2) * Real.sin w.arg) := by
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ = _ := by ring

/-- The cubic principal root lies strictly inside the linear angle `π / 3`. -/
theorem principalRoot_three_upper {z : ℂ} (hz : 0 < z.im) :
    0 < (principalRoot 3 z).im ∧
      Real.sqrt 3 * (principalRoot 3 z).im < 3 * (principalRoot 3 z).re := by
  have ha := principalRoot_arg_mem_Ioo (by norm_num : 0 < 3) hz
  norm_num only [Nat.cast_ofNat] at ha
  have hw : principalRoot 3 z ≠ 0 := by
    rw [ne_eq, principalRoot_eq_zero_iff (by norm_num : 0 < 3)]
    exact fun h => by simpa only [h, zero_im, lt_self_iff_false] using hz
  constructor
  · rw [← norm_mul_sin_arg]
    exact mul_pos (norm_pos_iff.mpr hw)
      (Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [Real.pi_pos, ha.2]))
  · apply sub_pos.mp
    rw [cubic_sector_slack]
    exact mul_pos (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num)))
      (norm_pos_iff.mpr hw))
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [ha.2])
        (by linarith [Real.pi_pos, ha.1]))

/-- The closed upper half-plane maps to the closed cubic corner sector. -/
theorem principalRoot_three_closedUpper {z : ℂ} (hz : 0 ≤ z.im) :
    0 ≤ (principalRoot 3 z).im ∧
      Real.sqrt 3 * (principalRoot 3 z).im ≤ 3 * (principalRoot 3 z).re := by
  have ha := principalRoot_arg_mem_Icc (by norm_num : 0 < 3) hz
  norm_num only [Nat.cast_ofNat] at ha
  constructor
  · exact arg_nonneg_iff.mp ha.1
  · apply sub_nonneg.mp
    rw [cubic_sector_slack]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (norm_nonneg _))
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ha.2])
        (by linarith [Real.pi_pos, ha.1]))

/-- A nonnegative real input maps to the horizontal boundary ray. -/
theorem principalRoot_three_ofReal_nonneg_im {x : ℝ} (hx : 0 ≤ x) :
    (principalRoot 3 (x : ℂ)).im = 0 := by
  rw [principalRoot_ofReal_nonneg 3 hx]
  exact ofReal_im _

/-- A nonpositive real input maps to the sloping boundary ray. -/
theorem principalRoot_three_ofReal_nonpos_boundary {x : ℝ} (hx : x ≤ 0) :
    Real.sqrt 3 * (principalRoot 3 (x : ℂ)).im =
      3 * (principalRoot 3 (x : ℂ)).re := by
  rw [principalRoot_ofReal_nonpos 3 hx]
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, zero_mul, add_zero, sub_zero,
    exp_ofReal_mul_I_im, exp_ofReal_mul_I_re, Nat.cast_ofNat,
    Real.sin_pi_div_three, Real.cos_pi_div_three]
  have hsq := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  calc
    Real.sqrt 3 * ((-x) ^ (3 : ℝ)⁻¹ * (Real.sqrt 3 / 2)) =
        (Real.sqrt 3 * Real.sqrt 3) * ((-x) ^ (3 : ℝ)⁻¹ / 2) := by ring
    _ = _ := by rw [hsq]; ring

/-- Every real input maps to one of the two cubic boundary rays. -/
theorem principalRoot_three_real_boundary {z : ℂ} (hz : z.im = 0) :
    (principalRoot 3 z).im = 0 ∨
      Real.sqrt 3 * (principalRoot 3 z).im = 3 * (principalRoot 3 z).re := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [he]
  rcases le_total 0 z.re with hp | hn
  · exact Or.inl (principalRoot_three_ofReal_nonneg_im hp)
  · exact Or.inr (principalRoot_three_ofReal_nonpos_boundary hn)

/-- The fixed rotation of the fourth-root corner. -/
def quarticRootRotation : ℂ := exp (((-Real.pi / 4 : ℝ) : ℂ) * I)

@[simp]
theorem quarticRootRotation_re : quarticRootRotation.re = Real.sqrt 2 / 2 := by
  simp only [quarticRootRotation, exp_ofReal_mul_I_re, neg_div, Real.cos_neg,
    Real.cos_pi_div_four]

@[simp]
theorem quarticRootRotation_im : quarticRootRotation.im = -(Real.sqrt 2 / 2) := by
  simp only [quarticRootRotation, exp_ofReal_mul_I_im, neg_div, Real.sin_neg,
    Real.sin_pi_div_four]

@[simp]
theorem norm_quarticRootRotation : ‖quarticRootRotation‖ = 1 :=
  norm_exp_ofReal_mul_I _

theorem quarticRootRotation_ne_zero : quarticRootRotation ≠ 0 :=
  exp_ne_zero _

@[simp]
theorem quarticRootRotation_pow_four : quarticRootRotation ^ 4 = -1 := by
  rw [quarticRootRotation, ← exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (4 : ℂ) * (((-Real.pi / 4 : ℝ) : ℂ) * I) = -(Real.pi * I) := by
    push_cast
    ring
  rw [he, exp_neg, exp_pi_mul_I]
  norm_num

/-- The fourth root in the angle between the negative diagonal and real axis. -/
def rotatedPrincipalRootFour (z : ℂ) : ℂ := quarticRootRotation * principalRoot 4 z

@[simp]
theorem rotatedPrincipalRootFour_pow (z : ℂ) : rotatedPrincipalRootFour z ^ 4 = -z := by
  rw [rotatedPrincipalRootFour, mul_pow, quarticRootRotation_pow_four,
    principalRoot_pow (by norm_num : 0 < 4)]
  ring

@[simp]
theorem rotatedPrincipalRootFour_zero : rotatedPrincipalRootFour 0 = 0 := by
  rw [rotatedPrincipalRootFour, principalRoot_zero (by norm_num : 0 < 4), mul_zero]

@[simp]
theorem rotatedPrincipalRootFour_eq_zero_iff {z : ℂ} :
    rotatedPrincipalRootFour z = 0 ↔ z = 0 := by
  rw [rotatedPrincipalRootFour, mul_eq_zero]
  simp only [quarticRootRotation_ne_zero, false_or,
    principalRoot_eq_zero_iff (by norm_num : 0 < 4)]

@[simp]
theorem norm_rotatedPrincipalRootFour (z : ℂ) :
    ‖rotatedPrincipalRootFour z‖ = ‖z‖ ^ (4 : ℝ)⁻¹ := by
  rw [rotatedPrincipalRootFour, norm_mul, norm_quarticRootRotation, one_mul,
    norm_principalRoot]
  norm_num only [Nat.cast_ofNat]

theorem rotatedPrincipalRootFour_injective : Function.Injective rotatedPrincipalRootFour := by
  intro z w h
  have he := congrArg (fun s : ℂ => s ^ 4) h
  simpa only [rotatedPrincipalRootFour_pow, neg_inj] using he

theorem rotatedPrincipalRootFour_re (z : ℂ) :
    (rotatedPrincipalRootFour z).re = (Real.sqrt 2 / 2) *
      ((principalRoot 4 z).re + (principalRoot 4 z).im) := by
  simp only [rotatedPrincipalRootFour, mul_re, quarticRootRotation_re,
    quarticRootRotation_im]
  ring

theorem rotatedPrincipalRootFour_im (z : ℂ) :
    (rotatedPrincipalRootFour z).im = (Real.sqrt 2 / 2) *
      ((principalRoot 4 z).im - (principalRoot 4 z).re) := by
  simp only [rotatedPrincipalRootFour, mul_im, quarticRootRotation_re,
    quarticRootRotation_im]
  ring

theorem rotatedPrincipalRootFour_re_add_im (z : ℂ) :
    (rotatedPrincipalRootFour z).re + (rotatedPrincipalRootFour z).im =
      Real.sqrt 2 * (principalRoot 4 z).im := by
  rw [rotatedPrincipalRootFour_re, rotatedPrincipalRootFour_im]
  ring

/-- The rotated fourth root lies strictly inside its required linear sector. -/
theorem rotatedPrincipalRootFour_upper {z : ℂ} (hz : 0 < z.im) :
    (rotatedPrincipalRootFour z).im < 0 ∧
      0 < (rotatedPrincipalRootFour z).re + (rotatedPrincipalRootFour z).im := by
  have ha := principalRoot_arg_mem_Ioo (by norm_num : 0 < 4) hz
  norm_num only [Nat.cast_ofNat] at ha
  have hw : principalRoot 4 z ≠ 0 := by
    rw [ne_eq, principalRoot_eq_zero_iff (by norm_num : 0 < 4)]
    exact fun h => by simpa only [h, zero_im, lt_self_iff_false] using hz
  have hi : 0 < (principalRoot 4 z).im := by
    rw [← norm_mul_sin_arg]
    exact mul_pos (norm_pos_iff.mpr hw)
      (Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [Real.pi_pos, ha.2]))
  have hri : (principalRoot 4 z).im < (principalRoot 4 z).re := by
    apply sub_pos.mp
    rw [quartic_sector_slack]
    exact mul_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (norm_pos_iff.mpr hw))
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [ha.2])
        (by linarith [Real.pi_pos, ha.1]))
  constructor
  · rw [rotatedPrincipalRootFour_im]
    exact mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hri)
  · rw [rotatedPrincipalRootFour_re_add_im]
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) hi

/-- The rotated fourth root sends the closed upper half-plane to the closed sector. -/
theorem rotatedPrincipalRootFour_closedUpper {z : ℂ} (hz : 0 ≤ z.im) :
    (rotatedPrincipalRootFour z).im ≤ 0 ∧
      0 ≤ (rotatedPrincipalRootFour z).re + (rotatedPrincipalRootFour z).im := by
  have ha := principalRoot_arg_mem_Icc (by norm_num : 0 < 4) hz
  norm_num only [Nat.cast_ofNat] at ha
  have hi : 0 ≤ (principalRoot 4 z).im := arg_nonneg_iff.mp ha.1
  have hri : (principalRoot 4 z).im ≤ (principalRoot 4 z).re := by
    apply sub_nonneg.mp
    rw [quartic_sector_slack]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ha.2])
        (by linarith [Real.pi_pos, ha.1]))
  constructor
  · rw [rotatedPrincipalRootFour_im]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hri)
  · rw [rotatedPrincipalRootFour_re_add_im]
    exact mul_nonneg (Real.sqrt_nonneg _) hi

/-- A nonnegative real input maps to the negative-diagonal boundary ray. -/
theorem rotatedPrincipalRootFour_ofReal_nonneg_boundary {x : ℝ} (hx : 0 ≤ x) :
    (rotatedPrincipalRootFour (x : ℂ)).re +
      (rotatedPrincipalRootFour (x : ℂ)).im = 0 := by
  rw [rotatedPrincipalRootFour_re_add_im, principalRoot_ofReal_nonneg 4 hx]
  simp only [ofReal_im, mul_zero]

/-- A nonpositive real input maps to the horizontal boundary ray. -/
theorem rotatedPrincipalRootFour_ofReal_nonpos_im {x : ℝ} (hx : x ≤ 0) :
    (rotatedPrincipalRootFour (x : ℂ)).im = 0 := by
  rw [rotatedPrincipalRootFour_im, principalRoot_ofReal_nonpos 4 hx]
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, zero_mul, add_zero, sub_zero,
    exp_ofReal_mul_I_im, exp_ofReal_mul_I_re, Nat.cast_ofNat,
    Real.sin_pi_div_four, Real.cos_pi_div_four, sub_self, mul_zero]

/-- Every real input maps to one of the two rotated quartic boundary rays. -/
theorem rotatedPrincipalRootFour_real_boundary {z : ℂ} (hz : z.im = 0) :
    (rotatedPrincipalRootFour z).im = 0 ∨
      (rotatedPrincipalRootFour z).re + (rotatedPrincipalRootFour z).im = 0 := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [he]
  rcases le_total 0 z.re with hp | hn
  · exact Or.inr (rotatedPrincipalRootFour_ofReal_nonneg_boundary hp)
  · exact Or.inl (rotatedPrincipalRootFour_ofReal_nonpos_im hn)

theorem continuousOn_rotatedPrincipalRootFour_closedUpper :
    ContinuousOn rotatedPrincipalRootFour {z : ℂ | 0 ≤ z.im} :=
  continuousOn_const.mul (continuousOn_principalRoot_closedUpper (by norm_num : 0 < 4))

theorem continuousAt_rotatedPrincipalRootFour_zero :
    ContinuousAt rotatedPrincipalRootFour 0 :=
  continuousAt_const.mul (continuousAt_principalRoot_zero (by norm_num : 0 < 4))

theorem analyticOnNhd_rotatedPrincipalRootFour_upper :
    AnalyticOnNhd ℂ rotatedPrincipalRootFour {z : ℂ | 0 < z.im} := by
  intro z hz
  exact analyticAt_const.mul (analyticOnNhd_principalRoot_upper 4 z hz)

end Wikipedia.HopfProblem.RiemannBoundary
