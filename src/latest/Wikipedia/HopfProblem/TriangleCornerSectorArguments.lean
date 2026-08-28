import Wikipedia.HopfProblem.TriangleCornerSectorsTopology
import Wikipedia.HopfProblem.TriangleCornerRootSectors

/-!
# Principal-root inverses on the actual linear corner sectors

The linear inequalities defining the two corner sectors imply the exact
principal-argument bounds.  Consequently the actual principal roots invert
the cubic and rotated quartic powers on these sectors.  In particular these
powers take their values in the open upper half-plane.
-/

noncomputable section

open Complex Set

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

open Wikipedia.HopfProblem.RiemannBoundary

theorem cornerSectorThree_re_pos {z : ℂ} (hz : z ∈ cornerSectorThree) : 0 < z.re := by
  change 0 < z.im ∧ Real.sqrt 3 * z.im < 3 * z.re at hz
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [mul_pos hsqrt hz.1]

/-- The cubic linear inequalities give the strict argument interval `(0, π / 3)`. -/
theorem cornerSectorThree_arg {z : ℂ} (hz : z ∈ cornerSectorThree) :
    z.arg ∈ Ioo 0 (Real.pi / 3) := by
  have hr := cornerSectorThree_re_pos hz
  change 0 < z.im ∧ Real.sqrt 3 * z.im < 3 * z.re at hz
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hm : Real.sqrt 3 * z.im < Real.sqrt 3 * (Real.sqrt 3 * z.re) := by
    rw [← mul_assoc, hsq]
    exact hz.2
  have him : z.im < Real.sqrt 3 * z.re := (mul_lt_mul_iff_right₀ hsqrt).mp hm
  have hargHalf : z.arg ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr))
  have hthird : Real.pi / 3 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have htan : Real.tan z.arg < Real.tan (Real.pi / 3) := by
    rw [tan_arg, Real.tan_pi_div_three]
    exact (div_lt_iff₀ hr).mpr him
  have harg0 : 0 < z.arg := by
    have hn : z.arg ≠ 0 := fun h => (ne_of_gt hz.1) (arg_eq_zero_iff.mp h).2
    exact lt_of_le_of_ne (arg_nonneg_iff.mpr hz.1.le) hn.symm
  exact ⟨harg0, (Real.strictMonoOn_tan.lt_iff_lt hargHalf hthird).mp htan⟩

/-- Cubing and taking the actual principal cubic root are inverse on the corner sector. -/
theorem cornerSectorThree_root_pow {z : ℂ} (hz : z ∈ cornerSectorThree) :
    principalRoot 3 (z ^ 3) = z := by
  apply principalRoot_pow_of_sector (by norm_num : 0 < 3)
  exact ⟨(cornerSectorThree_arg hz).1.le, (cornerSectorThree_arg hz).2.le⟩

private theorem im_pos_of_principalRoot_arg {n : ℕ} (hn : 0 < n) {z : ℂ}
    (ha : (principalRoot n z).arg ∈ Ioo 0 (Real.pi / (n : ℝ))) : 0 < z.im := by
  rw [arg_principalRoot hn] at ha
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have harg0 : 0 < z.arg := (div_pos_iff_of_pos_right hnR).mp ha.1
  have hargPi : z.arg < Real.pi := (div_lt_div_iff_of_pos_right hnR).mp ha.2
  have hz0 : z ≠ 0 := by
    intro hz
    simp only [hz, arg_zero, lt_self_iff_false] at harg0
  rw [← norm_mul_sin_arg]
  exact mul_pos (norm_pos_iff.mpr hz0)
    (Real.sin_pos_of_pos_of_lt_pi harg0 hargPi)

/-- The cubic corner power lands in the open upper half-plane. -/
theorem cornerSectorThree_pow_im_pos {z : ℂ} (hz : z ∈ cornerSectorThree) :
    0 < (z ^ 3).im := by
  apply im_pos_of_principalRoot_arg (by norm_num : 0 < 3)
  rw [cornerSectorThree_root_pow hz]
  exact cornerSectorThree_arg hz

theorem cornerSectorFour_re_pos {z : ℂ} (hz : z ∈ cornerSectorFour) : 0 < z.re := by
  change z.im < 0 ∧ 0 < z.re + z.im at hz
  linarith [hz.1, hz.2]

/-- The quartic linear inequalities give the strict argument interval `(-π / 4, 0)`. -/
theorem cornerSectorFour_arg {z : ℂ} (hz : z ∈ cornerSectorFour) :
    z.arg ∈ Ioo (-Real.pi / 4) 0 := by
  have hr := cornerSectorFour_re_pos hz
  change z.im < 0 ∧ 0 < z.re + z.im at hz
  have hargHalf : z.arg ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr))
  have hfourth : -Real.pi / 4 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have htan : Real.tan (-Real.pi / 4) < Real.tan z.arg := by
    rw [neg_div, Real.tan_neg, Real.tan_pi_div_four, tan_arg]
    apply (lt_div_iff₀ hr).mpr
    linarith [hz.2]
  exact ⟨(Real.strictMonoOn_tan.lt_iff_lt hfourth hargHalf).mp htan,
    arg_neg_iff.mpr hz.1⟩

theorem quarticRootRotation_arg : quarticRootRotation.arg = -Real.pi / 4 := by
  rw [quarticRootRotation, arg_exp_mul_I]
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  constructor <;> linarith [Real.pi_pos]

theorem quarticRootRotation_inv_arg : (quarticRootRotation⁻¹).arg = Real.pi / 4 := by
  rw [arg_inv, quarticRootRotation_arg]
  have hn : -Real.pi / 4 ≠ Real.pi := by linarith [Real.pi_pos]
  rw [if_neg hn]
  ring

/-- Undoing the fixed rotation places the quartic corner in the principal root sector. -/
theorem cornerSectorFour_unrotate_arg {z : ℂ} (hz : z ∈ cornerSectorFour) :
    (quarticRootRotation⁻¹ * z).arg ∈ Ioo 0 (Real.pi / 4) := by
  have ha := cornerSectorFour_arg hz
  have hz0 : z ≠ 0 := by
    intro h
    have hi := hz.1
    simpa only [h, zero_im, lt_self_iff_false] using hi
  have hsum : (quarticRootRotation⁻¹).arg + z.arg ∈ Ioc (-Real.pi) Real.pi := by
    rw [quarticRootRotation_inv_arg]
    constructor <;> linarith [ha.1, ha.2, Real.pi_pos]
  rw [arg_mul (inv_ne_zero quarticRootRotation_ne_zero) hz0 hsum,
    quarticRootRotation_inv_arg]
  constructor <;> linarith [ha.1, ha.2]

theorem quarticRootRotation_inv_mul_pow_four (z : ℂ) :
    (quarticRootRotation⁻¹ * z) ^ 4 = -(z ^ 4) := by
  rw [mul_pow, inv_pow, quarticRootRotation_pow_four]
  norm_num

/-- The unrotated principal fourth root recovers the original corner coordinate. -/
theorem cornerSectorFour_unrotate_root_pow {z : ℂ} (hz : z ∈ cornerSectorFour) :
    principalRoot 4 (-(z ^ 4)) = quarticRootRotation⁻¹ * z := by
  rw [← quarticRootRotation_inv_mul_pow_four]
  apply principalRoot_pow_of_sector (by norm_num : 0 < 4)
  exact ⟨(cornerSectorFour_unrotate_arg hz).1.le,
    (cornerSectorFour_unrotate_arg hz).2.le⟩

/-- The rotated principal fourth root inverts the negative fourth power on the corner. -/
theorem cornerSectorFour_root_pow {z : ℂ} (hz : z ∈ cornerSectorFour) :
    rotatedPrincipalRootFour (-(z ^ 4)) = z := by
  rw [rotatedPrincipalRootFour, cornerSectorFour_unrotate_root_pow hz,
    ← mul_assoc, mul_inv_cancel₀ quarticRootRotation_ne_zero, one_mul]

/-- The negative fourth power of the quartic corner lands in the open upper half-plane. -/
theorem cornerSectorFour_pow_im_pos {z : ℂ} (hz : z ∈ cornerSectorFour) :
    0 < (-(z ^ 4)).im := by
  apply im_pos_of_principalRoot_arg (by norm_num : 0 < 4)
  rw [cornerSectorFour_unrotate_root_pow hz]
  exact cornerSectorFour_unrotate_arg hz

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
