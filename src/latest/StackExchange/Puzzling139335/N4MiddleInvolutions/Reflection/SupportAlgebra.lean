import StackExchange.Puzzling139335.Definitions

/-!
# Support-line arithmetic for a reflected pair

Two distinct contacts with a lower supporting line constrain its normal
when the region lies above a unit base. These facts need no topological
or convexity assumptions on the region.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.Reflection

/-- The linear functional with normal vector `ν`. -/
def normalValue (ν x : Plane) : ℝ := ν 0 * x 0 + ν 1 * x 1

theorem continuous_normalValue (ν : Plane) : Continuous (normalValue ν) :=
  (continuous_const.mul (EuclideanSpace.proj 0).continuous).add
    (continuous_const.mul (EuclideanSpace.proj 1).continuous)

@[simp] theorem normalValue_corner_zero (ν : Plane) :
    normalValue ν (corner 0) = 0 := by
  norm_num [normalValue, corner, Fin.ext_iff]

@[simp] theorem normalValue_corner_one (ν : Plane) :
    normalValue ν (corner 1) = ν 0 := by
  norm_num [normalValue, corner, Fin.ext_iff]

@[simp] theorem normalValue_neg_left (ν x : Plane) :
    normalValue (-ν) x = -normalValue ν x := by
  simp only [normalValue, PiLp.neg_apply]
  ring

@[simp] theorem normalValue_neg_right (ν x : Plane) :
    normalValue ν (-x) = -normalValue ν x := by
  simp only [normalValue, PiLp.neg_apply]
  ring

private theorem eq_bottomLeft_of_positive_normal {ν x : Plane}
    (hνx : 0 < ν 0) (hνy : 0 < ν 1)
    (hx : 0 ≤ x 0) (hy : 0 ≤ x 1) (hlevel : normalValue ν x ≤ 0) :
    x = corner 0 := by
  change ν 0 * x 0 + ν 1 * x 1 ≤ 0 at hlevel
  have hmulx := mul_nonneg hνx.le hx
  have hmuly := mul_nonneg hνy.le hy
  have hxzero : ν 0 * x 0 = 0 := by linarith
  have hyzero : ν 1 * x 1 = 0 := by linarith
  have hx' := (mul_eq_zero.mp hxzero).resolve_left (ne_of_gt hνx)
  have hy' := (mul_eq_zero.mp hyzero).resolve_left (ne_of_gt hνy)
  ext i
  fin_cases i
  · exact hx'
  · exact hy'

private theorem eq_bottomRight_of_negative_normal {ν x : Plane}
    (hνx : ν 0 < 0) (hνy : 0 < ν 1)
    (hx : x 0 ≤ 1) (hy : 0 ≤ x 1) (hlevel : normalValue ν x ≤ ν 0) :
    x = corner 1 := by
  change ν 0 * x 0 + ν 1 * x 1 ≤ ν 0 at hlevel
  have hmulx : 0 ≤ ν 0 * (x 0 - 1) :=
    mul_nonneg_of_nonpos_of_nonpos hνx.le (sub_nonpos.mpr hx)
  have hmuly := mul_nonneg hνy.le hy
  have hxzero : ν 0 * (x 0 - 1) = 0 := by nlinarith
  have hyzero : ν 1 * x 1 = 0 := by nlinarith
  have hx' := sub_eq_zero.mp ((mul_eq_zero.mp hxzero).resolve_left (ne_of_lt hνx))
  have hy' := (mul_eq_zero.mp hyzero).resolve_left (ne_of_gt hνy)
  ext i
  fin_cases i
  · exact hx'
  · exact hy'

/-- With a positive upward normal, a lower supporting line can contain two
distinct points of a region above the unit base only if it is the base line. -/
theorem support_two_contacts {P : Set Plane} {ν : Plane} {c : ℝ} {p q : Plane}
    (hνy : 0 < ν 1)
    (hstrip : ∀ x ∈ P, 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1)
    (hbl : corner 0 ∈ P) (hbr : corner 1 ∈ P)
    (hsupport : ∀ x ∈ P, c ≤ normalValue ν x)
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q)
    (hpc : normalValue ν p = c) (hqc : normalValue ν q = c) :
    ν 0 = 0 ∧ c = 0 := by
  have hc0 : c ≤ 0 := by simpa using hsupport (corner 0) hbl
  have hcνx : c ≤ ν 0 := by simpa using hsupport (corner 1) hbr
  have hνxzero : ν 0 = 0 := by
    by_contra hνxzero
    rcases lt_or_gt_of_ne hνxzero with hνx | hνx
    · have hp' := eq_bottomRight_of_negative_normal hνx hνy
        (hstrip p hp).2.1 (hstrip p hp).2.2 (hpc.le.trans hcνx)
      have hq' := eq_bottomRight_of_negative_normal hνx hνy
        (hstrip q hq).2.1 (hstrip q hq).2.2 (hqc.le.trans hcνx)
      exact hpq (hp'.trans hq'.symm)
    · have hp' := eq_bottomLeft_of_positive_normal hνx hνy
        (hstrip p hp).1 (hstrip p hp).2.2 (hpc.le.trans hc0)
      have hq' := eq_bottomLeft_of_positive_normal hνx hνy
        (hstrip q hq).1 (hstrip q hq).2.2 (hqc.le.trans hc0)
      exact hpq (hp'.trans hq'.symm)
  refine ⟨hνxzero, le_antisymm hc0 ?_⟩
  rw [← hpc, normalValue, hνxzero, zero_mul, zero_add]
  exact mul_nonneg hνy.le (hstrip p hp).2.2

/-- Reflection in the unit-normal line reverses the signed normal coordinate. -/
theorem normalValue_reflect (ν x : Plane) (c : ℝ)
    (hunit : ν 0 ^ 2 + ν 1 ^ 2 = 1) :
    normalValue ν (x - (2 * (normalValue ν x - c)) • ν) =
      2 * c - normalValue ν x := by
  simp only [normalValue, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  linear_combination -(2 * (ν 0 * x 0 + ν 1 * x 1 - c)) * hunit

/-- Reversing the normal and offset leaves the reflection formula unchanged. -/
theorem reflect_formula_neg (ν x : Plane) (c : ℝ) :
    x - (2 * (normalValue (-ν) x - (-c))) • (-ν) =
      x - (2 * (normalValue ν x - c)) • ν := by
  ext i
  simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply,
    smul_eq_mul, normalValue_neg_left]
  ring

/-- A supporting normal with nonpositive upward component reflects every
point above the base to another point above the base. -/
theorem reflect_y_nonneg {ν x : Plane} {c : ℝ}
    (hνy : ν 1 ≤ 0) (hy : 0 ≤ x 1) (hsupport : c ≤ normalValue ν x) :
    0 ≤ (x - (2 * (normalValue ν x - c)) • ν) 1 := by
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  have hfactor : 0 ≤ 2 * (normalValue ν x - c) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr hsupport)
  have hproduct := mul_nonpos_of_nonneg_of_nonpos hfactor hνy
  linarith

end Puzzling139335.N4MiddleInvolutions.Reflection
