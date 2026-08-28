import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Tactic.Ring

/-!
# The continuous coordinate for three consecutive cube slices

Nested convex combinations give one continuous formula on all pairs of
interval points. The clamped coordinates reduce to the exact three branches
of `transAt 2 (transAt 2 L M) U`, without any piecewise continuity argument.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

/-- The three-slice warp. Its first two slices occupy quarters of the
parameter interval, and its third slice occupies the remaining half. -/
def subdivisionWarpThreeCoordinate : C((I × I) × I, I) where
  toFun p := Set.Icc.convexComb
    (p.1.1 * Set.projIcc 0 1 zero_le_one (4 * (p.2 : ℝ)))
    (Set.Icc.convexComb p.1.2 1
      (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1)))
    (Set.projIcc 0 1 zero_le_one (4 * (p.2 : ℝ) - 1))
  continuous_toFun := by
    unfold Set.Icc.convexComb
    fun_prop

theorem subdivisionWarpThreeCoordinate_apply (a b w : I) :
    subdivisionWarpThreeCoordinate ((a, b), w) = Set.Icc.convexComb
      (a * Set.projIcc 0 1 zero_le_one (4 * (w : ℝ)))
      (Set.Icc.convexComb b 1 (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ) - 1)))
      (Set.projIcc 0 1 zero_le_one (4 * (w : ℝ) - 1)) := rfl

@[simp] theorem subdivisionWarpThreeCoordinate_zero (a b : I) :
    subdivisionWarpThreeCoordinate ((a, b), 0) = 0 := by
  norm_num [subdivisionWarpThreeCoordinate, Set.projIcc, Set.Icc.convexComb]

@[simp] theorem subdivisionWarpThreeCoordinate_one (a b : I) :
    subdivisionWarpThreeCoordinate ((a, b), 1) = 1 := by
  norm_num [subdivisionWarpThreeCoordinate, Set.projIcc, Set.Icc.convexComb]

/-- The first quarter is the segment from zero to `a`. -/
theorem subdivisionWarpThreeCoordinate_of_le_quarter (a b w : I)
    (hw : (w : ℝ) ≤ 1 / 4) :
    subdivisionWarpThreeCoordinate ((a, b), w) =
      a * Set.projIcc 0 1 zero_le_one (4 * (w : ℝ)) := by
  have hz : Set.projIcc 0 1 zero_le_one (4 * (w : ℝ) - 1) = (0 : I) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [subdivisionWarpThreeCoordinate_apply, hz, Set.Icc.convexComb_zero]

/-- The second quarter is the segment from `a` to `b`. -/
theorem subdivisionWarpThreeCoordinate_of_quarter_le_of_le_half (a b w : I)
    (hl : 1 / 4 ≤ (w : ℝ)) (hu : (w : ℝ) ≤ 1 / 2) :
    subdivisionWarpThreeCoordinate ((a, b), w) = Set.Icc.convexComb a b
      (Set.projIcc 0 1 zero_le_one (4 * (w : ℝ) - 1)) := by
  have hone : Set.projIcc 0 1 zero_le_one (4 * (w : ℝ)) = (1 : I) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  have hzero : Set.projIcc 0 1 zero_le_one (2 * (w : ℝ) - 1) = (0 : I) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [subdivisionWarpThreeCoordinate_apply, hone, hzero, mul_one,
    Set.Icc.convexComb_zero]

/-- The last half is the segment from `b` to one. -/
theorem subdivisionWarpThreeCoordinate_of_half_le (a b w : I)
    (hw : 1 / 2 ≤ (w : ℝ)) :
    subdivisionWarpThreeCoordinate ((a, b), w) = Set.Icc.convexComb b 1
      (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ) - 1)) := by
  have hone : Set.projIcc 0 1 zero_le_one (4 * (w : ℝ) - 1) = (1 : I) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  rw [subdivisionWarpThreeCoordinate_apply, hone, Set.Icc.convexComb_one]

theorem subdivisionWarpThreeCoordinate_of_half_lt (a b w : I)
    (hw : 1 / 2 < (w : ℝ)) :
    subdivisionWarpThreeCoordinate ((a, b), w) = Set.Icc.convexComb b 1
      (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ) - 1)) :=
  subdivisionWarpThreeCoordinate_of_half_le a b w hw.le

/-- The outer first-half clamp is literally the doubled real coordinate. -/
theorem subdivisionWarpThree_clip_two_coe (w : I) (hw : (w : ℝ) ≤ 1 / 2) :
    (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ) = 2 * (w : ℝ) := by
  have hmem : 2 * (w : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [w.property.1], by linarith⟩
  exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hmem)

/-- The exact first branch of nested native concatenation. -/
theorem subdivisionWarpThreeCoordinate_nested_lower (a b w : I)
    (hw : (w : ℝ) ≤ 1 / 2)
    (hi : (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ) ≤ 1 / 2) :
    subdivisionWarpThreeCoordinate ((a, b), w) = a *
      Set.projIcc 0 1 zero_le_one
        (2 * (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ)) := by
  have hc := subdivisionWarpThree_clip_two_coe w hw
  have hquarter : (w : ℝ) ≤ 1 / 4 := by rw [hc] at hi; linarith
  have he : 2 * (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ) =
      4 * (w : ℝ) := by rw [hc]; ring
  rw [he]
  exact subdivisionWarpThreeCoordinate_of_le_quarter a b w hquarter

/-- The exact middle branch of nested native concatenation. -/
theorem subdivisionWarpThreeCoordinate_nested_middle (a b w : I)
    (hw : (w : ℝ) ≤ 1 / 2)
    (hi : 1 / 2 < (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ)) :
    subdivisionWarpThreeCoordinate ((a, b), w) = Set.Icc.convexComb a b
      (Set.projIcc 0 1 zero_le_one
        (2 * (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ) - 1)) := by
  have hc := subdivisionWarpThree_clip_two_coe w hw
  have hquarter : 1 / 4 ≤ (w : ℝ) := by rw [hc] at hi; linarith
  have he : 2 * (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ) - 1 =
      4 * (w : ℝ) - 1 := by rw [hc]; ring
  rw [he]
  exact subdivisionWarpThreeCoordinate_of_quarter_le_of_le_half a b w hquarter hw

/-- The exact upper branch of nested native concatenation. -/
theorem subdivisionWarpThreeCoordinate_nested_upper (a b w : I)
    (hw : 1 / 2 < (w : ℝ)) :
    subdivisionWarpThreeCoordinate ((a, b), w) = Set.Icc.convexComb b 1
      (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ) - 1)) :=
  subdivisionWarpThreeCoordinate_of_half_lt a b w hw

end Wikipedia.HopfProblem.ThirdHurewicz
