import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Tactic.Ring

/-!
# A continuous square-subdivision coordinate

The two clamped affine coordinates give one continuous formula for the warp
used to identify a square subdivision with native loop concatenation.
-/

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

/-- The continuous warp interpolating between the two clamped subdivision
coordinates. Its branch formulas use exactly the coordinates of `GenLoop.transAt`. -/
noncomputable def subdivisionWarpCoordinate : C(I × I, I) where
  toFun p := Set.Icc.convexComb
    (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
    (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ))) p.1
  continuous_toFun := by
    unfold Set.Icc.convexComb
    fun_prop

theorem subdivisionWarpCoordinate_apply (u v : I) :
    subdivisionWarpCoordinate (u, v) = Set.Icc.convexComb
      (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1))
      (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ))) u := rfl

@[simp]
theorem subdivisionWarpCoordinate_zero (u : I) :
    subdivisionWarpCoordinate (u, 0) = 0 := by
  simp [subdivisionWarpCoordinate, Set.projIcc, Set.Icc.convexComb]

@[simp]
theorem subdivisionWarpCoordinate_one (u : I) :
    subdivisionWarpCoordinate (u, 1) = 1 := by
  norm_num [subdivisionWarpCoordinate, Set.projIcc, Set.Icc.convexComb]

/-- On the first half, the lower clamped coordinate is zero. -/
theorem subdivisionWarpCoordinate_of_le_half (u v : I) (hv : (v : ℝ) ≤ 1 / 2) :
    subdivisionWarpCoordinate (u, v) =
      u * Set.projIcc 0 1 zero_le_one (2 * (v : ℝ)) := by
  have hzero : Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1) = (0 : I) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [subdivisionWarpCoordinate_apply, hzero]
  apply Subtype.ext
  simp

/-- On the second half, the upper clamped coordinate is one. -/
theorem subdivisionWarpCoordinate_of_half_le (u v : I) (hv : 1 / 2 ≤ (v : ℝ)) :
    subdivisionWarpCoordinate (u, v) = Set.Icc.convexComb u 1
      (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1)) := by
  have hone : Set.projIcc 0 1 zero_le_one (2 * (v : ℝ)) = (1 : I) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  rw [subdivisionWarpCoordinate_apply, hone]
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb]
  change (1 - (u : ℝ)) * _ + (u : ℝ) * 1 =
    (1 - _) * (u : ℝ) + _ * 1
  ring

theorem subdivisionWarpCoordinate_of_half_lt (u v : I) (hv : 1 / 2 < (v : ℝ)) :
    subdivisionWarpCoordinate (u, v) = Set.Icc.convexComb u 1
      (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1)) :=
  subdivisionWarpCoordinate_of_half_le u v hv.le

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
