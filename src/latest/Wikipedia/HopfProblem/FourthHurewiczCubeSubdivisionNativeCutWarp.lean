import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# A continuous binary warp between three interval points

The nested convex combination follows the segment from `a` to `b` on the
first half of the parameter interval and from `b` to `c` on the second half.
The formula is jointly continuous without any ordering hypotheses on the
three points, including when consecutive points coincide.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

/-- The continuous coordinate used to concatenate two adjacent cube slices. -/
def cutBinaryWarp : C((I × I × I) × I, I) where
  toFun p := Set.Icc.convexComb
    (Set.Icc.convexComb p.1.1 p.1.2.1
      (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ))))
    p.1.2.2 (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
  continuous_toFun := by
    unfold Set.Icc.convexComb
    fun_prop

theorem cutBinaryWarp_apply (a b c t : I) :
    cutBinaryWarp ((a, b, c), t) = Set.Icc.convexComb
      (Set.Icc.convexComb a b (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))))
      c (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) := rfl

@[simp] theorem cutBinaryWarp_zero (a b c : I) :
    cutBinaryWarp ((a, b, c), 0) = a := by
  norm_num [cutBinaryWarp, Set.projIcc, Set.Icc.convexComb]

@[simp] theorem cutBinaryWarp_one (a b c : I) :
    cutBinaryWarp ((a, b, c), 1) = c := by
  norm_num [cutBinaryWarp, Set.projIcc, Set.Icc.convexComb]

/-- On the first half, the warp follows the first segment. -/
theorem cutBinaryWarp_of_le_half (a b c t : I) (ht : (t : ℝ) ≤ 1 / 2) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb a b (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))) := by
  have hz : Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1) = (0 : I) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [cutBinaryWarp_apply, hz, Set.Icc.convexComb_zero]

/-- On the second half, the warp follows the second segment. -/
theorem cutBinaryWarp_of_half_le (a b c t : I) (ht : 1 / 2 ≤ (t : ℝ)) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb b c (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) := by
  have ho : Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)) = (1 : I) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  rw [cutBinaryWarp_apply, ho, Set.Icc.convexComb_one]

theorem cutBinaryWarp_of_half_lt (a b c t : I) (ht : 1 / 2 < (t : ℝ)) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb b c (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) :=
  cutBinaryWarp_of_half_le a b c t ht.le

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
