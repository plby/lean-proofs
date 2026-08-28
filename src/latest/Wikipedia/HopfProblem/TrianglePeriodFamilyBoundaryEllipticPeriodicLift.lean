import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticPeriodicLiftCore
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticPeriodicLiftClockwise

/-!
# The full real final edge in the original native deck frame

Covering uniqueness compares the entire final real edge of the lifted
attaching square with the normalized clockwise real lift. The deck frame
is exactly the one already determined by the original unit square. This
also packages the actual upstairs homotopy, retaining every unit-square
value and every integer deck transformation.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle Meridians BoundaryLoopSquares
open SpecialPeriods.EllipticAttachingMeridians
open SpecialPeriods.Threefold.EllipticGeometry

/-- The entire final real edge, not only its unit restriction, has the original native frame. -/
theorem chosenAttachingPeriodicSquareLift_final (j : Elliptic.Kind) (t : ℝ) :
    chosenAttachingPeriodicSquareLift j (1, t) =
      nativeTailFrame j • clockwisePeriodicLift (attachingMeridianIndex j) t := by
  have hleft : Continuous (fun u : ℝ => chosenAttachingPeriodicSquareLift j (1, u)) :=
    (chosenAttachingPeriodicSquareLift j).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hright : Continuous (fun u : ℝ =>
      nativeTailFrame j • clockwisePeriodicLift (attachingMeridianIndex j) u) :=
    (continuous_const_smul (nativeTailFrame j)).comp
      (clockwisePeriodicLift (attachingMeridianIndex j)).continuous
  have he : triangleRegularProject ∘
      (fun u : ℝ => chosenAttachingPeriodicSquareLift j (1, u)) =
      triangleRegularProject ∘ (fun u : ℝ =>
        nativeTailFrame j • clockwisePeriodicLift (attachingMeridianIndex j) u) := by
    funext u
    simp only [Function.comp_apply, chosenAttachingPeriodicSquareLift_projection,
      chosenAttachingPeriodicHomotopy_final, triangleRegularProject_covering.map_smul,
      clockwisePeriodicLift_projection]
  have hzero : chosenAttachingPeriodicSquareLift j (1, 0) =
      nativeTailFrame j • clockwisePeriodicLift (attachingMeridianIndex j) 0 := by
    rw [clockwisePeriodicLift_zero]
    exact chosenAttachingPeriodicSquareLift_frame j
  exact congr_fun (triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
    hleft hright he 0 hzero) t

/-- The actual final real curve as a continuous map, with its original deck frame retained. -/
def chosenAttachingPeriodicFinalLift (j : Elliptic.Kind) : C(ℝ, TriangleRegularPoint) :=
  baseHomotopySlice (chosenAttachingPeriodicSquareLift j) 1

@[simp] theorem chosenAttachingPeriodicFinalLift_apply (j : Elliptic.Kind) (t : ℝ) :
    chosenAttachingPeriodicFinalLift j t = chosenAttachingPeriodicSquareLift j (1, t) := rfl

theorem chosenAttachingPeriodicFinalLift_frame (j : Elliptic.Kind) (t : ℝ) :
    chosenAttachingPeriodicFinalLift j t =
      nativeTailFrame j • clockwisePeriodicLift (attachingMeridianIndex j) t :=
  chosenAttachingPeriodicSquareLift_final j t

@[simp] theorem chosenAttachingPeriodicFinalLift_projection (j : Elliptic.Kind) (t : ℝ) :
    triangleRegularProject (chosenAttachingPeriodicFinalLift j t) =
      loopPeriodic (clockwiseRegularMeridian (attachingMeridianIndex j)) t :=
  (chosenAttachingPeriodicSquareLift_projection j 1 t).trans
    (chosenAttachingPeriodicHomotopy_final j t)

@[simp] theorem chosenAttachingPeriodicFinalLift_unit (j : Elliptic.Kind) (t : unitInterval) :
    chosenAttachingPeriodicFinalLift j (t : ℝ) =
      nativeTailFrame j • clockwiseFinalLift (attachingMeridianIndex j) t :=
  chosenAttachingPeriodicSquareLift_final_unit j t

theorem chosenAttachingPeriodicFinalLift_translate
    (j : Elliptic.Kind) (k : ℤ) (t : ℝ) :
    chosenAttachingPeriodicFinalLift j (t + k) =
      ((ellipticGenerator j)⁻¹ ^ (-k)) • chosenAttachingPeriodicFinalLift j t :=
  chosenAttachingPeriodicSquareLift_translate j 1 k t

theorem chosenAttachingPeriodicFinalLift_add_int
    (j : Elliptic.Kind) (t : ℝ) (k : ℤ) :
    chosenAttachingPeriodicFinalLift j (t + (k : ℝ)) =
      (ellipticGenerator j ^ k) • chosenAttachingPeriodicFinalLift j t :=
  chosenAttachingPeriodicSquareLift_add_int j 1 t k

/-- The actual upstairs continuous homotopy between the original and final real lifts. -/
def chosenAttachingLiftedPeriodicHomotopy (j : Elliptic.Kind) :
    (chosenAttachingPeriodicLift j).Homotopy (chosenAttachingPeriodicFinalLift j) where
  toFun := chosenAttachingPeriodicSquareLift j
  continuous_toFun := (chosenAttachingPeriodicSquareLift j).continuous
  map_zero_left := chosenAttachingPeriodicSquareLift_zero j
  map_one_left _ := rfl

@[simp] theorem chosenAttachingLiftedPeriodicHomotopy_unit
    (j : Elliptic.Kind) (s t : unitInterval) :
    chosenAttachingLiftedPeriodicHomotopy j (s, (t : ℝ)) =
      chosenNativeSquareLift j (s, t) :=
  chosenAttachingPeriodicSquareLift_unit j s t

theorem chosenAttachingLiftedPeriodicHomotopy_add_int
    (j : Elliptic.Kind) (s : unitInterval) (t : ℝ) (k : ℤ) :
    chosenAttachingLiftedPeriodicHomotopy j (s, t + (k : ℝ)) =
      (ellipticGenerator j ^ k) • chosenAttachingLiftedPeriodicHomotopy j (s, t) :=
  chosenAttachingPeriodicSquareLift_add_int j s t k

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
