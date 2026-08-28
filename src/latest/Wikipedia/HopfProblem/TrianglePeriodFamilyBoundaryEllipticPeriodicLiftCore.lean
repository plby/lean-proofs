import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryLiftedCurve
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticFrames
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryLoopSquares

/-!
# Actual periodic lifts of the chosen elliptic attaching square

Lift the actual periodic extension of the chosen attaching loop from its
original native root point. Covering uniqueness identifies its complete
unit-interval restriction with the original root path. Its actual endpoint
then determines every integer translate. Lifting the periodic square from
that entire real curve retains the original square lift on the unit square,
including its actual final deck frame, without an orientation assumption.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle Meridians BoundaryLoopSquares
open SpecialPeriods.EllipticAttachingMeridians
open SpecialPeriods.Threefold.EllipticGeometry

/-- The periodic attaching curve starts under the original native root point. -/
theorem chosenAttachingPeriodicBasepoint (j : Elliptic.Kind) :
    triangleRegularProject (chosenNativeLift j 0) =
      loopPeriodic (chosenAttachingBaseLoop j) 0 := by
  rw [loopPeriodic_zero]
  exact (chosenNativeLift_projection j 0).trans (chosenAttachingBaseLoop j).source

/-- The actual real-time covering lift normalized at the original native root point. -/
def chosenAttachingPeriodicLift (j : Elliptic.Kind) : C(ℝ, TriangleRegularPoint) :=
  realCurveLift (loopPeriodic (chosenAttachingBaseLoop j)) (chosenNativeLift j 0)
    (chosenAttachingPeriodicBasepoint j)

@[simp] theorem chosenAttachingPeriodicLift_zero (j : Elliptic.Kind) :
    chosenAttachingPeriodicLift j 0 = chosenNativeLift j 0 :=
  realCurveLift_zero _ _ _

@[simp] theorem chosenAttachingPeriodicLift_projection (j : Elliptic.Kind) (t : ℝ) :
    triangleRegularProject (chosenAttachingPeriodicLift j t) =
      loopPeriodic (chosenAttachingBaseLoop j) t :=
  realCurveLift_projection _ _ _ t

/-- Uniqueness identifies every unit-interval value with the literal native lift. -/
@[simp] theorem chosenAttachingPeriodicLift_unit (j : Elliptic.Kind) (t : unitInterval) :
    chosenAttachingPeriodicLift j (t : ℝ) = chosenNativeLift j t := by
  have he : triangleRegularProject ∘
      (fun u : unitInterval => chosenAttachingPeriodicLift j (u : ℝ)) =
      triangleRegularProject ∘ chosenNativeLift j := by
    funext u
    simp only [Function.comp_apply, chosenAttachingPeriodicLift_projection,
      loopPeriodic_unit, chosenNativeLift_projection]
  exact congr_fun (triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
    ((chosenAttachingPeriodicLift j).continuous.comp continuous_subtype_val)
    (chosenNativeLift j).continuous he 0 (chosenAttachingPeriodicLift_zero j)) t

/-- The real lift has the endpoint dictated by the actual native root rotation. -/
theorem chosenAttachingPeriodicLift_one (j : Elliptic.Kind) :
    chosenAttachingPeriodicLift j 1 =
      ellipticGenerator j • chosenAttachingPeriodicLift j 0 := by
  rw [chosenAttachingPeriodicLift_zero]
  exact (chosenAttachingPeriodicLift_unit j 1).trans (chosenNativeLift_one j)

/-- Integer deck equivariance in the convention used for the family cylinder. -/
theorem chosenAttachingPeriodicLift_translate (j : Elliptic.Kind) (k : ℤ) (t : ℝ) :
    chosenAttachingPeriodicLift j (t + k) =
      ((ellipticGenerator j)⁻¹ ^ (-k)) • chosenAttachingPeriodicLift j t := by
  apply realCurveLift_translate (loopPeriodic (chosenAttachingBaseLoop j))
    (chosenNativeLift j 0) (chosenAttachingPeriodicBasepoint j)
    (loopPeriodic_add_one (chosenAttachingBaseLoop j)) (ellipticGenerator j)⁻¹ _ k t
  change chosenAttachingPeriodicLift j 1 =
    ((ellipticGenerator j)⁻¹)⁻¹ • chosenNativeLift j 0
  rw [inv_inv]
  exact (chosenAttachingPeriodicLift_unit j 1).trans (chosenNativeLift_one j)

/-- The original positive native root path gives the literal positive integer powers. -/
theorem chosenAttachingPeriodicLift_add_int (j : Elliptic.Kind) (t : ℝ) (k : ℤ) :
    chosenAttachingPeriodicLift j (t + (k : ℝ)) =
      (ellipticGenerator j ^ k) • chosenAttachingPeriodicLift j t := by
  simpa only [inv_zpow, zpow_neg, inv_inv] using
    chosenAttachingPeriodicLift_translate j k t

theorem chosenAttachingPeriodicLift_int (j : Elliptic.Kind) (k : ℤ) :
    chosenAttachingPeriodicLift j (k : ℝ) =
      (ellipticGenerator j ^ k) • chosenNativeLift j 0 := by
  simpa only [zero_add, chosenAttachingPeriodicLift_zero] using
    chosenAttachingPeriodicLift_add_int j 0 k

/-- The entire chosen real lift is the prescribed initial edge of the periodic square. -/
theorem chosenAttachingPeriodicHomotopy_initialLift (j : Elliptic.Kind) (t : ℝ) :
    chosenAttachingPeriodicHomotopy j (0, t) =
      triangleRegularProject (chosenAttachingPeriodicLift j t) :=
  (chosenAttachingPeriodicHomotopy_initial j t).trans
    (chosenAttachingPeriodicLift_projection j t).symm

/-- Lift the actual periodic square from the entire original-frame real lift. -/
def chosenAttachingPeriodicSquareLift (j : Elliptic.Kind) :
    C(unitInterval × ℝ, TriangleRegularPoint) :=
  baseHomotopyLift (chosenAttachingPeriodicHomotopy j).toContinuousMap
    (chosenAttachingPeriodicLift j) (chosenAttachingPeriodicHomotopy_initialLift j)

@[simp] theorem chosenAttachingPeriodicSquareLift_zero (j : Elliptic.Kind) (t : ℝ) :
    chosenAttachingPeriodicSquareLift j (0, t) = chosenAttachingPeriodicLift j t :=
  baseHomotopyLift_zero _ _ _ t

@[simp] theorem chosenAttachingPeriodicSquareLift_projection
    (j : Elliptic.Kind) (s : unitInterval) (t : ℝ) :
    triangleRegularProject (chosenAttachingPeriodicSquareLift j (s, t)) =
      chosenAttachingPeriodicHomotopy j (s, t) :=
  baseHomotopyLift_projection _ _ _ s t

/-- The full unit-square restriction is exactly the previously chosen native square lift. -/
@[simp] theorem chosenAttachingPeriodicSquareLift_unit
    (j : Elliptic.Kind) (s t : unitInterval) :
    chosenAttachingPeriodicSquareLift j (s, (t : ℝ)) =
      chosenNativeSquareLift j (s, t) := by
  have hleft : Continuous (fun u : unitInterval =>
      chosenAttachingPeriodicSquareLift j (u, (t : ℝ))) :=
    (chosenAttachingPeriodicSquareLift j).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hright : Continuous (fun u : unitInterval => chosenNativeSquareLift j (u, t)) :=
    (chosenNativeSquareLift j).continuous.comp (continuous_id.prodMk continuous_const)
  have he : triangleRegularProject ∘
      (fun u : unitInterval => chosenAttachingPeriodicSquareLift j (u, (t : ℝ))) =
      triangleRegularProject ∘ (fun u : unitInterval => chosenNativeSquareLift j (u, t)) := by
    funext u
    exact (chosenAttachingPeriodicSquareLift_projection j u t).trans
      ((chosenAttachingPeriodicHomotopy_unit j u t).trans
        (loopSquareLift_projection (chosenAttachingSquare j) (chosenNativeLift j)
          (chosenNativeLift_projection j) u t).symm)
  have hzero : chosenAttachingPeriodicSquareLift j (0, (t : ℝ)) =
      chosenNativeSquareLift j (0, t) :=
    (chosenAttachingPeriodicSquareLift_zero j t).trans
      ((chosenAttachingPeriodicLift_unit j t).trans
        (loopSquareLift_zero (chosenAttachingSquare j) (chosenNativeLift j)
          (chosenNativeLift_projection j) t).symm)
  exact congr_fun (triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
    hleft hright he 0 hzero) s

/-- The actual final path retains the exact native tail frame. -/
theorem chosenAttachingPeriodicSquareLift_final_unit
    (j : Elliptic.Kind) (t : unitInterval) :
    chosenAttachingPeriodicSquareLift j (1, (t : ℝ)) =
      nativeTailFrame j • clockwiseFinalLift (attachingMeridianIndex j) t :=
  (chosenAttachingPeriodicSquareLift_unit j 1 t).trans (chosenNativeSquareLift_final j t)

@[simp] theorem chosenAttachingPeriodicSquareLift_tail (j : Elliptic.Kind) (s : unitInterval) :
    chosenAttachingPeriodicSquareLift j (s, 0) = chosenNativeSquareLift j (s, 0) :=
  chosenAttachingPeriodicSquareLift_unit j s 0

/-- The actual final point is in the original, geometrically determined deck frame. -/
theorem chosenAttachingPeriodicSquareLift_frame (j : Elliptic.Kind) :
    chosenAttachingPeriodicSquareLift j (1, 0) =
      nativeTailFrame j • normalizedRegularMeridianBasepoint :=
  (chosenAttachingPeriodicSquareLift_tail j 1).trans (nativeTailFrame_apply j)

/-- The original deck relation is preserved at every actual homotopy time. -/
theorem chosenAttachingPeriodicSquareLift_translate
    (j : Elliptic.Kind) (s : unitInterval) (k : ℤ) (t : ℝ) :
    chosenAttachingPeriodicSquareLift j (s, t + k) =
      ((ellipticGenerator j)⁻¹ ^ (-k)) • chosenAttachingPeriodicSquareLift j (s, t) :=
  baseHomotopyLift_translate (chosenAttachingPeriodicHomotopy j).toContinuousMap
    (chosenAttachingPeriodicLift j) (chosenAttachingPeriodicHomotopy_initialLift j)
    (ellipticGenerator j)⁻¹ (fun u k v => chosenAttachingPeriodicHomotopy_add_int j u v k)
    (chosenAttachingPeriodicLift_translate j) s k t

theorem chosenAttachingPeriodicSquareLift_add_int
    (j : Elliptic.Kind) (s : unitInterval) (t : ℝ) (k : ℤ) :
    chosenAttachingPeriodicSquareLift j (s, t + (k : ℝ)) =
      (ellipticGenerator j ^ k) • chosenAttachingPeriodicSquareLift j (s, t) := by
  simpa only [inv_zpow, zpow_neg, inv_inv] using
    chosenAttachingPeriodicSquareLift_translate j s k t

/-- Every integer-time edge remains the corresponding translate of the original lifted tail. -/
theorem chosenAttachingPeriodicSquareLift_int
    (j : Elliptic.Kind) (s : unitInterval) (k : ℤ) :
    chosenAttachingPeriodicSquareLift j (s, (k : ℝ)) =
      (ellipticGenerator j ^ k) • chosenNativeSquareLift j (s, 0) := by
  simpa only [zero_add, chosenAttachingPeriodicSquareLift_tail] using
    chosenAttachingPeriodicSquareLift_add_int j s 0 k

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
