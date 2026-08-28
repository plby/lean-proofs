import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspOuterHomotopy
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryLoopSquaresHomotopy
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryLiftedHomotopy

/-!
# The entire actual periodic cusp homotopy and its covering lift

The genuine native-to-outer loop square extends periodically to every
real boundary time.  Its actual covering-homotopy lift starts at the
original logarithmic curve and retains the same inverse cusp-generator
deck transformation at every homotopy parameter.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

open SpecialPeriods SpecialPeriods.Triangle ThreefoldOverlapMappingTorus.Cusp
open BoundaryLoopSquares

/-- The periodic extension of the actual native loop is its literal original real curve. -/
theorem projectedCurve_eq_periodic (h : Height specialData.radius) :
    (projectedCurve h : ℝ → TriangleRegularQuotient) = loopPeriodic (nativeLoop h) :=
  loopPeriodic_unique (projectedCurve h) (baseLift_projection_periodic h) (fun _ => rfl)

/-- The complete actual cusp square, now with real periodic boundary time. -/
def nativePeriodicSquare : C(unitInterval × ℝ, TriangleRegularQuotient) :=
  periodicSquare nativeOuterSquare

@[simp] theorem nativePeriodicSquare_zero (t : ℝ) :
    nativePeriodicSquare (0, t) = triangleRegularProject (baseLift controlledHeight t) :=
  (periodicSquare_initial nativeOuterSquare t).trans
    (congrFun (projectedCurve_eq_periodic controlledHeight) t).symm

@[simp] theorem nativePeriodicSquare_unit (s t : unitInterval) :
    nativePeriodicSquare (s, (t : ℝ)) = nativeOuterSquare.map (s, t) :=
  periodicSquare_unit nativeOuterSquare s t

theorem nativePeriodicSquare_translate (s : unitInterval) (k : ℤ) (t : ℝ) :
    nativePeriodicSquare (s, t + k) = nativePeriodicSquare (s, t) :=
  periodicSquare_add_int nativeOuterSquare s t k

/-- Lift the whole actual periodic square from the original native logarithmic curve. -/
def nativeLiftedSquare : C(unitInterval × ℝ, TriangleRegularPoint) :=
  baseHomotopyLift nativePeriodicSquare (baseLift controlledHeight) nativePeriodicSquare_zero

@[simp] theorem nativeLiftedSquare_zero (t : ℝ) :
    nativeLiftedSquare (0, t) = baseLift controlledHeight t :=
  baseHomotopyLift_zero nativePeriodicSquare (baseLift controlledHeight)
    nativePeriodicSquare_zero t

/-- Its projection is the genuine homotopy at every point, not merely on the edges. -/
theorem nativeLiftedSquare_projection (s : unitInterval) (t : ℝ) :
    triangleRegularProject (nativeLiftedSquare (s, t)) = nativePeriodicSquare (s, t) :=
  baseHomotopyLift_projection nativePeriodicSquare (baseLift controlledHeight)
    nativePeriodicSquare_zero s t

/-- The original inverse cusp deck relation persists through the complete actual homotopy. -/
theorem nativeLiftedSquare_translate (s : unitInterval) (k : ℤ) (t : ℝ) :
    nativeLiftedSquare (s, t + k) =
      (triangleCuspGenerator ^ (-k)) • nativeLiftedSquare (s, t) :=
  baseHomotopyLift_translate nativePeriodicSquare (baseLift controlledHeight)
    nativePeriodicSquare_zero triangleCuspGenerator nativePeriodicSquare_translate
    (baseLift_translate controlledHeight) s k t

/-- The actual moving lifted basepoint is retained as a genuine path. -/
def nativeLiftedTail :
    Path (baseLift controlledHeight 0) (nativeLiftedSquare (1, 0)) where
  toFun s := nativeLiftedSquare (s, 0)
  continuous_toFun := nativeLiftedSquare.continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := nativeLiftedSquare_zero 0
  target' := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
