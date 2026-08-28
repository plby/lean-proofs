import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryLoopSquaresHomotopy
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridians

/-!
# Periodic homotopies for the actual chosen attaching meridians

Apply the genuine endpoint-quotient construction to the already constructed
attaching-loop square. The resulting homotopy has real periodic loop time,
retains the literal original square on the unit square, and follows the
chosen attaching tail at every integer. No new loop-comparison hypothesis
or change of marking is introduced.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryLoopSquares

open SpecialPeriods SpecialPeriods.EllipticAttachingMeridians
open SpecialPeriods.Threefold.EllipticGeometry

/-- The actual chosen attaching square descends to a continuous circle homotopy. -/
def chosenAttachingCircleHomotopy (j : Elliptic.Kind) :
    (loopOnCircle (chosenAttachingBaseLoop j)).Homotopy
      (loopOnCircle (clockwiseRegularMeridian (attachingMeridianIndex j))) :=
  circleHomotopy (chosenAttachingSquare j)

@[simp] theorem chosenAttachingCircleHomotopy_unit
    (j : Elliptic.Kind) (s t : unitInterval) :
    chosenAttachingCircleHomotopy j (s, ((t : ℝ) : LoopCircle)) =
      (chosenAttachingSquare j).map (s, t) :=
  circleSquare_unit (chosenAttachingSquare j) s t

/-- The actual chosen attaching square extends to a jointly continuous periodic homotopy. -/
def chosenAttachingPeriodicHomotopy (j : Elliptic.Kind) :
    (loopPeriodic (chosenAttachingBaseLoop j)).Homotopy
      (loopPeriodic (clockwiseRegularMeridian (attachingMeridianIndex j))) :=
  periodicHomotopy (chosenAttachingSquare j)

/-- The extension retains every original point of the geometric attaching square. -/
@[simp] theorem chosenAttachingPeriodicHomotopy_unit
    (j : Elliptic.Kind) (s t : unitInterval) :
    chosenAttachingPeriodicHomotopy j (s, (t : ℝ)) =
      (chosenAttachingSquare j).map (s, t) :=
  periodicHomotopy_unit (chosenAttachingSquare j) s t

@[simp] theorem chosenAttachingPeriodicHomotopy_initial (j : Elliptic.Kind) (t : ℝ) :
    chosenAttachingPeriodicHomotopy j (0, t) =
      loopPeriodic (chosenAttachingBaseLoop j) t :=
  periodicSquare_initial (chosenAttachingSquare j) t

@[simp] theorem chosenAttachingPeriodicHomotopy_final (j : Elliptic.Kind) (t : ℝ) :
    chosenAttachingPeriodicHomotopy j (1, t) =
      loopPeriodic (clockwiseRegularMeridian (attachingMeridianIndex j)) t :=
  periodicSquare_final (chosenAttachingSquare j) t

theorem chosenAttachingPeriodicHomotopy_add_int
    (j : Elliptic.Kind) (s : unitInterval) (t : ℝ) (k : ℤ) :
    chosenAttachingPeriodicHomotopy j (s, t + (k : ℝ)) =
      chosenAttachingPeriodicHomotopy j (s, t) :=
  periodicHomotopy_add_int (chosenAttachingSquare j) s t k

theorem chosenAttachingPeriodicHomotopy_periodic (j : Elliptic.Kind) (s : unitInterval) :
    Function.Periodic (fun t : ℝ => chosenAttachingPeriodicHomotopy j (s, t)) 1 :=
  periodicSquare_periodic (chosenAttachingSquare j) s

/-- Real time zero follows the original attaching tail, without a new path choice. -/
@[simp] theorem chosenAttachingPeriodicHomotopy_tail
    (j : Elliptic.Kind) (s : unitInterval) :
    chosenAttachingPeriodicHomotopy j (s, 0) = chosenAttachingTail j s :=
  periodicSquare_tail (chosenAttachingSquare j) s

/-- Every integer time follows that same original attaching tail. -/
theorem chosenAttachingPeriodicHomotopy_int
    (j : Elliptic.Kind) (s : unitInterval) (k : ℤ) :
    chosenAttachingPeriodicHomotopy j (s, (k : ℝ)) = chosenAttachingTail j s :=
  periodicSquare_int (chosenAttachingSquare j) s k

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryLoopSquares
