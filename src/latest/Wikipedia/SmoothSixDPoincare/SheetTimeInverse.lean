import Wikipedia.SmoothSixDPoincare.RetimedSheetTransition

/-! # The explicit inverse of the native/model sheet time coordinates -/

noncomputable section

open Function
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

def sheetTimeInverse (q : (ℝ × A)) : (ℝ × A) := (2 * q.1 - 1, q.2)

theorem contDiff_sheetTimeInverse : ContDiff ℝ ∞ (sheetTimeInverse (A := A)) := by
  unfold sheetTimeInverse
  fun_prop

theorem sheetTimeInverse_leftInverse :
    LeftInverse (sheetTimeInverse (A := A)) sheetTimeCoordinates := by
  intro q
  rw [sheetTimeCoordinates_apply]
  apply Prod.ext
  · change 2 * ((q.1 + 1) / 2) - 1 = q.1
    ring
  · rfl

theorem sheetTimeInverse_rightInverse :
    RightInverse (sheetTimeInverse (A := A)) sheetTimeCoordinates := by
  intro q
  rw [sheetTimeCoordinates_apply]
  apply Prod.ext
  · change (2 * q.1 - 1 + 1) / 2 = q.1
    ring
  · rfl

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
