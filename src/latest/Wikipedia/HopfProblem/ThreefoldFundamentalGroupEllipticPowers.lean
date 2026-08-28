import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansGlobal
import Wikipedia.HopfProblem.ThreefoldFundamentalGroupPowerReduction

/-!
# The two actual elliptic power relations in one orientation

The global attaching maps have been evaluated on the original source
columns and on the fixed jointly based meridians.  Reversing their common
clockwise orientation changes only the surviving central generator.
This file records the two resulting relations with every geometric
input already discharged.
-/

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.PiOne

open Elliptic TrianglePeriodFamily.Meridians

/-- The actual fixed free generators obey the source-column power law,
with the same central orientation at both elliptic points. -/
theorem meridian_pow_order (j : Kind) :
    meridian (EllipticGeometry.attachingMeridianIndex j) ^ j.order =
      orientedCentral normalizationReversesMeridians ^ γ j.twist := by
  have h := EllipticGeometry.clockwise_meridian_pow_order j
  rw [latticeHom_eq_c_zpow] at h
  cases hreverse : normalizationReversesMeridians with
  | false =>
    have hinv : meridian (EllipticGeometry.attachingMeridianIndex j) ^ j.order =
        (c ^ γ j.twist)⁻¹ := by
      simpa only [hreverse, Bool.false_eq_true, ↓reduceIte, inv_pow, inv_inv] using
        congrArg (fun g : GlobalGroup => g⁻¹) h
    simpa only [orientedCentral, hreverse, Bool.false_eq_true, ↓reduceIte, inv_zpow] using hinv
  | true =>
    simpa only [orientedCentral, hreverse, ↓reduceIte] using h

/-- The genuine order-three filling has the first positive twist column. -/
theorem meridian_first_cube :
    meridian false ^ 3 = orientedCentral normalizationReversesMeridians := by
  have h := meridian_pow_order Kind.three
  change meridian false ^ 3 = orientedCentral normalizationReversesMeridians ^ (1 : ℤ) at h
  simpa only [zpow_one] using h

/-- The genuine order-four filling has the negative second twist column. -/
theorem meridian_second_fourth :
    meridian true ^ 4 = (orientedCentral normalizationReversesMeridians)⁻¹ := by
  have h := meridian_pow_order Kind.four
  change meridian true ^ 4 = orientedCentral normalizationReversesMeridians ^ (-1 : ℤ) at h
  simpa only [zpow_neg_one] using h

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.PiOne
