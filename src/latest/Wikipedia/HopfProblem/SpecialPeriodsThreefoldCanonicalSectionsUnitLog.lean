import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsUnit
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The literal exponential units in the elliptic canonical sections

The explicit period denominator always has positive imaginary part, so
the principal complex logarithm is holomorphic on its whole image.
Its negative supplies the source's globally holomorphic exponent `φ`,
with `exp φ` equal to the already constructed period unit.  This uses
neither a supplied logarithm nor a general logarithm-existence assumption.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.SectionsUnit

open Elliptic
open Elliptic.Equivariant.Data.Canonical (multiplier)

local notation "I" => modelWithCornersSelf ℂ ℂ

variable {j : Kind} (D : Equivariant.Data j)

/-- The actual denominator lies strictly above the logarithm's branch cut. -/
theorem denominator_mem_slitPlane (s : Disc) : denominator D s ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inr (denominator_im_pos D s).ne')

/-- The source's exponent is an explicit global holomorphic logarithm of
the previously constructed unit. -/
def unitLog (s : Disc) : ℂ := -Complex.log (denominator D s)

theorem unitLog_holomorphic : ContMDiff I I ω (unitLog D) := by
  intro s
  have hlog : ContMDiffAt I I ω Complex.log (denominator D s) :=
    (Complex.contDiffAt_log (denominator_mem_slitPlane D s)).contMDiffAt
  exact (hlog.comp s (denominator_holomorphic D s)).neg

/-- Exponentiating the explicit logarithm gives the actual reciprocal
period unit, on the entire disc. -/
theorem exp_unitLog (s : Disc) : Complex.exp (unitLog D s) = periodUnit D s := by
  change Complex.exp (-Complex.log (denominator D s)) = (denominator D s)⁻¹
  rw [Complex.exp_neg, Complex.exp_log (denominator_ne_zero D s)]

/-- The constructed canonical coefficient has literally the source form
`s^k exp(φ(s))`. -/
theorem coefficient_eq_pow_mul_exp (s : Disc) :
    coefficient D s = (s : ℂ) ^ vanishingOrder j * Complex.exp (unitLog D s) := by
  rw [exp_unitLog]
  rfl

theorem coefficient_exp_covariance (s : Disc) :
    (familyRotation j s : ℂ) ^ vanishingOrder j *
        Complex.exp (unitLog D (familyRotation j s)) * multiplier D s =
      (s : ℂ) ^ vanishingOrder j * Complex.exp (unitLog D s) := by
  simpa only [coefficient, exp_unitLog] using coefficient_covariance D s

/-- The exponent for the actual restrictions of the global special periods. -/
def specialUnitLog (j : Kind) : Disc → ℂ := unitLog (EllipticFilling.specialLocalData j)

theorem specialUnitLog_holomorphic (j : Kind) : ContMDiff I I ω (specialUnitLog j) :=
  unitLog_holomorphic (EllipticFilling.specialLocalData j)

theorem exp_specialUnitLog (j : Kind) (s : Disc) :
    Complex.exp (specialUnitLog j s) = specialUnit j s :=
  exp_unitLog (EllipticFilling.specialLocalData j) s

/-- Literal exponential form for the actual global-family coefficients,
with the already proved exact vanishing orders zero and two. -/
theorem specialCoefficient_eq_pow_mul_exp (j : Kind) (s : Disc) :
    specialCoefficient j s =
      (s : ℂ) ^ vanishingOrder j * Complex.exp (specialUnitLog j s) :=
  coefficient_eq_pow_mul_exp (EllipticFilling.specialLocalData j) s

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.SectionsUnit
