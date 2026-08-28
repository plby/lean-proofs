import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsUnitBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsUnitOrders
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsDerivativesMultiplier
import Wikipedia.HopfProblem.SpecialPeriodsEllipticFilling

/-!
# Canonical coefficients with the exact elliptic vanishing orders

The explicit period unit solves the actual canonical multiplier equation
on the whole disc.  Its coefficient has exact ambient analytic order zero
or two at the centre.  The final specialization uses the restrictions of
the unconditionally constructed global special periods, not separately
chosen or constant local period data.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.SectionsUnit

open Elliptic
open Elliptic.Equivariant.Data.Canonical (multiplier canonicalExponent)

local notation "I" => modelWithCornersSelf ℂ ℂ

@[simp] theorem vanishingOrder_three : vanishingOrder .three = 0 := rfl

@[simp] theorem vanishingOrder_four : vanishingOrder .four = 2 := rfl

/-- The explicit exponents are exactly the source's `m - 1 - a`. -/
theorem vanishingOrder_eq_order_sub_exponent (j : Kind) :
    vanishingOrder j = j.order - 1 - canonicalExponent j := by
  cases j <;> rfl

theorem vanishingOrder_add_one_add_exponent (j : Kind) :
    vanishingOrder j + 1 + canonicalExponent j = j.order := by
  cases j <;> rfl

variable {j : Kind} (D : Equivariant.Data j)

/-- The explicit unit solves the normalized actual multiplicative cocycle. -/
theorem periodUnit_multiplier (s : Disc) :
    periodUnit D (familyRotation j s) *
        (normalPhase j ^ vanishingOrder j * multiplier D s) = periodUnit D s :=
  periodUnit_covariance D s

/-- The source's exact invariance equation, with its actual top Jacobian. -/
theorem coefficient_covariance (s : Disc) :
    coefficient D (familyRotation j s) * multiplier D s = coefficient D s :=
  coefficient_covariance_raw D s

/-- The actual inverse disc chart gives the ambient analytic germ. -/
theorem coefficient_extension_analyticAt : AnalyticAt ℂ (discExtension (coefficient D)) 0 :=
  discExtension_analyticAt (coefficient_holomorphic D)

theorem coefficient_extension_factorization :
    discExtension (coefficient D) =ᶠ[𝓝 (0 : ℂ)]
      (fun z : ℂ => z ^ vanishingOrder j * discExtension (periodUnit D) z) :=
  discExtension_power_mul_eventually (periodUnit D) (vanishingOrder j)

/-- The unit contributes no zero or pole, so the ambient order is exactly
zero at the order-three point and two at the order-four point. -/
theorem coefficient_analyticOrderAt :
    analyticOrderAt (discExtension (coefficient D)) 0 = (vanishingOrder j : ℕ∞) :=
  analyticOrderAt_discExtension_power_mul (periodUnit_holomorphic D)
    (periodUnit_ne_zero D discZero) (vanishingOrder j)

/-- An explicit existence result; no holomorphic coboundary is an input. -/
theorem exists_holomorphic_unit_coefficient :
    ∃ u : Disc → ℂ, ContMDiff I I ω u ∧ (∀ s, u s ≠ 0) ∧
      (∀ s : Disc,
        (familyRotation j s : ℂ) ^ vanishingOrder j * u (familyRotation j s) * multiplier D s =
          (s : ℂ) ^ vanishingOrder j * u s) ∧
      analyticOrderAt (discExtension (fun s : Disc => (s : ℂ) ^ vanishingOrder j * u s)) 0 =
        (vanishingOrder j : ℕ∞) :=
  ⟨periodUnit D, periodUnit_holomorphic D, periodUnit_ne_zero D,
    coefficient_covariance D, coefficient_analyticOrderAt D⟩

/-- The actual global special period map supplies the two disc units. -/
def specialUnit (j : Kind) : Disc → ℂ := periodUnit (EllipticFilling.specialLocalData j)

/-- These coefficients use the actual period restrictions of the constructed
global family, with the prescribed exponents zero and two. -/
def specialCoefficient (j : Kind) : Disc → ℂ := coefficient (EllipticFilling.specialLocalData j)

theorem specialUnit_formula (j : Kind) (s : Disc) :
    specialUnit j s =
      ((specialPeriodMap.point (EllipticFilling.neighborhoodLift j s)).val.τ - lowerFixedTau j)⁻¹ :=
  rfl

theorem specialUnit_holomorphic (j : Kind) : ContMDiff I I ω (specialUnit j) :=
  periodUnit_holomorphic (EllipticFilling.specialLocalData j)

theorem specialUnit_ne_zero (j : Kind) (s : Disc) : specialUnit j s ≠ 0 :=
  periodUnit_ne_zero (EllipticFilling.specialLocalData j) s

theorem specialCoefficient_eq (j : Kind) (s : Disc) :
    specialCoefficient j s = (s : ℂ) ^ vanishingOrder j * specialUnit j s := rfl

theorem specialCoefficient_holomorphic (j : Kind) : ContMDiff I I ω (specialCoefficient j) :=
  coefficient_holomorphic (EllipticFilling.specialLocalData j)

theorem specialCoefficient_ne_zero_iff (j : Kind) (s : Disc) :
    specialCoefficient j s ≠ 0 ↔ vanishingOrder j = 0 ∨ (s : ℂ) ≠ 0 :=
  coefficient_ne_zero_iff (EllipticFilling.specialLocalData j) s

theorem specialCoefficient_eq_zero_iff (j : Kind) (s : Disc) :
    specialCoefficient j s = 0 ↔ vanishingOrder j ≠ 0 ∧ (s : ℂ) = 0 :=
  coefficient_eq_zero_iff (EllipticFilling.specialLocalData j) s

/-- Invariance for the actual local restrictions of the global special periods. -/
theorem specialCoefficient_covariance (j : Kind) (s : Disc) :
    specialCoefficient j (familyRotation j s) *
        multiplier (EllipticFilling.specialLocalData j) s = specialCoefficient j s :=
  coefficient_covariance (EllipticFilling.specialLocalData j) s

theorem specialCoefficient_extension_analyticAt (j : Kind) :
    AnalyticAt ℂ (discExtension (specialCoefficient j)) 0 :=
  coefficient_extension_analyticAt (EllipticFilling.specialLocalData j)

/-- Exact order for the actual globally constructed periods, without
any period-map, unit-existence, or order assumption. -/
theorem specialCoefficient_analyticOrderAt (j : Kind) :
    analyticOrderAt (discExtension (specialCoefficient j)) 0 = (vanishingOrder j : ℕ∞) :=
  coefficient_analyticOrderAt (EllipticFilling.specialLocalData j)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.SectionsUnit
