import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyInvariantFilling
import Wikipedia.HopfProblem.EllipticHigherHomologySpecialCohomologyInjective

/-!
# Actual invariant-valued cohomology pullbacks for the special elliptic fillings

The maps below are literal specializations of the actual period-cover
pullback and the actual map into the full filling, with codomain restricted
to all deck-invariant cohomology classes.  Their image quotients are the
corresponding integral cokernels.  The central retraction identifies the
two images and preserves each original invariant class in the quotient.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic Elliptic.HigherHomology SingularCohomologyFree

/-- The actual special central-cover pullback with codomain restricted to deck invariants. -/
abbrev specialCentralPeriodCoverCohomologyToInvariants (j : Kind) (n : ℕ) :
    SingularCohomology (SpecialCentralSurface j) n →ₗ[ℤ]
      periodCohomologyInvariants j (specialLocalData j).centralPeriod
        j.twist (mainTwist_admissible j) n :=
  periodCoverCohomologyToInvariants j (specialLocalData j).centralPeriod
    j.twist (mainTwist_admissible j) n

/-- The literal special filling pullback with the same actual invariant codomain. -/
abbrev specialPeriodTorusIntoFillingCohomologyToInvariants (j : Kind) (n : ℕ) :
    SingularCohomology (SpecialFullFilling j) n →ₗ[ℤ]
      periodCohomologyInvariants j (specialLocalData j).centralPeriod
        j.twist (mainTwist_admissible j) n :=
  periodTorusIntoFillingCohomologyToInvariants (specialLocalData j) n

@[simp] theorem specialCentralPeriodCoverCohomologyToInvariants_coe (j : Kind) (n : ℕ)
    (a : SingularCohomology (SpecialCentralSurface j) n) :
    (specialCentralPeriodCoverCohomologyToInvariants j n a :
      SingularCohomology (SpecialCentralPeriodTorus j) n) =
        singularCohomologyPullback (specialCentralPeriodCover j) n a := rfl

@[simp] theorem specialPeriodTorusIntoFillingCohomologyToInvariants_coe
    (j : Kind) (n : ℕ) (a : SingularCohomology (SpecialFullFilling j) n) :
    (specialPeriodTorusIntoFillingCohomologyToInvariants j n a :
      SingularCohomology (SpecialCentralPeriodTorus j) n) =
        singularCohomologyPullback (specialPeriodTorusIntoFilling j) n a :=
  periodTorusIntoFillingCohomologyToInvariants_coe (specialLocalData j) n a

/-- The actual invariant-valued filling pullback is injective in every degree. -/
theorem specialPeriodTorusIntoFillingCohomologyToInvariants_injective (j : Kind) (n : ℕ) :
    Function.Injective (specialPeriodTorusIntoFillingCohomologyToInvariants j n) :=
  periodTorusIntoFillingCohomologyToInvariants_injective (specialLocalData j) n

/-- The genuine central inclusion identifies the two actual images inside deck invariants. -/
theorem specialPeriodTorusIntoFillingCohomologyToInvariants_range (j : Kind) (n : ℕ) :
    LinearMap.range (specialPeriodTorusIntoFillingCohomologyToInvariants j n) =
      LinearMap.range (specialCentralPeriodCoverCohomologyToInvariants j n) :=
  periodTorusIntoFillingCohomologyToInvariants_range (specialLocalData j) n

/-- The quotient by the actual special central-cover pullback image. -/
abbrev SpecialCentralPeriodCoverInvariantCohomologyCokernel (j : Kind) (n : ℕ) :=
  PeriodCoverInvariantCohomologyCokernel j (specialLocalData j).centralPeriod n

/-- The quotient by the actual special filling pullback image. -/
abbrev SpecialPeriodTorusIntoFillingInvariantCohomologyCokernel (j : Kind) (n : ℕ) :=
  PeriodTorusIntoFillingInvariantCohomologyCokernel (specialLocalData j) n

/-- The actual two cokernels agree through the identity on invariant classes. -/
def specialPeriodTorusIntoFillingInvariantCohomologyCokernelEquivCentral
    (j : Kind) (n : ℕ) :
    SpecialPeriodTorusIntoFillingInvariantCohomologyCokernel j n ≃ₗ[ℤ]
      SpecialCentralPeriodCoverInvariantCohomologyCokernel j n :=
  periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral (specialLocalData j) n

@[simp] theorem specialPeriodTorusIntoFillingInvariantCohomologyCokernelEquivCentral_apply_mk
    (j : Kind) (n : ℕ)
    (a : periodCohomologyInvariants j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) n) :
    specialPeriodTorusIntoFillingInvariantCohomologyCokernelEquivCentral j n
        (Submodule.Quotient.mk a) = Submodule.Quotient.mk a :=
  periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral_apply_mk
    (specialLocalData j) n a

/-- The actual filling and central-cover images have equal indices in all deck invariants. -/
theorem specialPeriodTorusIntoFillingCohomologyToInvariants_range_index_eq_central
    (j : Kind) (n : ℕ) :
    (LinearMap.range
      (specialPeriodTorusIntoFillingCohomologyToInvariants j n)).toAddSubgroup.index =
        (LinearMap.range
          (specialCentralPeriodCoverCohomologyToInvariants j n)).toAddSubgroup.index := by
  rw [specialPeriodTorusIntoFillingCohomologyToInvariants_range]

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
