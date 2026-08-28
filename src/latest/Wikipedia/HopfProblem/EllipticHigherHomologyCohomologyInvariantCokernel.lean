import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyInvariantDual
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDualComparisonCore

/-!
# The actual invariant-cohomology image quotient

The proven native evaluation square identifies the cokernel of the
actual covering pullback into all deck-invariant cohomology classes with
the cokernel of the actual dual map on homological deck coinvariants.
The comparison preserves every original invariant cohomology class.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris SingularCohomologyFree

/-- The literal quotient of actual invariant cohomology by actual covering pullback. -/
abbrev PeriodCoverInvariantCohomologyCokernel (j : Kind) (p : FixedPeriod j) (n : ℕ) :=
  periodCohomologyInvariants j p j.twist (mainTwist_admissible j) n ⧸
    LinearMap.range (periodCoverCohomologyToInvariants j p j.twist (mainTwist_admissible j) n)

/-- The actual invariant-cohomology cokernel is the actual homological
coinvariant dual cokernel, not a rationalized or merely ranked substitute. -/
def periodCoverInvariantCohomologyCokernelEquivDual (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    PeriodCoverInvariantCohomologyCokernel j p n ≃ₗ[ℤ]
      (Module.Dual ℤ (SingularHomology p.val.Torus n ⧸
        LinearMap.range (periodDeckDifference j p n)) ⧸
          LinearMap.range (periodCoverFromDeckCoinvariants j p n).dualMap) :=
  CohomologyDualComparison.cokernelEquivOfIntertwining
    (periodCoverCohomologyToInvariants j p j.twist (mainTwist_admissible j) n)
    (periodCoverFromDeckCoinvariants j p n).dualMap
    (surfaceEvaluationEquiv j p n)
    (periodCohomologyInvariantsEquivDualCoinvariants j p n)
    (periodCoverCohomologyToInvariants_dual j p n)

/-- The comparison sends an original invariant class to its evaluation functional class. -/
@[simp] theorem periodCoverInvariantCohomologyCokernelEquivDual_apply_mk
    (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) n) :
    periodCoverInvariantCohomologyCokernelEquivDual j p n (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (periodCohomologyInvariantsEquivDualCoinvariants j p n a) := rfl

/-- Both genuine image subgroups have exactly the same integral index. -/
theorem periodCoverCohomologyToInvariants_range_index_eq_deckDual
    (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    (LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) n)).toAddSubgroup.index =
      (LinearMap.range (periodCoverFromDeckCoinvariants j p n).dualMap).toAddSubgroup.index :=
  CohomologyDualComparison.range_index_of_intertwining
    (periodCoverCohomologyToInvariants j p j.twist (mainTwist_admissible j) n)
    (periodCoverFromDeckCoinvariants j p n).dualMap
    (surfaceEvaluationEquiv j p n)
    (periodCohomologyInvariantsEquivDualCoinvariants j p n)
    (periodCoverCohomologyToInvariants_dual j p n)

end Wikipedia.HopfProblem.Elliptic.HigherHomology
