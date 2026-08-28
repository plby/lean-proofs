import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyInvariantCokernel
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDualComparisonTop
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDualComparisonZero

/-!
# Actual invariant-cohomology cover indices in degrees zero and four

The native invariant pullback is onto in degree zero.  In degree four
its actual image has index equal to the covering order; the cokernel
residue is evaluation on the established marked homology generator.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularCohomologyFree CohomologyDualAlgebra

/-- The marked integer coordinate on the actual top invariant cohomology. -/
def periodInvariantCohomologyH4Coordinates (j : Kind) (p : FixedPeriod j) :
    periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 4 ≃ₗ[ℤ] ℤ :=
  ((periodCohomologyInvariantsEquivDualCoinvariants j p 4).trans
    (periodDeckCoinvariantsH4FunEquiv j p).symm.dualMap).trans rankOneDualEquivInt

/-- This coordinate is evaluation on the genuine marked coinvariant generator. -/
@[simp] theorem periodInvariantCohomologyH4Coordinates_apply (j : Kind) (p : FixedPeriod j)
    (a : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 4) :
    periodInvariantCohomologyH4Coordinates j p a =
      periodCohomologyInvariantsEquivDualCoinvariants j p 4 a
        ((periodDeckCoinvariantsH4Equiv j p).symm 1) := by
  simp only [periodInvariantCohomologyH4Coordinates, LinearEquiv.trans_apply,
    rankOneDualEquivInt_apply, LinearEquiv.dualMap_apply,
    periodDeckCoinvariantsH4FunEquiv_symm_apply, Pi.single_eq_same]

/-- Degree zero has the trivial genuine invariant-cohomology cokernel. -/
def periodCoverInvariantCohomologyH0CokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    PeriodCoverInvariantCohomologyCokernel j p 0 ≃ₗ[ℤ] ZMod 1 :=
  (periodCoverInvariantCohomologyCokernelEquivDual j p 0).trans
    (periodCoverDeckDualH0CokernelEquivZMod j p)

@[simp] theorem periodCoverInvariantCohomologyH0CokernelEquivZMod_apply_mk
    (j : Kind) (p : FixedPeriod j)
    (a : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 0) :
    periodCoverInvariantCohomologyH0CokernelEquivZMod j p (Submodule.Quotient.mk a) = 0 :=
  Subsingleton.elim _ _

/-- Top-degree actual invariant cohomology modulo covering pullback has the sheet-count residue. -/
def periodCoverInvariantCohomologyH4CokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    PeriodCoverInvariantCohomologyCokernel j p 4 ≃ₗ[ℤ] ZMod j.order :=
  (periodCoverInvariantCohomologyCokernelEquivDual j p 4).trans
    (periodCoverDeckDualH4CokernelEquivZMod j p)

@[simp] theorem periodCoverInvariantCohomologyH4CokernelEquivZMod_apply_mk
    (j : Kind) (p : FixedPeriod j)
    (a : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 4) :
    periodCoverInvariantCohomologyH4CokernelEquivZMod j p (Submodule.Quotient.mk a) =
      (periodInvariantCohomologyH4Coordinates j p a : ZMod j.order) := by
  rw [periodCoverInvariantCohomologyH4CokernelEquivZMod, LinearEquiv.trans_apply,
    periodCoverInvariantCohomologyCokernelEquivDual_apply_mk,
    periodCoverDeckDualH4CokernelEquivZMod_apply_mk,
    periodInvariantCohomologyH4Coordinates_apply]

/-- Exact divisibility, for actual top-degree invariant cohomology classes. -/
theorem periodCoverCohomologyToInvariants_h4_mem_range (j : Kind) (p : FixedPeriod j)
    (a : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 4) :
    a ∈ LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) 4) ↔
      (j.order : ℤ) ∣ periodInvariantCohomologyH4Coordinates j p a := by
  rw [← Submodule.Quotient.mk_eq_zero,
    ← (periodCoverInvariantCohomologyH4CokernelEquivZMod j p).map_eq_zero_iff,
    periodCoverInvariantCohomologyH4CokernelEquivZMod_apply_mk,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem periodCoverCohomologyToInvariants_h0_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) 0)).toAddSubgroup.index = 1 := by
  rw [periodCoverCohomologyToInvariants_range_index_eq_deckDual,
    periodCoverDeckDual_h0_range_index]

theorem periodCoverCohomologyToInvariants_h4_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) 4)).toAddSubgroup.index = j.order := by
  rw [periodCoverCohomologyToInvariants_range_index_eq_deckDual,
    periodCoverDeckDual_h4_range_index]

/-- Every actual degree-zero deck-invariant cohomology class is an actual covering pullback. -/
theorem periodCoverCohomologyToInvariants_h0_surjective (j : Kind) (p : FixedPeriod j) :
    Function.Surjective
      (periodCoverCohomologyToInvariants j p j.twist (mainTwist_admissible j) 0) := by
  intro a
  obtain ⟨φ, hφ⟩ := (periodCoverDeckDual_h0_bijective j p).surjective
    (periodCohomologyInvariantsEquivDualCoinvariants j p 0 a)
  refine ⟨(surfaceEvaluationEquiv j p 0).symm φ, ?_⟩
  apply (periodCohomologyInvariantsEquivDualCoinvariants j p 0).injective
  rw [periodCoverCohomologyToInvariants_dual, LinearEquiv.apply_symm_apply, hφ]

theorem periodCoverCohomologyToInvariants_h0_range_finiteIndex
    (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) 0)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodCoverCohomologyToInvariants_h0_range_index]
  exact one_ne_zero

theorem periodCoverCohomologyToInvariants_h4_range_finiteIndex
    (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) 4)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodCoverCohomologyToInvariants_h4_range_index]
  exact j.order_pos.ne'

end Wikipedia.HopfProblem.Elliptic.HigherHomology
