import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyInvariantCokernel
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDualComparisonRankTwo

/-!
# Actual integral cohomological cover indices in degrees one through three

The literal covering pullback lands in the actual all-deck invariant
cohomology.  The proven native evaluation comparison and the actual
triangular covering matrices identify its cokernel with the indicated
integer residue module.  The original off-diagonal coordinate is retained
in every representative formula.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularCohomologyFree

/-- Integral coordinates on the actual degree-one invariant cohomology. -/
def periodInvariantCohomologyH1Coordinates (j : Kind) (p : FixedPeriod j) :
    periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (periodCohomologyInvariantsEquivDualCoinvariants j p 1).trans
    (intDualCoordinatesOfEquiv (periodDeckCoinvariantsH1Equiv j p))

/-- Integral coordinates on the actual degree-two invariant cohomology. -/
def periodInvariantCohomologyH2Coordinates (j : Kind) (p : FixedPeriod j) :
    periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 2 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (periodCohomologyInvariantsEquivDualCoinvariants j p 2).trans
    (intDualCoordinatesOfEquiv (periodDeckCoinvariantsH2Equiv j p))

/-- Integral coordinates on the actual degree-three invariant cohomology. -/
def periodInvariantCohomologyH3Coordinates (j : Kind) (p : FixedPeriod j) :
    periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (periodCohomologyInvariantsEquivDualCoinvariants j p 3).trans
    (intDualCoordinatesOfEquiv (periodDeckCoinvariantsH3Equiv j p))

/-- The actual degree-one invariant-cohomology cokernel is reduction modulo the sheet count. -/
def periodCoverInvariantCohomologyH1CokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    PeriodCoverInvariantCohomologyCokernel j p 1 ≃ₗ[ℤ] ZMod j.order :=
  (periodCoverInvariantCohomologyCokernelEquivDual j p 1).trans
    (periodCoverDeckDualH1CokernelEquivZMod j p)

/-- The degree-two image has its actual one-or-two integral residue cokernel. -/
def periodCoverInvariantCohomologyH2CokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    PeriodCoverInvariantCohomologyCokernel j p 2 ≃ₗ[ℤ] ZMod (fibreNormIndex j) :=
  (periodCoverInvariantCohomologyCokernelEquivDual j p 2).trans
    (periodCoverDeckDualH2CokernelEquivZMod j p)

/-- The degree-three image has the same actual one-or-two integral residue cokernel. -/
def periodCoverInvariantCohomologyH3CokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    PeriodCoverInvariantCohomologyCokernel j p 3 ≃ₗ[ℤ] ZMod (fibreNormIndex j) :=
  (periodCoverInvariantCohomologyCokernelEquivDual j p 3).trans
    (periodCoverDeckDualH3CokernelEquivZMod j p)

@[simp] theorem periodCoverInvariantCohomologyH1CokernelEquivZMod_apply_mk
    (j : Kind) (p : FixedPeriod j)
    (a : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 1) :
    periodCoverInvariantCohomologyH1CokernelEquivZMod j p (Submodule.Quotient.mk a) =
      ((periodInvariantCohomologyH1Coordinates j p a 1 - periodCoverDeckDualH1Shear j p *
        periodInvariantCohomologyH1Coordinates j p a 0 : ℤ) : ZMod j.order) := by
  rw [periodCoverInvariantCohomologyH1CokernelEquivZMod, LinearEquiv.trans_apply,
    periodCoverInvariantCohomologyCokernelEquivDual_apply_mk,
    periodCoverDeckDualH1CokernelEquivZMod_apply_mk]
  rfl

@[simp] theorem periodCoverInvariantCohomologyH2CokernelEquivZMod_apply_mk
    (j : Kind) (p : FixedPeriod j)
    (a : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 2) :
    periodCoverInvariantCohomologyH2CokernelEquivZMod j p (Submodule.Quotient.mk a) =
      ((periodInvariantCohomologyH2Coordinates j p a 1 - periodCoverDeckDualH2Shear j p *
        periodInvariantCohomologyH2Coordinates j p a 0 : ℤ) : ZMod (fibreNormIndex j)) := by
  rw [periodCoverInvariantCohomologyH2CokernelEquivZMod, LinearEquiv.trans_apply,
    periodCoverInvariantCohomologyCokernelEquivDual_apply_mk,
    periodCoverDeckDualH2CokernelEquivZMod_apply_mk]
  rfl

@[simp] theorem periodCoverInvariantCohomologyH3CokernelEquivZMod_apply_mk
    (j : Kind) (p : FixedPeriod j)
    (a : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 3) :
    periodCoverInvariantCohomologyH3CokernelEquivZMod j p (Submodule.Quotient.mk a) =
      ((periodInvariantCohomologyH3Coordinates j p a 1 - periodCoverDeckDualH3Shear j p *
        periodInvariantCohomologyH3Coordinates j p a 0 : ℤ) : ZMod (fibreNormIndex j)) := by
  rw [periodCoverInvariantCohomologyH3CokernelEquivZMod, LinearEquiv.trans_apply,
    periodCoverInvariantCohomologyCokernelEquivDual_apply_mk,
    periodCoverDeckDualH3CokernelEquivZMod_apply_mk]
  rfl

/-- The actual degree-one image is exactly the indicated integral divisibility lattice. -/
theorem periodCoverCohomologyToInvariants_h1_mem_range (j : Kind) (p : FixedPeriod j)
    (a : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 1) :
    a ∈ LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) 1) ↔
      (j.order : ℤ) ∣ periodInvariantCohomologyH1Coordinates j p a 1 -
        periodCoverDeckDualH1Shear j p * periodInvariantCohomologyH1Coordinates j p a 0 := by
  rw [← Submodule.Quotient.mk_eq_zero,
    ← (periodCoverInvariantCohomologyH1CokernelEquivZMod j p).map_eq_zero_iff,
    periodCoverInvariantCohomologyH1CokernelEquivZMod_apply_mk,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The order-four parity obstruction in degree two is an actual cohomological image condition. -/
theorem periodCoverCohomologyToInvariants_h2_mem_range (j : Kind) (p : FixedPeriod j)
    (a : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 2) :
    a ∈ LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) 2) ↔
      (fibreNormIndex j : ℤ) ∣ periodInvariantCohomologyH2Coordinates j p a 1 -
        periodCoverDeckDualH2Shear j p * periodInvariantCohomologyH2Coordinates j p a 0 := by
  rw [← Submodule.Quotient.mk_eq_zero,
    ← (periodCoverInvariantCohomologyH2CokernelEquivZMod j p).map_eq_zero_iff,
    periodCoverInvariantCohomologyH2CokernelEquivZMod_apply_mk,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The same integral parity obstruction is proved for the actual degree-three image. -/
theorem periodCoverCohomologyToInvariants_h3_mem_range (j : Kind) (p : FixedPeriod j)
    (a : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 3) :
    a ∈ LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) 3) ↔
      (fibreNormIndex j : ℤ) ∣ periodInvariantCohomologyH3Coordinates j p a 1 -
        periodCoverDeckDualH3Shear j p * periodInvariantCohomologyH3Coordinates j p a 0 := by
  rw [← Submodule.Quotient.mk_eq_zero,
    ← (periodCoverInvariantCohomologyH3CokernelEquivZMod j p).map_eq_zero_iff,
    periodCoverInvariantCohomologyH3CokernelEquivZMod_apply_mk,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The degree-one actual pullback has index equal to the covering order in deck invariants. -/
theorem periodCoverCohomologyToInvariants_h1_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) 1)).toAddSubgroup.index = j.order := by
  rw [periodCoverCohomologyToInvariants_range_index_eq_deckDual,
    periodCoverDeckDual_h1_range_index]

/-- The degree-two actual pullback has index one or two, respectively, in all deck invariants. -/
theorem periodCoverCohomologyToInvariants_h2_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) 2)).toAddSubgroup.index = fibreNormIndex j := by
  rw [periodCoverCohomologyToInvariants_range_index_eq_deckDual,
    periodCoverDeckDual_h2_range_index]

/-- The degree-three actual pullback has the same integral invariant-subgroup index. -/
theorem periodCoverCohomologyToInvariants_h3_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) 3)).toAddSubgroup.index = fibreNormIndex j := by
  rw [periodCoverCohomologyToInvariants_range_index_eq_deckDual,
    periodCoverDeckDual_h3_range_index]

theorem periodCoverCohomologyToInvariants_h1_range_finiteIndex
    (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) 1)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodCoverCohomologyToInvariants_h1_range_index]
  exact j.order_pos.ne'

theorem periodCoverCohomologyToInvariants_h2_range_finiteIndex
    (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) 2)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodCoverCohomologyToInvariants_h2_range_index]
  exact (fibreNormIndex_pos j).ne'

theorem periodCoverCohomologyToInvariants_h3_range_finiteIndex
    (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) 3)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodCoverCohomologyToInvariants_h3_range_index]
  exact (fibreNormIndex_pos j).ne'

end Wikipedia.HopfProblem.Elliptic.HigherHomology
