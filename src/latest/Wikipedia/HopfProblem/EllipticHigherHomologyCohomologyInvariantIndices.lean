import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyInvariantIndicesRankTwo
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyInvariantIndicesEdges
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyInjective

/-!
# The actual integral invariant-cohomology cover-index profile

For the genuine elliptic surfaces the actual integral singular-cohomology
pullback is injective and has indices `(1,3,1,1,3)` and `(1,4,2,2,4)`
in the actual all-deck invariant subgroups.  The imported results give
native cokernel equivalences and representative residue formulas, not
merely abstract rank computations.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

theorem periodCoverCohomologyToInvariants_range_index_vector (j : Kind) (p : FixedPeriod j) :
    (fun n : Fin 5 => (LinearMap.range (periodCoverCohomologyToInvariants
      j p j.twist (mainTwist_admissible j) n.val)).toAddSubgroup.index) =
        ![1, j.order, fibreNormIndex j, fibreNormIndex j, j.order] := by
  funext n
  fin_cases n
  · exact periodCoverCohomologyToInvariants_h0_range_index j p
  · exact periodCoverCohomologyToInvariants_h1_range_index j p
  · exact periodCoverCohomologyToInvariants_h2_range_index j p
  · exact periodCoverCohomologyToInvariants_h3_range_index j p
  · exact periodCoverCohomologyToInvariants_h4_range_index j p

/-- The literal order-three invariant-cohomology image-index vector. -/
theorem periodCoverCohomologyToInvariants_range_index_vector_three (p : FixedPeriod .three) :
    (fun n : Fin 5 => (LinearMap.range (periodCoverCohomologyToInvariants
      .three p Kind.three.twist (mainTwist_admissible .three) n.val)).toAddSubgroup.index) =
        ![1, 3, 1, 1, 3] :=
  periodCoverCohomologyToInvariants_range_index_vector .three p

/-- The literal order-four invariant-cohomology image-index vector. -/
theorem periodCoverCohomologyToInvariants_range_index_vector_four (p : FixedPeriod .four) :
    (fun n : Fin 5 => (LinearMap.range (periodCoverCohomologyToInvariants
      .four p Kind.four.twist (mainTwist_admissible .four) n.val)).toAddSubgroup.index) =
        ![1, 4, 2, 2, 4] :=
  periodCoverCohomologyToInvariants_range_index_vector .four p

/-- There is no degree-two descent obstruction for the actual order-three surface. -/
theorem periodCoverCohomologyToInvariants_h2_surjective_three (p : FixedPeriod .three) :
    Function.Surjective (periodCoverCohomologyToInvariants
      .three p Kind.three.twist (mainTwist_admissible .three) 2) := by
  intro a
  apply (periodCoverCohomologyToInvariants_h2_mem_range .three p a).mpr
  exact one_dvd _

/-- There is no degree-three descent obstruction for the actual order-three surface. -/
theorem periodCoverCohomologyToInvariants_h3_surjective_three (p : FixedPeriod .three) :
    Function.Surjective (periodCoverCohomologyToInvariants
      .three p Kind.three.twist (mainTwist_admissible .three) 3) := by
  intro a
  apply (periodCoverCohomologyToInvariants_h3_mem_range .three p a).mpr
  exact one_dvd _

end Wikipedia.HopfProblem.Elliptic.HigherHomology
