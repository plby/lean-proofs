import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDualComparisonRankTwo
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDualComparisonTop
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDualComparisonZero

/-!
# Exact cokernels of the actual descended period-cover duals

For the genuine map from deck coinvariants of period-torus homology to
central-surface homology, its actual integer dual has indices
`(1,m,d,d,m)` in degrees zero through four.  Here `m` is the elliptic
order and `d` is the proved norm index, giving `(1,3,1,1,3)` and
`(1,4,2,2,4)` for the two actual elliptic kinds.

The imported equivalences identify each actual dual cokernel with the
corresponding residue module and give formulas on represented classes.
The degree-one through degree-three residue retains the actual shear.
These conclusions use the proved covering-map coordinates; no desired
matrix identity or cohomological comparison is a hypothesis.
-/

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

theorem periodCoverDeckDual_range_indices_firstFive (j : Kind) (p : FixedPeriod j) :
    (fun n : Fin 5 =>
      (LinearMap.range (periodCoverFromDeckCoinvariants j p n).dualMap).toAddSubgroup.index) =
        ![1, j.order, fibreNormIndex j, fibreNormIndex j, j.order] := by
  funext n
  fin_cases n
  · exact periodCoverDeckDual_h0_range_index j p
  · exact periodCoverDeckDual_h1_range_index j p
  · exact periodCoverDeckDual_h2_range_index j p
  · exact periodCoverDeckDual_h3_range_index j p
  · exact periodCoverDeckDual_h4_range_index j p

theorem periodCoverDeckDual_range_indices_three (p : FixedPeriod .three) :
    (fun n : Fin 5 =>
      (LinearMap.range (periodCoverFromDeckCoinvariants .three p n).dualMap).toAddSubgroup.index) =
        ![1, 3, 1, 1, 3] :=
  periodCoverDeckDual_range_indices_firstFive .three p

theorem periodCoverDeckDual_range_indices_four (p : FixedPeriod .four) :
    (fun n : Fin 5 =>
      (LinearMap.range (periodCoverFromDeckCoinvariants .four p n).dualMap).toAddSubgroup.index) =
        ![1, 4, 2, 2, 4] :=
  periodCoverDeckDual_range_indices_firstFive .four p

end Wikipedia.HopfProblem.Elliptic.HigherHomology
