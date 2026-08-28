import Wikipedia.HopfProblem.DegreeCollapseRelativeIntegralCohomology
import Wikipedia.NoExoticSixSphere.RelativeConnectedLowHomology

/-!
# The two lowest integral relative cohomology groups of a connected pair

For path-connected ambient and subspace, relative H0 vanishes. Vanishing
ambient H1 also gives relative H1 = 0 by the original pair sequence.
The original integral evaluation maps then give relative H0 and H1
cohomology vanishing, with no contractibility assumption.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCohomology

open SingularMayerVietoris SingularCohomologyFree
open NoExoticSixSphere.RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X)
  [PathConnectedSpace X] [PathConnectedSpace U]

theorem connected_first_homology_subsingleton [Subsingleton (SingularHomology X 1)] :
    Subsingleton (Homology U 1) := by
  have hs : Surjective (toRelative U 1) := by
    intro c
    have hc : c ∈ LinearMap.ker (connecting U 0) := connected_connecting_zero U c
    rw [← exact_at_relative] at hc
    exact hc
  exact hs.subsingleton

theorem connected_zero_cohomology_subsingleton :
    Subsingleton (Cohomology (complex U) 0) := by
  let : Subsingleton (Homology U 0) := connected_homologyZero_subsingleton U
  exact (LocalEvaluation.cohomologyEvaluation_zero_injective (complex U)).subsingleton

theorem connected_first_cohomology_subsingleton [Subsingleton (SingularHomology X 1)] :
    Subsingleton (Cohomology (complex U) 1) := by
  let : Subsingleton (Homology U 0) := connected_homologyZero_subsingleton U
  let : Subsingleton (Homology U 1) := connected_first_homology_subsingleton U
  exact relative_cohomology_succ_subsingleton U 0

end Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCohomology
