import ErdosProblems.Erdos19.Completion
import ErdosProblems.Erdos19.GraphMatching
import ErdosProblems.Erdos19.PairCompletion
import ErdosProblems.Erdos19.ApproximateListColoring
import ErdosProblems.Erdos19.BoundedRankLinear
import ErdosProblems.Erdos19.ApproximateCapacityColoring
import ErdosProblems.Erdos19.Vizing
import ErdosProblems.Erdos19.MatchingCoreColoring
import ErdosProblems.Erdos19.LargeEdgeCore
import ErdosProblems.Erdos19.SmallVolumeMinThree
import ErdosProblems.Erdos19.NearCompleteLargeEdges
import ErdosProblems.Erdos19.EventualBalancedPartition
import ErdosProblems.Erdos19.GraphReservoir
import ErdosProblems.Erdos19.MaximumMatchingCoverage
import ErdosProblems.Erdos19.ReservoirCompletion
import ErdosProblems.Erdos19.GraphLoadStep
import ErdosProblems.Erdos19.DiscreteGrowth
import ErdosProblems.Erdos19.EventualPrescribedPacking
import ErdosProblems.Erdos19.SparseClassCompletion
import ErdosProblems.Erdos19.SmallClassRefinement
import ErdosProblems.Erdos19.NearCompleteRegular
import ErdosProblems.Erdos19.CapacityRepresentatives
import ErdosProblems.Erdos19.UniformlyDenseColoring
import ErdosProblems.Erdos19.OutlierActiveColors
import ErdosProblems.Erdos19.RequestAssignment
import ErdosProblems.Erdos19.NearCompleteColoring
import ErdosProblems.Erdos19.DilutedLocalLemma
import ErdosProblems.Erdos19.LargeEdgeColoring
import ErdosProblems.Erdos19.LargeEdgeCoverColoring
import ErdosProblems.Erdos19.ReservedCoverExtension
import ErdosProblems.Erdos19.ReservedProjectiveColoring
import ErdosProblems.Erdos19.MediumExtension
import ErdosProblems.Erdos19.LargeMediumDichotomy
import ErdosProblems.Erdos19.TotalIncidenceColoring
import ErdosProblems.Erdos19.StarColorSelection
import ErdosProblems.Erdos19.SavingBranchReduction
import ErdosProblems.Erdos19.EventualBufferedLists
import ErdosProblems.Erdos19.LowDegreeBuffer
import ErdosProblems.Erdos19.ExceptionalColorTrace
import ErdosProblems.Erdos19.ExceptionalColorMatching
import ErdosProblems.Erdos19.BufferedMatchingFamily
import ErdosProblems.Erdos19.BlockReservoir
import ErdosProblems.Erdos19.BlockMatchingRepair
import ErdosProblems.Erdos19.MatchingRequestLoads
import ErdosProblems.Erdos19.BufferedPartialCompletion
import ErdosProblems.Erdos19.RankSeparatedBufferedColoring
import ErdosProblems.Erdos19.SpecialPaletteInitialization
import ErdosProblems.Erdos19.SpecialPaletteBuffer
import ErdosProblems.Erdos19.LargeCoverageColors
import ErdosProblems.Erdos19.ReservoirDegreePartition
import ErdosProblems.Erdos19.PaletteCoverageCounts
import ErdosProblems.Erdos19.SavingFullCompletion

/-!
# Erdős problem 19: asymptotic Erdős–Faber–Lovász

`asymptotic_efl` proves the unconditional sufficiently-large-n edge-coloring
theorem for linear hypergraphs whose edges have size at least two.
`erdos19` gives the corresponding exact chromatic-number equality for an
edge-disjoint union of n copies of K_n. Neither asserts the all-n conjecture.

The near-complete and complementary cases are proved in the supporting
modules. The latter combines the large/medium-edge dichotomy with the
projective completion or the saved-palette block-reservoir construction.
Approximate coloring, matching, reservoir, and completion inputs are proved
locally; no published coloring theorem is assumed as an extra hypothesis.
The earlier reductions and counterexamples remain in the supporting tree.
-/

namespace Erdos19

/-- Every sufficiently large linear hypergraph with no edges of size below two
has a proper edge coloring using at most its number of vertices. -/
theorem asymptotic_efl :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ H : SetHypergraph (Fin n), H.IsLinear →
      (∀ e : H, 2 ≤ e.1.ncard) → H.EdgeColorable n := by
  obtain ⟨s, hs, N₀, hnear⟩ := SetHypergraph.eventually_color_of_few_missing_pairs
  obtain ⟨N₁, hfar⟩ := SetHypergraph.eventually_edgeColorable_of_many_missing_pairs s hs
  refine ⟨max N₀ N₁, ?_⟩
  intro n hn H hlinear hmin
  by_cases hmissing : s * H.missingOrderedPairs.card < n ^ 2
  · exact hnear n ((le_max_left _ _).trans hn) H hlinear hmin hmissing
  · exact hfar n ((le_max_right _ _).trans hn) H hlinear hmin (Nat.le_of_not_gt hmissing)

/-- Empty and singleton set-valued edges can also be included. -/
theorem asymptotic_efl_set_hypergraphs : EventuallySetLinearHypergraphColorable :=
  eventuallySetLinearHypergraphColorable_of_nontrivial asymptotic_efl

/-- The exact sufficiently-large-n clique-union formulation of Erdős problem 19.
`Configuration.edge_disjoint` retains the original edge-disjointness hypothesis. -/
theorem erdos19 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (V : Type) [Fintype V], ∀ C : Configuration n V,
        C.graph.chromaticNumber = n :=
  erdos19_of_eventuallyLinearHypergraphColorable
    (eventuallyLinearHypergraphColorable_of_setVersion asymptotic_efl_set_hypergraphs)

theorem erdos_19 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (V : Type) [Fintype V], ∀ C : Configuration n V,
        C.graph.chromaticNumber = n :=
  erdos19

#print axioms asymptotic_efl
#print axioms asymptotic_efl_set_hypergraphs
#print axioms erdos19

end Erdos19
