import ErdosProblems.Erdos547.Ramsey
import ErdosProblems.Erdos547.LeafExtension
import ErdosProblems.Erdos547.DegreeDichotomy
import ErdosProblems.Erdos547.TreeCore
import ErdosProblems.Erdos547.HighDegreeCore
import ErdosProblems.Erdos547.Unbalanced
import ErdosProblems.Erdos547.LeafBunch
import ErdosProblems.Erdos547.PartialEmbedding
import ErdosProblems.Erdos547.SkewMatching
import ErdosProblems.Erdos547.MatchingCompactness
import ErdosProblems.Erdos547.PairedTree
import ErdosProblems.Erdos547.PairChoices
import ErdosProblems.Erdos547.ExposedSeed
import ErdosProblems.Erdos547.PairedEmbedding
import ErdosProblems.Erdos547.PrefixPotential
import ErdosProblems.Erdos547.BipartiteEmbedding
import ErdosProblems.Erdos547.Escape
import ErdosProblems.Erdos547.DenseCrossAbsorption
import ErdosProblems.Erdos547.EscapeRamsey
import ErdosProblems.Erdos547.NearCoreMany
import ErdosProblems.Erdos547.ManyNonleaves
import ErdosProblems.Erdos547.NearCore
import ErdosProblems.Erdos547.FactorCriticalFractional
import ErdosProblems.Erdos547.MatchingCombination
import ErdosProblems.Erdos547.GallaiEdmonds
import ErdosProblems.Erdos547.GELocalOptimality
import ErdosProblems.Erdos547.GEReachableSets
import ErdosProblems.Erdos547.GEPairOptimization
import ErdosProblems.Erdos547.GESeparationOne
import ErdosProblems.Erdos547.GESeparationRestricted
import ErdosProblems.Erdos547.ImprovedBalancing
import ErdosProblems.Erdos547.MatchingCompletion
import ErdosProblems.Erdos547.SkewFractionalExtraction
import ErdosProblems.Erdos547.GreedyAnchored
import ErdosProblems.Erdos547.WeightNormalization
import ErdosProblems.Erdos547.PieceCombination
import ErdosProblems.Erdos547.TwoAnchorEasyCases
import ErdosProblems.Erdos547.TwoAnchorMatching
import ErdosProblems.Erdos547.StructuralEasySkew
import ErdosProblems.Erdos547.StructuralSkewCover
import ErdosProblems.Erdos547.StructuralBalancedOptimal
import ErdosProblems.Erdos547.StructuralSmallOverlap
import ErdosProblems.Erdos547.StructuralFlabellum
import ErdosProblems.Erdos547.GEAvoidingAnchor
import ErdosProblems.Erdos547.GEAvoidingPiece
import ErdosProblems.Erdos547.GEPairFixedLoads
import ErdosProblems.Erdos547.GEAvoidingRemainder
import ErdosProblems.Erdos547.FullFlabellum
import ErdosProblems.Erdos547.TransportHall
import ErdosProblems.Erdos547.StructuralAssembly
import ErdosProblems.Erdos547.StructuralRealScaling
import ErdosProblems.Erdos547.RegularityManyTypical
import ErdosProblems.Erdos547.RootedRegularMargins
import ErdosProblems.Erdos547.ShrubEmbedding
import ErdosProblems.Erdos547.ParitySeparator
import ErdosProblems.Erdos547.FineTreePartition
import ErdosProblems.Erdos547.ShrubColours
import ErdosProblems.Erdos547.TreeCoating
import ErdosProblems.Erdos547.RegularitySlicing
import ErdosProblems.Erdos547.RegularityClusterCleaning
import ErdosProblems.Erdos547.StrongRegularity
import ErdosProblems.Erdos547.ReducedMaximumDegree
import ErdosProblems.Erdos547.SeedForestEmbedding
import ErdosProblems.Erdos547.ShrubAllocation
import ErdosProblems.Erdos547.AllowedWeight
import ErdosProblems.Erdos547.PrivateClassBounds
import ErdosProblems.Erdos547.ShrubRoots
import ErdosProblems.Erdos547.ShrubRootCount
import ErdosProblems.Erdos547.TargetCapacity
import ErdosProblems.Erdos547.ShrubGlue
import ErdosProblems.Erdos547.AvailableVertices
import ErdosProblems.Erdos547.PostponedMass
import ErdosProblems.Erdos547.ShrubRootColours
import ErdosProblems.Erdos547.ShrubHostStep
import ErdosProblems.Erdos547.ShrubPostponement
import ErdosProblems.Erdos547.ShrubStateEndpoints
import ErdosProblems.Erdos547.ShrubReservoirPhase
import ErdosProblems.Erdos547.ShrubGlobalEmbedding
import ErdosProblems.Erdos547.CanonicalShrubAllocation
import ErdosProblems.Erdos547.SkewHeadBudgets
import ErdosProblems.Erdos547.SetupMargins
import ErdosProblems.Erdos547.TwoSkewFamily
import ErdosProblems.Erdos547.AllowedSeedDegrees
import ErdosProblems.Erdos547.SkewHostAssembly
import ErdosProblems.Erdos547.SeededSkewSetup
import ErdosProblems.Erdos547.ReducedSeedEmbedding
import ErdosProblems.Erdos547.ReducedStructureEmbedding
import ErdosProblems.Erdos547.RamseyAssembly

/-!
# Erdős problem 547 for every sufficiently large tree order

The main theorem is the sufficiently-large statement: there exists `n₀` such that,
for every `n ≥ n₀`, every tree on `Fin n` embeds in one colour of every
red/blue complete graph on `Fin (2 * n - 2)`.

The imported modules prove finite and partial embedding, Hall leaf-restoration,
the graph-degree dichotomy, the small-bipartition and large-leaf-bunch cases,
the pendant-package absorption argument and the full uniform sufficiently-large
near-core Ramsey proposition, covering both many and few nonleaves.
They also prove fractional-allocation optimization, compatible anchored sums,
conversion of neighbourhood saturation to a fitted skew matching, and a
Gallai–Edmonds decomposition proved from Tutte's theorem and Hall's theorem,
its fractional completion, saturation optimization, alternating-reachability
inequalities, the reachable-set load identity, both GE separation lemmas,
improved balancing, the full matching-completion lemma, and the three anchored
greedy allocation lemmas for positive skew.
The saturation decomposition and its second-anchor refinement, exact weight
normalization, and the full `(k, k/2)` two-anchor matching lemma are also proved.
The full weighted degree structure theorem is proved for positive integer part
budgets, rational rescaling, and real rescaling under strict degree surplus.
This includes every structural case, a strengthened flabellum case,
and the full avoiding case. The latter uses a proved finite fractional Hall
theorem and a bounded-deficit saturation theorem to account for all load lost
when the covered reachable region is removed.
The typical-vertex estimates for regular pairs and the full one-root and
two-root small-tree embedding in a regular pair are also proved, with explicit
numerical margins and an optional-second-root shrub formulation.
The tree decomposition into disjoint small shrubs is also proved, with a
bounded rooted cut set, one or two attachments per shrub, equal attachment
colours, and distance at least six between distinct attachments.
Integer tree padding is proved with a uniform large-order threshold, an actual
supertree of order at most `(1+10η)n`, and lower bounds on all four shrub parts.
Equitable regularity is proved with a uniform large-order threshold, a bounded
number of equal nonempty clusters, few discarded vertices, and a bound on
the irregular partners of every retained cluster.
The density-weighted reduced graph is constructed, and its inherited minimum
degree and maximum degree from a positive proportion of high-degree host
vertices are proved with explicit additive losses.
The seed-forest embedding with two external typicality conditions is proved.
A finite quadratic-potential argument proves simultaneous weighted allocation
of the actual shrubs' two colour classes to allowed clusters, with explicit
error bounds; the weight lost to small and exceptional clusters is bounded.
Weighted Hall constructs disjoint private sets from separate and joint class
capacities. Every actual shrub is converted to a one-root or two-root shrub,
including its complete attachment interface, parity, and distance conditions.
The partial shrub embedding, its insertion step, exact occupied-set update,
cluster occupancy bounds, shared private-set budgets, routed target capacities,
and distinguished-root reservoir counts are proved. The common local step for
both embedding phases preserves all capacities and future reservations.
The entire reservoir phase is proved: a sufficiently small postponed family
can be completed by a finite induction, reserving only its distinguished roots.
The private-root phase is also proved by induction over the head clusters.
Together they embed the whole tree from the explicitly stated regular-pair,
allocation, private-set, seed, and numerical data in `ShrubHostSetup`.
All that setup data is constructed from the positive-proportion degree hypotheses;
no setup existence is postulated.
The intermediate construction from allocated skew heads and actual root sets
is proved, as are relative shrub allocation, attachment-typical head selection,
and the construction of private sets and both reservoir root pools.
The full finite tree-embedding theorem from strict reduced-degree bounds and
explicit scalar margins is proved. Uniform choices satisfying those margins
from the positive-proportion host degrees are constructed in dependency order.
The unconditional positive-proportion tree-embedding theorem is proved, including
its weighted structural input. The two alternatives of the degree dichotomy
give the final Ramsey theorem below. The order-one counterexample is preserved;
no all-orders conclusion is asserted.
-/

namespace Erdos547

open SimpleGraph

/-- Every sufficiently large tree has two-colour Ramsey number at most `2*n-2`. -/
theorem eventually_tree_ramsey :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ T : SimpleGraph (Fin n), T.IsTree →
      ∀ R : SimpleGraph (Fin (2 * n - 2)), T ⊑ R ∨ T ⊑ Rᶜ := by
  obtain ⟨m₀, hm₀⟩ := eventually_ramsey_at_twice_edges
  refine ⟨m₀ + 2, ?_⟩
  intro n hn T hT
  cases n with
  | zero => omega
  | succ m =>
      have hm : m₀ ≤ m := by omega
      have hhost : 2 * (m + 1) - 2 = 2 * m := by omega
      change RamseyAt T (2 * (m + 1) - 2)
      rw [hhost]
      exact hm₀ m hm T hT

/-- The established tree Ramsey bound, uniformly for sufficiently large orders. -/
theorem erdos_547 :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ T : SimpleGraph (Fin n), T.IsTree →
      ∀ G : SimpleGraph (Fin (2 * n - 2)), T ⊑ G ∨ T ⊑ Gᶜ :=
  eventually_tree_ramsey

/-- The unrestricted version fails for the one-vertex tree. -/
theorem not_erdos_547 :
    ¬ ∀ n : ℕ, ∀ T : SimpleGraph (Fin n), T.IsTree →
      ∀ G : SimpleGraph (Fin (2 * n - 2)), T ⊑ G ∨ T ⊑ Gᶜ := by
  intro h
  apply not_ramseyAt_one_zero
  simpa [RamseyAt] using
    h 1 (⊥ : SimpleGraph (Fin 1)) SimpleGraph.IsTree.of_subsingleton

end Erdos547

#print axioms Erdos547.eventually_tree_ramsey
#print axioms Erdos547.eventually_positive_proportion_tree_embedding
#print axioms Erdos547.eventually_ramsey_at_twice_edges

#print axioms Erdos547.DPRS.exists_anchored_totals_of_degree
#print axioms Erdos547.DPRS.exists_anchored_totals_scaled_of_strict_degree
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsOptimalGEPair.anchoredTotals_of_avoiding
#print axioms Erdos547.DPRS.exists_fractional_saturation_of_deficit_bound
#print axioms Erdos547.card_many_nonTypical_le
#print axioms Erdos547.exists_small_rooted_copy_in_regular_pair
#print axioms Erdos547.exists_shrub_copy_in_regular_pair
#print axioms Erdos547.exists_parity_separator
#print axioms Erdos547.nonempty_fine_tree_partition
#print axioms Erdos547.FineTreePartition.four_part_count
#print axioms Erdos547.eventually_tree_coating
#print axioms Erdos547.regular_pair_trim_one
#print axioms Erdos547.exists_cluster_clean_subfamily
#print axioms Erdos547.eventually_equitable_regular_partition
#print axioms Erdos547.EquitableRegularPartition.reduced_min_degree_lower
#print axioms Erdos547.EquitableRegularPartition.exists_reduced_high_degree
#print axioms Erdos547.exists_typical_seed_forest_copy
#print axioms Erdos547.FineTreePartition.exists_shrub_allocation
#print axioms Erdos547.allowed_weight_lower
#print axioms Erdos547.exists_private_sets_of_class_bounds
#print axioms Erdos547.FineTreePartition.nonempty_shrub_root_data
#print axioms Erdos547.FineTreePartition.second_roots_add_one_le_seeds
#print axioms Erdos547.exists_target_capacity
#print axioms Erdos547.FineTreePartition.extend_copy_by_shrub
#print axioms Erdos547.available_vertices_half_buffer
#print axioms Erdos547.postponed_private_mass_le
#print axioms Erdos547.FineTreePartition.shrub_root_even_iff_near
#print axioms Erdos547.ShrubState.exists_insert
#print axioms Erdos547.ShrubState.available_from_capacities
#print axioms Erdos547.ShrubState.capacities_after_insert
#print axioms Erdos547.ShrubHostSetup.step_from_root
#print axioms Erdos547.ShrubHostSetup.failedAt_after_release
#print axioms Erdos547.ShrubHostSetup.postponed_group_count
#print axioms Erdos547.ShrubState.isContained_of_all_placed
#print axioms Erdos547.ShrubHostSetup.complete_reservoir_phase
#print axioms Erdos547.ShrubHostSetup.process_heads
#print axioms Erdos547.ShrubHostSetup.isContained
#print axioms Erdos547.FineTreePartition.exists_relative_shrub_heads
#print axioms Erdos547.FineTreePartition.cluster_budget_of_skew_heads
#print axioms Erdos547.FineTreePartition.group_demand_of_skew_heads
#print axioms Erdos547.exists_clusterwise_private_sets
#print axioms Erdos547.relative_allocation_mean
#print axioms Erdos547.DPRS.SkewMatching.sum_outLoad_of_part_total
#print axioms Erdos547.FineTreePartition.allowedHeads_weight
#print axioms Erdos547.FineTreePartition.allowed_attachment_degrees
#print axioms Erdos547.FineTreePartition.exists_prepared_root_sets
#print axioms Erdos547.FineTreePartition.exists_host_setup_of_skew_heads
#print axioms Erdos547.FineTreePartition.exists_setup_from_typical_seed
#print axioms Erdos547.FineTreePartition.exists_reduced_seed_copy
#print axioms Erdos547.FineTreePartition.isContained_of_reduced_degrees

#print axioms Erdos547.exists_rooted_copy_of_minDegree
#print axioms Erdos547.extend_copy_of_leaf_parent_degree
#print axioms Erdos547.isContained_of_leaf_bunch
#print axioms Erdos547.majority_edge_count
#print axioms Erdos547.majority_core_dichotomy
#print axioms Erdos547.majority_degreeMass
#print axioms Erdos547.eventually_colour_degree_dichotomy
#print axioms Erdos547.card_treeCore_add_one_le
#print axioms Erdos547.exists_high_degree_colour_core
#print axioms Erdos547.ramseyAt_of_small_bipartition
#print axioms Erdos547.ramsey_of_near_core_of_leaf_bunch
#print axioms Erdos547.extend_connected_copy
#print axioms Erdos547.extend_connected_copy_in
#print axioms Erdos547.DPRS.SkewMatching.toFractional_total
#print axioms Erdos547.DPRS.exists_maximizing_skew
#print axioms Erdos547.exists_paired_prefix
#print axioms Erdos547.card_pairChoices_outside_lower
#print axioms Erdos547.extend_of_small_exposurePotential
#print axioms Erdos547.exists_pair_exposure_contraction
#print axioms Erdos547.extend_copy_pair
#print axioms Erdos547.isContained_of_escape_many_nonleaves
#print axioms Erdos547.isContained_of_bipartite_cross_degree
#print axioms Erdos547.escape_failure_dense_configuration
#print axioms Erdos547.DPRS.exists_maximizing_skew_with_tiebreak
#print axioms Erdos547.exists_bounded_rooted_piece
#print axioms Erdos547.exists_pendant_package
#print axioms Erdos547.exists_copy_of_labelled_degree
#print axioms Erdos547.isContained_of_absorbing_pair
#print axioms Erdos547.isContained_of_dense_cross_edges
#print axioms Erdos547.ramsey_of_near_clique
#print axioms Erdos547.ramsey_of_dense_bipartite_pair
#print axioms Erdos547.ramsey_or_induced_escape
#print axioms Erdos547.ramsey_of_near_core_many_nonleaves
#print axioms Erdos547.eventually_pair_decay_threshold
#print axioms Erdos547.eventually_ramsey_of_near_core_many_nonleaves
#print axioms Erdos547.exists_weighted_vertex_pairing
#print axioms Erdos547.exists_copy_with_matching_constraints
#print axioms Erdos547.exists_leaf_assignment_of_pairing
#print axioms Erdos547.isContained_of_small_core_and_escape
#print axioms Erdos547.ramsey_of_near_core_few_nonleaves
#print axioms Erdos547.eventually_ramsey_of_near_core
#print axioms Erdos547.DPRS.FractionalMatching.ofMatching_load
#print axioms Erdos547.DPRS.exists_perfect_fractional_of_factorCritical
#print axioms Erdos547.DPRS.AnchoredPair.add_truncated
#print axioms Erdos547.DPRS.FractionalMatching.exists_maximal_bounded_with_residual
#print axioms Erdos547.DPRS.exists_skew_of_saturation_exact
#print axioms Erdos547.DPRS.exists_gallaiEdmonds_partition
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.exists_fractional_completion
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.exists_max_saturation
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsMaxSaturation.singleton_partner_le
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.exists_alternating_optimal
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsMaxSaturation.reachable_card_bound
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.exists_optimal_gePair
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsOptimalGEPair.separation_one
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsOptimalGEPair.separation_two
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsOptimalGEPair.separation_restricted
#print axioms Erdos547.DPRS.exists_improved_balancing
#print axioms Erdos547.DPRS.exists_matching_completion
#print axioms Erdos547.DPRS.SkewMatching.extractFractional_total
#print axioms Erdos547.DPRS.AnchoredPair.first_greedy
#print axioms Erdos547.DPRS.AnchoredPair.second_greedy
#print axioms Erdos547.DPRS.AnchoredPair.third_greedy
#print axioms Erdos547.DPRS.zero_skew_disjoint_capacity_counterexample
#print axioms Erdos547.DPRS.EdgeWeights.exists_two_prescribed_saturations
#print axioms Erdos547.DPRS.AnchoredPair.combine_pieces
#print axioms Erdos547.DPRS.exists_saturation_decomposition
#print axioms Erdos547.DPRS.exists_cross_anchor_split
#print axioms Erdos547.DPRS.SaturationDecomposition.remainder_saturation_lower
#print axioms Erdos547.DPRS.exists_pair_of_full_piece
#print axioms Erdos547.DPRS.SaturationDecomposition.pair_of_large_remainder
#print axioms Erdos547.DPRS.exists_two_anchor_matching
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsMaxSaturation.saturation_ge_min_degree
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.anchoredTotals_of_outside_separator
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsMaxSaturation.anchoredTotals_of_easy_skew
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsGEPair.anchoredTotals_of_skew_cover
#print axioms Erdos547.DPRS.exists_fixed_anchor_matching
#print axioms Erdos547.DPRS.Transport.exists_full_rows_of_hall
namespace Erdos547.DPRS.GallaiEdmondsPartition
#print axioms IsGEPair.anchoredTotals_of_mixed_saturation
#print axioms IsOptimalGEPair.anchoredTotals_of_balanced
#print axioms IsMaxSaturation.anchoredTotals_of_large_neighbourhood
#print axioms IsMaxSaturation.anchoredTotals_of_small_overlap
#print axioms IsOptimalGEPair.anchoredTotals_of_flabellum
#print axioms IsOptimalGEPair.exists_avoiding_anchor
#print axioms IsGEPair.restricted_reverse_mass_gt
#print axioms IsGEPair.exists_reverse_piece_below_budget
#print axioms IsGEPair.covers_neighbours_of_not_separator
#print axioms IsGEPair.exists_avoiding_allocation_of_not_separator
#print axioms IsOptimalGEPair.anchoredTotals_of_full_flabellum
end Erdos547.DPRS.GallaiEdmondsPartition
