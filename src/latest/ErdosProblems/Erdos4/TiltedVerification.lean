import ErdosProblems.Erdos4.TiltedPrimeAccuracy
import ErdosProblems.Erdos4.TiltedBlockCorrelation
import ErdosProblems.Erdos4.TiltedCappedLaw
import ErdosProblems.Erdos4.TiltedTargets
import ErdosProblems.Erdos4.TiltedRootedGlobal
import ErdosProblems.Erdos4.TiltedBlockLower
import ErdosProblems.Erdos4.TiltedRoughCount
import ErdosProblems.Erdos4.TiltedDensity
import ErdosProblems.Erdos4.TiltedPartitionDivisors
import ErdosProblems.Erdos4.TiltedFiniteGcdMoments
import ErdosProblems.Erdos4.TiltedBlockVariance
import ErdosProblems.Erdos4.TiltedPartitionCover
import ErdosProblems.Erdos4.TiltedCompositeErrorBudget
import ErdosProblems.Erdos4.TiltedCompositeFamily
import ErdosProblems.Erdos4.TiltedCompositeCover
import ErdosProblems.Erdos4.TiltedPrimeLayer
import ErdosProblems.Erdos4Tilted

/-! Kernel dependency audit for the completed tilted-sieve components. -/

#print axioms Erdos4.Tilted.roughComposites_survival
#print axioms Erdos4.Tilted.rootedSieveLaw_prob_all
#print axioms Erdos4.Tilted.exists_all_fiber_partition
#print axioms Erdos4.Tilted.fiber_product_squarefree
#print axioms Erdos4.Tilted.eventNormalizer_cap_le
#print axioms Erdos4.Tilted.cappedLabelLaw_support
#print axioms Erdos4.Tilted.eventually_tilted_prime_accuracy
#print axioms Erdos4.Tilted.localLaw_pair_ratio_le
#print axioms Erdos4.Tilted.sieveLaw_pair_ratio_uniform
#print axioms Erdos4.Tilted.rootedSieveLaw_pair_ratio_uniform
#print axioms Erdos4.Tilted.sieveLaw_block_lower
#print axioms Erdos4.Tilted.roughComposites_card_le
#print axioms Erdos4.Tilted.roughNonsquarefree_card_le
#print axioms Erdos4.Tilted.exists_tilted_density_bounds
#print axioms Erdos4.Tilted.partition_divisor_count_of_interval
#print axioms Erdos4.Tilted.partition_gcd_pair_count
#print axioms Erdos4.Tilted.rooted_gcd_pair_count
#print axioms Erdos4.Tilted.squarefree_tilt_moment
#print axioms Erdos4.Tilted.partition_gcd_tilt_moment
#print axioms Erdos4.Tilted.rooted_gcd_tilt_moment
#print axioms Erdos4.Tilted.disjoint_block_variance
#print axioms Erdos4.Tilted.rooted_block_variance
#print axioms Erdos4.Tilted.eventually_actual_composite_survival
#print axioms Erdos4.Tilted.eventually_actual_block_weight_bounds
#print axioms Erdos4.Tilted.eventually_actual_gcd_error
#print axioms Erdos4.Tilted.exists_independent_cover
#print axioms Erdos4.Tilted.partitionMissCost_mean_le
#print axioms Erdos4.Tilted.exists_partition_cover
#print axioms Erdos4.Tilted.CompositeFiberFamily.part_squarefree
#print axioms Erdos4.Tilted.CompositeFiberFamily.companions_disjoint
#print axioms Erdos4.Tilted.eventually_composite_block_variance
#print axioms Erdos4.Tilted.eventually_composite_root_variance
#print axioms Erdos4.Tilted.exists_composite_cover_cost
#print axioms Erdos4.Tilted.pinned_subsetNormalizer_variance
#print axioms Erdos4.Tilted.capped_prime_degree_error
#print axioms Erdos4.Tilted.exists_primeExposureData
#print axioms Erdos4.Tilted.exists_prime_cover_cost
#print axioms Erdos4.Tilted.exists_tilted_interval_cover
#print axioms Erdos4.Tilted.maximumCoverLength_spec
/- The final statements must remain free of additional axioms. -/
/--
info: 'Erdos4.Tilted.covering_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Erdos4.Tilted.covering_theorem
/--
info: 'Erdos4.Tilted.prime_gap_corollary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Erdos4.Tilted.prime_gap_corollary
/--
info: 'Erdos4.Tilted.all_endpoint_consecutive_prime_gaps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Erdos4.Tilted.all_endpoint_consecutive_prime_gaps
