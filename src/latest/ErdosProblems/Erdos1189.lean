/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Erdős Problem 1189: all five conclusions of the selected writeup.

Selected informal writeup:
Jeff Pickhardt and Omniscience Research Agent, "Irreducible Covering Sets:
A Solution of Erdős Problem 1189", displayed version v2 erdos_1189_solution.pdf.
https://omniscienceproject.com/papers/irreducible-covering-sets-a-solution-of-erds-problem-1189-KvXvJjCl

Formal author: OpenAI Codex.

The proof preserves set irreducibility under every residue assignment on every
proper subset. It proves Simpson's theorem and the required generalized-frame
and counting inputs of Balister, Bollobás, Morris, Sahasrabudhe, and Tiba:
https://arxiv.org/abs/1904.04806
The analytic construction uses the repository's proved prime number theorem.
See Erdos1189/STATUS.md for the proof map and verification commands.
-/

import ErdosProblems.Erdos1189.DivisorsTwelve
import ErdosProblems.Erdos1189.SunDivisors
import ErdosProblems.Erdos1189.ExtremalConstruction
import ErdosProblems.Erdos1189.Statements
import ErdosProblems.Erdos1189.GeometricSimpson
import ErdosProblems.Erdos1189.Simpson
import ErdosProblems.Erdos1189.MaximumModulus
import ErdosProblems.Erdos1189.ReciprocalUpper
import ErdosProblems.Erdos1189.DigitFrame
import ErdosProblems.Erdos1189.PrimeWeights
import ErdosProblems.Erdos1189.SeedExceptions
import ErdosProblems.Erdos1189.PrimeBudget
import ErdosProblems.Erdos1189.PaddingCutoff
import ErdosProblems.Erdos1189.MinimumModulus
import ErdosProblems.Erdos1189.MaximumReciprocal
import ErdosProblems.Erdos1189.FrameEntropy
import ErdosProblems.Erdos1189.FrameOrdering
import ErdosProblems.Erdos1189.OptimalFrameCount
import ErdosProblems.Erdos1189.CountingEntropy
import ErdosProblems.Erdos1189.PrimePowerAsymptotics
import ErdosProblems.Erdos1189.CountingSizeAsymptotic
import ErdosProblems.Erdos1189.CountingLoss
import ErdosProblems.Erdos1189.CountingNormalization
import ErdosProblems.Erdos1189.CountingLower
import ErdosProblems.Erdos1189.GridSlices
import ErdosProblems.Erdos1189.LocalLemma
import ErdosProblems.Erdos1189.FiniteLocalLemma
import ErdosProblems.Erdos1189.GridLocalLemma
import ErdosProblems.Erdos1189.IncidentLocalLemma
import ErdosProblems.Erdos1189.BoxMeasure
import ErdosProblems.Erdos1189.GridRestriction
import ErdosProblems.Erdos1189.GeometricCutoff
import ErdosProblems.Erdos1189.CoordinateDichotomy
import ErdosProblems.Erdos1189.GridProjection
import ErdosProblems.Erdos1189.ProjectedSlices
import ErdosProblems.Erdos1189.ExplorationTree
import ErdosProblems.Erdos1189.ExplorationPaths
import ErdosProblems.Erdos1189.ExplorationWeights
import ErdosProblems.Erdos1189.ExplorationFrame
import ErdosProblems.Erdos1189.FrameStructure
import ErdosProblems.Erdos1189.ProfileEntropy
import ErdosProblems.Erdos1189.RootLogPrefixSums
import ErdosProblems.Erdos1189.FrameEntropyBudget
import ErdosProblems.Erdos1189.FrameExceptionalCoordinates
import ErdosProblems.Erdos1189.UniformFrameEntropy
import ErdosProblems.Erdos1189.CompressedRanks
import ErdosProblems.Erdos1189.FiniteFamilyEncoding
import ErdosProblems.Erdos1189.CountingUpper

namespace Erdos1189

/-- The standard finite example from Problem 1189, with irreducibility
quantifying over all residue assignments on every proper subset. -/
theorem erdos1189_divisors_twelve : IsIrreducibleCoveringSet (nontrivialDivisors 12) :=
  irreducible_twelve

/-- Part (v) of the selected writeup, for every odd prime. -/
theorem erdos1189_divisor_family {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsIrreducibleCoveringSet (nontrivialDivisors (2 ^ (p - 1) * p)) :=
  irreducible_sun_divisors hp hp2

/-- The affirmative answer to Erdős's infinite-divisor-family question. -/
theorem erdos1189_infinite_divisor_sets :
    {n : ℕ | IsIrreducibleCoveringSet (nontrivialDivisors n)}.Infinite :=
  infinite_irreducible_divisor_sets

/-- The explicit extremal construction in part (ii), for every `k ≥ 5`. -/
theorem erdos1189_extremal_construction {k : ℕ} (hk : 5 ≤ k) :
    ∃ D : Finset ℕ, IsIrreducibleCoveringSet D ∧ D.card = k ∧
      D.sup id = 3 * 2 ^ (k - 3) :=
  exists_irreducible_extremal hk

/-- Part (ii), with both the universal upper bound and attainment for all `k ≥ 5`. -/
theorem erdos1189_maximum_largest_modulus : MaximumLargestModulusClaim :=
  maximumLargestModulus

/-- Covering sets of distinct nontrivial moduli have at least five members. -/
theorem erdos1189_minimum_cardinality {D : Finset ℕ} (h : IsCoveringSet D) :
    5 ≤ D.card := h.five_le_card

/-- Part (iii), including the bound `C k (log k)^2` for every `k ≥ 5`. -/
theorem erdos1189_minimum_largest_modulus : MinimumLargestModulusClaim :=
  minimumLargestModulus

/-- Part (iv), with both bounds for all sufficiently large cardinalities. -/
theorem erdos1189_maximum_reciprocal_sum : MaximumReciprocalSumClaim :=
  maximumReciprocalSum

/-- Part (i): the sharp counting asymptotic for irreducible modulus sets. -/
theorem erdos1189_counting_asymptotic : CountingAsymptotic := counting_asymptotic

/-- All five conclusions of the selected writeup, with irreducibility testing
every residue assignment on every proper subset and with the `k ≥ 5` range. -/
theorem erdos1189 : Erdos1189Statement :=
  ⟨fun _ h => h.five_le_card, counting_asymptotic, maximumLargestModulus,
    minimumLargestModulus, maximumReciprocalSum,
    fun _ hp hp2 => irreducible_sun_divisors hp hp2, infinite_irreducible_divisor_sets⟩

theorem erdos_1189 : Erdos1189Statement := erdos1189

#print axioms erdos1189
-- 'Erdos1189.erdos1189' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms erdos1189_counting_asymptotic
-- 'Erdos1189.erdos1189_counting_asymptotic' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms erdos1189_maximum_reciprocal_sum
-- 'Erdos1189.erdos1189_maximum_reciprocal_sum' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms erdos1189_minimum_largest_modulus
-- 'Erdos1189.erdos1189_minimum_largest_modulus' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms erdos1189_maximum_largest_modulus
-- 'Erdos1189.erdos1189_maximum_largest_modulus' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms erdos1189_minimum_cardinality
-- 'Erdos1189.erdos1189_minimum_cardinality' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms erdos1189_extremal_construction
-- 'Erdos1189.erdos1189_extremal_construction' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms erdos1189_divisor_family
-- 'Erdos1189.erdos1189_divisor_family' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms erdos1189_infinite_divisor_sets
-- 'Erdos1189.erdos1189_infinite_divisor_sets' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms erdos1189_divisors_twelve
-- 'Erdos1189.erdos1189_divisors_twelve' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms IsCoveringSet.one_le_reciprocalSum
-- 'Erdos1189.IsCoveringSet.one_le_reciprocalSum' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms Grid.simpson_grid
-- 'Erdos1189.Grid.simpson_grid' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms IsMinimalCoveringSystem.simpson
-- 'Erdos1189.IsMinimalCoveringSystem.simpson' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms truncated_digit_frame
-- 'Erdos1189.truncated_digit_frame' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms eventually_reciprocalSum_le_two_log
-- 'Erdos1189.eventually_reciprocalSum_le_two_log' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms exists_uniform_seed_constant
-- 'Erdos1189.exists_uniform_seed_constant' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms optimal_frame_count
-- 'Erdos1189.optimal_frame_count' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms tau_pos
-- 'Erdos1189.tau_pos' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms countingEntropy_lower_count
-- 'Erdos1189.countingEntropy_lower_count' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms prime_weight_square_sum_ratio
-- 'Erdos1189.prime_weight_square_sum_ratio' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms countingSize_asymptotic
-- 'Erdos1189.countingSize_asymptotic' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms counting_frame_log_eventually_lower
-- 'Erdos1189.counting_frame_log_eventually_lower' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms counting_frame_cardinality_lower
-- 'Erdos1189.counting_frame_cardinality_lower' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms irreducibleCount_eventually_lower
-- 'Erdos1189.irreducibleCount_eventually_lower' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms finite_local_lemma
-- 'Erdos1189.finite_local_lemma' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms Grid.box_local_lemma
-- 'Erdos1189.Grid.box_local_lemma' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms Grid.exists_large_incident_weight
-- 'Erdos1189.Grid.exists_large_incident_weight' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms exists_uniform_coordinate_dichotomy
-- 'Erdos1189.exists_uniform_coordinate_dichotomy' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms exists_uniform_exploration_trees
-- 'Erdos1189.exists_uniform_exploration_trees' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms Grid.ExplorationTree.bad_coordinate_sum_le
-- 'Erdos1189.Grid.ExplorationTree.bad_coordinate_sum_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms Grid.ExplorationTree.good_boxes_disjoint
-- 'Erdos1189.Grid.ExplorationTree.good_boxes_disjoint' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms exists_uniform_generalized_frames
-- 'Erdos1189.exists_uniform_generalized_frames' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms exists_uniform_profileEntropy_bound
-- 'Erdos1189.exists_uniform_profileEntropy_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms sum_rootLog_prefix_eventually_upper
-- 'Erdos1189.sum_rootLog_prefix_eventually_upper' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms frame_and_remainder_entropy_budget
-- 'Erdos1189.frame_and_remainder_entropy_budget' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms exists_uniform_frame_entropy_bounds
-- 'Erdos1189.exists_uniform_frame_entropy_bounds' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms familyUnionUniverse_card_le_exp
-- 'Erdos1189.familyUnionUniverse_card_le_exp' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos1189
