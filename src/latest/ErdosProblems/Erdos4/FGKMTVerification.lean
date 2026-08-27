import ErdosProblems.Erdos4
import ErdosProblems.Erdos4.FGKMTFiniteCovering
import ErdosProblems.Erdos4.FGKMTLogarithmicProfile
import ErdosProblems.Erdos4.FGKMTUniformZeroFree
import ErdosProblems.Erdos4.FGKMTUniformTwists
import ErdosProblems.Erdos4.FGKMTPrimeDistribution
import ErdosProblems.Erdos4.FGKMTGrowingDistribution
import ErdosProblems.Erdos4.FGKMTRationalMass
import ErdosProblems.Erdos4.FGKMTGoodDivisorProbability
import ErdosProblems.Erdos4.FGKMTHarmonicModulusSize
import ErdosProblems.Erdos4.FGKMTSieveProfileParameters
import ErdosProblems.Erdos4.FGKMTSmallShifts
import ErdosProblems.Erdos4.FGKMTTranslatedEdges
import ErdosProblems.Erdos4.FGKMTSieveDivisorLaw
import ErdosProblems.Erdos4.FGKMTHarmonicErrorBudget
import ErdosProblems.Erdos4.FGKMTGrowingDivisorLaw
import ErdosProblems.Erdos4.FGKMTModulusLevel
import ErdosProblems.Erdos4.FGKMTGrowingIdealGain
import ErdosProblems.Erdos4.FGKMTGrowingTrueGain
import ErdosProblems.Erdos4.FGKMTCombinedPrimeFamily
import ErdosProblems.Erdos4.FGKMTSourceLowerBound
import ErdosProblems.Erdos4.FGKMTLowerDegreeCovering
import ErdosProblems.Erdos4.FGKMTRationalNormalization
import ErdosProblems.Erdos4.FGKMTAllowedResidueCount
import ErdosProblems.Erdos4.FGKMTGrowingPrimeExposure
import ErdosProblems.Erdos4.FGKMTFullTupleNormalizerLoss
import ErdosProblems.Erdos4.FGKMTTranslatedMomentLaw
import ErdosProblems.Erdos4.FGKMTGrowingInitialConfiguration
import ErdosProblems.Erdos4.FGKMTSourcePartition

/-! Exact-statement and kernel-dependency audit of the unconditional FGKMT18 theorem. -/

example :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∃ n : ℕ, (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ X ∧
        C * (Real.log X * Real.log (Real.log X) *
          Real.log (Real.log (Real.log (Real.log X))) /
            Real.log (Real.log (Real.log X))) ≤
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n :=
  Erdos4.fgkmt18

example (C : ℝ) (hC : 0 < C) : Erdos4.Erdos4For C := Erdos4.erdos4 C hC

#print axioms Erdos4.FGKMT.round_accuracy
#print axioms Erdos4.FGKMT.finite_covering_accuracy
#print axioms Erdos4.FGKMT.finite_covering
#print axioms Erdos4.VariableMaynard.parameter_ratio_gt
#print axioms Erdos4.VariableMaynard.candidate_admissible
#print axioms Erdos4.FGKMT.logarithmic_profile_family
#print axioms Erdos4.FGKMT.exists_landauPage_unique
#print axioms Erdos4.FGKMT.exists_uniform_zero_free_prime_excision
#print axioms Erdos4.FGKMT.exists_uniform_twisted_sum
#print axioms Erdos4.FGKMT.exists_uniform_primitive_maximum
#print axioms Erdos4.FGKMT.exists_exponential_centered_distribution
#print axioms Erdos4.FGKMT.exists_exponential_prime_distribution
#print axioms Erdos4.FGKMT.exists_growing_dimension_distribution
#print axioms Erdos4.FGKMT.squarefreeHarmonic_uniform_log_error
#print axioms Erdos4.FGKMT.reciprocal_harmonic_mass_error
#print axioms Erdos4.FGKMT.reciprocal_sq_harmonic_mass_error
#print axioms Erdos4.FGKMT.rationalProduct_good_probability
#print axioms Erdos4.FGKMT.rationalSquareLaw_prob_divisor_le
#print axioms Erdos4.FGKMT.exists_harmonicModulus_density_lower
#print axioms Erdos4.FGKMT.harmonicTransferError_excision
#print axioms Erdos4.FGKMT.rationalMass_moment_budget
#print axioms Erdos4.FGKMT.sieveProfileScale_moment_budget
#print axioms Erdos4.FGKMT.exists_small_admissible_shifts
#print axioms Erdos4.FGKMT.translated_anchor_mem
#print axioms Erdos4.FGKMT.translatedEdge_common_point_unique
#print axioms Erdos4.FGKMT.sieveDivisorLaw_good_probability
#print axioms Erdos4.FGKMT.eventually_sieve_harmonic_error
#print axioms Erdos4.FGKMT.eventually_growing_divisor_probability
#print axioms Erdos4.FGKMT.eventually_growing_modulus_level
#print axioms Erdos4.FGKMT.rationalLinearLaw_prob_divisor_le
#print axioms Erdos4.FGKMT.independent_bad_coprime_probability
#print axioms Erdos4.FGKMT.mixedDivisor_good_mass_half
#print axioms Erdos4.FGKMT.coordinateDivisor_labelOfTuple
#print axioms Erdos4.FGKMT.rationalCoefficient_energy_upper
#print axioms Erdos4.FGKMT.faceTuple_product_le
#print axioms Erdos4.FGKMT.faceLabelPair_injOn
#print axioms Erdos4.FGKMT.rationalIdealForm_energy_gain
#print axioms Erdos4.FGKMT.rationalSieve_sum_ideal_gain
#print axioms Erdos4.FGKMT.rationalSieve_dimension_gain
#print axioms Erdos4.FGKMT.eventually_growing_ideal_gain
#print axioms Erdos4.FGKMT.rationalSlice_energy_le
#print axioms Erdos4.FGKMT.rational_ideal_sub_error_le_true
#print axioms Erdos4.FGKMT.harmonic_window_density_lower
#print axioms Erdos4.FGKMT.exists_window_density_uniform_lower
#print axioms Erdos4.FGKMT.rational_ideal_sum_sub_tail_le_true
#print axioms Erdos4.FGKMT.eventually_growing_true_gain
#print axioms Erdos4.FGKMT.smallAnchorGoodStates_card
#print axioms Erdos4.FGKMT.smallMaskFourier_norm_le_density_ratio
#print axioms Erdos4.FGKMT.harmonicDensity_smallPresieve_lower
#print axioms Erdos4.FGKMT.norm_rationalUnitFourier_le
#print axioms Erdos4.FGKMT.rationalUnitFourier_eq_zero_of_large_conductor
#print axioms Erdos4.FGKMT.smallProductFourier_eq_transform
#print axioms Erdos4.FGKMT.smallSievePrime_density_ratio
#print axioms Erdos4.FGKMT.combinedSievePrime_injective
#print axioms Erdos4.FGKMT.aggregateUnitWeight_inversion
#print axioms Erdos4.FGKMT.aggregateUnitFourier_conductor_le
#print axioms Erdos4.ProductPrimeMeanSquare.weighted_source_error_mean_square
#print axioms Erdos4.ProductPrimeMeanSquare.activation_source_error_mean_square
#print axioms Erdos4.FGKMT.aggregateUnitWeight_truncated_inversion
#print axioms Erdos4.FGKMT.aggregate_weighted_source_average_eq
#print axioms Erdos4.FGKMT.high_masked_activation_error_mean_square
#print axioms Erdos4.FGKMT.high_masked_exceptional_targets_card_le
#print axioms Erdos4.FGKMT.card_lowMaskedIndices_le
#print axioms Erdos4.FGKMT.low_masked_source_error_le
#print axioms Erdos4.FGKMT.aggregate_real_source_average_lower
#print axioms Erdos4.FGKMT.equalizedFamily_degree
#print axioms Erdos4.FGKMT.equalizedFamily_support
#print axioms Erdos4.FGKMT.geometric_degree_covering
#print axioms Erdos4.FGKMT.lower_degree_covering
#print axioms Erdos4.FGKMT.maskedTranslatedWeight_anchor
#print axioms Erdos4.FGKMT.rational_sum_abs_coefficient_le
#print axioms Erdos4.FGKMT.maskedTranslatedWeight_le
#print axioms Erdos4.FGKMT.allowedResidueCount_density_error
#print axioms Erdos4.FGKMT.rational_coefficient_joint_sum_eq_energy
#print axioms Erdos4.FGKMT.maskedTranslatedNormalizer_eq_pairs
#print axioms Erdos4.FGKMT.maskedTranslatedNormalizer_error_le
#print axioms Erdos4.FGKMT.maskedTranslatedLabelCount_error
#print axioms Erdos4.FGKMT.maskedTranslatedPairCount_error
#print axioms Erdos4.FGKMT.maskedTranslatedNormalizer_crt_error
#print axioms Erdos4.FGKMT.maskedTranslatedNormalizer_tail_error
#print axioms Erdos4.FGKMT.maskedTranslatedNormalizer_bounds
#print axioms Erdos4.FGKMT.maskedTranslatedNormalizer_pos_of_lower
#print axioms Erdos4.FGKMT.rationalCenterLaw_weight
#print axioms Erdos4.FGKMT.rationalCenterLaw_prob_eq_sum
#print axioms Erdos4.FGKMT.rationalCenterLaw_weight_le_modulus
#print axioms Erdos4.FGKMT.translatedSites_card
#print axioms Erdos4.FGKMT.translatedSites_common_point_unique
#print axioms Erdos4.FGKMT.translatedCenter_incidence_eq
#print axioms Erdos4.FGKMT.rationalBaseIncidence_eq_unitWeight
#print axioms Erdos4.FGKMT.rationalSourceIncidence_fourier_lower
#print axioms Erdos4.FGKMT.eventually_growing_weight_numerator
#print axioms Erdos4.FGKMT.eventually_growing_center_laws
#print axioms Erdos4.FGKMT.norm_primeCharacterSum_le
#print axioms Erdos4.FGKMT.norm_primeCharacterInterval_le_excised
#print axioms Erdos4.FGKMT.productEntry_nonprincipal
#print axioms Erdos4.FGKMT.low_masked_interval_error
#print axioms Erdos4.FGKMT.eventually_smallPresieve_cubic_decay
#print axioms Erdos4.FGKMT.exists_growing_low_mode_bound
#print axioms Erdos4.FGKMT.growingRadius_tendsto
#print axioms Erdos4.FGKMT.growingRadius_pow_fifty_le
#print axioms Erdos4.FGKMT.growing_large_local_decay_bound
#print axioms Erdos4.FGKMT.growing_highMaskedCoefficient_norm_le
#print axioms Erdos4.FGKMT.eventually_growing_smallModulus_le_radius
#print axioms Erdos4.FGKMT.eventually_growing_fourier_cutoff
#print axioms Erdos4.FGKMT.growing_prime_coprime_modulus
#print axioms Erdos4.FGKMT.eventually_growing_high_error_mean_square
#print axioms Erdos4.FGKMT.growing_maskedFourierScale_pos
#print axioms Erdos4.FGKMT.exists_growing_principal_scale_gain
#print axioms Erdos4.FGKMT.eventually_growing_principal_density_gain
#print axioms Erdos4.FGKMT.growingRadius_sq_le_source_start
#print axioms Erdos4.FGKMT.eventually_growing_source_count
#print axioms Erdos4.FGKMT.eventually_growing_source_supply
#print axioms Erdos4.FGKMT.exists_norm_exceptional_finset
#print axioms Erdos4.FGKMT.high_error_budget_cancel
#print axioms Erdos4.FGKMT.low_error_budget
#print axioms Erdos4.FGKMT.incidence_gain_budget
#print axioms Erdos4.FGKMT.exists_growing_prime_exposure
#print axioms Erdos4.FGKMT.tuple_extension_mean_upper
#print axioms Erdos4.FGKMT.tuple_extension_mean_lower
#print axioms Erdos4.FGKMT.mixed_product_lower
#print axioms Erdos4.FGKMT.mean_mixed_square_product
#print axioms Erdos4.FGKMT.mixed_square_product_upper
#print axioms Erdos4.FGKMT.conditionalResidueLaw_mean
#print axioms Erdos4.FGKMT.full_tuple_mixed_moment_bounds
#print axioms Erdos4.FGKMT.FiniteLaw.mean_weighted_sq_sub_one
#print axioms Erdos4.FGKMT.FiniteLaw.weighted_normalizer_deviation
#print axioms Erdos4.FGKMT.FiniteLaw.bad_normalizer_weighted_loss
#print axioms Erdos4.FGKMT.FiniteLaw.normalized_weighted_deviation
#print axioms Erdos4.FGKMT.full_tuple_normalizer_deviation
#print axioms Erdos4.FGKMT.full_tuple_bad_normalizer_loss
#print axioms Erdos4.FGKMT.rationalCenterMass_nonneg
#print axioms Erdos4.FGKMT.rationalCenterMass_sum
#print axioms Erdos4.FGKMT.rationalCenterMass_eq_weight
#print axioms Erdos4.FGKMT.rationalCenterMass_hitMass
#print axioms Erdos4.FGKMT.eventually_growing_joint_accuracy
#print axioms Erdos4.FGKMT.full_tuple_total_moment_bounds
#print axioms Erdos4.FGKMT.full_tuple_total_variance
#print axioms Erdos4.FGKMT.initialEdgeLaw_support
#print axioms Erdos4.FGKMT.initial_degree_lower_of_retained
#print axioms Erdos4.FGKMT.center_pinned_prob_eq_hittingMass
#print axioms Erdos4.FGKMT.full_tuple_discarded_total_mean
#print axioms Erdos4.FGKMT.full_tuple_retained_lower_tail
#print axioms Erdos4.FGKMT.translated_initial_degree_lower_tail
#print axioms Erdos4.FGKMT.rational_initial_degree_lower_tail
#print axioms Erdos4.FGKMT.translatedInitialEdgeLaw_card_le
#print axioms Erdos4.FGKMT.translatedInitialEdgeLaw_residue
#print axioms Erdos4.FGKMT.translatedInitialEdgeLaw_survives
#print axioms Erdos4.FGKMT.translatedInitialEdgeLaw_marginal_le
#print axioms Erdos4.FGKMT.translatedInitialEdgeLaw_pair_source_unique
#print axioms Erdos4.FGKMT.translatedInitialEdgeLaw_pair_sum_le
#print axioms Erdos4.FGKMT.uniform_surviving_event_eq
#print axioms Erdos4.FGKMT.mean_initialBadSurvivors_le
#print axioms Erdos4.FGKMT.exists_initial_sieve_good_vertices
#print axioms Erdos4.FGKMT.FiniteLaw.restrictVertices_pair
#print axioms Erdos4.FGKMT.FiniteLaw.restrictVertices_support
#print axioms Erdos4.FGKMT.exists_rational_initial_configuration
#print axioms Erdos4.FGKMT.eventually_growingIndex_log_bounds
#print axioms Erdos4.FGKMT.eventually_growing_outer_log_budget
#print axioms Erdos4.FGKMT.eventually_growing_random_cutoff_logs
#print axioms Erdos4.FGKMT.exists_growing_random_density_bounds
#print axioms Erdos4.FGKMT.eventually_growing_random_density_lower
#print axioms Erdos4.FGKMT.eventually_growing_random_inverse_power
#print axioms Erdos4.FGKMT.eventually_growing_initial_loss_bounds
#print axioms Erdos4.FGKMT.eventually_growing_initial_error_budget
#print axioms Erdos4.FGKMT.eventually_growing_gap_length_bounds
#print axioms Erdos4.FGKMT.eventually_growing_random_end_le_radius
#print axioms Erdos4.FGKMT.initial_scale_product
#print axioms Erdos4.FGKMT.initial_configuration_count_budget
#print axioms Erdos4.FGKMT.eventually_growing_target_count
#print axioms Erdos4.FGKMT.eventually_growing_count_budgets
#print axioms Erdos4.FGKMT.exists_growing_initial_configuration
#print axioms Erdos4.FGKMT.exp_neg_le_one_sub_two_thirds
#print axioms Erdos4.FGKMT.FiniteLaw.independent_weighted_lower_tail
#print axioms Erdos4.FGKMT.dyadic_round_total
#print axioms Erdos4.FGKMT.exists_dyadic_source_partition
#print axioms Erdos4.FGKMT.assignedChoice_covers
#print axioms Erdos4.FGKMT.source_covering
#print axioms Erdos4.FGKMT.dyadic_log_density_bounds
#print axioms Erdos4.FGKMT.propagationCoefficient_exp_bound
#print axioms Erdos4.FGKMT.coveringThreshold_exp_lower
#print axioms Erdos4.FGKMT.eventually_growing_cover_sparsity
#print axioms Erdos4.FGKMT.eventually_growing_partition_budget
#print axioms Erdos4.FGKMT.exists_growing_prime_covering
#print axioms Erdos4.FGKMT.eventually_prime_harmonic_bounds
#print axioms Erdos4.FGKMT.rpow_le_log_chord
#print axioms Erdos4.FGKMT.eventually_sharp_rankin_euler
#print axioms Erdos4.FGKMT.eventually_growing_rankin_euler
#print axioms Erdos4.FGKMT.eventually_growing_smooth_bound
#print axioms Erdos4.FGKMT.exists_cover_of_residue_choices
#print axioms Erdos4.FGKMT.exists_complete_cover_from_choices
#print axioms Erdos4.FGKMT.eventually_growing_zero_parameters
#print axioms Erdos4.FGKMT.exists_growing_reserve
#print axioms Erdos4.FGKMT.exists_growing_interval_cover
#print axioms Erdos4.FGKMT.nth_prime_succ_le_twice
#print axioms Erdos4.FGKMT.exists_gap_with_right_endpoint
#print axioms Erdos4.FGKMT.exists_growing_prime_gaps
#print axioms Erdos4.FGKMT.realOuterScale_compare
#print axioms Erdos4.FGKMT.eventually_endpoint_scale_compare
#print axioms Erdos4.FGKMT.exists_all_endpoint_gaps
#print axioms Erdos4.fgkmt18
#print axioms Erdos4.erdos4
