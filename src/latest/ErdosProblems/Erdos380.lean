/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos380.AntiSieve
import ErdosProblems.Erdos380.Intervals
import ErdosProblems.Erdos380.PrimeMoments
import ErdosProblems.Erdos380.ConductorMoments
import ErdosProblems.Erdos380.PrimeProductMixing
import ErdosProblems.Erdos380.CountComparison
import ErdosProblems.Erdos380.ShortIntervalPrime
import ErdosProblems.Erdos380.PrimeCounts
import ErdosProblems.Erdos380.PrimeReciprocals
import ErdosProblems.Erdos380.MixingScale
import ErdosProblems.Erdos380.FiniteProbability
import ErdosProblems.Erdos380.ShiftedPrimeHits
import ErdosProblems.Erdos380.PrimeProgressionSieve
import ErdosProblems.Erdos380.SmallPrimeTupleMoments
import ErdosProblems.Erdos380.SmoothTupleProbability
import ErdosProblems.Erdos380.SmoothRankin
import ErdosProblems.Erdos380.SmoothLogLower
import ErdosProblems.Erdos380.SingletonCompression
import ErdosProblems.Erdos380.LongSmoothIntervals
import ErdosProblems.Erdos380.SquareExclusions
import ErdosProblems.Erdos380.SingletonLower
import ErdosProblems.Erdos380.SieveOrder
import ErdosProblems.Erdos380.ShortExcessReduction
import ErdosProblems.Erdos380.SaddleParameters
import ErdosProblems.Erdos380.ShortExcessScale
import ErdosProblems.Erdos380.SingletonScaleLower
import ErdosProblems.Erdos380.ExcessNegligible

/-!
# Erdős Problem 380: the two-sided asymptotic

`intervalPrime u v` is the greatest prime factor of the entire product
`∏ n ∈ Icc u v, n`. A bad interval is positive and nonempty, its product is
greater than one, and the square of this prime divides that product.
Witnessing interval endpoints need not lie below the counting cutoff.

The proof counts singleton anchors and shows that all additional covered
points contribute little-o of that count. Explicit smooth-number bounds and
prime compression replace a local smooth-number asymptotic. Counting short
interval neighbors by their distance from an anchor gives a harmonic sum.
The remaining intervals are controlled by one high-order smooth-run sieve
and a large-square exclusion, without a prime-gap theorem or a subdivision
by intermediate interval lengths. All parameter inequalities and analytic
inputs used by these estimates are proved in the imported development.

The convention `largestPrimeFactor 1 = 1` puts `1` into the displayed
comparison set. Its contribution is handled explicitly by
`repeatedLargestPrimeCount_isEquivalent_A`.
-/

open Filter Asymptotics
open scoped Asymptotics Topology

namespace Erdos380

/-- The original two-sided asymptotic for integers covered by bad intervals. -/
theorem erdos380 : B ~[Filter.atTop] repeatedLargestPrimeCount :=
  bad_asymptotic_iff_excess_littleO.mpr excessCount_isLittleO_A

/-- Equivalently, the ratio of the exact two counting functions tends to one. -/
theorem erdos380_ratio : Tendsto (fun x : ℝ => B x / repeatedLargestPrimeCount x)
    atTop (𝓝 1) := by
  have hnonzero : ∀ᶠ x : ℝ in atTop, repeatedLargestPrimeCount x ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [repeatedLargestPrimeCount_eq_A_add_one hx]
    have hA := A_nonneg x
    linarith
  exact (isEquivalent_iff_tendsto_one hnonzero).mp erdos380

/-- The canonical statement of Erdős problem 380. -/
theorem erdos_380 : B ~[Filter.atTop] repeatedLargestPrimeCount :=
  erdos380

end Erdos380

#print axioms Erdos380.A_le_B
#print axioms Erdos380.intervalPrime_eq_sup
#print axioms Erdos380.BadInterval.exists_square_anchor_of_short
#print axioms Erdos380.BadInterval.right_lt_two_mul_left
#print axioms Erdos380.prime_character_tenth_moment_le
#print axioms Erdos380.ten_prime_residue_uniform_error_le
#print axioms Erdos380.nonprincipalMeanMoment_le_divisorMeanMoment
#print axioms Erdos380.ten_prime_product_mixing_bound
#print axioms Erdos380.A_eq_sum_smoothCount
#print axioms Erdos380.bad_asymptotic_iff_excess_littleO
#print axioms Erdos380.BadInterval.not_prime_mem
#print axioms Erdos380.BadInterval.exists_square_anchor_of_cubic
#print axioms Erdos380.eventually_dyadicPrimes_card_bounds
#print axioms Erdos380.exists_prime_band_totient_bound
#print axioms Erdos380.exists_uniform_ten_prime_mixing_bound
#print axioms Erdos380.finite_centered_second_moment_le
#print axioms Erdos380.finite_chebyshev
#print axioms Erdos380.expect_ten_prime_residue_pair_error_le
#print axioms Erdos380.primeResidueHitCount_second_moment_le
#print axioms Erdos380.exists_uniform_shifted_prime_hit_tail
#print axioms Erdos380.residueClassSurvivors_card_le_productCutoff
#print axioms Erdos380.coprime_harmonic_ge_totient_ratio
#print axioms Erdos380.sieveDenominator_ge_log
#print axioms Erdos380.affinePrimesAbove_card_le_log
#print axioms Erdos380.exists_uniform_dyadicPrimeResidueProbability_bound
#print axioms Erdos380.finite_high_moment_from_joint_bounds
#print axioms Erdos380.smallPrime_joint_bound
#print axioms Erdos380.exists_uniform_smallPrime_fiftieth_moment
#print axioms Erdos380.exists_uniform_smallPrime_shift_sum_tail
#print axioms Erdos380.le_square_cutoff_mul_primeRadical
#print axioms Erdos380.smooth_shift_log_le_masses
#print axioms Erdos380.exists_uniform_smoothShift_probability_bound
#print axioms Erdos380.smoothCount_growing_parameter_upper
#print axioms Erdos380.exists_smoothCount_dyadic_exponential_lower
#print axioms Erdos380.exists_compressedPrime_scale_bounds
#print axioms Erdos380.exists_largeCofactorSingletons_dilation_bound
#print axioms Erdos380.exists_badInterval_square_anchor_threshold
#print axioms Erdos380.exists_uniform_longBadPoints_card_bound
#print axioms Erdos380.exists_longBadPoints_card_bound
#print axioms Erdos380.exists_largeIntervalPrime_card_bound
#print axioms Erdos380.exists_singletonBadUpTo_dyadic_exponential_lower
#print axioms Erdos380.residueClassSurvivors_card_le_uniform
#print axioms Erdos380.exists_uniform_anchoredSmoothRunStarts_bound
#print axioms Erdos380.exists_uniform_badPointsInLengthBand_bound
#print axioms Erdos380.exists_interval_sieve_order
#print axioms Erdos380.top_prime_product_cofactor_unique
#print axioms Erdos380.validPrimeRecords_card_le_largeCofactorSingletons
#print axioms Erdos380.exists_primeBoxMass_normalization
#print axioms Erdos380.SingletonBad.canonicalPrimeRecord_value
#print axioms Erdos380.exists_uniform_goodPrimeBoxAnchors_bound
#print axioms Erdos380.exists_uniform_goodEligibleAnchors_bound
#print axioms Erdos380.exists_uniform_goodAnchorNeighbors_bound
#print axioms Erdos380.exists_shortExcess_normalized_bound
#print axioms Erdos380.scaleBase_saddle_relation
#print axioms Erdos380.eventually_scaleBase_pow_le
#print axioms Erdos380.eventually_log_pow_le_scaleBase
#print axioms Erdos380.neighborErrorFactor_tendsto_zero
#print axioms Erdos380.exists_eventually_shortExcess_scale_bound
#print axioms Erdos380.eventually_singletonBadUpTo_scale_lower
#print axioms Erdos380.eventually_ineligibleSingletons_scale_bound
#print axioms Erdos380.shortExcess_isLittleO_singletonCount
#print axioms Erdos380.excessPointsUpTo_card_le_short_large_runs
#print axioms Erdos380.eventually_smoothRunStarts_scale_bound
#print axioms Erdos380.eventually_largeIntervalPrime_scale_bound
#print axioms Erdos380.excessCount_isLittleO_A
#print axioms Erdos380.erdos380
#print axioms Erdos380.erdos380_ratio
