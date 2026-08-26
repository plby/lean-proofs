/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An unconditional disproof of Erdős Problem 521 for one infinite iid sequence
of symmetric signs, counting distinct real roots.

Informal sources:
- Paul Erdős (problem statement)
- XianJun An and Vincent Lin (the selected oscillation claim)
- The 29 April 2026 working note, Section 7 (cone records)
- Rob Sneiderman (finite-prefix restart)
- Do (the interior-root strong-law strategy)
- Can–Nguyen (local root and sign-grid estimates)

Formal author: Codex.

https://www.erdosproblems.com/521
https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_521_Kac.pdf
https://github.com/Robby955/erdos-521-zero-one
https://arxiv.org/html/2403.06353v2
https://arxiv.org/html/2311.15446v2
-/
import ErdosProblems.Erdos521.CoefficientProbability
import ErdosProblems.Erdos521.ProbabilitySpaceTransfer
import ErdosProblems.Erdos521.CentralStrongLaw
import ErdosProblems.Erdos521.InteriorStrongLaw
import ErdosProblems.Erdos521.RootStatistics
import ErdosProblems.Erdos521.SmallBall
import ErdosProblems.Erdos521.MaximalMoment
import ErdosProblems.Erdos521.CircularMaximal
import ErdosProblems.Erdos521.JensenDisk
import ErdosProblems.Erdos521.LocalMaximal
import ErdosProblems.Erdos521.EndpointLimit
import ErdosProblems.Erdos521.SignSymmetry
import ErdosProblems.Erdos521.RepulsionSmallBall
import ErdosProblems.Erdos521.RepulsionGrid
import ErdosProblems.Erdos521.AlmostSureRepulsion
import ErdosProblems.Erdos521.BulkStability
import ErdosProblems.Erdos521.InteriorStability
import ErdosProblems.Erdos521.DyadicInterpolation
import ErdosProblems.Erdos521.TwoRootProbability
import ErdosProblems.Erdos521.ComplexMoments
import ErdosProblems.Erdos521.NormalizedLocalRoots
import ErdosProblems.Erdos521.NormalizedTwoRoots
import ErdosProblems.Erdos521.SignGridProbability
import ErdosProblems.Erdos521.WeightedCentralLimit
import ErdosProblems.Erdos521.ValueCentralLimit
import ErdosProblems.Erdos521.VectorCentralLimit
import ErdosProblems.Erdos521.SignGridLowerBound
import ErdosProblems.Erdos521.CorrelationLimits
import ErdosProblems.Erdos521.UniformLocalMoments
import ErdosProblems.Erdos521.RareEventMoments
import ErdosProblems.Erdos521.PolynomialSignProbability
import ErdosProblems.Erdos521.GaussianAbsoluteMoment
import ErdosProblems.Erdos521.GaussianSignSlope
import ErdosProblems.Erdos521.IntervalMoments
import ErdosProblems.Erdos521.RootGridError
import ErdosProblems.Erdos521.LogGridExpectation
import ErdosProblems.Erdos521.LogGridDisagreement
import ErdosProblems.Erdos521.BoundedConcentration
import ErdosProblems.Erdos521.DyadicWindows
import ErdosProblems.Erdos521.WindowIndependence
import ErdosProblems.Erdos521.LocalMeanLimit
import ErdosProblems.Erdos521.UniformLogarithmicMean
import ErdosProblems.Erdos521.DyadicIntervals
import ErdosProblems.Erdos521.WindowGridIndependence
import ErdosProblems.Erdos521.MainBinMean
import ErdosProblems.Erdos521.CentralIntervalMean
import ErdosProblems.Erdos521.WindowGridMoments
import ErdosProblems.Erdos521.BlockConcentration
import ErdosProblems.Erdos521.ColoredConcentration
import ErdosProblems.Erdos521.CentralIntervalMoments
import ErdosProblems.Erdos521.LeftTrim
import ErdosProblems.Erdos521.RightTrim
import ErdosProblems.Erdos521.WindowAlmostSureConcentration
import ErdosProblems.Erdos521.FineGridRootError
import ErdosProblems.Erdos521.FineGridCapping
import ErdosProblems.Erdos521.MainWindowValueError

/-!
# Erdős Problem 521: unconditional disproof

`not_erdos521` disproves almost-sure convergence to `2 / pi` for one infinite
iid symmetric-sign sequence. `erdos521_oscillation` proves the stronger
almost-sure liminf and limsup statement, with extended-real limits so that
an infinite limsup retains its intended meaning.

The proof establishes the interior-root strong law, Abel cone criterion,
harmonic cone-survival bound, record second-moment bound, and finite-prefix
zero-one upgrade. Infinitely many exterior-free degrees give the liminf;
coefficient reversal and convergence in measure give the limsup. All these
inputs are proved, with no assumptions of Do's theorem or the selected claims.
Endpoints and distinct-root conventions are preserved throughout. The imported
probability-space transfer gives the same conclusions for any independent
sequence with the fair-sign law.

See `Erdos521/README.md` for the proof structure and reproducible check.
-/

namespace Erdos521

open MeasureTheory Filter

/-- The full oscillation claim, for prefixes of one infinite iid sign sequence. -/
theorem erdos521_oscillation :
    ∀ᵐ ε ∂sequenceLaw,
      liminf (fun n ↦ (normalizedRootCount ε n : EReal)) atTop = (1 / Real.pi : ℝ) ∧
      (2 / Real.pi : ℝ) ≤ limsup (fun n ↦ (normalizedRootCount ε n : EReal)) atTop :=
  ae_rootCount_oscillation

/-- The almost-sure convergence conjecture in Erdős Problem 521 is false. -/
theorem not_erdos521 : ¬ Conjecture := not_conjecture

theorem not_erdos_521 : ¬ Conjecture := not_erdos521

end Erdos521

#print axioms Erdos521.coefficientRecord_no_exterior_root
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_record_rootCount_eq
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.InfiniteRecords.shift
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.Pitman.survivingWords_card_lower
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.Pitman.pairedDirection_infiniteRecords_measure_one
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_infinite_no_exterior_roots
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_infinite_rootCount_eq_interior
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_smallRootCount_div_log_tendsto_zero
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.rootCount_integrable
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.powerSum_smallBall
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.integral_maximumSquaredPartialSum_le
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.polynomial_norm_sq_le_circleAverage_disk
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.integral_circleAverage_maximum_le
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.polynomial_zeros_pow_le
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.localRootCount_maximal_probability
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_endpointRootCount_div_log_tendsto_zero
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_negativeEndpointRootCount_div_log_tendsto_zero
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.powerSum_smallBall_repulsion_scale
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.smallValueDerivative_grid_probability
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_root_repulsion
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_bulk_stability
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_interiorRootCount_dyadic_oscillation
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_interiorRootCount_dyadic_error
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.two_interval_roots_probability
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.integral_complexPowerSum_norm_sq
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.localRootCount_normalized_probability
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.two_interval_roots_normalized_probability
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.rootCount_signGrid_probability
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.triangular_sign_central_limit
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.polynomial_value_central_limit
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.triangular_vector_sign_central_limit
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.gridSignChanges_le_intervalRootCount
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.normalized_geometricCovariance_tendsto
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.localRootCount_exponential_tail
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.eventually_bulk_local_moments
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.setIntegral_nat_le_eighth_moment
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.polynomial_sign_probability_tendsto
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.integral_standardGaussian_abs
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.gaussian_log_sign_probability_slope
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.eventually_bulk_interval_moments
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.root_grid_expectation_error
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.logGrid_sign_expectation_tendsto
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.logGrid_disagreement_probability
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.bounded_independent_sum_probability
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.dyadicCoefficientWindow_disjoint_same_color
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.independent_window_statistics
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.local_logarithmic_mean_limit
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.uniform_logarithmic_mean
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.uniform_polynomial_zero_probability
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.eventually_dyadic_interval_moments
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.capped_window_grid_concentration
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.central_bin_sum_mean_limit
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.central_interval_mean_div_log_limit
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.window_grid_capping_probability
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.subGaussian_block_sum_probability
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.colored_window_grid_concentration
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.eventually_central_interval_moments
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_left_trim_div_index_tendsto_zero
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_right_trim_div_index_tendsto_zero
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_cappedCentralSum_centered_div_index_tendsto_zero
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.eventually_fineGrid_root_disagreement
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.eventually_mainBin_window_value_error
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.eventually_fineGrid_capping_probability
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_eventually_centralRootCount_eq_capped
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_centralRootCount_div_log_limit
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_interiorRootCount_div_log_limit
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.erdos521_oscillation
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_rootCount_oscillation_of_independent_signs
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.ae_not_tendsto_normalizedRootCount
-- [propext, Classical.choice, Quot.sound]

#print axioms Erdos521.not_erdos521
-- [propext, Classical.choice, Quot.sound]
