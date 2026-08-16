import ErdosProblems.Erdos6.LargeRestrictedYLimit
import ErdosProblems.Erdos6.GenericRestrictedCrossLimit

/-!
# Positive normalized compatible restricted S2 kernel

The coordinate-one diagonal has a fixed positive lower bound, while the
incompatible CRT correction tends to zero on the same natural scale.
-/

namespace Erdos6.Maynard

open Filter

noncomputable section

theorem eventually_tupleRestrictedGKernel_normalized_gt
    (m : largePowerTuple) {alpha c : ℝ} (halpha : 0 < alpha)
    (hc : c < largeFiberLowerCoefficient) :
    ∀ᶠ N : ℕ in atTop,
      c < tupleRestrictedGKernel largePowerTuple alpha
          (tupleLargeCandidate largePowerTuple) N m /
        (BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          Real.log (maynardRadius alpha N) ^ 2 *
          tupleNaturalScale (largeOffFace m) alpha N) := by
  let scale : ℕ → ℝ := fun N =>
    BoundedGaps.Maynard.preSieveSingularSeries
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
      Real.log (maynardRadius alpha N) ^ 2 *
      tupleNaturalScale (largeOffFace m) alpha N
  let mid := (c + largeFiberLowerCoefficient) / 2
  let eps := (largeFiberLowerCoefficient - c) / 2
  have hmid : mid < largeFiberLowerCoefficient := by
    dsimp [mid]
    linarith
  have heps : 0 < eps := by
    dsimp [eps]
    linarith
  have hy := eventually_tupleCoordinateOneYDiagonal_normalized_gt
    m halpha hmid
  have hcross := tendsto_normalizedTupleRestrictedCross_zero
    (H := largePowerTuple) halpha m
  have hcrossSmall : ∀ᶠ N : ℕ in atTop,
      |tupleRestrictedCross largePowerTuple alpha
          (tupleLargeCandidate largePowerTuple) N m / scale N| < eps := by
    have h := hcross.eventually (Metric.ball_mem_nhds (0 : ℝ) heps)
    simpa only [Real.dist_eq, sub_zero, scale,
      tupleOffFace_largePowerTuple] using h
  filter_upwards [hy, hcrossSmall] with N hyN hcrossN
  have hidentity := tupleRestrictedGKernel_eq_quadratic_sub_cross
    largePowerTuple alpha (tupleLargeCandidate largePowerTuple) N m
  rw [tupleRestrictedQuadratic_eq_yDiagonal,
    tupleRestrictedYDiagonal_eq_coordinateOne] at hidentity
  have hcrossUpper :
      tupleRestrictedCross largePowerTuple alpha
          (tupleLargeCandidate largePowerTuple) N m / scale N < eps :=
    (le_abs_self _).trans_lt hcrossN
  have htarget : c <
      tupleRestrictedGKernel largePowerTuple alpha
          (tupleLargeCandidate largePowerTuple) N m / scale N := by
    rw [hidentity, sub_div]
    dsimp [mid, eps] at hyN hcrossUpper
    linarith
  simpa [scale] using htarget

end

end Erdos6.Maynard
