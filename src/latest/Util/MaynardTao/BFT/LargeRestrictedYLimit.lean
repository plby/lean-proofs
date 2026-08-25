import ErdosProblems.Erdos6.GenericRestrictedYPerturbationLimit
import Util.MaynardTao.BFT.LargeRestrictedYBridge

/-!
# Positive normalized restricted-Y diagonal
-/

namespace MaynardBFT.Sieve

open Erdos6.Maynard

open Filter

noncomputable section

variable [P : Parameters] [T : ShiftTuple]

theorem eventually_tupleCoordinateOneYDiagonal_normalized_gt
    (m : largePowerTuple) {alpha c : ℝ} (halpha : 0 < alpha)
    (hc : c < largeFiberLowerCoefficient) :
    ∀ᶠ N : ℕ in atTop,
      c < tupleCoordinateOneYDiagonal largePowerTuple alpha
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
  have hfiber :=
    eventually_largeCoordinateFiberSquareDiagonal_normalized_gt m halpha
  have hpert := tendsto_normalizedTupleCoordinateOneSquarePerturbation_zero
    (H := largePowerTuple) halpha m
  have hgap : 0 < largeFiberLowerCoefficient - c := sub_pos.mpr hc
  have hpertSmall : ∀ᶠ N : ℕ in atTop,
      tupleCoordinateOneSquarePerturbation largePowerTuple alpha N m /
          scale N < largeFiberLowerCoefficient - c := by
    have he := hpert.eventually (eventually_lt_nhds hgap)
    simpa only [scale, tupleOffFace_largePowerTuple,
      tupleCoordinateOneSquarePerturbation,
      Erdos6.Maynard.tupleCoordinateOneSquarePerturbation,
      tupleCoordinateOneSquarePerturbationEnvelope,
      Erdos6.Maynard.tupleCoordinateOneSquarePerturbationEnvelope] using he
  have hcond :=
    BoundedGaps.Maynard.eventually_engelsmaMaynardCrossBound_conditions halpha
  have hRone :=
    BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha
  have houter := eventually_tupleNaturalScale_pos
    (H := largeOffFace m) halpha
  filter_upwards [hfiber, hpertSmall, hcond, hRone, houter] with
      N hfiberN hpertN hcondN hRoneN houterN
  have hlog : 0 < Real.log (maynardRadius alpha N) := by
    exact Real.log_pos (by exact_mod_cast hRoneN)
  have hpre : 0 < BoundedGaps.Maynard.preSieveSingularSeries
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) :=
    BoundedGaps.Maynard.preSieveSingularSeries_pos _
  have hscale : 0 < scale N := by
    dsimp [scale]
    exact mul_pos (mul_pos (sq_pos_of_pos hpre) (sq_pos_of_pos hlog)) houterN
  have hbridge := abs_tupleCoordinateOneYDiagonal_sub_fiberSquareDiagonal_le
    (H := largePowerTuple) N m hcondN.2.1 hcondN.2.2
  have hlower :
      tupleCoordinateFiberSquareDiagonal largePowerTuple alpha N m -
          tupleCoordinateOneSquarePerturbation largePowerTuple alpha N m ≤
        tupleCoordinateOneYDiagonal largePowerTuple alpha
          (tupleLargeCandidate largePowerTuple) N m := by
    have hn := neg_le_of_abs_le hbridge
    linarith
  have hdiv := div_le_div_of_nonneg_right hlower hscale.le
  have hfiberN' : largeFiberLowerCoefficient <
      tupleCoordinateFiberSquareDiagonal largePowerTuple alpha N m /
        scale N := by
    simpa [scale] using hfiberN
  have htarget : c <
      tupleCoordinateOneYDiagonal largePowerTuple alpha
          (tupleLargeCandidate largePowerTuple) N m / scale N := by
    rw [sub_div] at hdiv
    linarith
  simpa [scale] using htarget

end

end MaynardBFT.Sieve
