import ErdosProblems.Erdos327.Analytic.CenteredTailBounds
import ErdosProblems.Erdos327.Analytic.ResidualMeanBridge

/-!
# Normalized residual-moment envelopes

The raw residual estimate contains two reciprocal-prime tails.  After
Mertens normalization, their common `log log Y` contribution cancels the
front factor `1 / log Y`.  What remains is the rough-density scale
`Y / log L` and the negative cutoff power

`exp ((q - 1) * cutoffLogScale L (min X Y))`.

This saving is essential in both scheduled dyadic summations.
-/

namespace Erdos327.Analytic

open Finset Real

noncomputable section

/-- Cutoff-independent constant in the normalized residual estimate. -/
def residualMomentConstant (q : ℝ) : ℝ :=
  2 * (log 4 + 5) *
    exp
      (q * cutoffTailReserve +
        2 * reciprocalPrimeErrorReserve + 38)

theorem residualMomentConstant_pos (q : ℝ) :
    0 < residualMomentConstant q := by
  unfold residualMomentConstant
  positivity

theorem residualMomentConstant_nonneg (q : ℝ) :
    0 ≤ residualMomentConstant q :=
  (residualMomentConstant_pos q).le

/-- Mertens-normalized residual moment on the full interval. -/
theorem residualMoment_le_normalized
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ n ∈ Icc 1 Y,
        if OddRough L n then
          q ^ primeFactorCountBetween L X n else 0) ≤
      residualMomentConstant q * ((Y : ℝ) / log L) *
        exp
          ((q - 1) *
            cutoffLogScale L (min X Y)) := by
  have hLT : L ≤ min X Y := le_min hLX hLY
  have hTY : min X Y ≤ Y := min_le_right _ _
  have hT2 : 2 ≤ min X Y := by omega
  have hbase :=
    residualMoment_le_mertens hL hLX hLY hY hq0 hq1
  have htail1 :=
    primeInvTailUpper_pred_le_scale_add_reserve hL hLT
  have htail2 :=
    primeInvTailUpper_le_main_add_error hT2 hTY
  have htail1Mul :=
    mul_le_mul_of_nonneg_left htail1 hq0
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogT : 0 < log ((min X Y : ℕ) : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < min X Y by omega))
  have hlogY : 0 < log (Y : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hexponent :
      q * primeInvTailUpper (L - 1) (min X Y) +
          primeInvTailUpper (min X Y) Y + 38 ≤
        log (log Y) - log (log L) +
          (q - 1) * cutoffLogScale L (min X Y) +
          (q * cutoffTailReserve +
            2 * reciprocalPrimeErrorReserve + 38) := by
    unfold cutoffLogScale at htail1Mul ⊢
    rw [log_div hlogT.ne' hlogL.ne'] at htail1Mul ⊢
    nlinarith
  have hexp := exp_le_exp.mpr hexponent
  have hfront :
      0 ≤ 2 * ((log 4 + 5) * (Y : ℝ) / log Y) := by
    positivity
  calc
    (∑ n ∈ Icc 1 Y,
        if OddRough L n then
          q ^ primeFactorCountBetween L X n else 0)
        ≤ 2 * ((log 4 + 5) * Y / log Y) *
            exp
              (q * primeInvTailUpper (L - 1) (min X Y) +
                primeInvTailUpper (min X Y) Y + 38) :=
      hbase
    _ ≤ 2 * ((log 4 + 5) * Y / log Y) *
          exp
            (log (log Y) - log (log L) +
              (q - 1) * cutoffLogScale L (min X Y) +
              (q * cutoffTailReserve +
                2 * reciprocalPrimeErrorReserve + 38)) :=
      mul_le_mul_of_nonneg_left hexp hfront
    _ = residualMomentConstant q * ((Y : ℝ) / log L) *
          exp
            ((q - 1) *
              cutoffLogScale L (min X Y)) := by
      unfold residualMomentConstant
      rw [show
          log (log (Y : ℝ)) - log (log (L : ℝ)) +
                (q - 1) * cutoffLogScale L (min X Y) +
                (q * cutoffTailReserve +
                  2 * reciprocalPrimeErrorReserve + 38) =
            log (log (Y : ℝ)) - log (log (L : ℝ)) +
              ((q * cutoffTailReserve +
                2 * reciprocalPrimeErrorReserve + 38) +
              (q - 1) * cutoffLogScale L (min X Y)) by ring,
        ← log_div hlogY.ne' hlogL.ne',
        exp_add, exp_log (div_pos hlogY hlogL),
        exp_add]
      field_simp [hlogY.ne', hlogL.ne']

/-- Mertens-normalized fully rough moment on an arbitrary positive
subinterval. -/
theorem roughResidualSubinterval_le_normalized
    {L X a Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (ha : 1 ≤ a)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ n ∈ Icc a Y,
        if Rough L n then
          q ^ primeFactorCountBetween L X n else 0) ≤
      residualMomentConstant q * ((Y : ℝ) / log L) *
        exp
          ((q - 1) *
            cutoffLogScale L (min X Y)) := by
  exact (sum_roughResidual_subinterval_le ha hq0).trans
    (residualMoment_le_normalized hL hLX hLY hY hq0 hq1)

/-- The exponential cutoff factor is exactly a real power of the
logarithmic scale ratio. -/
theorem exp_mul_cutoffLogScale
    {L T : ℕ} {r : ℝ}
    (hL : 3 ≤ L) (hLT : L ≤ T) :
    exp (r * cutoffLogScale L T) =
      (log (T : ℝ) / log (L : ℝ)) ^ r := by
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogT : 0 < log (T : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < T by omega))
  rw [Real.rpow_def_of_pos (div_pos hlogT hlogL)]
  unfold cutoffLogScale
  congr 1
  ring

/-- Power-form version of the normalized residual estimate. -/
theorem residualMoment_le_normalized_rpow
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ n ∈ Icc 1 Y,
        if OddRough L n then
          q ^ primeFactorCountBetween L X n else 0) ≤
      residualMomentConstant q * ((Y : ℝ) / log L) *
        (log ((min X Y : ℕ) : ℝ) / log (L : ℝ)) ^ (q - 1) := by
  simpa [exp_mul_cutoffLogScale hL (le_min hLX hLY)] using
    (residualMoment_le_normalized hL hLX hLY hY hq0 hq1)

end

end Erdos327.Analytic
