import ErdosProblems.Erdos327.Analytic.CenteredTail

/-!
# Explicit centered-tail bounds

This file normalizes the Mertens envelopes in `CutoffMoment` and sums the
concrete logarithmic grid from `CenteredTail`.
-/

namespace Erdos327.Analytic

open Finset Real

/-- Uniform reserve for one endpoint error in Mertens' reciprocal-prime
estimate. -/
noncomputable def reciprocalPrimeErrorReserve : ℝ :=
  (log 4 + 3) / log 2

/-- Uniform reserve when changing the lower endpoint from `L` to `L-1`
and paying both reciprocal-prime endpoint errors. -/
noncomputable def cutoffTailReserve : ℝ :=
  log 2 + 2 * reciprocalPrimeErrorReserve

theorem reciprocalPrimeErrorReserve_nonneg :
    0 ≤ reciprocalPrimeErrorReserve := by
  unfold reciprocalPrimeErrorReserve
  positivity

theorem cutoffTailReserve_nonneg :
    0 ≤ cutoffTailReserve := by
  unfold cutoffTailReserve
  positivity [reciprocalPrimeErrorReserve_nonneg]

theorem reciprocalPrimeError_le_reserve
    {N : ℕ} (hN : 2 ≤ N) :
    (log 4 + 3) / log N ≤ reciprocalPrimeErrorReserve := by
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlogMono : log (2 : ℝ) ≤ log (N : ℝ) :=
    log_le_log (by norm_num) (by exact_mod_cast hN)
  have hinv :
      1 / log (N : ℝ) ≤ 1 / log (2 : ℝ) :=
    one_div_le_one_div_of_le hlog2 hlogMono
  unfold reciprocalPrimeErrorReserve
  simpa [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ log 4 + 3)

/-- The harmless `L-1` endpoint differs from `L` by at most `log 2` on
the log-log scale. -/
theorem logLog_sub_logLog_pred_le_log_two
    {L : ℕ} (hL : 3 ≤ L) :
    log (log (L : ℝ)) -
      log (log ((L - 1 : ℕ) : ℝ)) ≤ log 2 := by
  have hLm1 : 2 ≤ L - 1 := by omega
  have hlogLm1 : 0 < log ((L - 1 : ℕ) : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L - 1 by omega))
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hnat : L ≤ 2 * (L - 1) := by omega
  have hlogNat :
      log (L : ℝ) ≤ log ((2 * (L - 1) : ℕ) : ℝ) :=
    log_le_log (by positivity) (by exact_mod_cast hnat)
  have hmul :
      log ((2 * (L - 1) : ℕ) : ℝ) =
        log 2 + log ((L - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by positivity : ((L - 1 : ℕ) : ℝ) ≠ 0)
  have hlog2le :
      log (2 : ℝ) ≤ log ((L - 1 : ℕ) : ℝ) :=
    log_le_log (by norm_num) (by exact_mod_cast hLm1)
  have hlogRatio :
      log (L : ℝ) / log ((L - 1 : ℕ) : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hlogLm1]
    rw [hmul] at hlogNat
    linarith
  have hratioPos :
      0 < log (L : ℝ) / log ((L - 1 : ℕ) : ℝ) :=
    div_pos hlogL hlogLm1
  have hlogRatio' :
      log (log (L : ℝ) / log ((L - 1 : ℕ) : ℝ)) ≤ log 2 :=
    log_le_log hratioPos hlogRatio
  rw [log_div hlogL.ne' hlogLm1.ne'] at hlogRatio'
  exact hlogRatio'

/-- Uniform comparison between the explicit Mertens tail envelope and
the centered log-log scale. -/
theorem primeInvTailUpper_pred_le_scale_add_reserve
    {L T : ℕ} (hL : 3 ≤ L) (hLT : L ≤ T) :
    primeInvTailUpper (L - 1) T ≤
      cutoffLogScale L T + cutoffTailReserve := by
  have hLm1 : 2 ≤ L - 1 := by omega
  have hT2 : 2 ≤ T := by omega
  have hlogT : 0 < log (T : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < T by omega))
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hmain := logLog_sub_logLog_pred_le_log_two hL
  have herrT := reciprocalPrimeError_le_reserve hT2
  have herrL := reciprocalPrimeError_le_reserve hLm1
  unfold primeInvTailUpper cutoffLogScale cutoffTailReserve
  rw [log_div hlogT.ne' hlogL.ne']
  linarith

theorem primeInvTailUpper_le_main_add_error
    {P Q : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    primeInvTailUpper P Q ≤
      log (log Q) - log (log P) +
        2 * reciprocalPrimeErrorReserve := by
  have hQ : 2 ≤ Q := hP.trans hPQ
  have herrP := reciprocalPrimeError_le_reserve hP
  have herrQ := reciprocalPrimeError_le_reserve hQ
  unfold primeInvTailUpper
  linarith

theorem primeInvSumUpper_le_logLog_add
    {Y : ℕ} (hY : 2 ≤ Y) :
    primeInvSumUpper Y ≤
      log (log Y) +
        Mertens.Weight.M (f := Mertens.Weight.prime) +
        reciprocalPrimeErrorReserve := by
  have herr := reciprocalPrimeError_le_reserve hY
  unfold primeInvSumUpper
  linarith

/-- Cutoff-independent constant for unrestricted centered moments. -/
noncomputable def unrestrictedCenteredMomentConstant (z : ℝ) : ℝ :=
  2 * (uniformWeightedMangoldtConstant + 1) *
    exp
      (Mertens.Weight.M (f := Mertens.Weight.prime) +
        reciprocalPrimeErrorReserve +
        (z - 1) * cutoffTailReserve + 38)

/-- Cutoff-independent constant for rough centered moments. -/
noncomputable def roughCenteredMomentConstant (z : ℝ) : ℝ :=
  (2 * (uniformWeightedMangoldtConstant + 1) /
      mertensLowerConstant) *
    exp
      (z * cutoffTailReserve +
        2 * reciprocalPrimeErrorReserve + 38)

theorem unrestrictedCenteredMomentConstant_nonneg (z : ℝ) :
    0 ≤ unrestrictedCenteredMomentConstant z := by
  unfold unrestrictedCenteredMomentConstant
  positivity [uniformWeightedMangoldtConstant_nonneg]

theorem roughCenteredMomentConstant_nonneg (z : ℝ) :
    0 ≤ roughCenteredMomentConstant z := by
  unfold roughCenteredMomentConstant
  positivity [uniformWeightedMangoldtConstant_nonneg,
    mertensLowerConstant_pos]

/-- Uniform unrestricted moment in the scale used by the logarithmic
grid. -/
theorem unrestrictedCutoffMoment_le_normalized
    {L X Y : ℕ} {z : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hXY : X ≤ Y)
    (hY : 2 ≤ Y) (hz1 : 1 ≤ z) (hz52 : z ≤ 5 / 2) :
    (∑ n ∈ Icc 1 Y, z ^ primeFactorCountBetween L X n) ≤
      unrestrictedCenteredMomentConstant z * Y *
        exp ((z - 1) * cutoffLogScale L X) := by
  have hLY : L ≤ Y := hLX.trans hXY
  have hbase :=
    centeredUnrestrictedCutoffMoment
      hL hLX hLY hY hz1 hz52
  have hsum := primeInvSumUpper_le_logLog_add hY
  have htail :=
    primeInvTailUpper_pred_le_scale_add_reserve hL hLX
  have hzsub : 0 ≤ z - 1 := sub_nonneg.mpr hz1
  have hexponent :
      primeInvSumUpper Y +
          (z - 1) * primeInvTailUpper (L - 1) X + 38 ≤
        log (log Y) +
          (Mertens.Weight.M (f := Mertens.Weight.prime) +
            reciprocalPrimeErrorReserve +
            (z - 1) * cutoffTailReserve + 38) +
          (z - 1) * cutoffLogScale L X := by
    have htailMul :=
      mul_le_mul_of_nonneg_left htail hzsub
    linarith
  have hexp := exp_le_exp.mpr hexponent
  have hlogY : 0 < log (Y : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hfront :
      0 ≤ 2 *
        ((uniformWeightedMangoldtConstant + 1) * (Y : ℝ) / log Y) := by
    positivity [uniformWeightedMangoldtConstant_nonneg]
  have hbase' :
      (∑ n ∈ Icc 1 Y, z ^ primeFactorCountBetween L X n) ≤
        2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
          exp
            (primeInvSumUpper Y +
              (z - 1) * primeInvTailUpper (L - 1) X + 38) := by
    simpa [min_eq_left hXY] using hbase
  calc
    (∑ n ∈ Icc 1 Y, z ^ primeFactorCountBetween L X n)
        ≤ 2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
          exp
            (primeInvSumUpper Y +
              (z - 1) * primeInvTailUpper (L - 1) X + 38) :=
      hbase'
    _ ≤ 2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
          exp
            (log (log Y) +
              (Mertens.Weight.M (f := Mertens.Weight.prime) +
                reciprocalPrimeErrorReserve +
                (z - 1) * cutoffTailReserve + 38) +
              (z - 1) * cutoffLogScale L X) :=
      mul_le_mul_of_nonneg_left hexp hfront
    _ = unrestrictedCenteredMomentConstant z * Y *
          exp ((z - 1) * cutoffLogScale L X) := by
      unfold unrestrictedCenteredMomentConstant
      rw [show
          log (log (Y : ℝ)) +
              (Mertens.Weight.M (f := Mertens.Weight.prime) +
                reciprocalPrimeErrorReserve +
                (z - 1) * cutoffTailReserve + 38) +
              (z - 1) * cutoffLogScale L X =
            log (log (Y : ℝ)) +
              ((Mertens.Weight.M (f := Mertens.Weight.prime) +
                reciprocalPrimeErrorReserve +
                (z - 1) * cutoffTailReserve + 38) +
              (z - 1) * cutoffLogScale L X) by ring,
        exp_add, exp_log hlogY,
        exp_add]
      field_simp [hlogY.ne']

/-- Uniform full-rough moment, with the exact periodic rough density
factored out. -/
theorem fullRoughCutoffMoment_le_normalized
    {L X Y : ℕ} {z : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hXY : X ≤ Y)
    (hY : 2 ≤ Y) (hz1 : 1 ≤ z) (hz52 : z ≤ 5 / 2) :
    (∑ n ∈ Icc 1 Y,
        if Rough L n then
          z ^ primeFactorCountBetween L X n else 0) ≤
      roughCenteredMomentConstant z * Y *
        (((roughPrimeModulus L).totient : ℕ) : ℝ) /
          roughPrimeModulus L *
        exp ((z - 1) * cutoffLogScale L X) := by
  have hLY : L ≤ Y := hLX.trans hXY
  have hbase :=
    centeredFullRoughCutoffMoment
      hL hLX hLY hY hz1 hz52
  have htail1 :=
    primeInvTailUpper_pred_le_scale_add_reserve hL hLX
  have htail2 :=
    primeInvTailUpper_le_main_add_error
      (show 2 ≤ X by omega) hXY
  have hz0 : 0 ≤ z := le_trans (by norm_num) hz1
  have hzsub : 0 ≤ z - 1 := sub_nonneg.mpr hz1
  have hlogX : 0 < log (X : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hexponent :
      z * primeInvTailUpper (L - 1) X +
          primeInvTailUpper X Y + 38 ≤
        log (log Y) - log (log L) +
          (z - 1) * cutoffLogScale L X +
          (z * cutoffTailReserve +
            2 * reciprocalPrimeErrorReserve + 38) := by
    have htail1Mul := mul_le_mul_of_nonneg_left htail1 hz0
    unfold cutoffLogScale at *
    rw [log_div hlogX.ne' hlogL.ne'] at htail1Mul ⊢
    linarith
  have hexp := exp_le_exp.mpr hexponent
  have hlogY : 0 < log (Y : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hfront :
      0 ≤ 2 *
        ((uniformWeightedMangoldtConstant + 1) * (Y : ℝ) / log Y) := by
    positivity [uniformWeightedMangoldtConstant_nonneg]
  have hbase' :
      (∑ n ∈ Icc 1 Y,
          if Rough L n then
            z ^ primeFactorCountBetween L X n else 0) ≤
        2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
          exp
            (z * primeInvTailUpper (L - 1) X +
              primeInvTailUpper X Y + 38) := by
    simpa [min_eq_left hXY] using hbase
  let rawC : ℝ :=
    2 * (uniformWeightedMangoldtConstant + 1) *
      exp
        (z * cutoffTailReserve +
          2 * reciprocalPrimeErrorReserve + 38)
  have hrawC : 0 ≤ rawC := by
    dsimp [rawC]
    positivity [uniformWeightedMangoldtConstant_nonneg]
  have hraw :
      (∑ n ∈ Icc 1 Y,
          if Rough L n then
            z ^ primeFactorCountBetween L X n else 0) ≤
        rawC * ((Y : ℝ) / log L) *
          exp ((z - 1) * cutoffLogScale L X) := by
    calc
      _ ≤ 2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
            exp
              (z * primeInvTailUpper (L - 1) X +
                primeInvTailUpper X Y + 38) :=
        hbase'
      _ ≤ 2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
            exp
              (log (log Y) - log (log L) +
                (z - 1) * cutoffLogScale L X +
                (z * cutoffTailReserve +
                  2 * reciprocalPrimeErrorReserve + 38)) :=
        mul_le_mul_of_nonneg_left hexp hfront
      _ = rawC * ((Y : ℝ) / log L) *
            exp ((z - 1) * cutoffLogScale L X) := by
        dsimp [rawC]
        rw [show
            log (log (Y : ℝ)) - log (log (L : ℝ)) +
                (z - 1) * cutoffLogScale L X +
                (z * cutoffTailReserve +
                  2 * reciprocalPrimeErrorReserve + 38) =
              log (log (Y : ℝ)) - log (log (L : ℝ)) +
                ((z * cutoffTailReserve +
                  2 * reciprocalPrimeErrorReserve + 38) +
                (z - 1) * cutoffLogScale L X) by ring,
          ← log_div hlogY.ne' hlogL.ne',
          exp_add, exp_log (div_pos hlogY hlogL),
          exp_add]
        field_simp [hlogY.ne', hlogL.ne']
  let ρ : ℝ :=
    (((roughPrimeModulus L).totient : ℕ) : ℝ) /
      roughPrimeModulus L
  have hρ :
      mertensLowerConstant / log L ≤ ρ := by
    dsimp [ρ]
    exact mertensLowerConstant_div_log_le_roughDensity hL
  have hc : 0 < mertensLowerConstant :=
    mertensLowerConstant_pos
  have hinv :
      1 / log (L : ℝ) ≤ ρ / mertensLowerConstant := by
    rw [le_div_iff₀ hc]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hρ
  have hYinv :
      (Y : ℝ) / log L ≤
        (Y : ℝ) * (ρ / mertensLowerConstant) := by
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg Y)
  calc
    (∑ n ∈ Icc 1 Y,
        if Rough L n then
          z ^ primeFactorCountBetween L X n else 0)
        ≤ rawC * ((Y : ℝ) / log L) *
            exp ((z - 1) * cutoffLogScale L X) :=
      hraw
    _ ≤ rawC * ((Y : ℝ) * (ρ / mertensLowerConstant)) *
          exp ((z - 1) * cutoffLogScale L X) := by
      gcongr
    _ = roughCenteredMomentConstant z * Y * ρ *
          exp ((z - 1) * cutoffLogScale L X) := by
      unfold roughCenteredMomentConstant
      dsimp [rawC]
      field_simp [hc.ne']
    _ = roughCenteredMomentConstant z * Y *
          (((roughPrimeModulus L).totient : ℕ) : ℝ) /
            roughPrimeModulus L *
          exp ((z - 1) * cutoffLogScale L X) := by
      dsimp [ρ]
      ring

/-! ## Bounds at one concrete grid level -/

/-- The unrestricted exceptional set at grid level `j`, before the
geometric decay is extracted. -/
theorem card_logGridLevelExceptional_le_normalized
    {L Y j : ℕ} {A K z : ℝ}
    (hL : 3 ≤ L) (hLY : L ≤ Y) (hY : 2 ≤ Y)
    (hz1 : 1 ≤ z) (hz52 : z ≤ 5 / 2) :
    ((logGridLevelExceptional L Y A K j).card : ℝ) ≤
      (unrestrictedCenteredMomentConstant z * Y *
          exp ((z - 1) * j)) /
        z ^ logGridThreshold A K j := by
  have hbounds := logGridCutoff_bounds (j := j) hL hLY
  have hscale :=
    cutoffLogScale_logGridCutoff_le (j := j) hL hLY
  have hmoment :=
    unrestrictedCutoffMoment_le_normalized
      hL hbounds.1 hbounds.2 hY hz1 hz52
  have hzsub : 0 ≤ z - 1 := sub_nonneg.mpr hz1
  have hexp :
      exp ((z - 1) *
          cutoffLogScale L (logGridCutoff L Y j)) ≤
        exp ((z - 1) * j) := by
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left hscale hzsub)
  have hmoment' :
      (∑ n ∈ Icc 1 Y,
          z ^ primeFactorCountBetween L (logGridCutoff L Y j) n) ≤
        unrestrictedCenteredMomentConstant z * Y *
          exp ((z - 1) * j) := by
    exact hmoment.trans
      (mul_le_mul_of_nonneg_left hexp
        (mul_nonneg
          (unrestrictedCenteredMomentConstant_nonneg z)
          (Nat.cast_nonneg Y)))
  unfold logGridLevelExceptional
  refine (card_filter_lt_natStat_le_sum_div_rpow
    (s := Icc 1 Y)
    (f := primeFactorCountBetween L (logGridCutoff L Y j))
    (B := logGridThreshold A K j) hz1).trans ?_
  exact div_le_div_of_nonneg_right hmoment'
    (Real.rpow_nonneg (le_trans (by norm_num) hz1) _)

/-- The full-rough exceptional set at grid level `j`, before the
geometric decay is extracted. -/
theorem card_logGridLevelRoughExceptional_le_normalized
    {L Y j : ℕ} {A K z : ℝ}
    (hL : 3 ≤ L) (hLY : L ≤ Y) (hY : 2 ≤ Y)
    (hz1 : 1 ≤ z) (hz52 : z ≤ 5 / 2) :
    ((logGridLevelRoughExceptional L Y A K j).card : ℝ) ≤
      (roughCenteredMomentConstant z * Y *
          ((((roughPrimeModulus L).totient : ℕ) : ℝ) /
            roughPrimeModulus L) *
          exp ((z - 1) * j)) /
        z ^ logGridThreshold A K j := by
  have hbounds := logGridCutoff_bounds (j := j) hL hLY
  have hscale :=
    cutoffLogScale_logGridCutoff_le (j := j) hL hLY
  have hmoment :=
    fullRoughCutoffMoment_le_normalized
      hL hbounds.1 hbounds.2 hY hz1 hz52
  have hzsub : 0 ≤ z - 1 := sub_nonneg.mpr hz1
  have hexp :
      exp ((z - 1) *
          cutoffLogScale L (logGridCutoff L Y j)) ≤
        exp ((z - 1) * j) := by
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left hscale hzsub)
  have hdensity :
      0 ≤ ((((roughPrimeModulus L).totient : ℕ) : ℝ) /
        roughPrimeModulus L) := by positivity
  have hmoment' :
      (∑ n ∈ Icc 1 Y,
          if Rough L n then
            z ^ primeFactorCountBetween L (logGridCutoff L Y j) n
          else 0) ≤
        roughCenteredMomentConstant z * Y *
          ((((roughPrimeModulus L).totient : ℕ) : ℝ) /
            roughPrimeModulus L) *
          exp ((z - 1) * j) := by
    have hmomentAssoc :
        (∑ n ∈ Icc 1 Y,
            if Rough L n then
              z ^ primeFactorCountBetween L (logGridCutoff L Y j) n
            else 0) ≤
          (roughCenteredMomentConstant z * Y *
            ((((roughPrimeModulus L).totient : ℕ) : ℝ) /
              roughPrimeModulus L)) *
            exp ((z - 1) *
              cutoffLogScale L (logGridCutoff L Y j)) := by
      simpa [div_eq_mul_inv, mul_assoc] using hmoment
    exact hmomentAssoc.trans
      (mul_le_mul_of_nonneg_left hexp
        (mul_nonneg
          (mul_nonneg
            (roughCenteredMomentConstant_nonneg z)
            (Nat.cast_nonneg Y))
          hdensity))
  let s := (Icc 1 Y).filter (Rough L)
  have hs :
      logGridLevelRoughExceptional L Y A K j =
        s.filter fun n ↦
          logGridThreshold A K j <
            (primeFactorCountBetween L (logGridCutoff L Y j) n : ℝ) := by
    ext n
    simp [logGridLevelRoughExceptional, s, and_left_comm, and_assoc]
  rw [hs]
  refine (card_filter_lt_natStat_le_sum_div_rpow
    (s := s)
    (f := primeFactorCountBetween L (logGridCutoff L Y j))
    (B := logGridThreshold A K j) hz1).trans ?_
  have hsum :
      (∑ n ∈ s,
          z ^ primeFactorCountBetween L (logGridCutoff L Y j) n) =
        ∑ n ∈ Icc 1 Y,
          if Rough L n then
            z ^ primeFactorCountBetween L (logGridCutoff L Y j) n
          else 0 := by
    rw [sum_filter]
  rw [hsum]
  exact div_le_div_of_nonneg_right hmoment'
    (Real.rpow_nonneg (le_trans (by norm_num) hz1) _)

/-! ## Geometric decay and its explicit sum -/

/-- Ratio between consecutive unit log-scale levels. -/
noncomputable def centeredTailRatio (A z : ℝ) : ℝ :=
  exp ((z - 1) - A * log z)

theorem centeredTailRatio_nonneg (A z : ℝ) :
    0 ≤ centeredTailRatio A z := by
  unfold centeredTailRatio
  positivity

theorem centeredTailRatio_lt_one
    {A z : ℝ} (hgap : z - 1 < A * log z) :
    centeredTailRatio A z < 1 := by
  unfold centeredTailRatio
  rw [exp_lt_one_iff]
  linarith

/-- Algebraic extraction of the geometric factor.  The `j = 0`
endpoint is covered by the same one-level loss as every later bucket. -/
theorem normalized_grid_level_decay
    {A K z : ℝ} {j : ℕ}
    (hA : 0 ≤ A) (hz : 1 < z) :
    exp ((z - 1) * j) / z ^ logGridThreshold A K j ≤
      z ^ (-K) * exp (A * log z) *
        centeredTailRatio A z ^ j := by
  have hz0 : 0 < z := zero_lt_one.trans hz
  have hlogz : 0 ≤ log z := (log_pos hz).le
  have hpred :
      (j : ℝ) - 1 ≤ ((j - 1 : ℕ) : ℝ) := by
    by_cases hj : j = 0
    · subst j
      norm_num
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
      rw [Nat.cast_sub hj1]
      norm_num
  rw [Real.rpow_def_of_pos hz0, Real.rpow_def_of_pos hz0]
  unfold logGridThreshold centeredTailRatio
  rw [← exp_sub, ← Real.exp_nat_mul]
  rw [← exp_add, ← exp_add]
  apply exp_le_exp.mpr
  have hmul :
      A * ((j : ℝ) - 1) ≤ A * ((j - 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hpred hA
  nlinarith

/-- Cutoff-independent constant after summing every grid level in the
unrestricted centered tail. -/
noncomputable def unrestrictedCenteredTailConstant (A z : ℝ) : ℝ :=
  unrestrictedCenteredMomentConstant z * exp (A * log z) *
    (1 - centeredTailRatio A z)⁻¹

/-- Cutoff-independent constant after summing every grid level in the
rough centered tail. -/
noncomputable def roughCenteredTailConstant (A z : ℝ) : ℝ :=
  roughCenteredMomentConstant z * exp (A * log z) *
    (1 - centeredTailRatio A z)⁻¹

theorem unrestrictedCenteredTailConstant_nonneg
    {A z : ℝ} (hgap : z - 1 < A * log z) :
    0 ≤ unrestrictedCenteredTailConstant A z := by
  unfold unrestrictedCenteredTailConstant
  have hr := centeredTailRatio_lt_one hgap
  exact mul_nonneg
    (mul_nonneg (unrestrictedCenteredMomentConstant_nonneg z)
      (exp_pos _).le)
    (inv_nonneg.mpr (sub_nonneg.mpr hr.le))

theorem roughCenteredTailConstant_nonneg
    {A z : ℝ} (hgap : z - 1 < A * log z) :
    0 ≤ roughCenteredTailConstant A z := by
  unfold roughCenteredTailConstant
  have hr := centeredTailRatio_lt_one hgap
  exact mul_nonneg
    (mul_nonneg (roughCenteredMomentConstant_nonneg z)
      (exp_pos _).le)
    (inv_nonneg.mpr (sub_nonneg.mpr hr.le))

theorem card_logGridLevelExceptional_le_geometric
    {L Y j : ℕ} {A K z : ℝ}
    (hL : 3 ≤ L) (hLY : L ≤ Y) (hY : 2 ≤ Y)
    (hA : 0 ≤ A) (hz : 1 < z) (hz52 : z ≤ 5 / 2) :
    ((logGridLevelExceptional L Y A K j).card : ℝ) ≤
      unrestrictedCenteredMomentConstant z * Y * z ^ (-K) *
        exp (A * log z) * centeredTailRatio A z ^ j := by
  have hlevel :=
    card_logGridLevelExceptional_le_normalized
      (j := j) (A := A) (K := K) hL hLY hY hz.le hz52
  have hdecay :=
    normalized_grid_level_decay (A := A) (K := K) (j := j) hA hz
  have hfront :
      0 ≤ unrestrictedCenteredMomentConstant z * (Y : ℝ) :=
    mul_nonneg (unrestrictedCenteredMomentConstant_nonneg z)
      (Nat.cast_nonneg Y)
  calc
    ((logGridLevelExceptional L Y A K j).card : ℝ)
        ≤ (unrestrictedCenteredMomentConstant z * Y *
            exp ((z - 1) * j)) /
          z ^ logGridThreshold A K j :=
      hlevel
    _ = (unrestrictedCenteredMomentConstant z * Y) *
          (exp ((z - 1) * j) /
            z ^ logGridThreshold A K j) := by ring
    _ ≤ (unrestrictedCenteredMomentConstant z * Y) *
          (z ^ (-K) * exp (A * log z) *
            centeredTailRatio A z ^ j) :=
      mul_le_mul_of_nonneg_left hdecay hfront
    _ = unrestrictedCenteredMomentConstant z * Y * z ^ (-K) *
          exp (A * log z) * centeredTailRatio A z ^ j := by ring

theorem card_logGridLevelRoughExceptional_le_geometric
    {L Y j : ℕ} {A K z : ℝ}
    (hL : 3 ≤ L) (hLY : L ≤ Y) (hY : 2 ≤ Y)
    (hA : 0 ≤ A) (hz : 1 < z) (hz52 : z ≤ 5 / 2) :
    ((logGridLevelRoughExceptional L Y A K j).card : ℝ) ≤
      roughCenteredMomentConstant z * Y *
        ((((roughPrimeModulus L).totient : ℕ) : ℝ) /
          roughPrimeModulus L) *
        z ^ (-K) * exp (A * log z) *
          centeredTailRatio A z ^ j := by
  have hlevel :=
    card_logGridLevelRoughExceptional_le_normalized
      (j := j) (A := A) (K := K) hL hLY hY hz.le hz52
  have hdecay :=
    normalized_grid_level_decay (A := A) (K := K) (j := j) hA hz
  have hdensity :
      0 ≤ ((((roughPrimeModulus L).totient : ℕ) : ℝ) /
        roughPrimeModulus L) := by positivity
  have hfront :
      0 ≤ roughCenteredMomentConstant z * (Y : ℝ) *
        ((((roughPrimeModulus L).totient : ℕ) : ℝ) /
          roughPrimeModulus L) :=
    mul_nonneg
      (mul_nonneg (roughCenteredMomentConstant_nonneg z)
        (Nat.cast_nonneg Y))
      hdensity
  calc
    ((logGridLevelRoughExceptional L Y A K j).card : ℝ)
        ≤ (roughCenteredMomentConstant z * Y *
            ((((roughPrimeModulus L).totient : ℕ) : ℝ) /
              roughPrimeModulus L) *
            exp ((z - 1) * j)) /
          z ^ logGridThreshold A K j :=
      hlevel
    _ = (roughCenteredMomentConstant z * Y *
          ((((roughPrimeModulus L).totient : ℕ) : ℝ) /
            roughPrimeModulus L)) *
          (exp ((z - 1) * j) /
            z ^ logGridThreshold A K j) := by ring
    _ ≤ (roughCenteredMomentConstant z * Y *
          ((((roughPrimeModulus L).totient : ℕ) : ℝ) /
            roughPrimeModulus L)) *
          (z ^ (-K) * exp (A * log z) *
            centeredTailRatio A z ^ j) :=
      mul_le_mul_of_nonneg_left hdecay hfront
    _ = roughCenteredMomentConstant z * Y *
          ((((roughPrimeModulus L).totient : ℕ) : ℝ) /
            roughPrimeModulus L) *
          z ^ (-K) * exp (A * log z) *
            centeredTailRatio A z ^ j := by ring

/-- The concrete logarithmic grid has a cutoff-independent unrestricted
tail bound. -/
theorem card_logarithmicGridExceptional_le_explicit
    {L Y : ℕ} {A K z : ℝ}
    (hL : 3 ≤ L) (hLY : L ≤ Y) (hY : 2 ≤ Y)
    (hA : 0 ≤ A) (hz : 1 < z) (hz52 : z ≤ 5 / 2)
    (hgap : z - 1 < A * log z) :
    ((logarithmicGridExceptional L Y A K).card : ℝ) ≤
      unrestrictedCenteredTailConstant A z * Y * z ^ (-K) := by
  let r := centeredTailRatio A z
  let C := unrestrictedCenteredMomentConstant z * (Y : ℝ) *
    z ^ (-K) * exp (A * log z)
  have hr0 : 0 ≤ r := centeredTailRatio_nonneg A z
  have hr1 : r < 1 := centeredTailRatio_lt_one hgap
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (unrestrictedCenteredMomentConstant_nonneg z)
          (Nat.cast_nonneg Y))
        (Real.rpow_nonneg (zero_le_one.trans hz.le) _))
      (exp_pos _).le
  have hcardNat :=
    card_logarithmicGridExceptional_le_sum L Y A K
  have hcard :
      ((logarithmicGridExceptional L Y A K).card : ℝ) ≤
        ∑ j ∈ logarithmicGridIndices L Y,
          ((logGridLevelExceptional L Y A K j).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((logarithmicGridExceptional L Y A K).card : ℝ)
        ≤ ∑ j ∈ logarithmicGridIndices L Y,
            ((logGridLevelExceptional L Y A K j).card : ℝ) :=
      hcard
    _ ≤ ∑ j ∈ logarithmicGridIndices L Y, C * r ^ j := by
      gcongr with j hj
      dsimp [C, r]
      exact card_logGridLevelExceptional_le_geometric
        hL hLY hY hA hz hz52
    _ = C * ∑ j ∈ logarithmicGridIndices L Y, r ^ j := by
      rw [mul_sum]
    _ ≤ C * (1 - r)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ hC
      unfold logarithmicGridIndices
      exact geomSum_le_inv_one_sub hr0 hr1 _
    _ = unrestrictedCenteredTailConstant A z * Y * z ^ (-K) := by
      dsimp [C, r]
      unfold unrestrictedCenteredTailConstant
      ring

/-- The concrete logarithmic grid has a cutoff-independent rough tail
bound, retaining the exact rough density. -/
theorem card_logarithmicGridRoughExceptional_le_explicit
    {L Y : ℕ} {A K z : ℝ}
    (hL : 3 ≤ L) (hLY : L ≤ Y) (hY : 2 ≤ Y)
    (hA : 0 ≤ A) (hz : 1 < z) (hz52 : z ≤ 5 / 2)
    (hgap : z - 1 < A * log z) :
    ((logarithmicGridRoughExceptional L Y A K).card : ℝ) ≤
      roughCenteredTailConstant A z * Y *
        ((((roughPrimeModulus L).totient : ℕ) : ℝ) /
          roughPrimeModulus L) *
        z ^ (-K) := by
  let r := centeredTailRatio A z
  let ρ : ℝ :=
    ((((roughPrimeModulus L).totient : ℕ) : ℝ) /
      roughPrimeModulus L)
  let C := roughCenteredMomentConstant z * (Y : ℝ) * ρ *
    z ^ (-K) * exp (A * log z)
  have hr0 : 0 ≤ r := centeredTailRatio_nonneg A z
  have hr1 : r < 1 := centeredTailRatio_lt_one hgap
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (roughCenteredMomentConstant_nonneg z)
            (Nat.cast_nonneg Y))
          hρ)
        (Real.rpow_nonneg (zero_le_one.trans hz.le) _))
      (exp_pos _).le
  have hcardNat :=
    card_logarithmicGridRoughExceptional_le_sum L Y A K
  have hcard :
      ((logarithmicGridRoughExceptional L Y A K).card : ℝ) ≤
        ∑ j ∈ logarithmicGridIndices L Y,
          ((logGridLevelRoughExceptional L Y A K j).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((logarithmicGridRoughExceptional L Y A K).card : ℝ)
        ≤ ∑ j ∈ logarithmicGridIndices L Y,
            ((logGridLevelRoughExceptional L Y A K j).card : ℝ) :=
      hcard
    _ ≤ ∑ j ∈ logarithmicGridIndices L Y, C * r ^ j := by
      gcongr with j hj
      dsimp [C, r, ρ]
      exact card_logGridLevelRoughExceptional_le_geometric
        hL hLY hY hA hz hz52
    _ = C * ∑ j ∈ logarithmicGridIndices L Y, r ^ j := by
      rw [mul_sum]
    _ ≤ C * (1 - r)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ hC
      unfold logarithmicGridIndices
      exact geomSum_le_inv_one_sub hr0 hr1 _
    _ = roughCenteredTailConstant A z * Y *
          ((((roughPrimeModulus L).totient : ℕ) : ℝ) /
            roughPrimeModulus L) *
          z ^ (-K) := by
      dsimp [C, r, ρ]
      unfold roughCenteredTailConstant
      ring

/-! ## Bounds for the two exceptional sets used by the construction -/

/-- Explicit density-scaled bound for the irregular rough source. -/
theorem card_irregularRoughSource_le_explicit
    {L N : ℕ} {A K z : ℝ}
    (hL : 3 ≤ L) (hLN : L ≤ N) (hN : 2 ≤ N)
    (hA : 0 ≤ A) (hz : 1 < z) (hz52 : z ≤ 5 / 2)
    (hgap : z - 1 < A * log z) :
    ((irregularRoughSource L A K N).card : ℝ) ≤
      roughCenteredTailConstant A z * N *
        ((((roughPrimeModulus L).totient : ℕ) : ℝ) /
          roughPrimeModulus L) *
        z ^ (-K) := by
  have hsubset :
      irregularRoughSource L A K N ⊆
        (Icc 1 N).filter
          (fun n ↦ Rough L n ∧ ¬CutoffRegular L A K n) := by
    intro n hn
    have hn' := mem_filter.mp hn
    have hnSource := mem_roughSourceInterval.mp hn'.1
    exact mem_filter.mpr
      ⟨mem_Icc.mpr ⟨by omega, hnSource.2.1⟩,
        hnSource.2.2, hn'.2⟩
  have hgridSubset :=
    irregular_rough_upto_subset_logarithmicGridRoughExceptional
      (A := A) (K := K) hL hLN hA
  have hcard :
      ((irregularRoughSource L A K N).card : ℝ) ≤
        ((logarithmicGridRoughExceptional L N A K).card : ℝ) := by
    exact_mod_cast card_le_card (hsubset.trans hgridSubset)
  exact hcard.trans
    (card_logarithmicGridRoughExceptional_le_explicit
      hL hLN hN hA hz hz52 hgap)

/-- Explicit unrestricted bound for the irregular odd host.  The host is
contained in `[1,2N]`, so no parity-specific moment estimate is needed. -/
theorem card_irregularOddHost_le_explicit
    {L N : ℕ} {A K z : ℝ}
    (hL : 3 ≤ L) (hLN : L ≤ 2 * N) (hN : 1 ≤ N)
    (hA : 0 ≤ A) (hz : 1 < z) (hz52 : z ≤ 5 / 2)
    (hgap : z - 1 < A * log z) :
    ((irregularOddHost L A K N).card : ℝ) ≤
      unrestrictedCenteredTailConstant A z * (2 * N) * z ^ (-K) := by
  have hsubset :
      irregularOddHost L A K N ⊆
        (Icc 1 (2 * N)).filter
          (fun n ↦ ¬CutoffRegular L A K n) := by
    intro n hn
    have hn' := mem_filter.mp hn
    have hnUpto := oddHost_subset_upto N hn'.1
    exact mem_filter.mpr
      ⟨mem_Icc.mpr (Erdos327.mem_upto.mp hnUpto), hn'.2⟩
  have hgridSubset :=
    irregular_upto_subset_logarithmicGridExceptional
      (A := A) (K := K) hL hLN hA
  have hcard :
      ((irregularOddHost L A K N).card : ℝ) ≤
        ((logarithmicGridExceptional L (2 * N) A K).card : ℝ) := by
    exact_mod_cast card_le_card (hsubset.trans hgridSubset)
  have h2N : 2 ≤ 2 * N := by omega
  exact hcard.trans (by
    simpa [Nat.cast_mul] using
      (card_logarithmicGridExceptional_le_explicit
        (K := K) hL hLN h2N hA hz hz52 hgap))

end Erdos327.Analytic
