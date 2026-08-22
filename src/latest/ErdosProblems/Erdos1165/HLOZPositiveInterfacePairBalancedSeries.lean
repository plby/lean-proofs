/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCheckerOriginShiftPayment
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairHarmonic
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSourceCapCover
import ErdosProblems.Erdos1165.HLOZRawFullGapProductPromotion

/-!
# Summable balanced exact-pair interface payments

The exact-pair comparison loses a harmonic factor in the number of possible
raised endpoint ranks.  At the HLOZ cutoff this factor is only logarithmic in
the cutoff, hence `O (sqrt m)`.  This module absorbs that loss into the
existing logarithmic-square adjacent-shell cost and sums over the finite
shell and endpoint-band families.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPositiveInterfacePairBalancedSeries

open HLOZCheckerOriginShiftPayment
open HLOZAllSixBandProductClosure
open HLOZCandidateLocalLazyCap
open HLOZDynamicThresholdedScreening
open HLOZDominantPositiveInterfaceBandRecurrence
open HLOZGapBetaNumerics
open HLOZGapRandomClockScreen
open HLOZFullBetaRegimeSplit
open HLOZPathEvents
open HLOZPositiveInterfacePairActualDeltaWalkCap
open HLOZPositiveInterfacePairHarmonic
open HLOZPositiveInterfacePairSourceCapCover
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairWeightedScreen
open HLOZProposition48Candidates
open HLOZRawFullGapProductPromotion
open HLOZSharpProductNumerics
open HLOZSharpPositiveShellNumerics
open HLOZSourceCorrectFilteredTransitions
open HLOZSourceCorrectFullGapClosure
open HLOZTilingEndpointBandExtraction
open HLOZUpperEstimates
open HLOZVariableDeltaHistoryCapSummation
open LazyDecomposition
open NearFavoriteShells NearFavoriteThresholded Screening
open ScreeningInstantiation
open TilingOrientedShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The rank-loss at the HLOZ random-clock cutoff is eventually bounded by
a linear function of the level.  The deliberately loose constant keeps all
integer/real/`ENNReal` coercions transparent downstream. -/
theorem eventually_variableDeltaHarmonic_cutoff_le :
    ∀ᶠ m : ℕ in atTop,
      variableDeltaHarmonic
          (2 * levelCutoffTime upperTailDelta m + 1) ≤
        (6 * m : ℕ) := by
  have hlog := LowerAssembly.eventually_log_levelCutoffTime_le_three_sqrt
    upperTailDelta (by norm_num [upperTailDelta])
  have hcutoff : ∀ᶠ m : ℕ in atTop,
      1 ≤ levelCutoffTime upperTailDelta m :=
    (tendsto_levelCutoffTime upperTailDelta).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hlog, hcutoff, eventually_ge_atTop (1 : ℕ)] with
      m hlogM hcutoffM hm
  let C := levelCutoffTime upperTailDelta m
  have hCpos : (0 : ℝ) < C := by
    exact_mod_cast (show 0 < C by omega)
  have hMcast : ((2 * C + 1 : ℕ) : ℝ) ≤ 3 * (C : ℝ) := by
    push_cast
    have hCone : (1 : ℝ) ≤ C := by exact_mod_cast hcutoffM
    linarith
  have hlogM' : Real.log (((2 * C + 1 : ℕ) : ℝ)) ≤
      Real.log (3 * (C : ℝ)) := Real.log_le_log (by positivity) hMcast
  have hlogThree : Real.log (3 : ℝ) ≤ 2 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)).trans_eq
      (by norm_num)
  have hsqrtLe : Real.sqrt (m : ℝ) ≤ m := by
    have hsqrtSq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    have hsqrtNonneg := Real.sqrt_nonneg (m : ℝ)
    have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hreal : 1 + Real.log (((2 * C + 1 : ℕ) : ℝ)) ≤
      (6 * m : ℕ) := by
    calc
      1 + Real.log (((2 * C + 1 : ℕ) : ℝ)) ≤
          1 + Real.log (3 * (C : ℝ)) := by linarith
      _ = 1 + Real.log 3 + Real.log (C : ℝ) := by
        rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hCpos.ne']
        ring
      _ ≤ 3 + 3 * Real.sqrt (m : ℝ) := by linarith
      _ ≤ (6 * m : ℕ) := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        nlinarith
  calc
    variableDeltaHarmonic (2 * C + 1) ≤
        ENNReal.ofReal (1 + Real.log (((2 * C + 1 : ℕ) : ℝ))) :=
      variableDeltaHarmonic_le_one_add_log _
    _ ≤ ENNReal.ofReal (((6 * m : ℕ) : ℝ)) := ENNReal.ofReal_mono hreal
    _ = (6 * m : ℕ) := ENNReal.ofReal_natCast _

noncomputable def normalizedCofinalPositiveShellRealCost
    (m : ℕ) (band : RandomClockBand) : ℝ :=
  ∑ shell ∈ Finset.range (shellCount48 m band.beta - 1),
    sharpInterfaceCost
      (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
        shellGrowth48) shell

lemma normalizedCofinalPositiveShellRealCost_nonneg
    (m : ℕ) (band : RandomClockBand) :
    0 ≤ normalizedCofinalPositiveShellRealCost m band := by
  unfold normalizedCofinalPositiveShellRealCost
  exact Finset.sum_nonneg fun shell _ ↦ sharpInterfaceCost_nonneg _ shell

theorem sharpInterfaceCost_normalized_geometric_le_exp_log_sq
    (m shell : ℕ) :
    sharpInterfaceCost
        (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
          shellGrowth48) shell ≤
      Real.exp (-(sharpProductRate / 4) * Real.log (m : ℝ) ^ 2) := by
  unfold sharpInterfaceCost
  rw [Real.exp_le_exp]
  have hbudget : Real.log (m : ℝ) ^ 2 ≤ (initialBudget48 m : ℝ) := by
    unfold initialBudget48
    have hceil : Real.log (m : ℝ) ^ 2 ≤
        (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  have hquarter : initialBudget48 m <
      4 * (normalizedPositiveInitialBudget48 m + 1) := by
    unfold normalizedPositiveInitialBudget48
    omega
  have hthreshold : normalizedPositiveInitialBudget48 m ≤
      geometricShellThreshold (normalizedPositiveInitialBudget48 m)
        shellGrowth48 (shell + 1) := by
    unfold geometricShellThreshold
    exact Nat.le_mul_of_pos_right _ (pow_pos shellGrowth48_pos _)
  have hcast : Real.log (m : ℝ) ^ 2 <
      4 * ((geometricShellThreshold (normalizedPositiveInitialBudget48 m)
        shellGrowth48 (shell + 1) + 1 : ℕ) : ℝ) := by
    calc
      Real.log (m : ℝ) ^ 2 ≤ (initialBudget48 m : ℝ) := hbudget
      _ < (4 * (normalizedPositiveInitialBudget48 m + 1) : ℕ) := by
        exact_mod_cast hquarter
      _ ≤ 4 * ((geometricShellThreshold
          (normalizedPositiveInitialBudget48 m) shellGrowth48
            (shell + 1) + 1 : ℕ) : ℝ) := by
        push_cast
        exact_mod_cast Nat.mul_le_mul_left 4 (Nat.add_le_add_right hthreshold 1)
  nlinarith [sharpProductRate_pos]

theorem normalizedCofinalPositiveShellRealCost_le_level_mul_exp
    {m : ℕ} (hm : 1 ≤ m) {band : RandomClockBand}
    (hbeta : band.beta ≤ (7 / 10 : ℝ)) :
    normalizedCofinalPositiveShellRealCost m band ≤
      (m : ℝ) * Real.exp
        (-(sharpProductRate / 4) * Real.log (m : ℝ) ^ 2) := by
  unfold normalizedCofinalPositiveShellRealCost
  calc
    (∑ shell ∈ Finset.range (shellCount48 m band.beta - 1),
        sharpInterfaceCost
          (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
            shellGrowth48) shell) ≤
      ∑ _shell ∈ Finset.range (shellCount48 m band.beta - 1),
        Real.exp (-(sharpProductRate / 4) * Real.log (m : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro shell _
      exact sharpInterfaceCost_normalized_geometric_le_exp_log_sq m shell
    _ = ((shellCount48 m band.beta - 1 : ℕ) : ℝ) *
        Real.exp (-(sharpProductRate / 4) * Real.log (m : ℝ) ^ 2) := by simp
    _ ≤ (m : ℝ) * Real.exp
        (-(sharpProductRate / 4) * Real.log (m : ℝ) ^ 2) := by
      gcongr
      exact_mod_cast (Nat.sub_le _ _).trans
        (shellCount48_le_level_of_beta_le_sevenTenths hm hbeta)

/-- Locally balanced exact-pair source carriers for one normalized endpoint
orientation. -/
def orientedBandPositiveInterfaceBalancedPairPaymentEvent
    (t : DominoTiling) (o : Orientation) (m : ℕ)
    (band : RandomClockBand) : Set WalkPath :=
  ⋃ shell ∈ Finset.range (shellCount48 m band.beta - 1),
    positiveInterfaceExternalPairBalancedSourceEvent t o m
      band.oldRank 1 (shellWidth48 m) shell
      (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
        shellGrowth48)
      (levelCutoffTime upperTailDelta m)

/-- Both endpoint orientations selected by the dominant normalization. -/
def bandPositiveInterfaceBalancedPairPaymentEvent
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  orientedBandPositiveInterfaceBalancedPairPaymentEvent t .even m band ∪
    orientedBandPositiveInterfaceBalancedPairPaymentEvent t .shifted m band

/-- The balanced carrier in one band is bounded by the sum of its exact
harmonic adjacent-shell costs. -/
theorem simpleRandomWalk_bandPositiveInterfaceBalancedPairPaymentEvent_le
    {t : DominoTiling} {m : ℕ} (hm : 1 < m)
    (band : RandomClockBand) :
    simpleRandomWalk
        (bandPositiveInterfaceBalancedPairPaymentEvent t m band) ≤
      2 * (∑ shell ∈ Finset.range (shellCount48 m band.beta - 1),
        variableDeltaHarmonic
            (2 * levelCutoffTime upperTailDelta m + 1) *
          ENNReal.ofReal
            (sharpRankConstant * sharpInterfaceCost
              (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
                shellGrowth48) shell)) := by
  let cost : ℝ≥0∞ := ∑ shell ∈
      Finset.range (shellCount48 m band.beta - 1),
    variableDeltaHarmonic
        (2 * levelCutoffTime upperTailDelta m + 1) *
      ENNReal.ofReal
        (sharpRankConstant * sharpInterfaceCost
          (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
            shellGrowth48) shell)
  have horiented : ∀ o : Orientation,
      simpleRandomWalk
          (orientedBandPositiveInterfaceBalancedPairPaymentEvent
            t o m band) ≤ cost := by
    intro o
    calc
      simpleRandomWalk
          (orientedBandPositiveInterfaceBalancedPairPaymentEvent
            t o m band) ≤
        ∑ shell ∈ Finset.range (shellCount48 m band.beta - 1),
          simpleRandomWalk
            (positiveInterfaceExternalPairBalancedSourceEvent t o m
              band.oldRank 1 (shellWidth48 m) shell
              (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
                shellGrowth48)
              (levelCutoffTime upperTailDelta m)) :=
        measure_biUnion_finset_le _ _
      _ ≤ cost := by
        apply Finset.sum_le_sum
        intro shell _hshell
        exact
          simpleRandomWalk_positiveInterfaceExternalPairBalancedSourceEvent_le
            hm band.oldRank_pos _ _
  calc
    simpleRandomWalk
        (bandPositiveInterfaceBalancedPairPaymentEvent t m band) ≤
      simpleRandomWalk
          (orientedBandPositiveInterfaceBalancedPairPaymentEvent
            t .even m band) +
        simpleRandomWalk
          (orientedBandPositiveInterfaceBalancedPairPaymentEvent
            t .shifted m band) := measure_union_le _ _
    _ ≤ cost + cost := add_le_add (horiented .even) (horiented .shifted)
    _ = 2 * cost := by ring
    _ = _ := rfl

/-- Summing the shell bounds factors out the common harmonic loss. -/
theorem simpleRandomWalk_bandPositiveInterfaceBalancedPairPaymentEvent_le_cost
    {t : DominoTiling} {m : ℕ} (hm : 1 < m)
    (band : RandomClockBand) :
    simpleRandomWalk
        (bandPositiveInterfaceBalancedPairPaymentEvent t m band) ≤
      variableDeltaHarmonic
          (2 * levelCutoffTime upperTailDelta m + 1) *
        (2 * ENNReal.ofReal
          (sharpRankConstant * normalizedCofinalPositiveShellRealCost
            m band)) := by
  refine (simpleRandomWalk_bandPositiveInterfaceBalancedPairPaymentEvent_le
    hm band).trans ?_
  have hsum :
      (∑ shell ∈ Finset.range (shellCount48 m band.beta - 1),
          variableDeltaHarmonic
              (2 * levelCutoffTime upperTailDelta m + 1) *
            ENNReal.ofReal
              (sharpRankConstant * sharpInterfaceCost
                (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
                  shellGrowth48) shell)) =
        variableDeltaHarmonic
            (2 * levelCutoffTime upperTailDelta m + 1) *
          ENNReal.ofReal
            (sharpRankConstant * normalizedCofinalPositiveShellRealCost
              m band) := by
    rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      unfold normalizedCofinalPositiveShellRealCost
      rw [Finset.mul_sum]
    · intro shell hshell
      exact mul_nonneg sharpRankConstant_pos.le
        (sharpInterfaceCost_nonneg _ shell)
  rw [hsum]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    (le_refl (2 * (ENNReal.ofReal
      (sharpRankConstant * normalizedCofinalPositiveShellRealCost m band) *
        variableDeltaHarmonic
          (2 * levelCutoffTime upperTailDelta m + 1))))

/-- A single variable factor `m` is absorbed by half of any positive
logarithmic-square rate. -/
theorem eventually_level_mul_exp_neg_two_log_sq_le_exp_neg
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)) ≤
        ENNReal.ofReal
          (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [hlog.eventually (eventually_ge_atTop (max 1 (1 / c))),
       eventually_ge_atTop (1 : ℕ)] with m hlarge hm
  have hlogOne : 1 ≤ Real.log (m : ℝ) := le_trans (le_max_left _ _) hlarge
  have hlogInv : 1 / c ≤ Real.log (m : ℝ) :=
    le_trans (le_max_right _ _) hlarge
  have hscaled : 1 ≤ c * Real.log (m : ℝ) := by
    rw [div_le_iff₀ hc] at hlogInv
    simpa only [one_mul, mul_comm] using hlogInv
  have hdom : Real.log (m : ℝ) +
      c * Real.log (m : ℝ) ^ 2 ≤
        2 * c * Real.log (m : ℝ) ^ 2 := by
    have hlinear : Real.log (m : ℝ) ≤
        c * Real.log (m : ℝ) ^ 2 := by
      calc
        Real.log (m : ℝ) = 1 * Real.log (m : ℝ) := by ring
        _ ≤ (c * Real.log (m : ℝ)) * Real.log (m : ℝ) := by
          gcongr
        _ = c * Real.log (m : ℝ) ^ 2 := by ring
    linarith
  simpa only [neg_mul] using
    (Gap.ennreal_nat_mul_exp_neg_le_exp_neg (J := m)
      (exponent := 2 * c * Real.log (m : ℝ) ^ 2)
      (target := c * Real.log (m : ℝ) ^ 2) (by omega) hdom)

/-- Uniform one-band estimate after absorbing the shell count and harmonic
rank loss. -/
theorem eventually_bandPositiveInterfaceBalancedPairPaymentEvent_le_exp
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) :
    ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ sourceProductEndpointBands m (sourceCandidateLazyCap48 m)
          (data.externalThreshold m),
        simpleRandomWalk
            (bandPositiveInterfaceBalancedPairPaymentEvent t m band) ≤
          ((12 * sharpRankNatConstant : ℕ) : ℝ≥0∞) * ENNReal.ofReal
            (Real.exp (-(sharpProductRate / 16) *
              Real.log (m : ℝ) ^ 2)) := by
  have hharmonic := eventually_variableDeltaHarmonic_cutoff_le
  have hpolyOne := eventually_level_mul_exp_neg_two_log_sq_le_exp_neg
    (show 0 < sharpProductRate / 8 by
      positivity [sharpProductRate_pos])
  have hpolyTwo := eventually_level_mul_exp_neg_two_log_sq_le_exp_neg
    (show 0 < sharpProductRate / 16 by
      positivity [sharpProductRate_pos])
  filter_upwards [hharmonic, hpolyOne, hpolyTwo,
      eventually_ge_atTop (2 : ℕ)] with
      m hharmonicM hpolyOneM hpolyTwoM hm
  intro band hband
  let qQuarter : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-(sharpProductRate / 4) * Real.log (m : ℝ) ^ 2))
  let qEighth : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-(sharpProductRate / 8) * Real.log (m : ℝ) ^ 2))
  let qSixteenth : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-(sharpProductRate / 16) * Real.log (m : ℝ) ^ 2))
  have hcofinal := normalizedCofinalPositiveShellRealCost_le_level_mul_exp
    (m := m) (band := band) (by omega)
      (sourceProductEndpointBand_betaUpperRange hband)
  have hcost : ENNReal.ofReal
        (sharpRankConstant * normalizedCofinalPositiveShellRealCost m band) ≤
      (sharpRankNatConstant : ℝ≥0∞) * ((m : ℝ≥0∞) * qQuarter) := by
    calc
      ENNReal.ofReal
          (sharpRankConstant * normalizedCofinalPositiveShellRealCost
            m band) ≤
          ENNReal.ofReal (sharpRankConstant * ((m : ℝ) * Real.exp
            (-(sharpProductRate / 4) * Real.log (m : ℝ) ^ 2))) := by
        apply ENNReal.ofReal_mono
        exact mul_le_mul_of_nonneg_left hcofinal sharpRankConstant_pos.le
      _ = (sharpRankNatConstant : ℝ≥0∞) *
          ((m : ℝ≥0∞) * qQuarter) := by
        rw [ENNReal.ofReal_mul sharpRankConstant_pos.le,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ m)]
        simp only [ofReal_sharpRankConstant, ENNReal.ofReal_natCast, qQuarter]
  have hpolyOneM' : (m : ℝ≥0∞) * qQuarter ≤ qEighth := by
    simpa only [qQuarter, qEighth, show 2 * (sharpProductRate / 8) =
      sharpProductRate / 4 by ring] using hpolyOneM
  have hpolyTwoM' : (m : ℝ≥0∞) * qEighth ≤ qSixteenth := by
    simpa only [qEighth, qSixteenth, show 2 * (sharpProductRate / 16) =
      sharpProductRate / 8 by ring] using hpolyTwoM
  calc
    simpleRandomWalk
        (bandPositiveInterfaceBalancedPairPaymentEvent t m band) ≤
      variableDeltaHarmonic
          (2 * levelCutoffTime upperTailDelta m + 1) *
        (2 * ENNReal.ofReal
          (sharpRankConstant * normalizedCofinalPositiveShellRealCost
            m band)) :=
      simpleRandomWalk_bandPositiveInterfaceBalancedPairPaymentEvent_le_cost
        (by omega) band
    _ ≤ ((6 * m : ℕ) : ℝ≥0∞) *
        (2 * ((sharpRankNatConstant : ℝ≥0∞) *
          ((m : ℝ≥0∞) * qQuarter))) := by
      gcongr
    _ = ((12 * sharpRankNatConstant : ℕ) : ℝ≥0∞) *
        ((m : ℝ≥0∞) * ((m : ℝ≥0∞) * qQuarter)) := by
      push_cast
      ring
    _ ≤ ((12 * sharpRankNatConstant : ℕ) : ℝ≥0∞) *
        ((m : ℝ≥0∞) * qEighth) := by
      gcongr
    _ ≤ ((12 * sharpRankNatConstant : ℕ) : ℝ≥0∞) *
        qSixteenth := by
      gcongr
    _ = _ := rfl

/-- Rankwise finite union of the balanced exact-pair payments. -/
def positiveInterfaceBalancedPairPaymentUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (bandPositiveInterfaceBalancedPairPaymentEvent t m)

theorem simpleRandomWalk_positiveInterfaceBalancedPairPaymentUnionAtRank_le
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) (hm : 1 < m) :
    simpleRandomWalk
        (positiveInterfaceBalancedPairPaymentUnionAtRank data t rank m) ≤
      ∑ band ∈ sourceProductEndpointBandsAtRank m
          (sourceCandidateLazyCap48 m) (data.externalThreshold m) rank,
        simpleRandomWalk
          (bandPositiveInterfaceBalancedPairPaymentEvent t m band) :=
  Screening.measure_someCandidateBad_le_sum simpleRandomWalk _ _

/-- The finite endpoint-band family preserves a positive logarithmic-square
rate for the locally balanced pair payment. -/
theorem
    eventually_simpleRandomWalk_positiveInterfaceBalancedPairPaymentUnionAtRank_le_exp
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (positiveInterfaceBalancedPairPaymentUnionAtRank data t rank m) ≤
        ENNReal.ofReal (Real.exp
          (-(sharpProductRate / 32) * Real.log (m : ℝ) ^ 2)) := by
  have heach := eventually_bandPositiveInterfaceBalancedPairPaymentEvent_le_exp
    data t
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
    (Nat.card CanonicalEndpointLowGapBandTag *
      (12 * sharpRankNatConstant))
    (show 0 < sharpProductRate / 32 by
      positivity [sharpProductRate_pos])
  filter_upwards [heach, habsorb, eventually_ge_atTop (2 : ℕ)] with
      m heachM habsorbM hm
  let q : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-(sharpProductRate / 16) * Real.log (m : ℝ) ^ 2))
  calc
    simpleRandomWalk
        (positiveInterfaceBalancedPairPaymentUnionAtRank data t rank m) ≤
      ∑ band ∈ sourceProductEndpointBandsAtRank m
          (sourceCandidateLazyCap48 m) (data.externalThreshold m) rank,
        simpleRandomWalk
          (bandPositiveInterfaceBalancedPairPaymentEvent t m band) :=
      Screening.measure_someCandidateBad_le_sum simpleRandomWalk _ _
    _ ≤ ∑ band ∈ sourceProductEndpointBandsAtRank m
          (sourceCandidateLazyCap48 m) (data.externalThreshold m) rank,
        ((12 * sharpRankNatConstant : ℕ) : ℝ≥0∞) * q := by
      apply Finset.sum_le_sum
      intro band hband
      exact heachM band (Finset.mem_filter.mp hband).1
    _ ≤ ∑ _band ∈ sourceProductEndpointBands m
          (sourceCandidateLazyCap48 m) (data.externalThreshold m),
        ((12 * sharpRankNatConstant : ℕ) : ℝ≥0∞) * q := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ((sourceProductEndpointBands m (sourceCandidateLazyCap48 m)
          (data.externalThreshold m)).card : ℝ≥0∞) *
        (((12 * sharpRankNatConstant : ℕ) : ℝ≥0∞) * q) := by simp
    _ ≤ (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) *
        (((12 * sharpRankNatConstant : ℕ) : ℝ≥0∞) * q) := by
      gcongr
      exact_mod_cast sourceProductEndpointBands_card_le m
        (sourceCandidateLazyCap48 m) (data.externalThreshold m)
    _ = ((Nat.card CanonicalEndpointLowGapBandTag *
          (12 * sharpRankNatConstant) : ℕ) : ℝ≥0∞) * q := by
      push_cast
      ring
    _ ≤ _ := by
      simpa only [q, show 2 * (sharpProductRate / 32) =
        sharpProductRate / 16 by ring] using habsorbM

theorem
    simpleRandomWalk_positiveInterfaceBalancedPairPaymentUnionAtRank_series_ne_top
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank : ℕ) :
    ∑' m, simpleRandomWalk
        (positiveInterfaceBalancedPairPaymentUnionAtRank data t rank m) ≠ ∞ :=
  measure_series_ne_top_of_eventually_exp_neg_log_sq_bound simpleRandomWalk _
    (show 0 < sharpProductRate / 32 by
      positivity [sharpProductRate_pos])
    (eventually_simpleRandomWalk_positiveInterfaceBalancedPairPaymentUnionAtRank_le_exp
      data t rank)

/-- The genuinely exceptional part of a physical interface failure is what
remains after removing the locally certified exact-pair carrier. -/
def bandPositiveInterfaceUnbalancedPairRemainderEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  bandPositiveInterfaceFailureEvent data t m band \
    bandPositiveInterfaceBalancedPairPaymentEvent t m band

/-- Rankwise finite union of the genuinely unbalanced pair histories. -/
def positiveInterfaceUnbalancedPairRemainderUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (bandPositiveInterfaceUnbalancedPairRemainderEvent data t m)

/-- The creation/no-next-level profile on which the canonical external-pair
source cap can be reconstructed.  Level zero is included automatically; it
is a single harmless term in every series and avoids imposing a positivity
hypothesis on the final concrete adapter. -/
def positiveInterfaceCreationNoNextProfileEvent
    (m rank : ℕ) : Set WalkPath :=
  if 0 < m then
    {s | ∃ n, ThresholdCreation s m rank n ∧
      thresholdCount s n (m + 1) = 0}
  else Set.univ

/-- Only the unbalanced histories carrying the source-reconstruction
profile need to be paid by the concrete balance adapter. -/
def positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  positiveInterfaceCreationNoNextProfileEvent m rank ∩
    positiveInterfaceUnbalancedPairRemainderUnionAtRank data t rank m

def normalizedPositiveInterfaceBand (o : Orientation)
    (band : RandomClockBand) : RandomClockBand :=
  { band with orientation := o, externalThreshold := 1 }

@[simp] theorem dominantOccupancy_normalizedPositiveInterfaceBand
    (t : DominoTiling) (o : Orientation) (m cutoff : ℕ)
    (band : RandomClockBand) :
    dominantPositiveInterfaceBandOccupancy t o m cutoff
        (normalizedPositiveInterfaceBand o band) =
      normalizedDominantBandOccupancy t o m cutoff band := by
  rfl

/-- A profiled path left outside the balanced carrier still has its canonical
exact-pair source cap.  Consequently the obstruction is local: either the
deleted external prefix is empty, or the arithmetic certificate for that
very history fails. -/
theorem exists_sourceCap_zeroPrefix_or_not_arithmetic_of_mem_bandUnbalanced
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {m : ℕ} {band : RandomClockBand} {s : WalkPath}
    (hm : 1 < m)
    (hband : band ∈ sourceProductEndpointBands m
      (sourceCandidateLazyCap48 m) (data.externalThreshold m))
    (hprofile : s ∈ positiveInterfaceCreationNoNextProfileEvent
      m band.oldRank)
    (hunbalanced : s ∈
      bandPositiveInterfaceUnbalancedPairRemainderEvent data t m band) :
    ∃ o : Orientation,
      ∃ shell ∈ Finset.range (shellCount48 m band.beta - 1),
      ∃ eta : PositiveInterfaceExternalPairSupportedIndex t o m
          band.oldRank 1 (shellWidth48 m) shell,
        ∃ cap : ℕ,
          s ∈ orientedBandPositiveInterfaceFailureEvent t o m band ∧
            eta.1.1 = fixedOrientedTypedExternalWordCode t o
              (creationTimeNat m band.oldRank s) s ∧
            s ∈ positiveInterfaceExternalPairSourceCap eta cap
              (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
                shellGrowth48)
              (levelCutoffTime upperTailDelta m) ∧
            (eta.1.1.initial.1.length + 2 * eta.1.1.retainedCount +
                  eta.1.1.tail.1.length = 0 ∨
              ¬ PositiveInterfaceExternalPairArithmetic eta cap) := by
  have hmpos : 0 < m := by omega
  rw [positiveInterfaceCreationNoNextProfileEvent, if_pos hmpos] at hprofile
  rcases hprofile with ⟨n, hcreation, hnext⟩
  rcases hunbalanced with ⟨hfailure, hnotBalanced⟩
  rcases Set.mem_iUnion.mp hfailure with ⟨o, hfailure⟩
  have horientedFailure :
      s ∈ orientedBandPositiveInterfaceFailureEvent t o m band := hfailure
  rcases Set.mem_iUnion.mp hfailure with ⟨shell, hfailure⟩
  rcases Set.mem_iUnion.mp hfailure with ⟨hshell, hfailure⟩
  have hvalid : s ∈ validStepWalk := hfailure.1.1.2
  have hclock : n ≤ levelCutoffTime upperTailDelta m := by
    have hclock' := hfailure.1.2
    change creationTimeNat m band.oldRank s ≤
      levelCutoffTime upperTailDelta m at hclock'
    rwa [creationTimeNat_eq_of_creation hcreation] at hclock'
  have hgrowth : s ∈ thresholdedGrowthFailure
      (normalizedDominantBandOccupancy t o m
        (levelCutoffTime upperTailDelta m) band)
      (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
        shellGrowth48)
      shellGrowth48 shell := by
    simpa only [thresholdedInterfaceBad, compl_univ, empty_union] using
      hfailure.2
  let normalizedBand := normalizedPositiveInterfaceBand o band
  rcases exists_positiveInterfaceExternalPairSourceCap_of_raw_growth
      (band := normalizedBand) hm
      (by simpa only [normalizedBand, normalizedPositiveInterfaceBand] using
        sourceProductEndpointBand_vertexPhase hband)
      (by simp only [normalizedBand, normalizedPositiveInterfaceBand]; omega)
      hcreation hnext hclock hvalid
      (by
        change s ∈ thresholdedGrowthFailure
          (normalizedDominantBandOccupancy t o m
            (levelCutoffTime upperTailDelta m) band)
          (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
            shellGrowth48) shellGrowth48 shell
        exact hgrowth) with
    ⟨eta, cap, hcode, hcap⟩
  refine ⟨o, shell, hshell, eta, cap, horientedFailure, ?_, hcap, ?_⟩
  · simpa only [normalizedBand, normalizedPositiveInterfaceBand] using hcode
  by_cases hpos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length
  · right
    intro harithmetic
    apply hnotBalanced
    cases o with
    | even =>
        exact Or.inl (Set.mem_iUnion.mpr ⟨shell,
          Set.mem_iUnion.mpr ⟨hshell,
            eta, cap, hpos, harithmetic, hcap⟩⟩)
    | shifted =>
        exact Or.inr (Set.mem_iUnion.mpr ⟨shell,
          Set.mem_iUnion.mpr ⟨hshell,
            eta, cap, hpos, harithmetic, hcap⟩⟩)
  · left
    omega

/-- The previous active-window reconstruction remainder is covered exactly
by the new summable balanced carrier and the genuinely unbalanced residual.
No relation between the mean-centered active window and the physical rows is
asserted here. -/
theorem positiveInterfaceBalanceRemainderUnionAtRank_subset_pair_split
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) :
    positiveInterfaceBalanceRemainderUnionAtRank data t rank m ⊆
      positiveInterfaceBalancedPairPaymentUnionAtRank data t rank m ∪
        positiveInterfaceUnbalancedPairRemainderUnionAtRank data t rank m := by
  rintro s ⟨band, hband, hfailure, hnotScreened⟩
  by_cases hbalanced :
      s ∈ bandPositiveInterfaceBalancedPairPaymentEvent t m band
  · exact Or.inl ⟨band, hband, hbalanced⟩
  · exact Or.inr ⟨band, hband, hfailure, hbalanced⟩

/-- On histories carrying the creation profile, the old reconstruction
remainder is covered by the balanced harmonic payment and the profiled
unbalanced residual. -/
theorem
    positiveInterfaceCreationProfile_inter_balanceRemainder_subset_pair_split
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) :
    positiveInterfaceCreationNoNextProfileEvent m rank ∩
        positiveInterfaceBalanceRemainderUnionAtRank data t rank m ⊆
      positiveInterfaceBalancedPairPaymentUnionAtRank data t rank m ∪
        positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank
          data t rank m := by
  rintro s ⟨hprofile, hremainder⟩
  rcases positiveInterfaceBalanceRemainderUnionAtRank_subset_pair_split
      data t rank m hremainder with hbalanced | hunbalanced
  · exact Or.inl hbalanced
  · exact Or.inr ⟨hprofile, hunbalanced⟩

end

end Erdos1165.HLOZPositiveInterfacePairBalancedSeries
