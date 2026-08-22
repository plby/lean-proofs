/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaPositiveSlotProduct
import ErdosProblems.Erdos1165.HLOZUpperEstimates

/-!
# Positive-prefix source-Theta payment

The literal source-window restricted-Theta event is split into a positive
deleted-prefix product payment and a zero-prefix origin event.  The former
has a premise-free logarithmic-square tail and a finite measure series.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceOrientedThetaPositiveSourcePayment

open ExternalProposition44 HLOZPathEvents HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaLowSingletonProduct
open HLOZSourceOrientedThetaPositiveSlotProduct
open HLOZSourceOrientedThetaProduct
open HLOZSourceOrientedThetaSingletonScaleProduct
open HLOZSourceOrientedThetaSourceSlotFiberCover
open HLOZSourceOrientedThetaWindowSplit
open HLOZUpperEstimates LazyDecomposition ScreeningInstantiation
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The full literal positive-prefix payment, including the null invalid-walk
branch and the already-paid Proposition 4.4 support overflow. -/
def positiveRestrictedThetaSourceProductMajorant
    (t : DominoTiling) (o : Orientation) (m k : ℕ) : Set WalkPath :=
  validStepWalkᶜ ∪
    (orientedThetaCandidateOverflow44 t o m ∪
      (positiveHighSourceProductMajorant t o m k
          (shellWidth48 m) (shellZeroExternalLow48 m)
            (shellZeroExternalHigh48 m) ∪
        positiveLowSourceProductMajorant t o m k
          (shellWidth48 m) (shellZeroExternalLow48 m)
            (shellZeroExternalHigh48 m)))

/-- The sole source-window slot branch not represented by a positive
deleted external prefix. -/
def zeroPrefixRestrictedThetaSourceEvent
    (t : DominoTiling) (o : Orientation) (m k : ℕ) : Set WalkPath :=
  {s | s ∈ validStepWalk ∧ ReachesThreshold s m k ∧
    creationTimeNat m k s ≤ hlozCutoff44 m ∧
    (orientedRestrictedThetaSourceAtCreation t o m k
      (shellWidth48 m) (shellZeroExternalLow48 m)
        (shellZeroExternalHigh48 m) s).Nonempty ∧
    s ∉ positiveExternalCreationPrefix t o m k}

theorem restrictedThetaSource_onTime_subset_positive_or_zero
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (hm : 1 < m) (hk : 0 < k) :
    {s | ReachesThreshold s m k ∧
      creationTimeNat m k s ≤ hlozCutoff44 m ∧
      (orientedRestrictedThetaSourceAtCreation t o m k
        (shellWidth48 m) (shellZeroExternalLow48 m)
          (shellZeroExternalHigh48 m) s).Nonempty} ⊆
      positiveRestrictedThetaSourceProductMajorant t o m k ∪
        zeroPrefixRestrictedThetaSourceEvent t o m k := by
  intro s hs
  have hpaid := restrictedThetaSource_onTime_subset_creationPaid t o m k
    (shellWidth48 m) (shellZeroExternalLow48 m)
      (shellZeroExternalHigh48 m) hm hk hs
  rcases hpaid with hinvalid | hoverflow | hslots
  · left
    left
    exact hinvalid
  · left
    right; left
    exact hoverflow
  · rcases hslots with hhigh | hlow
    · rcases hhigh with ⟨slot, _hslot, hbad⟩
      by_cases hpositive : s ∈ positiveExternalCreationPrefix t o m k
      · left
        right; right; left
        apply Set.mem_iUnion.mpr
        refine ⟨slot, positiveHighSourceSlotBad_subset_majorant
          t o m k (shellWidth48 m) (shellZeroExternalLow48 m)
            (shellZeroExternalHigh48 m) slot ?_⟩
        exact ⟨hbad, hpositive⟩
      · right
        exact ⟨hbad.1, hs.1, hs.2.1, hs.2.2, hpositive⟩
    · rcases hlow with ⟨slot, _hslot, hbad⟩
      by_cases hpositive : s ∈ positiveExternalCreationPrefix t o m k
      · left
        right; right; right
        apply Set.mem_iUnion.mpr
        refine ⟨slot, positiveLowSourceSlotBad_subset_majorant
          t o m k (shellWidth48 m) (shellZeroExternalLow48 m)
            (shellZeroExternalHigh48 m) slot hm hk ?_⟩
        exact ⟨hbad, hpositive⟩
      · right
        exact ⟨hbad.1, hs.1, hs.2.1, hs.2.2, hpositive⟩

private theorem lowRate_exp_le_balanceRate_exp
    {m : ℕ} (hm : 1 ≤ m) :
    Real.exp (-17 * thetaLowRateScale m) ≤
      Real.exp (-17 * balanceRateScale m) := by
  apply Real.exp_le_exp.mpr
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr : balanceRateScale m ≤ thetaLowRateScale m := by
    unfold balanceRateScale thetaLowRateScale kappaOne
    norm_num
    exact Real.rpow_le_rpow_of_exponent_le hmR (by norm_num)
  nlinarith

private theorem singletonRatio_le_two_highCost
    {m : ℕ} (hm : 1 ≤ m) :
    singletonSourceThetaRatio m ≤ 2 * thetaHighOneSlotCost m := by
  have hexp := lowRate_exp_le_balanceRate_exp hm
  unfold singletonSourceThetaRatio thetaHighOneSlotCost
  have hreal : 2 * (Real.exp (-17 * balanceRateScale m) +
      Real.exp (-17 * thetaLowRateScale m)) ≤
      4 * Real.exp (-17 * balanceRateScale m) := by
    nlinarith [Real.exp_pos (-17 * balanceRateScale m)]
  calc
    ENNReal.ofReal (2 * (Real.exp (-17 * balanceRateScale m) +
        Real.exp (-17 * thetaLowRateScale m))) ≤
      ENNReal.ofReal (4 * Real.exp (-17 * balanceRateScale m)) :=
        ENNReal.ofReal_mono hreal
    _ = 2 * (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
        ENNReal.ofReal (Real.exp (-17 * balanceRateScale m))) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ENNReal.ofReal_ofNat]
      ring

private theorem lowSingletonRatio_eq_two_lowCost (m : ℕ) :
    lowSingletonSourceThetaRatio m = 2 * thetaLowOneSlotCost m := by
  unfold lowSingletonSourceThetaRatio thetaLowOneSlotCost
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat]

theorem eventually_simpleRandomWalk_positiveSourceProductMajorant_le_cost
    (t : DominoTiling) (o : Orientation) (k : ℕ) (hk : 0 < k) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
        (positiveRestrictedThetaSourceProductMajorant t o m k) ≤
          6 * orientedThetaCost m := by
  filter_upwards [eventually_orientedThetaCandidateOverflow_lt_failureRate t o,
      eventually_orientedThetaScaleArithmetic, eventually_ge_atTop (2 : ℕ)]
      with m hcandidate scale hm
  have hm' : 1 ≤ m := by omega
  have hhigh := simpleRandomWalk_positiveHighSourceProductMajorant_le
    t o m k (by omega) hk scale
  have hlow := simpleRandomWalk_positiveLowSourceProductMajorant_le
    t o m k (by omega) hk scale
  have hratio := singletonRatio_le_two_highCost hm'
  have hhigh' : simpleRandomWalk
      (positiveHighSourceProductMajorant t o m k
        (shellWidth48 m) (shellZeroExternalLow48 m)
          (shellZeroExternalHigh48 m)) ≤
      6 * ((hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m) := by
    calc
      _ ≤ (hlozSiteBudget44 m : ℝ≥0∞) *
          (3 * singletonSourceThetaRatio m) := hhigh
      _ ≤ (hlozSiteBudget44 m : ℝ≥0∞) *
          (3 * (2 * thetaHighOneSlotCost m)) := by gcongr
      _ = _ := by ring
  have hlow' : simpleRandomWalk
      (positiveLowSourceProductMajorant t o m k
        (shellWidth48 m) (shellZeroExternalLow48 m)
          (shellZeroExternalHigh48 m)) ≤
      6 * (((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) *
        thetaLowOneSlotCost m) := by
    calc
      _ ≤ ((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) *
          (3 * lowSingletonSourceThetaRatio m) := hlow
      _ = _ := by rw [lowSingletonRatio_eq_two_lowCost]; ring
  unfold positiveRestrictedThetaSourceProductMajorant orientedThetaCost
  calc
    simpleRandomWalk
        (validStepWalkᶜ ∪
          (orientedThetaCandidateOverflow44 t o m ∪
            (positiveHighSourceProductMajorant t o m k
                (shellWidth48 m) (shellZeroExternalLow48 m)
                  (shellZeroExternalHigh48 m) ∪
              positiveLowSourceProductMajorant t o m k
                (shellWidth48 m) (shellZeroExternalLow48 m)
                  (shellZeroExternalHigh48 m)))) ≤
      simpleRandomWalk validStepWalkᶜ +
        (simpleRandomWalk (orientedThetaCandidateOverflow44 t o m) +
          (simpleRandomWalk (positiveHighSourceProductMajorant t o m k
              (shellWidth48 m) (shellZeroExternalLow48 m)
                (shellZeroExternalHigh48 m)) +
            simpleRandomWalk (positiveLowSourceProductMajorant t o m k
              (shellWidth48 m) (shellZeroExternalLow48 m)
                (shellZeroExternalHigh48 m)))) := by
      calc
        _ ≤ simpleRandomWalk validStepWalkᶜ +
            simpleRandomWalk
              (orientedThetaCandidateOverflow44 t o m ∪
                (positiveHighSourceProductMajorant t o m k
                    (shellWidth48 m) (shellZeroExternalLow48 m)
                      (shellZeroExternalHigh48 m) ∪
                  positiveLowSourceProductMajorant t o m k
                    (shellWidth48 m) (shellZeroExternalLow48 m)
                      (shellZeroExternalHigh48 m))) := measure_union_le _ _
        _ ≤ simpleRandomWalk validStepWalkᶜ +
            (simpleRandomWalk (orientedThetaCandidateOverflow44 t o m) +
              simpleRandomWalk
                (positiveHighSourceProductMajorant t o m k
                    (shellWidth48 m) (shellZeroExternalLow48 m)
                      (shellZeroExternalHigh48 m) ∪
                  positiveLowSourceProductMajorant t o m k
                    (shellWidth48 m) (shellZeroExternalLow48 m)
                      (shellZeroExternalHigh48 m))) := by
          gcongr
          exact measure_union_le _ _
        _ ≤ _ := by
          gcongr
          exact measure_union_le _ _
    _ ≤ 0 + (hlozFailureRate44 m +
        (6 * ((hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m) +
          6 * (((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) *
            thetaLowOneSlotCost m))) := by
      exact add_le_add
        HLOZLazyOverflowClosure.simpleRandomWalk_validStepWalk_compl.le
        (add_le_add hcandidate.le (add_le_add hhigh' hlow'))
    _ ≤ 6 * (hlozFailureRate44 m +
        (hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m +
        (hlozCutoff44 m + 1 : ℕ) * thetaLowOneSlotCost m) := by
      have hfailure : hlozFailureRate44 m ≤ 6 * hlozFailureRate44 m := by
        calc
          hlozFailureRate44 m = 1 * hlozFailureRate44 m := by simp
          _ ≤ 6 * hlozFailureRate44 m := by
            gcongr
            norm_num
      calc
        0 + (hlozFailureRate44 m +
            (6 * ((hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m) +
              6 * (((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) *
                thetaLowOneSlotCost m))) =
          hlozFailureRate44 m +
            (6 * ((hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m) +
              6 * (((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) *
                thetaLowOneSlotCost m)) := by simp
        _ ≤ 6 * hlozFailureRate44 m +
            (6 * ((hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m) +
              6 * (((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) *
                thetaLowOneSlotCost m)) :=
          add_le_add hfailure (le_refl _)
        _ = _ := by ring

theorem eventually_simpleRandomWalk_positiveSourceProductMajorant_le_exp
    (t : DominoTiling) (o : Orientation) (k : ℕ) (hk : 0 < k) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
        (positiveRestrictedThetaSourceProductMajorant t o m k) ≤
      ENNReal.ofReal (Real.exp (-Real.log (m : ℝ) ^ 2)) := by
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_simpleRandomWalk_positiveSourceProductMajorant_le_cost
      t o k hk,
      eventually_orientedThetaCost_le_exp 2,
      hlog.eventually (eventually_ge_atTop (Real.sqrt (Real.log 6)))] with
      m hmeasure hcost hlog
  have hmul : 6 * orientedThetaCost m ≤
      6 * ENNReal.ofReal (Real.exp (-2 * Real.log (m : ℝ) ^ 2)) := by
    gcongr
  refine hmeasure.trans (hmul.trans ?_)
  have hlog6 : Real.log (6 : ℝ) ≤ Real.log (m : ℝ) ^ 2 := by
    have hsqrt0 : 0 ≤ Real.sqrt (Real.log 6) := Real.sqrt_nonneg _
    have hsquare := mul_self_le_mul_self hsqrt0 hlog
    calc
      Real.log (6 : ℝ) = Real.sqrt (Real.log 6) *
          Real.sqrt (Real.log 6) :=
        (Real.mul_self_sqrt (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 6))).symm
      _ ≤ Real.log (m : ℝ) * Real.log (m : ℝ) := hsquare
      _ = Real.log (m : ℝ) ^ 2 := by ring
  have hdom : Real.log (6 : ℕ) + Real.log (m : ℝ) ^ 2 ≤
      2 * Real.log (m : ℝ) ^ 2 := by
    norm_num only [Nat.cast_ofNat]
    nlinarith
  simpa only [Nat.cast_ofNat, neg_mul] using
    (Gap.ennreal_nat_mul_exp_neg_le_exp_neg (J := 6)
      (exponent := 2 * Real.log (m : ℝ) ^ 2)
      (target := Real.log (m : ℝ) ^ 2)
      (by norm_num : 0 < 6) hdom)

theorem simpleRandomWalk_positiveSourceProductMajorant_series_ne_top
    (t : DominoTiling) (o : Orientation) (k : ℕ) (hk : 0 < k) :
    ∑' m, simpleRandomWalk
      (positiveRestrictedThetaSourceProductMajorant t o m k) ≠ ∞ :=
  measure_series_ne_top_of_eventually_exp_neg_log_sq_bound simpleRandomWalk _
    (by norm_num : (0 : ℝ) < 1)
    (by simpa only [neg_mul, one_mul] using
      (eventually_simpleRandomWalk_positiveSourceProductMajorant_le_exp
        t o k hk))

end

end Erdos1165.HLOZSourceOrientedThetaPositiveSourcePayment
