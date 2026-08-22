/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaStrongCreationCover
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaPositiveSourcePayment

/-!
# Summable positive-prefix broad strong source payment
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCandidateLocalBroadThetaStrongPositivePayment

open ExternalProposition44 HLOZPathEvents
open HLOZCandidateLocalBroadThetaProduct
open HLOZCandidateLocalBroadThetaStrongCreationCover
open HLOZCandidateLocalBroadThetaStrongPositiveSlotProduct
open HLOZCandidateLocalBroadThetaStrongSingletonProduct
open HLOZConcreteFullBetaProductData
open HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaPositiveSourcePayment
open HLOZSourceOrientedThetaProduct
open HLOZUpperEstimates LazyDecomposition
open ScreeningInstantiation
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

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

private theorem broadStrongSingletonRatio_le_two_highCost
    {m : ℕ} (hm : 1 ≤ m) :
    broadStrongSingletonRatio m ≤ 2 * thetaHighOneSlotCost m := by
  have hexp := lowRate_exp_le_balanceRate_exp hm
  unfold broadStrongSingletonRatio thetaHighOneSlotCost
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

private theorem broadStrongLowSingletonRatio_eq_two_lowCost (m : ℕ) :
    broadStrongLowSingletonRatio m = 2 * thetaLowOneSlotCost m := by
  unfold broadStrongLowSingletonRatio thetaLowOneSlotCost
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat]

theorem eventually_simpleRandomWalk_positiveBroadStrongSourceProductMajorant_le_cost
    (t : DominoTiling) (o : Orientation) (k : ℕ) (hk : 0 < k) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
        (positiveBroadStrongSourceProductMajorant t o m k
          (candidateLocalBroadWidth48 m) (concreteExternalThreshold48 m)) ≤
          6 * orientedThetaCost m := by
  filter_upwards
      [eventually_orientedThetaCandidateOverflow_lt_failureRate t o,
        eventually_candidateLocalBroadThetaScaleArithmetic,
        eventually_concreteFullBeta_capacity, eventually_ge_atTop (2 : ℕ)]
      with m hcandidate scale capacity hm
  have hm' : 1 ≤ m := by omega
  have hhigh := simpleRandomWalk_positiveBroadStrongHighProductMajorant_le
    t o m k (by omega) hk scale capacity
  have hlow := simpleRandomWalk_positiveBroadStrongLowProductMajorant_le
    t o m k (by omega) hk scale capacity
  have hratio := broadStrongSingletonRatio_le_two_highCost hm'
  have hhigh' : simpleRandomWalk
      (positiveBroadStrongHighProductMajorant t o m k
        (candidateLocalBroadWidth48 m) (concreteExternalThreshold48 m)) ≤
      6 * ((hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m) := by
    calc
      _ ≤ (hlozSiteBudget44 m : ℝ≥0∞) *
          (3 * broadStrongSingletonRatio m) := hhigh
      _ ≤ (hlozSiteBudget44 m : ℝ≥0∞) *
          (3 * (2 * thetaHighOneSlotCost m)) := by gcongr
      _ = _ := by ring
  have hlow' : simpleRandomWalk
      (positiveBroadStrongLowProductMajorant t o m k
        (candidateLocalBroadWidth48 m) (concreteExternalThreshold48 m)) ≤
      6 * (((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) *
        thetaLowOneSlotCost m) := by
    calc
      _ ≤ ((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) *
          (3 * broadStrongLowSingletonRatio m) := hlow
      _ = _ := by rw [broadStrongLowSingletonRatio_eq_two_lowCost]; ring
  unfold positiveBroadStrongSourceProductMajorant orientedThetaCost
  calc
    simpleRandomWalk
        (validStepWalkᶜ ∪
          (orientedThetaCandidateOverflow44 t o m ∪
            (positiveBroadStrongHighProductMajorant t o m k
                (candidateLocalBroadWidth48 m) (concreteExternalThreshold48 m) ∪
              positiveBroadStrongLowProductMajorant t o m k
                (candidateLocalBroadWidth48 m)
                  (concreteExternalThreshold48 m)))) ≤
      simpleRandomWalk validStepWalkᶜ +
        (simpleRandomWalk (orientedThetaCandidateOverflow44 t o m) +
          (simpleRandomWalk (positiveBroadStrongHighProductMajorant t o m k
              (candidateLocalBroadWidth48 m) (concreteExternalThreshold48 m)) +
            simpleRandomWalk (positiveBroadStrongLowProductMajorant t o m k
              (candidateLocalBroadWidth48 m)
                (concreteExternalThreshold48 m)))) := by
      calc
        _ ≤ simpleRandomWalk validStepWalkᶜ +
            simpleRandomWalk
              (orientedThetaCandidateOverflow44 t o m ∪
                (positiveBroadStrongHighProductMajorant t o m k
                    (candidateLocalBroadWidth48 m)
                      (concreteExternalThreshold48 m) ∪
                  positiveBroadStrongLowProductMajorant t o m k
                    (candidateLocalBroadWidth48 m)
                      (concreteExternalThreshold48 m))) := measure_union_le _ _
        _ ≤ simpleRandomWalk validStepWalkᶜ +
            (simpleRandomWalk (orientedThetaCandidateOverflow44 t o m) +
              simpleRandomWalk
                (positiveBroadStrongHighProductMajorant t o m k
                    (candidateLocalBroadWidth48 m)
                      (concreteExternalThreshold48 m) ∪
                  positiveBroadStrongLowProductMajorant t o m k
                    (candidateLocalBroadWidth48 m)
                      (concreteExternalThreshold48 m))) := by
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
          _ ≤ 6 * hlozFailureRate44 m := by gcongr; norm_num
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
                thetaLowOneSlotCost m)) := add_le_add hfailure (le_refl _)
        _ = _ := by ring

theorem eventually_simpleRandomWalk_positiveBroadStrongSourceProductMajorant_le_exp
    (t : DominoTiling) (o : Orientation) (k : ℕ) (hk : 0 < k) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
        (positiveBroadStrongSourceProductMajorant t o m k
          (candidateLocalBroadWidth48 m) (concreteExternalThreshold48 m)) ≤
      ENNReal.ofReal (Real.exp (-Real.log (m : ℝ) ^ 2)) := by
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_simpleRandomWalk_positiveBroadStrongSourceProductMajorant_le_cost
      t o k hk,
      eventually_orientedThetaCost_le_exp 2,
      hlog.eventually (eventually_ge_atTop (Real.sqrt (Real.log 6)))] with
      m hmeasure hcost hlog
  have hmul : 6 * orientedThetaCost m ≤
      6 * ENNReal.ofReal (Real.exp (-2 * Real.log (m : ℝ) ^ 2)) := by gcongr
  refine hmeasure.trans (hmul.trans ?_)
  have hlog6 : Real.log (6 : ℝ) ≤ Real.log (m : ℝ) ^ 2 := by
    have hsqrt0 : 0 ≤ Real.sqrt (Real.log 6) := Real.sqrt_nonneg _
    have hsquare := mul_self_le_mul_self hsqrt0 hlog
    calc
      Real.log (6 : ℝ) = Real.sqrt (Real.log 6) * Real.sqrt (Real.log 6) :=
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

theorem simpleRandomWalk_positiveBroadStrongSourceProductMajorant_series_ne_top
    (t : DominoTiling) (o : Orientation) (k : ℕ) (hk : 0 < k) :
    ∑' m, simpleRandomWalk
      (positiveBroadStrongSourceProductMajorant t o m k
        (candidateLocalBroadWidth48 m) (concreteExternalThreshold48 m)) ≠ ∞ :=
  measure_series_ne_top_of_eventually_exp_neg_log_sq_bound simpleRandomWalk _
    (by norm_num : (0 : ℝ) < 1)
    (by simpa only [neg_mul, one_mul] using
      (eventually_simpleRandomWalk_positiveBroadStrongSourceProductMajorant_le_exp
        t o k hk))

end

end Erdos1165.HLOZCandidateLocalBroadThetaStrongPositivePayment
