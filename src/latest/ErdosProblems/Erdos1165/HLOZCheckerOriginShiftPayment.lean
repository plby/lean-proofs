/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZFixedPointLocalTimeTail
import ErdosProblems.Erdos1165.HLOZThetaOneSourceShift
import ErdosProblems.Erdos1165.HLOZUpperEstimates

/-!
# Paying the genuine checker one-step-shift obstruction

Deleting the time-zero visit can change a level creation clock only when the
origin has already reached that level.  On an on-time creation this is a
fixed-site local-time event at the deterministic HLOZ cutoff; otherwise the
creation belongs to the ordinary late-level event.  The former is paid by
the stopped return ladder with `m - 1` returns, and the latter by Proposition
1.3's existing lower-deviation consequence.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZCheckerOriginShiftPayment

open HLOZFixedPointLocalTimeTail HLOZGapReturn HLOZPathEvents
open HLOZThetaOneSourceShift HLOZUpperEstimates
open HLOZThetaSourceBalance VariableStoppedTracePartition

noncomputable section

/-- The deterministic-cutoff fixed-origin obstruction. -/
def cutoffOriginLocalTimeEvent (m : ℕ) : Set WalkPath :=
  originLocalTimeEvent (levelCutoffTime upperTailDelta m) m

theorem measurableSet_cutoffOriginLocalTimeEvent (m : ℕ) :
    MeasurableSet (cutoffOriginLocalTimeEvent m) :=
  measurableSet_originLocalTimeEvent _ _

/-- The logarithm of the enlarged return deadline is still at most a fixed
multiple of `sqrt m`. -/
theorem eventually_log_originDeadline_le_four_sqrt :
    ∀ᶠ m : ℕ in atTop,
      Real.log (((levelCutoffTime upperTailDelta m + 1 : ℕ) : ℝ)) ≤
        4 * Real.sqrt (m : ℝ) := by
  have hlog := LowerAssembly.eventually_log_levelCutoffTime_le_three_sqrt
    upperTailDelta (by norm_num [upperTailDelta])
  have hcutoff : ∀ᶠ m : ℕ in atTop, 1 ≤ levelCutoffTime upperTailDelta m :=
    (tendsto_levelCutoffTime upperTailDelta).eventually
      (eventually_ge_atTop 1)
  have hm : ∀ᶠ m : ℕ in atTop, 1 ≤ m := eventually_ge_atTop 1
  filter_upwards [hlog, hcutoff, hm] with m hlogM hcutoffM hmM
  let C := levelCutoffTime upperTailDelta m
  have hCpos : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hcast : ((C + 1 : ℕ) : ℝ) ≤ 2 * (C : ℝ) := by
    push_cast
    have hCge : (1 : ℝ) ≤ C := by exact_mod_cast hcutoffM
    linarith
  have hlogMono : Real.log (((C + 1 : ℕ) : ℝ)) ≤
      Real.log (2 * (C : ℝ)) := Real.log_le_log (by positivity) hcast
  have hsqrt : 1 ≤ Real.sqrt (m : ℝ) := by
    have hmNonneg : (0 : ℝ) ≤ m := by positivity
    have hsqrtSq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) :=
      Real.sq_sqrt hmNonneg
    have hsqrtNonneg := Real.sqrt_nonneg (m : ℝ)
    have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hmM
    nlinarith
  calc
    Real.log (((C + 1 : ℕ) : ℝ)) ≤ Real.log (2 * (C : ℝ)) := hlogMono
    _ = Real.log 2 + Real.log (C : ℝ) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hCpos.ne']
    _ ≤ 1 + 3 * Real.sqrt (m : ℝ) := by
      have hlogTwo : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
      dsimp only [C]
      linarith
    _ ≤ 4 * Real.sqrt (m : ℝ) := by linarith

/-- A logarithmic square is eventually smaller than `sqrt m`; this is the
only asymptotic arithmetic needed for the fixed-origin payment. -/
theorem eventually_log_sq_le_sqrt :
    ∀ᶠ m : ℕ in atTop,
      Real.log (m : ℝ) ^ 2 ≤ Real.sqrt (m : ℝ) := by
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 by norm_num)
  have hsmall := tendsto_natCast_atTop_atTop.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with m hsmallM hm
  have hlog0 : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hm)
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 (2 : ℝ)),
    Real.norm_of_nonneg (Real.rpow_nonneg hm0 (1 / 2 : ℝ))] at hsmallM
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow, one_mul] using hsmallM

/-- The direct time-zero ladder gives a summable stretched-logarithmic bound
for the sole checker-shift obstruction. -/
theorem eventually_simpleRandomWalk_cutoffOriginLocalTimeEvent_le_exp :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (cutoffOriginLocalTimeEvent m) ≤
        ENNReal.ofReal
          (Real.exp (-(1 / 2000 : ℝ) * Real.log (m : ℝ) ^ 2)) := by
  have hdeadline := eventually_log_originDeadline_le_four_sqrt
  have hlogSq := eventually_log_sq_le_sqrt
  have hcutoff : ∀ᶠ m : ℕ in atTop, 1 ≤ levelCutoffTime upperTailDelta m :=
    (tendsto_levelCutoffTime upperTailDelta).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hdeadline, hlogSq, hcutoff,
    eventually_ge_atTop (4 : ℕ)] with m hdeadlineM hlogSqM hcutoffM hm
  let deadline := levelCutoffTime upperTailDelta m + 1
  let escape : ℝ := 1 / (100 * Real.log (deadline : ℝ))
  have hmpos : (0 : ℝ) < m := by positivity
  have hsqrt : 0 < Real.sqrt (m : ℝ) := by positivity
  have hdeadlineNat : 2 ≤ deadline := by dsimp only [deadline]; omega
  have hlogPos : 0 < Real.log (deadline : ℝ) :=
    Real.log_pos (by exact_mod_cast hdeadlineNat)
  have hescapePos : 0 < escape := by
    dsimp only [escape]
    positivity
  have hescapeOne : escape ≤ 1 := by
    dsimp only [escape]
    have hlogTwo : Real.log 2 ≥ 1 / 2 := Real.log_two_gt_d9.le.trans' (by norm_num)
    have hlogLower : 1 / 2 ≤ Real.log (deadline : ℝ) :=
      hlogTwo.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hdeadlineNat))
    apply (div_le_one (by positivity : 0 < 100 * Real.log (deadline : ℝ))).2
    nlinarith
  have hescapeLower : 1 / (400 * Real.sqrt (m : ℝ)) ≤ escape := by
    dsimp only [escape, deadline] at hdeadlineM ⊢
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hreturns : (m : ℝ) / 2 ≤ ((m - 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast (show m ≤ (m - 1) * 2 by omega)
  have hproduct : (1 / 800 : ℝ) * Real.sqrt (m : ℝ) ≤
      escape * ((m - 1 : ℕ) : ℝ) := by
    have hmul := mul_le_mul hescapeLower hreturns (by positivity) hescapePos.le
    have hsqrtSq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) :=
      Real.mul_self_sqrt hmpos.le
    calc
      (1 / 800 : ℝ) * Real.sqrt (m : ℝ) =
          (1 / (400 * Real.sqrt (m : ℝ))) * ((m : ℝ) / 2) := by
        field_simp
        nlinarith
      _ ≤ escape * ((m - 1 : ℕ) : ℝ) := hmul
  have hdominates : (1 / 2000 : ℝ) * Real.log (m : ℝ) ^ 2 ≤
      escape * ((m - 1 : ℕ) : ℝ) := by
    calc
      (1 / 2000 : ℝ) * Real.log (m : ℝ) ^ 2 ≤
          (1 / 2000 : ℝ) * Real.sqrt (m : ℝ) := by gcongr
      _ ≤ (1 / 800 : ℝ) * Real.sqrt (m : ℝ) := by
        gcongr
        norm_num
      _ ≤ _ := hproduct
  calc
    simpleRandomWalk (cutoffOriginLocalTimeEvent m) ≤
        Gap.geometricReturnCost escape (m - 1) := by
      exact simpleRandomWalk_originLocalTimeEvent_le hcutoffM (by omega)
    _ ≤ Gap.exponentialReturnCost escape (m - 1) :=
      Gap.geometricReturnCost_le_exponentialReturnCost hescapePos.le
        hescapeOne _
    _ ≤ ENNReal.ofReal
        (Real.exp (-(1 / 2000 : ℝ) * Real.log (m : ℝ) ^ 2)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith

theorem simpleRandomWalk_cutoffOriginLocalTimeEvent_series_ne_top :
    ∑' m, simpleRandomWalk (cutoffOriginLocalTimeEvent m) ≠ ∞ :=
  measure_series_ne_top_of_eventually_exp_neg_log_sq_bound simpleRandomWalk
    cutoffOriginLocalTimeEvent (by norm_num : (0 : ℝ) < 1 / 2000)
    eventually_simpleRandomWalk_cutoffOriginLocalTimeEvent_le_exp

/-! ## Routing the creation-clock obstruction -/

/-- At a fixed old-favorite rank, the checker shift is paid either by the
ordinary late-level event or by the deterministic-cutoff fixed-origin tail. -/
def checkerOriginShiftPaidEvent (rank m : ℕ) : Set WalkPath :=
  lateLevelSet upperTailDelta m rank ∪ cutoffOriginLocalTimeEvent m

theorem measurableSet_checkerOriginShiftPaidEvent
    (rank m : ℕ) (hrank : 0 < rank) :
    MeasurableSet (checkerOriginShiftPaidEvent rank m) :=
  (LowerAssembly.measurableSet_lateLevelSet upperTailDelta m rank hrank).union
    (measurableSet_cutoffOriginLocalTimeEvent m)

/-- A genuine creation profile turns the random-clock origin obstruction
into the paid late-or-fixed-cutoff event. -/
theorem checkerOriginShiftException_mem_paid_of_creation
    (omega : StepPath) (d : Tilings.CheckerDirection)
    {m rank w N : ℕ} (hrank : 0 < rank)
    (hcreation : ThresholdCreation (trajectory omega) m rank N)
    (hnext : thresholdCount (trajectory omega) N (m + 1) = 0)
    (horigin : trajectory omega ∈
      checkerOriginShiftExceptionEvent d m rank w) :
    trajectory omega ∈ checkerOriginShiftPaidEvent rank m := by
  have hclock : creationTimeNat m rank (trajectory omega) = N :=
    creationTimeNat_eq_of_creation hcreation
  have horiginN : m ≤ localTime (trajectory omega) N 0 := by
    change m ≤ localTime (trajectory omega)
      (creationTimeNat m rank (trajectory omega)) 0 at horigin
    simpa only [hclock] using horigin
  by_cases htime : N ≤ levelCutoffTime upperTailDelta m
  · exact Or.inr (horiginN.trans
      (localTime_mono_time (trajectory omega) 0 htime))
  · apply Or.inl
    have hcount : thresholdCount (trajectory omega) N m = rank :=
      thresholdCount_eq_of_creation hrank hcreation
    have hfavorite : levelFavorite (trajectory omega) m rank :=
      (levelFavorite_iff_thresholdCounts (trajectory omega) m rank hrank).2
        ⟨N, hcount, hnext⟩
    refine ⟨?_, hfavorite⟩
    rw [thresholdTime_eq_creationTime hcreation]
    have hfloorCeil : ⌊levelCutoff upperTailDelta m⌋₊ ≤
        ⌈levelCutoff upperTailDelta m⌉₊ := Nat.floor_le_ceil _
    have hceilN : levelCutoffTime upperTailDelta m < N :=
      Nat.lt_of_not_ge htime
    unfold levelCutoffTime at hceilN
    exact_mod_cast hfloorCeil.trans_lt hceilN

theorem simpleRandomWalk_lateLevelAtRank_series_ne_top
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (rank : ℕ) (hrank : 0 < rank) :
    ∑' m, simpleRandomWalk (lateLevelSet upperTailDelta m rank) ≠ ∞ := by
  obtain ⟨c, hc, hlate⟩ :=
    levelTime_tail_of_lowerDeviation simpleRandomWalk hProp13
      upperTailDelta upperTailDelta_pos
  apply measure_series_ne_top_of_eventually_exp_bound simpleRandomWalk
    (fun m ↦ lateLevelSet upperTailDelta m rank) hc
  filter_upwards [hlate] with m hm
  exact (hm rank hrank).le

private theorem measure_union_series_ne_top
    {first second : ℕ → Set WalkPath}
    (hfirst : ∑' m, simpleRandomWalk (first m) ≠ ∞)
    (hsecond : ∑' m, simpleRandomWalk (second m) ≠ ∞) :
    ∑' m, simpleRandomWalk (first m ∪ second m) ≠ ∞ := by
  have hmajor : ∑' m,
      (simpleRandomWalk (first m) + simpleRandomWalk (second m)) ≠ ∞ := by
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr ⟨hfirst, hsecond⟩
  exact ne_top_of_le_ne_top hmajor
    (ENNReal.tsum_le_tsum fun m ↦ measure_union_le _ _)

theorem simpleRandomWalk_checkerOriginShiftPaidEvent_series_ne_top
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (rank : ℕ) (hrank : 0 < rank) :
    ∑' m, simpleRandomWalk (checkerOriginShiftPaidEvent rank m) ≠ ∞ :=
  measure_union_series_ne_top
    (simpleRandomWalk_lateLevelAtRank_series_ne_top hProp13 rank hrank)
    simpleRandomWalk_cutoffOriginLocalTimeEvent_series_ne_top

/-- Rank-one transition route with the origin obstruction paid internally. -/
theorem firstTransition_opposite_cut_mem_shifted_source_or_restrictedTheta_or_paid
    (omega : StepPath) (d : Tilings.CheckerDirection)
    {m w low externalLow externalHigh cut : ℕ}
    (a : (GapScale × GapScale) × GapScale)
    (hm : 2 ≤ m) (hlow : low = m - w)
    (hstage : trajectory omega ∈ firstTransitionEvent (.checker d) m a)
    (hcut : cut <
      (tilingOppositeDominantNearEndpointsAtCreation (.checker d) m 1 w
        (trajectory omega)).card) :
    trajectory omega ∈
      (shiftedCheckerSourceEvent d m 1 w low externalLow externalHigh cut ∪
        shiftedCheckerRestrictedThetaFailureEvent d m 1 w low
          externalLow externalHigh) ∪
      checkerOriginShiftPaidEvent 1 m := by
  by_cases horigin : trajectory omega ∈ checkerOriginShiftExceptionEvent d m 1 w
  · apply Or.inr
    simp only [firstTransitionEvent, Set.mem_iUnion] at hstage
    obtain ⟨n₁, n₂, h₁, h₂, hnext, hsep, ha⟩ := hstage
    have htime : n₁ < n₂ := creation_time_lt (by omega) (by omega)
      (by omega) h₁ h₂
    have hmono := thresholdCount_mono_time (trajectory omega) (m + 1) htime.le
    have hnext₁ : thresholdCount (trajectory omega) n₁ (m + 1) = 0 := by
      change thresholdCount (trajectory omega) n₁ (m + 1) ≤
        thresholdCount (trajectory omega) n₂ (m + 1) at hmono
      omega
    exact checkerOriginShiftException_mem_paid_of_creation omega d (by omega)
      h₁ hnext₁ horigin
  · exact Or.inl
      (firstTransition_opposite_cut_mem_shifted_source_or_restrictedTheta
        omega d a hm hlow hstage horigin hcut)

/-- Rank-two transition route with the origin obstruction paid internally. -/
theorem secondTransition_opposite_cut_mem_shifted_source_or_restrictedTheta_or_paid
    (omega : StepPath) (d : Tilings.CheckerDirection)
    {m w low externalLow externalHigh cut : ℕ}
    (a : (GapScale × GapScale) × GapScale)
    (hm : 2 ≤ m) (hlow : low = m - w)
    (hstage : trajectory omega ∈ secondTransitionEvent (.checker d) m a)
    (hcut : cut <
      (tilingOppositeDominantNearEndpointsAtCreation (.checker d) m 2 w
        (trajectory omega)).card) :
    trajectory omega ∈
      (shiftedCheckerSourceEvent d m 2 w low externalLow externalHigh cut ∪
        shiftedCheckerRestrictedThetaFailureEvent d m 2 w low
          externalLow externalHigh) ∪
      checkerOriginShiftPaidEvent 2 m := by
  by_cases horigin : trajectory omega ∈ checkerOriginShiftExceptionEvent d m 2 w
  · apply Or.inr
    simp only [secondTransitionEvent, Set.mem_iUnion] at hstage
    obtain ⟨n₁, n₂, n₃, h₁, h₂, h₃, hnext, h₁₂, h₁₃, h₂₃,
      ha₁, ha₂⟩ := hstage
    have htime : n₂ < n₃ := creation_time_lt (by omega) (by omega)
      (by omega) h₂ h₃
    have hmono := thresholdCount_mono_time (trajectory omega) (m + 1) htime.le
    have hnext₂ : thresholdCount (trajectory omega) n₂ (m + 1) = 0 := by
      change thresholdCount (trajectory omega) n₂ (m + 1) ≤
        thresholdCount (trajectory omega) n₃ (m + 1) at hmono
      omega
    exact checkerOriginShiftException_mem_paid_of_creation omega d (by omega)
      h₂ hnext₂ horigin
  · exact Or.inl
      (secondTransition_opposite_cut_mem_shifted_source_or_restrictedTheta
        omega d a hm hlow hstage horigin hcut)

/-- Rank-three transition route with the origin obstruction paid internally. -/
theorem thirdTransition_opposite_cut_mem_shifted_source_or_restrictedTheta_or_paid
    (omega : StepPath) (d : Tilings.CheckerDirection)
    {m w low externalLow externalHigh cut : ℕ}
    (a : (GapScale × GapScale) × GapScale)
    (hm : 2 ≤ m) (hlow : low = m - w)
    (hstage : trajectory omega ∈ thirdTransitionEvent (.checker d) m a)
    (hcut : cut <
      (tilingOppositeDominantNearEndpointsAtCreation (.checker d) m 3 w
        (trajectory omega)).card) :
    trajectory omega ∈
      (shiftedCheckerSourceEvent d m 3 w low externalLow externalHigh cut ∪
        shiftedCheckerRestrictedThetaFailureEvent d m 3 w low
          externalLow externalHigh) ∪
      checkerOriginShiftPaidEvent 3 m := by
  by_cases horigin : trajectory omega ∈ checkerOriginShiftExceptionEvent d m 3 w
  · apply Or.inr
    simp only [thirdTransitionEvent, Set.mem_iUnion] at hstage
    obtain ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep,
      ha₁, ha₂, ha₃⟩ := hstage
    have htime : n₃ < n₄ := creation_time_lt (by omega) (by omega)
      (by omega) h₃ h₄
    have hmono := thresholdCount_mono_time (trajectory omega) (m + 1) htime.le
    have hnext₃ : thresholdCount (trajectory omega) n₃ (m + 1) = 0 := by
      change thresholdCount (trajectory omega) n₃ (m + 1) ≤
        thresholdCount (trajectory omega) n₄ (m + 1) at hmono
      omega
    exact checkerOriginShiftException_mem_paid_of_creation omega d (by omega)
      h₃ hnext₃ horigin
  · exact Or.inl
      (thirdTransition_opposite_cut_mem_shifted_source_or_restrictedTheta
        omega d a hm hlow hstage horigin hcut)

end

end Erdos1165.HLOZCheckerOriginShiftPayment
