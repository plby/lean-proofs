/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.ExternalProposition44Closed
import ErdosProblems.Erdos1165.HLOZPathEvents
import ErdosProblems.Erdos1165.HLOZSpatialAdapter
import ErdosProblems.Erdos1165.LevelTail
import ErdosProblems.Erdos1165.LowerAssembly
import ErdosProblems.Erdos1165.PrefixConditionalLaw
import ErdosProblems.Erdos1165.ScreeningSpatialBridge
import ErdosProblems.Erdos1165.SpatialInsertionClosedFiber
import ErdosProblems.Erdos1165.TwoPointLogAvoidance

/-!
# Canonical HLOZ upper estimates

This module connects the concrete path events in `HLOZPathEvents` to the
probabilistic estimates used by the upper-bound assembly.  It explicitly
places the late fourth level-`m` creation event in the exceptional family and
pays for it with `LevelTail`.  Spatial-mesh overflow is also summable because,
on a nearest-neighbour trajectory and eventually in the level, overflow
implies lateness.  The converse implication is neither used nor asserted.

The upper-facing transition interface uses countable trace/favorite-data
partitions, never atoms fixing a physical threshold-creation clock.  At mesh
scales above `κ₂`, no gap deficit is charged to Lemma 4.10: those paths remain
in the transition screens, where Proposition 4.7's annular Harnack cost is
paid.  Only the low-scale, on-time gap event enters exceptional summability.
-/

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace Erdos1165
namespace HLOZUpperEstimates

open HLOZPathEvents
open HLOZSpatialAdapter

/-! ## A reusable summability conversion -/

/-- An eventually geometric probability bound gives an `ENNReal`-summable
event family.  This packages the harmless finite prefix explicitly. -/
theorem measure_series_ne_top_of_eventually_exp_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (events : ℕ → Set Ω) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ᶠ m : ℕ in atTop,
      μ (events m) ≤ ENNReal.ofReal (Real.exp (-c * (m : ℝ)))) :
    ∑' m, μ (events m) ≠ ∞ := by
  let f : ℕ → ℝ≥0 := fun m ↦ (μ (events m)).toNNReal
  have hgeom : Summable (fun m : ℕ ↦ Real.exp (-c * (m : ℝ))) := by
    have hratio : ‖Real.exp (-c)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
      linarith
    have h := summable_geometric_of_norm_lt_one hratio
    simpa only [← Real.exp_nat_mul, mul_comm] using h
  have hf : Summable (fun m : ℕ ↦ (f m : ℝ)) := by
    apply Summable.of_norm_bounded_eventually hgeom
    have hbound' : ∀ᶠ m : ℕ in cofinite,
        μ (events m) ≤ ENNReal.ofReal (Real.exp (-c * (m : ℝ))) := by
      simpa only [Nat.cofinite_eq_atTop] using hbound
    filter_upwards [hbound'] with m hm
    have hfinite : μ (events m) ≠ ∞ := measure_ne_top μ _
    have hmReal : (μ (events m)).toReal ≤ Real.exp (-c * (m : ℝ)) := by
      rw [← ENNReal.toReal_ofReal (Real.exp_nonneg _)]
      exact ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hm
    simpa [f, ENNReal.toReal, Real.norm_eq_abs, abs_of_nonneg] using hmReal
  have hcoe : ∀ m, (f m : ℝ≥0∞) = μ (events m) := by
    intro m
    exact ENNReal.coe_toNNReal (measure_ne_top μ _)
  rw [← tsum_congr hcoe]
  exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hf

/-- The stretched logarithmic tail occurring in HLOZ Lemma 4.10 is
summable.  The proof compares it eventually with the `p = 2` series. -/
theorem measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (events : ℕ → Set Ω) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ᶠ m : ℕ in atTop,
      μ (events m) ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2))) :
    ∑' m, μ (events m) ≠ ∞ := by
  let f : ℕ → ℝ≥0 := fun m ↦ (μ (events m)).toNNReal
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpoly : Summable (fun m : ℕ ↦ (m : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hf : Summable (fun m : ℕ ↦ (f m : ℝ)) := by
    apply Summable.of_norm_bounded_eventually hpoly
    have hbound' : ∀ᶠ m : ℕ in cofinite,
        μ (events m) ≤
          ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
      simpa only [Nat.cofinite_eq_atTop] using hbound
    have hlarge : ∀ᶠ m : ℕ in cofinite, 2 / c ≤ Real.log (m : ℝ) := by
      simpa only [Nat.cofinite_eq_atTop] using
        hlog.eventually (eventually_ge_atTop (2 / c))
    have hmpos : ∀ᶠ m : ℕ in cofinite, 0 < m := by
      simpa only [Nat.cofinite_eq_atTop] using (eventually_gt_atTop 0)
    filter_upwards [hbound', hlarge, hmpos] with m hm hlogm hmpos
    have hmReal : (μ (events m)).toReal ≤
        Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
      rw [← ENNReal.toReal_ofReal (Real.exp_nonneg _)]
      exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    have hlogNonneg : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hmpos)
    have hexponent : -c * Real.log (m : ℝ) ^ 2 ≤
        Real.log (m : ℝ) * (-2) := by
      have hcMul : 2 ≤ c * Real.log (m : ℝ) := by
        calc
          2 = c * (2 / c) := by field_simp
          _ ≤ c * Real.log (m : ℝ) :=
            mul_le_mul_of_nonneg_left hlogm hc.le
      nlinarith
    have hexp : Real.exp (-c * Real.log (m : ℝ) ^ 2) ≤
        (m : ℝ) ^ (-2 : ℝ) := by
      rw [Real.rpow_def_of_pos (by exact_mod_cast hmpos)]
      exact Real.exp_le_exp.mpr hexponent
    simpa [f, ENNReal.toReal, Real.norm_eq_abs, abs_of_nonneg] using
      hmReal.trans hexp
  have hcoe : ∀ m, (f m : ℝ≥0∞) = μ (events m) := by
    intro m
    exact ENNReal.coe_toNNReal (measure_ne_top μ _)
  rw [← tsum_congr hcoe]
  exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hf

/-! ## Nearest-neighbour geometry of the overflow band -/

lemma latticeDistance_le_manhattanNorm (x y : Point) :
    latticeDistance x y ≤ (PotentialKernel.manhattanNorm (x - y) : ℝ) := by
  let a : ℝ := ((x.1 - y.1 : ℤ) : ℝ)
  let b : ℝ := ((x.2 - y.2 : ℤ) : ℝ)
  have ha : (((x.1 - y.1 : ℤ).natAbs : ℕ) : ℝ) = |a| := by
    simpa [a] using Int.natCast_natAbs (R := ℝ) (x.1 - y.1)
  have hb : (((x.2 - y.2 : ℤ).natAbs : ℕ) : ℝ) = |b| := by
    simpa [b] using Int.natCast_natAbs (R := ℝ) (x.2 - y.2)
  rw [latticeDistance, PotentialKernel.manhattanNorm]
  change Real.sqrt (a ^ 2 + b ^ 2) ≤
    (((x.1 - y.1 : ℤ).natAbs + (x.2 - y.2 : ℤ).natAbs : ℕ) : ℝ)
  rw [Nat.cast_add, ha, hb, Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b]

lemma latticeDistance_trajectory_le_timeDifference
    (ω : StepPath) {n₁ n₂ : ℕ} (h₁₂ : n₁ ≤ n₂) :
    latticeDistance (trajectory ω n₁) (trajectory ω n₂) ≤ (n₂ - n₁ : ℝ) := by
  let u : Fin (n₂ - n₁) → Direction := stepPrefix (n₂ - n₁) (shiftSteps n₁ ω)
  have hdisp : trajectory ω n₂ - trajectory ω n₁ =
      blockDisplacement u := by
    have hadd : n₁ + (n₂ - n₁) = n₂ := Nat.add_sub_of_le h₁₂
    calc
      trajectory ω n₂ - trajectory ω n₁ =
          trajectory ω (n₁ + (n₂ - n₁)) - trajectory ω n₁ := by rw [hadd]
      _ = trajectory (shiftSteps n₁ ω) (n₂ - n₁) :=
        trajectory_add_sub_trajectory ω n₁ (n₂ - n₁)
      _ = blockDisplacement u := by
        simpa [u, blockDisplacement, markovBlockDisplacement] using
          trajectory_eq_markovBlockDisplacement_stepPrefix
            (shiftSteps n₁ ω) (n₂ - n₁)
  have hmanhattan :
      PotentialKernel.manhattanNorm (trajectory ω n₂ - trajectory ω n₁) ≤ n₂ - n₁ := by
    rw [hdisp]
    exact PotentialKernel.manhattanNorm_blockDisplacement_le u
  have hsymm : latticeDistance (trajectory ω n₁) (trajectory ω n₂) =
      latticeDistance (trajectory ω n₂) (trajectory ω n₁) := by
    unfold latticeDistance
    congr 1
    push_cast
    ring
  rw [hsymm]
  exact (latticeDistance_le_manhattanNorm _ _).trans (by exact_mod_cast hmanhattan)

/-! ## The late clock and spatial-mesh overflow -/

lemma upperTailCutoffLog_eq {m : ℕ} (hm : 0 < m) :
    levelCutoffLog upperTailDelta m =
      Real.pi ^ (1 / 2 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ) +
        Real.pi ^ (21 / 16 : ℝ) * (m : ℝ) ^ (5 / 16 : ℝ) := by
  rw [levelCutoffLog_eq_hloz upperTailDelta hm]
  congr 1 <;> norm_num [upperTailDelta]

lemma eventually_const_mul_nat_rpow_le_half_linear (C a : ℝ) (ha : a < 1) :
    ∀ᶠ m : ℕ in atTop, C * (m : ℝ) ^ a ≤ (m : ℝ) / 2 := by
  have ht : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ (1 - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr ha)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (2 * C)),
      eventually_ge_atTop 1] with m hmPow hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hhalf : C ≤ (m : ℝ) ^ (1 - a) / 2 := by linarith
  calc
    C * (m : ℝ) ^ a ≤ ((m : ℝ) ^ (1 - a) / 2) * (m : ℝ) ^ a := by
      exact mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hmR.le _)
    _ = (m : ℝ) / 2 := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hmR]
      norm_num

lemma eventually_levelCutoff_le_exp_level :
    ∀ᶠ m : ℕ in atTop, levelCutoff upperTailDelta m ≤ Real.exp m := by
  have hlead := eventually_const_mul_nat_rpow_le_half_linear
    (Real.pi ^ (1 / 2 : ℝ)) (1 / 2 : ℝ) (by norm_num)
  have hcorr := eventually_const_mul_nat_rpow_le_half_linear
    (Real.pi ^ (21 / 16 : ℝ)) (5 / 16 : ℝ) (by norm_num)
  filter_upwards [hlead, hcorr, eventually_gt_atTop 0] with m hleadM hcorrM hm
  rw [levelCutoff, upperTailCutoffLog_eq hm]
  apply Real.exp_le_exp.mpr
  linarith

lemma thresholdTime_eq_creationTime {s : WalkPath} {m k n : ℕ}
    (h : ThresholdCreation s m k n) : thresholdTime s m k = n := by
  let hreach : ReachesThreshold s m k := ⟨n, h.1⟩
  have hfind_le : Nat.find hreach ≤ n := Nat.find_min' hreach h.1
  have hn_le : n ≤ Nat.find hreach := by
    by_contra hnot
    have hlt : Nat.find hreach < n := Nat.lt_of_not_ge hnot
    have hprior := h.2 (Nat.find hreach) hlt
    exact (Nat.not_lt_of_ge (Nat.find_spec hreach)) hprior
  rw [thresholdTime_eq_coe s m k hreach]
  exact_mod_cast Nat.le_antisymm hfind_le hn_le

/-- On the support of the canonical nearest-neighbour walk, an overflow gap
forces the fourth level-`m` creation past the deterministic level cutoff. -/
theorem trajectory_preimage_meshOverflow_subset_lateLevelSet
    (t : DominoTiling) (m : ℕ)
    (hcutoff : levelCutoff upperTailDelta m ≤ Real.exp m) :
    trajectory ⁻¹' meshOverflowEvent t m ⊆
      trajectory ⁻¹' lateLevelSet upperTailDelta m 4 := by
  intro ω hω
  change trajectory ω ∈ meshOverflowEvent t m at hω
  obtain ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep, hoverflow⟩ := hω
  have h₁₂ : n₁ < n₂ := creation_time_lt (by omega) (by omega) (by omega) h₁ h₂
  have h₂₃ : n₂ < n₃ := creation_time_lt (by omega) (by omega) (by omega) h₂ h₃
  have h₃₄ : n₃ < n₄ := creation_time_lt (by omega) (by omega) (by omega) h₃ h₄
  have hlateReal : Real.exp m < (n₄ : ℝ) := by
    rcases hoverflow with hoverflow | hoverflow | hoverflow
    · have hgap := distance_gt_exp_of_gapScaleOf_eq_overflow hoverflow
      have htime := latticeDistance_trajectory_le_timeDifference ω h₁₂.le
      have hdiff : Real.exp m < (n₂ - n₁ : ℝ) := hgap.trans_le htime
      have hdiffLe : (n₂ - n₁ : ℝ) ≤ (n₄ : ℝ) := by
        have hn₂ : (n₂ : ℝ) ≤ n₄ := by
          exact_mod_cast Nat.le_of_lt (h₂₃.trans h₃₄)
        have hn₁ : (0 : ℝ) ≤ n₁ := Nat.cast_nonneg n₁
        linarith
      exact hdiff.trans_le hdiffLe
    · have hgap := distance_gt_exp_of_gapScaleOf_eq_overflow hoverflow
      have htime := latticeDistance_trajectory_le_timeDifference ω h₂₃.le
      have hdiff : Real.exp m < (n₃ - n₂ : ℝ) := hgap.trans_le htime
      have hdiffLe : (n₃ - n₂ : ℝ) ≤ (n₄ : ℝ) := by
        have hn₃ : (n₃ : ℝ) ≤ n₄ := by exact_mod_cast Nat.le_of_lt h₃₄
        have hn₂ : (0 : ℝ) ≤ n₂ := Nat.cast_nonneg n₂
        linarith
      exact hdiff.trans_le hdiffLe
    · have hgap := distance_gt_exp_of_gapScaleOf_eq_overflow hoverflow
      have htime := latticeDistance_trajectory_le_timeDifference ω h₃₄.le
      have hdiff : Real.exp m < (n₄ - n₃ : ℝ) := hgap.trans_le htime
      have hn₃ : (0 : ℝ) ≤ n₃ := Nat.cast_nonneg n₃
      exact hdiff.trans_le (by linarith)
  have hfloorReal : (⌊levelCutoff upperTailDelta m⌋₊ : ℝ) ≤ Real.exp m := by
    exact (Nat.floor_le (Real.exp_nonneg _)).trans hcutoff
  have hfloorNat : ⌊levelCutoff upperTailDelta m⌋₊ < n₄ := by
    exact_mod_cast hfloorReal.trans_lt hlateReal
  have hcount : thresholdCount (trajectory ω) n₄ m = 4 :=
    thresholdCount_eq_of_creation (by omega) h₄
  have hfavorite : levelFavorite (trajectory ω) m 4 :=
    (levelFavorite_iff_thresholdCounts (trajectory ω) m 4 (by omega)).mpr
      ⟨n₄, hcount, hnext⟩
  change (⌊levelCutoff upperTailDelta m⌋₊ : WithTop ℕ) <
      thresholdTime (trajectory ω) m 4 ∧ levelFavorite (trajectory ω) m 4
  rw [thresholdTime_eq_creationTime h₄]
  exact ⟨by exact_mod_cast hfloorNat, hfavorite⟩

theorem simpleRandomWalk_meshOverflow_le_lateLevelSet
    (t : DominoTiling) (m : ℕ)
    (hcutoff : levelCutoff upperTailDelta m ≤ Real.exp m) :
    simpleRandomWalk (meshOverflowEvent t m) ≤
      simpleRandomWalk (lateLevelSet upperTailDelta m 4) := by
  rw [simpleRandomWalk,
    Measure.map_apply measurable_trajectory
      (measurableSet_meshOverflowEvent t m),
    Measure.map_apply measurable_trajectory
      (LowerAssembly.measurableSet_lateLevelSet upperTailDelta m 4 (by omega))]
  exact measure_mono
    (trajectory_preimage_meshOverflow_subset_lateLevelSet t m hcutoff)

/-- Proposition 1.3, through `LevelTail`, makes the explicit late-clock
exceptional family summable. -/
theorem simpleRandomWalk_lateLevel_series_ne_top
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk) :
    ∑' m, simpleRandomWalk (lateLevelSet upperTailDelta m 4) ≠ ∞ := by
  obtain ⟨c, hc, hlate⟩ :=
    levelTime_tail_of_lowerDeviation simpleRandomWalk hProp13
      upperTailDelta upperTailDelta_pos
  apply measure_series_ne_top_of_eventually_exp_bound simpleRandomWalk
    (fun m ↦ lateLevelSet upperTailDelta m 4) hc
  filter_upwards [hlate] with m hm
  exact (hm 4 (by omega)).le

/-- Proposition 1.3, through `LevelTail`, makes every fixed-tiling mesh
overflow family summable.  No gap-screening or transition estimate is used. -/
theorem simpleRandomWalk_meshOverflow_series_ne_top
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (t : DominoTiling) :
    ∑' m, simpleRandomWalk (meshOverflowEvent t m) ≠ ∞ := by
  obtain ⟨c, hc, hlate⟩ :=
    levelTime_tail_of_lowerDeviation simpleRandomWalk hProp13
      upperTailDelta upperTailDelta_pos
  apply measure_series_ne_top_of_eventually_exp_bound simpleRandomWalk
    (meshOverflowEvent t) hc
  filter_upwards [eventually_levelCutoff_le_exp_level, hlate] with m hcut htail
  exact (simpleRandomWalk_meshOverflow_le_lateLevelSet t m hcut).trans
    (htail 4 (by omega)).le

/-! ## The exact remaining conditional Harnack interface

`HLOZSpatialAdapter` supplies the conditional-to-unconditional conversion for
all three concrete path events.  Its three `StoppedPastSpatialDisintegration`
predicates are strictly stronger than the final measure inequalities and are
the exact cap-removal/stopped-prefix Harnack seam left after the checked finite
prefix and closed-fibre laws. -/

/-- The concrete one-transition envelope is finite.  Writing this explicitly
avoids asking typeclass search to unfold the whole numerical screen. -/
lemma hlozTransitionCost_ne_top (K : ℝ≥0) (m : ℕ) :
    UpperCanonical.hlozTransitionCost K m ≠ ∞ := by
  rw [UpperCanonical.hlozTransitionCost, UpperAssembly.pSeriesWeight]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top

/-- The three atomwise stopped-past inputs imply exactly the three
walk-specific transition inequalities consumed by `HLOZPathEvents`. -/
theorem simpleRandomWalk_transition_estimates_of_stoppedPastAtoms
    (K : ℝ≥0)
    (hfirst : HLOZSpatialAdapter.FirstStoppedPastSpatialDisintegration K)
    (hsecond : HLOZSpatialAdapter.SecondStoppedPastSpatialDisintegration K)
    (hthird : HLOZSpatialAdapter.ThirdStoppedPastSpatialDisintegration K) :
    (∀ t m a, simpleRandomWalk (firstTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m) ∧
    (∀ t m a, simpleRandomWalk (secondTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (firstTransitionEvent t m a)) ∧
    (∀ t m a, simpleRandomWalk (screenedThirdTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (secondTransitionEvent t m a)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t m a
    apply firstTransition_measure_le
    exact pathTransitionDomination_of_atomwiseRestrictedRealScreen
      (HLOZSpatialAdapter.firstCreationAtom m)
      (measurableSet_firstTransitionEvent t m a)
      (hlozTransitionCost_ne_top K m) (hfirst t m a)
  · intro t m a
    apply secondTransition_measure_le
    exact pathTransitionDomination_of_atomwiseRestrictedRealScreen
      (pairCreationAtom t m a) (measurableSet_secondTransitionEvent t m a)
      (hlozTransitionCost_ne_top K m) (hsecond t m a)
  · intro t m a
    apply screenedThirdTransition_measure_le
    exact pathTransitionDomination_of_atomwiseRestrictedRealScreen
      (tripleCreationAtom t m a)
      (measurableSet_screenedThirdTransitionEvent t m a)
      (hlozTransitionCost_ne_top K m) (hthird t m a)

/-! ## Exceptional summability -/

/-- The sole remaining gap input, in the exact asymptotic form needed after
the checked finite candidate union and logarithmic two-point escape estimate.
It is intentionally separated from mesh overflow, which was proved above. -/
def HasGapDeficitReturnHarnack (c : ℝ) : Prop :=
  ∀ t : DominoTiling, ∀ᶠ m : ℕ in atTop,
    simpleRandomWalk (onTimeLowGapDeficitExceptionalEvent t m) ≤
      ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2))

/-- The explicit two-point escape chance at the same deterministic horizon
used for the level-tail truncation. -/
noncomputable def canonicalGapEscapeChance (m : ℕ) : ℝ :=
  1 / (100 * Real.log (levelCutoffTime upperTailDelta m))

/-- The canonical walk has at least the displayed escape chance uniformly in
the second forbidden point.  This is the exact checked input used when the
stopped one-candidate return event is iterated geometrically. -/
theorem canonicalGapEscapeChance_le_twoPointAvoidance
    (x : Point) {m : ℕ} (hm : 2 ≤ levelCutoffTime upperTailDelta m) :
    ENNReal.ofReal (canonicalGapEscapeChance m) ≤
      simpleRandomWalk
        (TwoPointAvoidance.walkAvoidsTwoPointsThrough x
          (levelCutoffTime upperTailDelta m)) := by
  exact TwoPointLogAvoidance.simpleRandomWalk_walkAvoidsTwoPointsThrough_lower_log
    x hm

/-- The external candidate-count screen needed before the finite gap union.
`ExternalProposition44Closed` now supplies the sharp one-point input and the
complete Proposition 4.4 argument unconditionally for either orientation. -/
theorem eventually_externalCandidateOverflow_lt_failureRate
    (o : LazyDecomposition.Orientation) :
    ∀ᶠ m : ℕ in atTop,
      ExternalWalk.externalBlocks o {η |
          ExternalProposition44.hlozSiteBudget44 m <
            ExternalProposition44.externalThickCount o η
              (ExternalProposition44.hlozCutoff44 m)
              (ExternalProposition44.hlozThickLevel44 m)} <
        ExternalProposition44.hlozFailureRate44 m :=
  ExternalProposition44Closed.eventually_hloz_externalThickCount_failure44 o

/-- The finite `Gap` engine with a target enlarged by the logarithm of the
number of bands.  Candidate counting and event coverage are deterministic;
`hreturn` is the sole stopped-walk input.  The logarithmic two-point theorem
above supplies the escape probability used to establish `hreturn`. -/
theorem hasGapDeficitReturnHarnack_of_geometric_screen
    {Band Candidate : Type*} (c : ℝ)
    (bands : DominoTiling → ℕ → Finset Band)
    (candidates : DominoTiling → ℕ → Band → Finset Candidate)
    (succeeds : DominoTiling → ℕ → Band → Candidate → Set WalkPath)
    (budget : DominoTiling → ℕ → Band → ℕ)
    (escapeChance : DominoTiling → ℕ → Band → ℝ)
    (requiredReturns : DominoTiling → ℕ → Band → ℕ)
    (hcover : ∀ t m,
      Gap.GapEventCovered (onTimeLowGapDeficitExceptionalEvent t m)
      (bands t m) (candidates t m) (succeeds t m))
    (hcount : ∀ t m,
      Gap.CandidateCountBound (bands t m) (candidates t m) (budget t m))
    (hreturn : ∀ t m,
      Gap.PerCandidateGeometricReturnBound simpleRandomWalk
        (bands t m) (candidates t m) (succeeds t m)
        (escapeChance t m) (requiredReturns t m))
    (hzero : ∀ t m band, band ∈ bands t m → 0 ≤ escapeChance t m band)
    (hone : ∀ t m band, band ∈ bands t m → escapeChance t m band ≤ 1)
    (hdominates : ∀ t m band, band ∈ bands t m → 0 < budget t m band →
      Real.log (budget t m band) +
          (Real.log (bands t m).card +
            c * Real.log (m : ℝ) ^ 2) ≤
        escapeChance t m band * requiredReturns t m band) :
    HasGapDeficitReturnHarnack c := by
  intro t
  filter_upwards [] with m
  let target : ℝ := Real.log (bands t m).card +
    c * Real.log (m : ℝ) ^ 2
  have hraw := Gap.measure_gapEvent_le_card_bands_mul_exp_neg
    simpleRandomWalk (onTimeLowGapDeficitExceptionalEvent t m)
    (bands t m) (candidates t m) (succeeds t m) (budget t m)
    (escapeChance t m) (requiredReturns t m) target
    (hcover t m) (hcount t m) (hreturn t m) (hzero t m) (hone t m)
    (fun band hband hbudget ↦ by
      simpa only [target] using hdominates t m band hband hbudget)
  by_cases hcard : (bands t m).card = 0
  · exact hraw.trans (by simp [hcard])
  · have hcardPos : 0 < (bands t m).card := Nat.pos_of_ne_zero hcard
    refine hraw.trans ?_
    simpa only [neg_mul] using
      (Gap.ennreal_nat_mul_exp_neg_le_exp_neg hcardPos
        (exponent := target) (target := c * Real.log (m : ℝ) ^ 2)
          (by simp [target]))

theorem simpleRandomWalk_onTimeLowGapDeficitExceptional_series_ne_top
    {c : ℝ} (hc : 0 < c) (hgap : HasGapDeficitReturnHarnack c)
    (t : DominoTiling) :
    ∑' m, simpleRandomWalk (onTimeLowGapDeficitExceptionalEvent t m) ≠ ∞ := by
  exact measure_series_ne_top_of_eventually_exp_neg_log_sq_bound simpleRandomWalk
    (onTimeLowGapDeficitExceptionalEvent t) hc (hgap t)

theorem simpleRandomWalk_hlozExceptional_series_ne_top
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    {c : ℝ} (hc : 0 < c) (hgap : HasGapDeficitReturnHarnack c)
    (t : DominoTiling) :
    ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞ := by
  have hlate := simpleRandomWalk_lateLevel_series_ne_top hProp13
  have hoverflow := simpleRandomWalk_meshOverflow_series_ne_top hProp13 t
  have hdeficit :=
    simpleRandomWalk_onTimeLowGapDeficitExceptional_series_ne_top hc hgap t
  have hmajor : ∑' m,
      ((simpleRandomWalk (lateLevelSet upperTailDelta m 4) +
        simpleRandomWalk (meshOverflowEvent t m)) +
        simpleRandomWalk (onTimeLowGapDeficitExceptionalEvent t m)) ≠ ∞ := by
    rw [ENNReal.tsum_add, ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hlate, hoverflow⟩, hdeficit⟩
  apply ne_top_of_le_ne_top hmajor
  apply ENNReal.tsum_le_tsum
  intro m
  calc
    simpleRandomWalk (hlozExceptionalEvent t m) ≤
        simpleRandomWalk
            (lateLevelSet upperTailDelta m 4 ∪ meshOverflowEvent t m) +
          simpleRandomWalk (onTimeLowGapDeficitExceptionalEvent t m) := by
      exact measure_union_le _ _
    _ ≤ (simpleRandomWalk (lateLevelSet upperTailDelta m 4) +
          simpleRandomWalk (meshOverflowEvent t m)) +
        simpleRandomWalk (onTimeLowGapDeficitExceptionalEvent t m) := by
      gcongr
      exact measure_union_le _ _

end HLOZUpperEstimates
end Erdos1165
