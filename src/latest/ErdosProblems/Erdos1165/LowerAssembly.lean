/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.Lower
import ErdosProblems.Erdos1165.StoppedInsertion
import ErdosProblems.Erdos1165.StrongMarkovWithTop
import ErdosProblems.Erdos1165.LevelTail
import ErdosProblems.Erdos1165.TwoPointLogAvoidance
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Assembly of the HLOZ lower-bound clock argument

This file specializes the abstract conditional Borel--Cantelli theorem in
`Lower.lean` to the canonical planar walk.  It supplies the genuine HLOZ
level clocks on increment space, proves that they are stopping times, builds
the level filtration, and identifies its adapted events with `M_m^k`.

The final theorem below assumes only the two *localized conditional stage
estimates* which constitute HLOZ Lemma 4.1.  In particular it does not assume
the desired infinitely-often conclusion.  The finite-dimensional strong
Markov interface used to prove those estimates is also recorded here.  The
uniform logarithmic two-point avoidance estimate is imported from
`TwoPointLogAvoidance` and combined below with `LevelTail`; the resulting
fresh-walk event has probability at least `1 / (600 * sqrt m)`, with HLOZ
Proposition 1.3 left as the sole analytic hypothesis of that bound.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory Topology

namespace Erdos1165.LowerAssembly

open Lower

/-! ## The level clocks on increment space -/

/-- Pullback of `T_m^k` from canonical walk space to IID increment space. -/
noncomputable def levelTimeSteps (m k : ℕ) (omega : StepPath) : WithTop ℕ :=
  thresholdTime (trajectory omega) m k

theorem levelTimeSteps_le_iff (m k n : ℕ) (omega : StepPath) :
    levelTimeSteps m k omega ≤ n ↔
      k ≤ thresholdCount (trajectory omega) n m := by
  by_cases hreach : ReachesThreshold (trajectory omega) m k
  · rw [levelTimeSteps, thresholdTime_eq_coe _ _ _ hreach]
    norm_cast
    constructor
    · intro hfind
      exact (Nat.find_spec hreach).trans
        (thresholdCount_mono_time (trajectory omega) m hfind)
    · exact Nat.find_min' hreach
  · have hright : ¬k ≤ thresholdCount (trajectory omega) n m := by
      intro h
      exact hreach ⟨n, h⟩
    rw [levelTimeSteps, (thresholdTime_eq_top_iff _ _ _).mpr hreach]
    simp [hright]

/-- Every pulled-back level clock is a stopping time for the natural
increment filtration. -/
theorem isStoppingTime_levelTimeSteps (m k : ℕ) :
    IsStoppingTime incrementFiltration (levelTimeSteps m k) := by
  intro n
  convert StoppedInsertion.measurableSet_thresholdCount_ge n m k using 1
  ext omega
  exact levelTimeSteps_le_iff m k n omega

theorem levelTimeSteps_mono_level (k : ℕ) :
    Monotone fun m ↦ levelTimeSteps m k := by
  intro m q hmq omega
  exact thresholdTime_mono_level (trajectory omega) k hmq

theorem levelTimeSteps_mono_count (m : ℕ) :
    Monotone fun k ↦ levelTimeSteps m k := by
  intro k q hkq omega
  exact thresholdTime_mono_count (trajectory omega) m hkq

/-- The canonical level event on increment space. -/
def levelEventSteps (m k : ℕ) : Set StepPath :=
  {omega | levelTimeSteps m k omega < levelTimeSteps (m + 1) 1 omega}

theorem levelEventSteps_eq_preimage (m k : ℕ) (hk : 0 < k) :
    levelEventSteps m k = trajectory ⁻¹' levelFavoriteSet m k := by
  ext omega
  exact (levelFavorite_iff_thresholdTime_lt (trajectory omega) m k hk).symm

theorem measurableSet_levelEventSteps (m k : ℕ) (hk : 0 < k) :
    MeasurableSet (levelEventSteps m k) := by
  rw [levelEventSteps_eq_preimage m k hk]
  exact (measurableSet_levelFavoriteSet m k hk).preimage measurable_trajectory

/-- `M_m^k` is observable at the right-hand clock `T_(m+1)^1`. -/
theorem measurableSet_levelEventSteps_at_next (m k : ℕ) :
    MeasurableSet[(isStoppingTime_levelTimeSteps (m + 1) 1).measurableSpace]
      (levelEventSteps m k) := by
  exact measurableSet_stoppingTime_lt_right
    (isStoppingTime_levelTimeSteps m k)
    (isStoppingTime_levelTimeSteps (m + 1) 1)

/-- The same clock-ordering event is already known at the left-hand clock.
This is the stopped-sigma-algebra fact used when restarting at `T_m^k`. -/
theorem measurableSet_stoppingTime_lt_left
    {tau pi : StepPath → WithTop ℕ}
    (htau : IsStoppingTime incrementFiltration tau)
    (hpi : IsStoppingTime incrementFiltration pi) :
    MeasurableSet[htau.measurableSpace] {omega | tau omega < pi omega} := by
  have hnot : MeasurableSet[htau.measurableSpace]
      {omega | ¬pi omega ≤ tau omega} :=
    (IsStoppingTime.measurableSet_stopping_time_le hpi htau).compl
  simpa only [not_le] using hnot

theorem measurableSet_levelEventSteps_at_current (m k : ℕ) :
    MeasurableSet[(isStoppingTime_levelTimeSteps m k).measurableSpace]
      (levelEventSteps m k) := by
  unfold levelEventSteps
  exact measurableSet_stoppingTime_lt_left
    (isStoppingTime_levelTimeSteps m k)
    (isStoppingTime_levelTimeSteps (m + 1) 1)

/-- The filtration `G_m = F_(T_(m+1)^1)` used in the conditional
Borel--Cantelli argument. -/
noncomputable def levelFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace StepPath) :=
  filtrationAtIncreasingStoppingTimes incrementFiltration
    (fun m ↦ levelTimeSteps (m + 1) 1)
    (fun m ↦ isStoppingTime_levelTimeSteps (m + 1) 1)
    (by
      intro m q hmq omega
      exact levelTimeSteps_mono_level 1 (Nat.add_le_add_right hmq 1) omega)

theorem levelFiltration_apply (m : ℕ) :
    levelFiltration m =
      (isStoppingTime_levelTimeSteps (m + 1) 1).measurableSpace := rfl

theorem measurableSet_levelEventSteps_levelFiltration (m k : ℕ) :
    MeasurableSet[levelFiltration m] (levelEventSteps m k) := by
  exact measurableSet_levelEventSteps_at_next m k

/-! ## The raw first-level clock and the `LevelTail` estimate -/

theorem thresholdTime_le_iff (s : WalkPath) (m k n : ℕ) :
    thresholdTime s m k ≤ n ↔ k ≤ thresholdCount s n m := by
  by_cases hreach : ReachesThreshold s m k
  · rw [thresholdTime_eq_coe s m k hreach]
    norm_cast
    constructor
    · intro hfind
      exact (Nat.find_spec hreach).trans (thresholdCount_mono_time s m hfind)
    · exact Nat.find_min' hreach
  · have hright : ¬k ≤ thresholdCount s n m := by
      intro h
      exact hreach ⟨n, h⟩
    rw [(thresholdTime_eq_top_iff s m k).mpr hreach]
    simp [hright]

theorem measurableSet_lateLevelSet (delta : ℝ) (m k : ℕ) (hk : 0 < k) :
    MeasurableSet (lateLevelSet delta m k) := by
  let cutoff : ℕ := ⌊levelCutoff delta m⌋₊
  have hclock : MeasurableSet
      {s : WalkPath | (cutoff : WithTop ℕ) < thresholdTime s m k} := by
    have hreach : MeasurableSet {s : WalkPath | k ≤ thresholdCount s cutoff m} :=
      measurableSet_le measurable_const (measurable_thresholdCount cutoff m)
    have heq : {s : WalkPath | (cutoff : WithTop ℕ) < thresholdTime s m k} =
        {s | k ≤ thresholdCount s cutoff m}ᶜ := by
      ext s
      simp only [mem_ofPred_eq, mem_compl_iff]
      rw [← not_le, thresholdTime_le_iff]
    rw [heq]
    exact hreach.compl
  exact hclock.inter (measurableSet_levelFavoriteSet m k hk)

/-- Pullback of HLOZ's late-level event to increment space. -/
def lateLevelStepsSet (delta : ℝ) (m k : ℕ) : Set StepPath :=
  trajectory ⁻¹' lateLevelSet delta m k

theorem fairSteps_lateLevelStepsSet (delta : ℝ) (m k : ℕ) (hk : 0 < k) :
    fairSteps (lateLevelStepsSet delta m k) =
      simpleRandomWalk (lateLevelSet delta m k) := by
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory
    (measurableSet_lateLevelSet delta m k hk)]
  rfl

/-- If level `m+1` is ever reached, the one-favorite event at level `m`
necessarily occurred earlier. -/
theorem levelFavorite_one_of_reaches_next (s : WalkPath) (m : ℕ) (hm : 0 < m)
    (hnext : ReachesThreshold s (m + 1) 1) :
    levelFavorite s m 1 := by
  apply (levelFavorite_iff_thresholdTime_lt s m 1 (by omega)).mpr
  cases hq : Nat.find hnext with
  | zero =>
      have hspec : 1 ≤ thresholdCount s 0 (m + 1) := by
        simpa [hq] using Nat.find_spec hnext
      have hmax : maxLocalTime s 0 ≤ m :=
        (maxLocalTime_le_time_add_one s 0).trans (by omega)
      have hzero : thresholdCount s 0 (m + 1) = 0 :=
        (thresholdCount_succ_level_eq_zero_iff s 0 m).mpr hmax
      omega
  | succ n =>
      have hspec : 1 ≤ thresholdCount s (n + 1) (m + 1) := by
        simpa [hq] using Nat.find_spec hnext
      have hprev : thresholdCount s n (m + 1) = 0 := by
        by_contra hne
        have hone : 1 ≤ thresholdCount s n (m + 1) :=
          Nat.one_le_iff_ne_zero.mpr hne
        exact Nat.find_min hnext (by omega) hone
      have hnonempty : (thresholdSites s (n + 1) (m + 1)).Nonempty := by
        rw [← Finset.card_pos, ← thresholdCount]
        exact hspec
      obtain ⟨x, hx⟩ := hnonempty
      have hxlocal : m + 1 ≤ localTime s (n + 1) x :=
        (mem_thresholdSites_iff s (n + 1) (m + 1) x (by omega)).mp hx
      have hxcurrent : x = s (n + 1) := by
        by_contra hne
        have hxprevLocal : m + 1 ≤ localTime s n x := by
          rw [localTime_succ] at hxlocal
          simpa [Ne.symm hne] using hxlocal
        have hxprev : x ∈ thresholdSites s n (m + 1) :=
          (mem_thresholdSites_iff s n (m + 1) x (by omega)).mpr hxprevLocal
        have hpositive : 0 < thresholdCount s n (m + 1) := by
          rw [thresholdCount, Finset.card_pos]
          exact ⟨x, hxprev⟩
        omega
      have hxmCurrent : m ≤ localTime s n (s (n + 1)) := by
        rw [hxcurrent, localTime_succ, if_pos rfl] at hxlocal
        omega
      have hxm : m ≤ localTime s n x := by
        simpa only [hxcurrent] using hxmCurrent
      have hxAtM : x ∈ thresholdSites s n m :=
        (mem_thresholdSites_iff s n m x hm).mpr hxm
      have hcountM : 1 ≤ thresholdCount s n m := by
        rw [thresholdCount, Nat.one_le_iff_ne_zero, Finset.card_ne_zero]
        exact ⟨x, hxAtM⟩
      let hreachM : ReachesThreshold s m 1 := ⟨n, hcountM⟩
      rw [thresholdTime_eq_coe s m 1 hreachM,
        thresholdTime_eq_coe s (m + 1) 1 hnext]
      exact_mod_cast (Nat.find_min' hreachM hcountM).trans_lt (by omega)

/-- Divergence of maximal local time makes every positive first-level clock
finite and makes `M_m^1` occur. -/
theorem levelFavorite_one_of_maxLocalTimeDiverges (s : WalkPath) (m : ℕ)
    (hm : 0 < m) (hdiv : MaxLocalTimeDiverges s) :
    levelFavorite s m 1 := by
  have hevent : ∀ᶠ n in atTop, m + 1 ≤ maxLocalTime s n :=
    (tendsto_atTop.1 hdiv (m + 1))
  obtain ⟨n, hn⟩ := hevent.exists
  obtain ⟨x, hx⟩ := favoriteSites_nonempty s n
  have hxlocal : m + 1 ≤ localTime s n x := by
    rw [favoriteSites, favoritePrefix, Finset.mem_filter] at hx
    exact hn.trans_eq hx.2.symm
  have hxthreshold : x ∈ thresholdSites s n (m + 1) :=
    (mem_thresholdSites_iff s n (m + 1) x (by omega)).mpr hxlocal
  have hcount : 1 ≤ thresholdCount s n (m + 1) := by
    rw [thresholdCount, Nat.one_le_iff_ne_zero, Finset.card_ne_zero]
    exact ⟨x, hxthreshold⟩
  exact levelFavorite_one_of_reaches_next s m hm ⟨n, hcount⟩

/-- The unconditioned late first-level-clock event on increment space. -/
def lateFirstLevelClockSteps (delta : ℝ) (m : ℕ) : Set StepPath :=
  {omega | (⌊levelCutoff delta m⌋₊ : WithTop ℕ) < levelTimeSteps m 1 omega}

/-- `LevelTail.levelTime_tail_of_lowerDeviation` specialized to the fresh
first-level clock.  Recurrence removes the `M_m^1` conjunct from
`lateLevelSet`. -/
theorem firstLevelClock_tail_of_lowerDeviation
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      fairSteps (lateFirstLevelClockSteps delta m) <
        ENNReal.ofReal (Real.exp (-c * (m : ℝ))) := by
  obtain ⟨c, hc, htail⟩ :=
    levelTime_tail_of_lowerDeviation simpleRandomWalk hProp13 delta hdelta
  have hdivSteps : ∀ᵐ omega ∂fairSteps,
      MaxLocalTimeDiverges (trajectory omega) := by
    change ∀ᵐ omega ∂fairSteps,
      Tendsto (maxLocalTime (trajectory omega)) atTop atTop
    rw [← ae_map_iff measurable_trajectory.aemeasurable
      measurableSet_tendsto_maxLocalTime, ← simpleRandomWalk]
    exact ae_maxLocalTime_tendsto_atTop
  refine ⟨c, hc, ?_⟩
  filter_upwards [htail, eventually_gt_atTop 0] with m hmTail hm
  have hlevel : ∀ᵐ omega ∂fairSteps, levelFavorite (trajectory omega) m 1 := by
    filter_upwards [hdivSteps] with omega hdiv
    exact levelFavorite_one_of_maxLocalTimeDiverges (trajectory omega) m hm hdiv
  have heq : lateFirstLevelClockSteps delta m =ᵐ[fairSteps]
      lateLevelStepsSet delta m 1 := by
    filter_upwards [hlevel] with omega hfavorite
    exact propext (and_iff_left hfavorite).symm
  rw [measure_congr heq, fairSteps_lateLevelStepsSet delta m 1 (by omega)]
  exact hmTail 1 (by omega)

/-! ## The fresh avoidance-and-clock event -/

/-- Uniform logarithmic two-point avoidance pulled back to the IID increment
space used by the strong Markov theorem. -/
theorem fairSteps_avoidsTwoPointsThrough_lower_log
    (x : Point) {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal (1 / (100 * Real.log n)) ≤
      fairSteps (TwoPointAvoidance.avoidsTwoPointsThrough x n) := by
  calc
    ENNReal.ofReal (1 / (100 * Real.log n)) ≤
        simpleRandomWalk (TwoPointAvoidance.walkAvoidsTwoPointsThrough x n) :=
      TwoPointLogAvoidance.simpleRandomWalk_walkAvoidsTwoPointsThrough_lower_log x hn
    _ = fairSteps (TwoPointAvoidance.avoidsTwoPointsThrough x n) := by
      rw [simpleRandomWalk, Measure.map_apply measurable_trajectory
        (TwoPointAvoidance.measurableSet_walkAvoidsTwoPointsThrough x n)]
      rfl

/-- A fresh walk avoids the two distinguished old favorite sites through the
HLOZ cutoff and reaches local-time level `m` by that cutoff. -/
def freshCreationSteps (delta : ℝ) (m : ℕ) (x : Point) : Set StepPath :=
  TwoPointAvoidance.avoidsTwoPointsThrough x (levelCutoffTime delta m) ∩
    {omega | levelTimeSteps m 1 omega ≤ levelCutoffTime delta m}

theorem measurableSet_freshCreationSteps (delta : ℝ) (m : ℕ) (x : Point) :
    MeasurableSet (freshCreationSteps delta m x) := by
  rw [freshCreationSteps]
  have havoid : MeasurableSet
      (TwoPointAvoidance.avoidsTwoPointsThrough x (levelCutoffTime delta m)) := by
    rw [TwoPointAvoidance.avoidsTwoPointsThrough_eq_preimage]
    exact (TwoPointAvoidance.measurableSet_walkAvoidsTwoPointsThrough x
      (levelCutoffTime delta m)).preimage measurable_trajectory
  have heq : {omega : StepPath |
      levelTimeSteps m 1 omega ≤ levelCutoffTime delta m} =
      {omega | 1 ≤ thresholdCount (trajectory omega) (levelCutoffTime delta m) m} := by
    ext omega
    exact levelTimeSteps_le_iff m 1 (levelCutoffTime delta m) omega
  refine havoid.inter ?_
  rw [heq]
  exact incrementFiltration.le (levelCutoffTime delta m) _
    (StoppedInsertion.measurableSet_thresholdCount_ge
      (levelCutoffTime delta m) m 1)

/-- The exact union-bound combination of the logarithmic avoidance estimate
and the fresh first-level-clock tail.  This is the unconditional finite-event
estimate inserted after `T_m^1` and `T_m^2` in HLOZ Lemma 4.1. -/
theorem freshCreationSteps_lower_of_firstLevelClock_tail
    (delta : ℝ) (m : ℕ) (x : Point)
    (hcutoff : 2 ≤ levelCutoffTime delta m)
    {tail : ℝ} (htail :
      fairSteps.real (lateFirstLevelClockSteps delta m) ≤ tail) :
    1 / (100 * Real.log (levelCutoffTime delta m)) - tail ≤
      fairSteps.real (freshCreationSteps delta m x) := by
  let n := levelCutoffTime delta m
  let A := TwoPointAvoidance.avoidsTwoPointsThrough x n
  let R : Set StepPath := {omega | levelTimeSteps m 1 omega ≤ n}
  let L := lateFirstLevelClockSteps delta m
  have hA : 1 / (100 * Real.log n) ≤ fairSteps.real A := by
    have h := fairSteps_avoidsTwoPointsThrough_lower_log x hcutoff
    apply (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mp
    simpa [A] using h
  have hsub : A ⊆ (A ∩ R) ∪ L := by
    intro omega homega
    by_cases hreach : levelTimeSteps m 1 omega ≤ n
    · exact Or.inl ⟨homega, hreach⟩
    · refine Or.inr ?_
      change (⌊levelCutoff delta m⌋₊ : WithTop ℕ) < levelTimeSteps m 1 omega
      have hfloorCeil : ⌊levelCutoff delta m⌋₊ ≤ levelCutoffTime delta m := by
        simpa only [levelCutoffTime] using
          (Nat.floor_le_ceil (levelCutoff delta m))
      have hfloorTop : (⌊levelCutoff delta m⌋₊ : WithTop ℕ) ≤
          (n : WithTop ℕ) := by
        exact_mod_cast hfloorCeil
      exact hfloorTop.trans_lt (lt_of_not_ge hreach)
  have hmeasure : fairSteps.real A ≤
      fairSteps.real (A ∩ R) + fairSteps.real L := by
    calc
      fairSteps.real A ≤ fairSteps.real ((A ∩ R) ∪ L) :=
        measureReal_mono hsub
      _ ≤ fairSteps.real (A ∩ R) + fairSteps.real L :=
        measureReal_union_le _ _
  change 1 / (100 * Real.log n) - tail ≤ fairSteps.real (A ∩ R)
  linarith

/-- Fully discharged fresh-walk estimate: the only hypothesis is HLOZ
Proposition 1.3, and the logarithmic two-point term is supplied by
`TwoPointLogAvoidance`.  The bound is uniform in the second forbidden point.
-/
theorem eventually_freshCreationSteps_lower_of_lowerDeviation
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop, ∀ x : Point,
      1 / (100 * Real.log (levelCutoffTime delta m)) -
          Real.exp (-c * (m : ℝ)) ≤
        fairSteps.real (freshCreationSteps delta m x) := by
  obtain ⟨c, hc, htail⟩ :=
    firstLevelClock_tail_of_lowerDeviation hProp13 delta hdelta
  have hcutoff : ∀ᶠ m : ℕ in atTop, 2 ≤ levelCutoffTime delta m :=
    (tendsto_levelCutoffTime delta).eventually (eventually_ge_atTop 2)
  refine ⟨c, hc, ?_⟩
  filter_upwards [htail, hcutoff] with m hmTail hmCutoff
  intro x
  apply freshCreationSteps_lower_of_firstLevelClock_tail delta m x hmCutoff
  rw [measureReal_def]
  have hreal : (fairSteps (lateFirstLevelClockSteps delta m)).toReal ≤
      (ENNReal.ofReal (Real.exp (-c * (m : ℝ)))).toReal :=
    (ENNReal.toReal_le_toReal (by finiteness) (by simp)).mpr hmTail.le
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using hreal

/-- At the HLOZ cutoff, the logarithm of the time horizon is at most a fixed
multiple of `sqrt m`. -/
theorem eventually_log_levelCutoffTime_le_three_sqrt (delta : ℝ)
    (hdelta : delta < 2 / 5) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (levelCutoffTime delta m) ≤ 3 * Real.sqrt (m : ℝ) := by
  have hcorrection := eventually_levelCutoffCorrection_le delta hdelta
  have hlarge : ∀ᶠ m : ℕ in atTop, 20 ≤ levelCutoffLeading m :=
    tendsto_levelCutoffLeading.eventually (eventually_ge_atTop 20)
  have hmpos : ∀ᶠ m : ℕ in atTop, 0 < m := eventually_gt_atTop 0
  filter_upwards [hcorrection, hlarge, hmpos] with m hcorr hlead hm
  have hlog := (log_levelCutoffTime_lt delta m).le
  have hsqrt0 : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hleading0 : 0 ≤ levelCutoffLeading m := levelCutoffLeading_nonneg m
  have hpiM : Real.pi * (m : ℝ) ≤ 4 * (m : ℝ) := by
    gcongr
    exact Real.pi_lt_four.le
  have hleadingBound : levelCutoffLeading m ≤ 2 * Real.sqrt (m : ℝ) := by
    nlinarith [levelCutoffLeading_sq m]
  have hone : (1 : ℝ) ≤ levelCutoffLeading m / 20 := by linarith
  unfold levelCutoffLog at hlog
  calc
    Real.log (levelCutoffTime delta m) ≤
        levelCutoffLeading m + levelCutoffCorrection delta m + 1 := hlog
    _ ≤ levelCutoffLeading m + levelCutoffLeading m / 20 +
        levelCutoffLeading m / 20 := by gcongr
    _ ≤ 3 * Real.sqrt (m : ℝ) := by nlinarith

/-- Exponential decay beats the reciprocal square-root cost used in the two
successive HLOZ creation stages. -/
theorem eventually_exp_neg_mul_le_inv_sqrt {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop,
      Real.exp (-c * (m : ℝ)) ≤ 1 / (600 * Real.sqrt (m : ℝ)) := by
  have htend : Tendsto
      (fun m : ℕ ↦ Real.sqrt (m : ℝ) * Real.exp (-c * (m : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2 : ℝ) c hc).comp
      tendsto_natCast_atTop_atTop
    have h' : Tendsto
        (fun m : ℕ ↦ (m : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-c * (m : ℝ)))
        atTop (𝓝 0) := by
      exact h
    simpa only [Real.sqrt_eq_rpow] using h'
  have hsmall : ∀ᶠ m : ℕ in atTop,
      Real.sqrt (m : ℝ) * Real.exp (-c * (m : ℝ)) ≤ 1 / 600 :=
    htend.eventually (Iic_mem_nhds (by norm_num))
  filter_upwards [hsmall, eventually_gt_atTop 0] with m hsmall hm
  have hsqrt : 0 < Real.sqrt (m : ℝ) := by positivity
  apply (le_div_iff₀ (by positivity : 0 < 600 * Real.sqrt (m : ℝ))).2
  nlinarith

/-- Conventional `d / sqrt m` form of the fresh creation estimate, with an
explicit constant.  All probabilistic input except Proposition 1.3 has been
discharged. -/
theorem eventually_freshCreationSteps_lower_inv_sqrt
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (delta : ℝ) (hdeltaPos : 0 < delta) (hdeltaLt : delta < 2 / 5) :
    ∀ᶠ m : ℕ in atTop, ∀ x : Point,
      1 / (600 * Real.sqrt (m : ℝ)) ≤
        fairSteps.real (freshCreationSteps delta m x) := by
  obtain ⟨c, hc, hfresh⟩ :=
    eventually_freshCreationSteps_lower_of_lowerDeviation hProp13 delta hdeltaPos
  have hlog := eventually_log_levelCutoffTime_le_three_sqrt delta hdeltaLt
  have hexp := eventually_exp_neg_mul_le_inv_sqrt hc
  have hmpos : ∀ᶠ m : ℕ in atTop, 0 < m := eventually_gt_atTop 0
  filter_upwards [hfresh, hlog, hexp, hmpos] with m hfreshM hlogM hexpM hm
  intro x
  have hsqrt : 0 < Real.sqrt (m : ℝ) := by positivity
  have htime : 2 ≤ levelCutoffTime delta m := by
    have hcutlog : 0 < Real.log (levelCutoffTime delta m) := by
      have hlead := levelCutoffLog_le_log_time delta m
      exact (levelCutoffLeading_pos hm).trans_le
        ((le_add_of_nonneg_right (levelCutoffCorrection_nonneg delta m)).trans hlead)
    have hone : (1 : ℝ) < levelCutoffTime delta m :=
      (Real.log_pos_iff (by positivity)).mp hcutlog
    exact_mod_cast hone
  have hlogPos : 0 < Real.log (levelCutoffTime delta m) :=
    Real.log_pos (by exact_mod_cast htime)
  have havoid : 1 / (300 * Real.sqrt (m : ℝ)) ≤
      1 / (100 * Real.log (levelCutoffTime delta m)) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h := hfreshM x
  calc
    1 / (600 * Real.sqrt (m : ℝ)) =
        1 / (300 * Real.sqrt (m : ℝ)) -
          1 / (600 * Real.sqrt (m : ℝ)) := by
      field_simp
      norm_num
    _ ≤ 1 / (100 * Real.log (levelCutoffTime delta m)) -
          Real.exp (-c * (m : ℝ)) := sub_le_sub havoid hexpM
    _ ≤ fairSteps.real (freshCreationSteps delta m x) := h

/-! ## The localized two-stage tower estimate -/

/-- Localized form of the two-stage tower calculation.  The second-stage
lower bound only needs to hold on the first-stage event.  This is the form
actually produced by a strong-Markov restart at `T_m^2`. -/
theorem condExp_indicator_localized_lower_bound
    {Omega : Type*} {m0 : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {mG mH : MeasurableSpace Omega}
    (hGH : mG ≤ mH) (hH : mH ≤ m0) {B C : Set Omega}
    (hB : MeasurableSet[mH] B) (hC : @MeasurableSet Omega m0 C)
    {a b : ℝ} (ha : 0 ≤ a)
    (hCcond : ∀ᵐ omega ∂mu,
      a * B.indicator (1 : Omega → ℝ) omega ≤
        (mu[C.indicator (1 : Omega → ℝ) | mH]) omega)
    (hBcond : ∀ᵐ omega ∂mu,
      b ≤ (mu[B.indicator (1 : Omega → ℝ) | mG]) omega) :
    ∀ᵐ omega ∂mu,
      a * b ≤ (mu[C.indicator (1 : Omega → ℝ) | mG]) omega := by
  let iB : Omega → ℝ := B.indicator 1
  let iC : Omega → ℝ := C.indicator 1
  have hBglobal : @MeasurableSet Omega m0 B := hH B hB
  have hiB : Integrable iB mu := (integrable_const 1).indicator hBglobal
  have hiC : Integrable iC mu := (integrable_const 1).indicator hC
  have hmono :
      mu[fun omega ↦ a * iB omega | mG] ≤ᵐ[mu]
        mu[mu[iC | mH] | mG] := by
    exact condExp_mono (hiB.const_mul a) integrable_condExp hCcond
  have htower :
      mu[mu[iC | mH] | mG] =ᵐ[mu] mu[iC | mG] :=
    condExp_condExp_of_le hGH hH
  have hscale :
      mu[fun omega ↦ a * iB omega | mG] =ᵐ[mu]
        fun omega ↦ a * (mu[iB | mG]) omega := by
    exact condExp_mul_of_stronglyMeasurable_left
      stronglyMeasurable_const (hiB.const_mul a) hiB
  filter_upwards [hmono, htower, hscale, hBcond]
    with omega hmono_o htower_o hscale_o hB_o
  change b ≤ (mu[iB | mG]) omega at hB_o
  calc
    a * b ≤ a * (mu[iB | mG]) omega := mul_le_mul_of_nonneg_left hB_o ha
    _ = (mu[fun omega ↦ a * iB omega | mG]) omega := hscale_o.symm
    _ ≤ (mu[mu[iC | mH] | mG]) omega := hmono_o
    _ = (mu[iC | mG]) omega := htower_o

/-! ## Strong Markov as a conditional-probability identity -/

/-- A finite block following a possibly infinite stopping time is globally
measurable.  On the exceptional value `⊤`, `postWithTopStoppingBlock` uses
time zero, exactly as in its definition. -/
theorem measurable_postWithTopStoppingBlock
    {tau : StepPath → WithTop ℕ}
    (htau : IsStoppingTime incrementFiltration tau) (k : ℕ) :
    Measurable (postWithTopStoppingBlock tau k) := by
  intro C hC
  have hpre : postWithTopStoppingBlock tau k ⁻¹' C =
      ({omega | tau omega = ⊤} ∩ stepBlock 0 k ⁻¹' C) ∪
        ⋃ n : ℕ, {omega | tau omega = n} ∩ stepBlock n k ⁻¹' C := by
    ext omega
    simp only [mem_preimage, mem_union, mem_inter_iff, mem_ofPred_eq, mem_iUnion]
    cases h : tau omega with
    | top =>
        have hblock : postWithTopStoppingBlock tau k omega = stepBlock 0 k omega := by
          funext j
          simp [postWithTopStoppingBlock, stepBlock, h]
        rw [hblock]
        simp
    | coe n =>
        have hblock : postWithTopStoppingBlock tau k omega = stepBlock n k omega := by
          funext j
          change omega ((tau omega).untopD 0 + (j : ℕ)) = omega (n + (j : ℕ))
          rw [h, WithTop.untopD_coe]
        rw [hblock]
        simp
  rw [hpre]
  have hcoe (n : ℕ) : MeasurableSet {omega : StepPath | tau omega = (n : WithTop ℕ)} :=
    incrementFiltration.le n _ (htau.measurableSet_eq n)
  have htopEq : {omega : StepPath | tau omega = ⊤} =
      (⋃ n : ℕ, {omega | tau omega = (n : WithTop ℕ)})ᶜ := by
    ext omega
    cases h : tau omega <;> simp [h]
  have htop : MeasurableSet {omega : StepPath | tau omega = ⊤} := by
    rw [htopEq]
    exact (MeasurableSet.iUnion hcoe).compl
  exact (htop.inter ((measurable_stepBlock 0 k) hC)).union
    (MeasurableSet.iUnion fun n : ℕ ↦
      (hcoe n).inter ((measurable_stepBlock n k) hC))

/-- Conditional-expectation form of finite-dimensional strong Markov at an
almost surely finite `WithTop` stopping time.  It is useful because the HLOZ
stage estimates are stated as pointwise lower bounds for conditional
probabilities, whereas `StrongMarkovWithTop.lean` gives factorization on every
stopped-past event. -/
theorem condExp_indicator_postWithTopStoppingBlock
    {tau : StepPath → WithTop ℕ}
    (htau : IsStoppingTime incrementFiltration tau)
    (hfinite : ∀ᵐ omega ∂fairSteps, tau omega < ⊤)
    (k : ℕ) (C : Set (Fin k → Direction)) :
    fairSteps[(postWithTopStoppingBlock tau k ⁻¹' C).indicator
        (1 : StepPath → ℝ) | htau.measurableSpace] =ᵐ[fairSteps]
      fun _ ↦ (fairBlock k C).toReal := by
  let D : Set StepPath := postWithTopStoppingBlock tau k ⁻¹' C
  have hD : MeasurableSet D :=
    (measurable_postWithTopStoppingBlock htau k) (Set.to_countable C).measurableSet
  have hiD : Integrable (D.indicator (1 : StepPath → ℝ)) fairSteps :=
    (integrable_const 1).indicator hD
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq htau.measurableSpace_le hiD
  · intro A _ _
    exact (integrable_const (fairBlock k C).toReal).integrableOn
  · intro A hA _
    rw [setIntegral_const, smul_eq_mul, mul_comm]
    rw [setIntegral_indicator hD]
    change (fairBlock k C).toReal * fairSteps.real A =
      ∫ _ in A ∩ D, (1 : ℝ) ∂fairSteps
    rw [setIntegral_const, smul_eq_mul, mul_one]
    rw [measureReal_def, measureReal_def]
    rw [strongMarkov_withTop_of_ae_finite_of_measurableSet_stopping
      htau hA hfinite k C]
    rw [mul_comm]
    exact ENNReal.toReal_mul.symm
  · exact stronglyMeasurable_const.aestronglyMeasurable

/-- Localized strong Markov identity.  Global almost-sure finiteness of the
clock is unnecessary when the stopped-past event `B` itself forces finiteness.
This is the exact form needed at `T_m^2`, where finiteness is known on
`M_m^2`. -/
theorem condExp_indicator_inter_postWithTopStoppingBlock
    {tau : StepPath → WithTop ℕ}
    (htau : IsStoppingTime incrementFiltration tau)
    {B : Set StepPath} (hB : MeasurableSet[htau.measurableSpace] B)
    (hBfinite : B ⊆ {omega | tau omega < ⊤})
    (k : ℕ) (C : Set (Fin k → Direction)) :
    fairSteps[((B ∩ postWithTopStoppingBlock tau k ⁻¹' C).indicator
        (1 : StepPath → ℝ)) | htau.measurableSpace] =ᵐ[fairSteps]
      fun omega ↦ (fairBlock k C).toReal * B.indicator (1 : StepPath → ℝ) omega := by
  let D : Set StepPath := postWithTopStoppingBlock tau k ⁻¹' C
  let E : Set StepPath := B ∩ D
  have hBglobal : MeasurableSet B := htau.measurableSpace_le B hB
  have hD : MeasurableSet D :=
    (measurable_postWithTopStoppingBlock htau k) (Set.to_countable C).measurableSet
  have hE : MeasurableSet E := hBglobal.inter hD
  have hiE : Integrable (E.indicator (1 : StepPath → ℝ)) fairSteps :=
    (integrable_const 1).indicator hE
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq htau.measurableSpace_le hiE
  · intro A _ _
    exact ((integrable_const 1).indicator hBglobal).const_mul
      (fairBlock k C).toReal |>.integrableOn
  · intro A hA _
    have hAB : MeasurableSet[htau.measurableSpace] (A ∩ B) := hA.inter hB
    have hfiniteEq : (A ∩ B) ∩ {omega | tau omega < ⊤} = A ∩ B := by
      ext omega
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact and_iff_left_of_imp fun h ↦ hBfinite h.2
    have hfactor := strongMarkov_withTop_finiteEvent_of_measurableSet_stopping
      htau hAB k C
    rw [hfiniteEq] at hfactor
    rw [integral_const_mul]
    rw [setIntegral_indicator hBglobal]
    change (fairBlock k C).toReal * (∫ _ in A ∩ B, (1 : ℝ) ∂fairSteps) =
      ∫ _ in A, E.indicator (1 : StepPath → ℝ) _ ∂fairSteps
    rw [setIntegral_const, smul_eq_mul, mul_one]
    rw [setIntegral_indicator hE]
    change (fairBlock k C).toReal * fairSteps.real (A ∩ B) =
      ∫ _ in A ∩ E, (1 : ℝ) ∂fairSteps
    rw [setIntegral_const, smul_eq_mul, mul_one]
    rw [measureReal_def, measureReal_def]
    have hset : A ∩ E = (A ∩ B) ∩ D := by
      ext omega
      simp [E, D, and_assoc]
    rw [hset, hfactor, ENNReal.toReal_mul, mul_comm]
  · exact ((stronglyMeasurable_one.indicator hB).const_mul
      (fairBlock k C).toReal).aestronglyMeasurable

/-- The first-level clock is almost surely finite for every positive level. -/
theorem ae_levelTimeSteps_one_lt_top (m : ℕ) (hm : 0 < m) :
    ∀ᵐ omega ∂fairSteps, levelTimeSteps m 1 omega < ⊤ := by
  have hdivSteps : ∀ᵐ omega ∂fairSteps,
      MaxLocalTimeDiverges (trajectory omega) := by
    change ∀ᵐ omega ∂fairSteps,
      Tendsto (maxLocalTime (trajectory omega)) atTop atTop
    rw [← ae_map_iff measurable_trajectory.aemeasurable
      measurableSet_tendsto_maxLocalTime, ← simpleRandomWalk]
    exact ae_maxLocalTime_tendsto_atTop
  filter_upwards [hdivSteps] with omega hdiv
  have hlevel := levelFavorite_one_of_maxLocalTimeDiverges
    (trajectory omega) m hm hdiv
  exact ((levelFavorite_iff_thresholdTime_lt (trajectory omega) m 1 (by omega)).mp
    hlevel).trans_le le_top

/-! ## Canonical conditional-Borel--Cantelli assembly -/

/-- The exact lower-bound conclusion from HLOZ's two successive localized
`m^{-1/2}` estimates.  The hypotheses are conditional estimates, not the
desired infinitely-often conclusion: `hsecond` creates `M_m^2` after
`T_m^1`, while `hthird` creates `M_m^3` after `T_m^2`, localized on
`M_m^2`. -/
theorem ae_frequently_favoriteCount_ge_three_of_two_stage_bounds
    (a b : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) {c : ℝ} (hc : 0 < c)
    (hproduct : ∀ m, c / (m + 1 : ℕ) ≤ a m * b m)
    (hsecond : ∀ m, ∀ᵐ omega ∂fairSteps,
      b m ≤
        (fairSteps[(levelEventSteps (m + 1) 2).indicator
          (1 : StepPath → ℝ) | levelFiltration m]) omega)
    (hthird : ∀ m, ∀ᵐ omega ∂fairSteps,
      a m * (levelEventSteps (m + 1) 2).indicator
          (1 : StepPath → ℝ) omega ≤
        (fairSteps[(levelEventSteps (m + 1) 3).indicator
          (1 : StepPath → ℝ) |
            (isStoppingTime_levelTimeSteps (m + 1) 2).measurableSpace]) omega) :
    ∀ᵐ s ∂simpleRandomWalk, ∃ᶠ n in atTop, 3 ≤ favoriteCount s n := by
  have hmiddleLe (m : ℕ) :
      levelFiltration m ≤
        (isStoppingTime_levelTimeSteps (m + 1) 2).measurableSpace := by
    rw [levelFiltration_apply]
    exact IsStoppingTime.measurableSpace_mono
      (isStoppingTime_levelTimeSteps (m + 1) 1)
      (isStoppingTime_levelTimeSteps (m + 1) 2)
      (levelTimeSteps_mono_count (m + 1) (by omega))
  have hcond : ∀ᵐ omega ∂fairSteps, ∀ m,
      c / (m + 1 : ℕ) ≤
        (fairSteps[(levelEventSteps (m + 1) 3).indicator
          (1 : StepPath → ℝ) | levelFiltration m]) omega := by
    rw [ae_all_iff]
    intro m
    have htwo := condExp_indicator_localized_lower_bound
      (hmiddleLe m)
      (isStoppingTime_levelTimeSteps (m + 1) 2).measurableSpace_le
      (measurableSet_levelEventSteps_at_current (m + 1) 2)
      (measurableSet_levelEventSteps (m + 1) 3 (by omega))
      (ha m) (hthird m) (hsecond m)
    filter_upwards [htwo] with omega homega
    exact (hproduct m).trans homega
  have hfreqSteps : ∀ᵐ omega ∂fairSteps,
      ∃ᶠ m in atTop, omega ∈ levelEventSteps m 3 := by
    exact ae_frequently_mem_of_harmonic_conditional_lower_bound
      (F := levelFiltration) (events := fun m ↦ levelEventSteps m 3)
      (fun m ↦ measurableSet_levelEventSteps_levelFiltration m 3) hc hcond
  have hfreqWalk : ∀ᵐ s ∂simpleRandomWalk,
      ∃ᶠ m in atTop, levelFavorite s m 3 := by
    rw [simpleRandomWalk, ae_map_iff measurable_trajectory.aemeasurable
      (measurableSet_frequentLevelFavoriteSet 3 (by omega))]
    filter_upwards [hfreqSteps] with omega homega
    exact (frequently_congr (by
      filter_upwards [] with m
      exact levelFavorite_iff_thresholdTime_lt (trajectory omega) m 3 (by omega))).mpr
        homega
  exact ae_frequently_favoriteCount_ge_three_of_frequently_levelFavorite hfreqWalk

/-- The asymptotic form of
`ae_frequently_favoriteCount_ge_three_of_two_stage_bounds`.  The two
conditional estimates need only hold for all sufficiently large local-time
levels, exactly as supplied by the planar lower-deviation estimate. -/
theorem ae_frequently_favoriteCount_ge_three_of_eventually_two_stage_bounds
    (a b : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) {c : ℝ} (hc : 0 < c)
    (hproduct : ∀ m, c / (m + 1 : ℕ) ≤ a m * b m)
    (hsecond : ∀ᶠ m in atTop, ∀ᵐ omega ∂fairSteps,
      b m ≤
        (fairSteps[(levelEventSteps (m + 1) 2).indicator
          (1 : StepPath → ℝ) | levelFiltration m]) omega)
    (hthird : ∀ᶠ m in atTop, ∀ᵐ omega ∂fairSteps,
      a m * (levelEventSteps (m + 1) 2).indicator
          (1 : StepPath → ℝ) omega ≤
        (fairSteps[(levelEventSteps (m + 1) 3).indicator
          (1 : StepPath → ℝ) |
            (isStoppingTime_levelTimeSteps (m + 1) 2).measurableSpace]) omega) :
    ∀ᵐ s ∂simpleRandomWalk, ∃ᶠ n in atTop, 3 ≤ favoriteCount s n := by
  have hmiddleLe (m : ℕ) :
      levelFiltration m ≤
        (isStoppingTime_levelTimeSteps (m + 1) 2).measurableSpace := by
    rw [levelFiltration_apply]
    exact IsStoppingTime.measurableSpace_mono
      (isStoppingTime_levelTimeSteps (m + 1) 1)
      (isStoppingTime_levelTimeSteps (m + 1) 2)
      (levelTimeSteps_mono_count (m + 1) (by omega))
  have hcondEventually : ∀ᶠ m in atTop, ∀ᵐ omega ∂fairSteps,
      c / (m + 1 : ℕ) ≤
        (fairSteps[(levelEventSteps (m + 1) 3).indicator
          (1 : StepPath → ℝ) | levelFiltration m]) omega := by
    filter_upwards [hsecond, hthird] with m hsecond_m hthird_m
    have htwo := condExp_indicator_localized_lower_bound
      (hmiddleLe m)
      (isStoppingTime_levelTimeSteps (m + 1) 2).measurableSpace_le
      (measurableSet_levelEventSteps_at_current (m + 1) 2)
      (measurableSet_levelEventSteps (m + 1) 3 (by omega))
      (ha m) hthird_m hsecond_m
    filter_upwards [htwo] with omega homega
    exact (hproduct m).trans homega
  obtain ⟨K, hK⟩ := eventually_atTop.mp hcondEventually
  have hcond : ∀ᵐ omega ∂fairSteps, ∀ᶠ m in atTop,
      c / (m + 1 : ℕ) ≤
        (fairSteps[(levelEventSteps (m + 1) 3).indicator
          (1 : StepPath → ℝ) | levelFiltration m]) omega := by
    have hall : ∀ᵐ omega ∂fairSteps, ∀ m, K ≤ m →
        c / (m + 1 : ℕ) ≤
          (fairSteps[(levelEventSteps (m + 1) 3).indicator
            (1 : StepPath → ℝ) | levelFiltration m]) omega := by
      rw [ae_all_iff]
      intro m
      by_cases hm : K ≤ m
      · filter_upwards [hK m hm] with omega homega
        exact fun _ ↦ homega
      · exact Filter.Eventually.of_forall fun _ hKm ↦ (hm hKm).elim
    filter_upwards [hall] with omega homega
    exact eventually_atTop.mpr ⟨K, fun m hm ↦ homega m hm⟩
  have hfreqSteps : ∀ᵐ omega ∂fairSteps,
      ∃ᶠ m in atTop, omega ∈ levelEventSteps m 3 := by
    exact ae_frequently_mem_of_eventually_harmonic_conditional_lower_bound
      (F := levelFiltration) (events := fun m ↦ levelEventSteps m 3)
      (fun m ↦ measurableSet_levelEventSteps_levelFiltration m 3) hc hcond
  have hfreqWalk : ∀ᵐ s ∂simpleRandomWalk,
      ∃ᶠ m in atTop, levelFavorite s m 3 := by
    rw [simpleRandomWalk, ae_map_iff measurable_trajectory.aemeasurable
      (measurableSet_frequentLevelFavoriteSet 3 (by omega))]
    filter_upwards [hfreqSteps] with omega homega
    exact (frequently_congr (by
      filter_upwards [] with m
      exact levelFavorite_iff_thresholdTime_lt (trajectory omega) m 3 (by omega))).mpr
        homega
  exact ae_frequently_favoriteCount_ge_three_of_frequently_levelFavorite hfreqWalk

end Erdos1165.LowerAssembly
