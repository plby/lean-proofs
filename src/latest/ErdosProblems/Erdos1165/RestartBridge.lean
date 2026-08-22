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

import ErdosProblems.Erdos1165.LowerAssembly
import ErdosProblems.Erdos1165.HLOZPathEvents

/-!
# Restart bridges for the HLOZ lower bound

This file supplies the deterministic seam between a fresh two-point-avoidance
event after `T_m^k` and the next favorite-level event `M_m^(k+1)`.  It also
packages the finite fresh event as a block event and defines the random
displacement from the second newly-created favorite to the other old favorite.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165.RestartBridge

open HLOZPathEvents LowerAssembly

/-! ## Local-time comparison under a deterministic restart -/

/-- Local time accumulated by the shifted walk is bounded by the global local
time at the correspondingly translated site.  The shifted time zero maps to
global time `n`, so this comparison includes the endpoint of the old prefix. -/
theorem localTime_shift_le_localTime_add (omega : StepPath) (n q : ℕ) (y : Point) :
    localTime (trajectory (shiftSteps n omega)) q y ≤
      localTime (trajectory omega) (n + q) (trajectory omega n + y) := by
  let e : Fin (q + 1) ↪ Fin (n + q + 1) :=
    ⟨fun j ↦ ⟨n + j, by omega⟩, fun i j h ↦ by
      exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))⟩
  unfold localTime localTimePrefix pathPrefix
  apply Finset.card_le_card_of_injOn e
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    have hshift := trajectory_add_sub_trajectory omega n (j : ℕ)
    have hadd : trajectory omega (n + (j : ℕ)) =
        trajectory omega n + trajectory (shiftSteps n omega) j := by
      simpa [add_comm] using (sub_eq_iff_eq_add.mp hshift)
    change trajectory omega (n + (j : ℕ)) = trajectory omega n + y
    rw [hadd, hj]
  · intro i _ j _ hij
    exact e.injective hij

/-- If a site is avoided at every positive time after `n`, its local time is
unchanged through `n + q`. -/
theorem localTime_add_eq_of_avoids (s : WalkPath) (n q : ℕ) (x : Point)
    (havoid : ∀ j, 0 < j → j ≤ q → s (n + j) ≠ x) :
    localTime s (n + q) x = localTime s n x := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show n + (q + 1) = (n + q) + 1 by omega, localTime_succ]
      have hne : s (n + q + 1) ≠ x := by
        simpa [Nat.add_assoc] using havoid (q + 1) (by omega) le_rfl
      rw [if_neg hne]
      simpa using ih (fun j hjpos hjq ↦ havoid j hjpos (by omega))

/-! ## The deterministic creation lemma -/

/-- If level `m` has exactly `k` threshold sites at time `n`, none is yet at
level `m+1`, the old sites are avoided, and one more `m`-threshold site exists
by time `n+N`, then `M_m^(k+1)` occurs. -/
theorem levelFavorite_succ_of_avoids_old_until_reach
    (s : WalkPath) (m k n N : ℕ) (hm : 0 < m)
    (hcount : thresholdCount s n m = k)
    (hnext : thresholdCount s n (m + 1) = 0)
    (havoid : ∀ j, 0 < j → j ≤ N →
      s (n + j) ∉ thresholdSites s n m)
    (hreach : k + 1 ≤ thresholdCount s (n + N) m) :
    levelFavorite s m (k + 1) := by
  let P : ℕ → Prop := fun q ↦ k + 1 ≤ thresholdCount s (n + q) m
  let hex : ∃ q, P q := ⟨N, hreach⟩
  let q := Nat.find hex
  have hqspec : P q := Nat.find_spec hex
  have hqN : q ≤ N := Nat.find_min' hex hreach
  have hqpos : 0 < q := by
    by_contra hq0
    have hqzero : q = 0 := Nat.eq_zero_of_not_pos hq0
    rw [hqzero] at hqspec
    simp only [P, Nat.add_zero, hcount] at hqspec
    omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hqpos.ne'
  have hrlt : r < q := by omega
  have hprev_lt : thresholdCount s (n + r) m < k + 1 := by
    have hnot := Nat.find_min hex hrlt
    exact Nat.lt_of_not_ge hnot
  have hprev_ge : k ≤ thresholdCount s (n + r) m := by
    rw [← hcount]
    exact thresholdCount_mono_time s m (Nat.le_add_right n r)
  have hprev_eq : thresholdCount s (n + r) m = k := by omega
  have hcur_ge : k + 1 ≤ thresholdCount s ((n + r) + 1) m := by
    change k + 1 ≤ thresholdCount s (n + q) m at hqspec
    rw [hr] at hqspec
    simpa [Nat.add_assoc] using hqspec
  have hcur_le := thresholdCount_succ_le s (n + r) m
  have hcur_eq : thresholdCount s ((n + r) + 1) m = k + 1 := by
    rw [hprev_eq] at hcur_le
    omega
  let D := thresholdSites s n m
  have hDsub : D ⊆ thresholdSites s (n + r) m := by
    exact thresholdSites_mono_time s m (Nat.le_add_right n r)
  have hDeq : thresholdSites s (n + r) m = D := by
    symm
    apply Finset.eq_of_subset_of_card_le hDsub
    change thresholdCount s (n + r) m ≤ thresholdCount s n m
    omega
  have hqN' : r + 1 ≤ N := by omega
  have hcurrent_not : s ((n + r) + 1) ∉ D := by
    change s ((n + r) + 1) ∉ thresholdSites s n m
    rw [show (n + r) + 1 = n + (r + 1) by omega]
    exact havoid (r + 1) (by omega) hqN'
  have hnextCur : thresholdCount s ((n + r) + 1) (m + 1) = 0 := by
    rw [thresholdCount_eq_zero_iff_forall_lt s ((n + r) + 1) (m + 1) (by omega)]
    intro x
    by_cases hxD : x ∈ D
    · have hstay : localTime s ((n + r) + 1) x = localTime s n x := by
        rw [show (n + r) + 1 = n + (r + 1) by omega]
        apply localTime_add_eq_of_avoids
        intro j hjpos hjle hvisit
        exact (havoid j hjpos (hjle.trans hqN')) (hvisit ▸ hxD)
      have hlt : localTime s n x < m + 1 :=
        (thresholdCount_eq_zero_iff_forall_lt s n (m + 1) (by omega)).mp hnext x
      rw [hstay]
      exact hlt
    · have hxPrev : x ∉ thresholdSites s (n + r) m := by
        rwa [hDeq]
      have hxlt : localTime s (n + r) x < m := by
        simpa only [mem_thresholdSites_iff s (n + r) m x hm, not_le] using hxPrev
      rw [localTime_succ]
      by_cases hcur : s ((n + r) + 1) = x
      · rw [if_pos hcur]
        omega
      · rw [if_neg hcur]
        omega
  apply (levelFavorite_iff_thresholdCounts s m (k + 1) (by omega)).mpr
  exact ⟨(n + r) + 1, hcur_eq, hnextCur⟩

/-! ## A fresh restart supplies the extra threshold site -/

/-- A fresh one-site threshold reached by time `N`, while all old sites are
avoided, forces one more global threshold site by time `n+N`. -/
theorem thresholdCount_succ_le_of_fresh_reaches
    (omega : StepPath) (m k n N : ℕ) (hm : 2 ≤ m)
    (hcount : thresholdCount (trajectory omega) n m = k)
    (havoid : ∀ j, 0 < j → j ≤ N →
      trajectory omega n + trajectory (shiftSteps n omega) j ∉
        thresholdSites (trajectory omega) n m)
    (hfresh : levelTimeSteps m 1 (shiftSteps n omega) ≤ N) :
    k + 1 ≤ thresholdCount (trajectory omega) (n + N) m := by
  let w := shiftSteps n omega
  have hcountFresh : 1 ≤ thresholdCount (trajectory w) N m :=
    (levelTimeSteps_le_iff m 1 N w).mp hfresh
  let hreachFresh : ReachesThreshold (trajectory w) m 1 := ⟨N, hcountFresh⟩
  let q := Nat.find hreachFresh
  have hqN : q ≤ N := Nat.find_min' hreachFresh hcountFresh
  have hcreation : ThresholdCreation (trajectory w) m 1 q :=
    thresholdCreation_natFind hreachFresh
  have hqpos : 0 < q := by
    by_contra hnot
    have hqzero : q = 0 := Nat.eq_zero_of_not_pos hnot
    have hy := position_mem_thresholdSites_of_creation (s := trajectory w)
      (m := m) (k := 1) (n := q) (by omega) hcreation
    have hylocal : m ≤ localTime (trajectory w) 0 (trajectory w 0) := by
      simpa [hqzero] using
        (mem_thresholdSites_iff (trajectory w) q m (trajectory w q) (by omega)).mp hy
    have hupper := localTime_le_time_add_one (trajectory w) 0 (trajectory w 0)
    omega
  let y := trajectory w q
  have hyFresh : y ∈ thresholdSites (trajectory w) q m :=
    position_mem_thresholdSites_of_creation (s := trajectory w)
      (m := m) (k := 1) (n := q) (by omega) hcreation
  have hym : m ≤ localTime (trajectory w) q y :=
    (mem_thresholdSites_iff (trajectory w) q m y (by omega)).mp hyFresh
  let z := trajectory omega n + y
  have hznot : z ∉ thresholdSites (trajectory omega) n m := by
    exact havoid q hqpos hqN
  have hzlocal : m ≤ localTime (trajectory omega) (n + N) z := by
    exact hym.trans
      ((localTime_shift_le_localTime_add omega n q y).trans
        (localTime_mono_time (trajectory omega) z (Nat.add_le_add_left hqN n)))
  have hzmem : z ∈ thresholdSites (trajectory omega) (n + N) m :=
    (mem_thresholdSites_iff (trajectory omega) (n + N) m z (by omega)).mpr hzlocal
  have hsub : thresholdSites (trajectory omega) n m ⊆
      thresholdSites (trajectory omega) (n + N) m :=
    thresholdSites_mono_time (trajectory omega) m (Nat.le_add_right n N)
  have hproper : thresholdSites (trajectory omega) n m ⊂
      thresholdSites (trajectory omega) (n + N) m := by
    refine ⟨hsub, ?_⟩
    intro hreverse
    exact hznot (hreverse hzmem)
  have hcard := Finset.card_lt_card hproper
  change thresholdCount (trajectory omega) n m <
    thresholdCount (trajectory omega) (n + N) m at hcard
  rw [hcount] at hcard
  omega

/-- General deterministic restart implication in the form used at both
`T_m^1` and `T_m^2`. -/
theorem levelFavorite_succ_of_fresh_restart
    (omega : StepPath) (m k n N : ℕ) (hm : 2 ≤ m)
    (hcount : thresholdCount (trajectory omega) n m = k)
    (hnext : thresholdCount (trajectory omega) n (m + 1) = 0)
    (havoid : ∀ j, 0 < j → j ≤ N →
      trajectory omega n + trajectory (shiftSteps n omega) j ∉
        thresholdSites (trajectory omega) n m)
    (hfresh : levelTimeSteps m 1 (shiftSteps n omega) ≤ N) :
    levelFavorite (trajectory omega) m (k + 1) := by
  apply levelFavorite_succ_of_avoids_old_until_reach
    (trajectory omega) m k n N (by omega) hcount hnext
  · intro j hjpos hjN
    have hadd : trajectory omega (n + j) =
        trajectory omega n + trajectory (shiftSteps n omega) j := by
      simpa [add_comm] using
        (sub_eq_iff_eq_add.mp (trajectory_add_sub_trajectory omega n j))
    rw [hadd]
    exact havoid j hjpos hjN
  · exact thresholdCount_succ_le_of_fresh_reaches
      omega m k n N hm hcount havoid hfresh

/-! ## The fresh event as a finite block event -/

lemma trajectory_extendPrefix_stepPrefix_of_le (omega : StepPath) (N q : ℕ)
    (hq : q ≤ N) :
    trajectory (StoppedInsertion.extendPrefix (stepPrefix N omega)) q =
      trajectory omega q := by
  have h := congrFun (StoppedInsertion.trajectoryPrefix_stepPrefix omega N)
    (⟨q, by omega⟩ : Fin (N + 1))
  exact h

lemma thresholdCount_extendPrefix_stepPrefix (omega : StepPath) (N m : ℕ) :
    thresholdCount
        (trajectory (StoppedInsertion.extendPrefix (stepPrefix N omega))) N m =
      thresholdCount (trajectory omega) N m := by
  have hp := StoppedInsertion.trajectoryPrefix_stepPrefix omega N
  unfold thresholdCount thresholdSites visitedSites localTime
  rw [show pathPrefix (trajectory (StoppedInsertion.extendPrefix (stepPrefix N omega))) N =
      pathPrefix (trajectory omega) N by
    funext j
    change trajectory (StoppedInsertion.extendPrefix (stepPrefix N omega)) j =
      trajectory omega j
    exact congrFun hp j]

/-- Finite block form of `freshCreationSteps`. -/
def freshCreationBlock (delta : ℝ) (m : ℕ) (x : Point) :
    Set (Fin (levelCutoffTime delta m) → Direction) :=
  {u | StoppedInsertion.extendPrefix u ∈ freshCreationSteps delta m x}

theorem measurableSet_freshCreationBlock (delta : ℝ) (m : ℕ) (x : Point) :
    MeasurableSet (freshCreationBlock delta m x) :=
  (Set.to_countable _).measurableSet

theorem mem_freshCreationBlock_stepPrefix_iff
    (delta : ℝ) (m : ℕ) (x : Point) (omega : StepPath) :
    stepPrefix (levelCutoffTime delta m) omega ∈ freshCreationBlock delta m x ↔
      omega ∈ freshCreationSteps delta m x := by
  let N := levelCutoffTime delta m
  change StoppedInsertion.extendPrefix (stepPrefix N omega) ∈
      freshCreationSteps delta m x ↔ omega ∈ freshCreationSteps delta m x
  unfold freshCreationSteps TwoPointAvoidance.avoidsTwoPointsThrough
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  have htraj (q : ℕ) (hq : q ≤ N) :
      trajectory (StoppedInsertion.extendPrefix (stepPrefix N omega)) q =
        trajectory omega q :=
    trajectory_extendPrefix_stepPrefix_of_le omega N q hq
  have hclock :
      levelTimeSteps m 1 (StoppedInsertion.extendPrefix (stepPrefix N omega)) ≤ N ↔
        levelTimeSteps m 1 omega ≤ N := by
    rw [levelTimeSteps_le_iff, levelTimeSteps_le_iff,
      thresholdCount_extendPrefix_stepPrefix]
  constructor
  · rintro ⟨havoid, hlevel⟩
    refine ⟨?_, hclock.mp hlevel⟩
    intro q hqpos hqN
    simpa only [htraj q hqN] using havoid q hqpos hqN
  · rintro ⟨havoid, hlevel⟩
    refine ⟨?_, hclock.mpr hlevel⟩
    intro q hqpos hqN
    simpa only [htraj q hqN] using havoid q hqpos hqN

theorem postWithTopStoppingBlock_mem_freshCreationBlock_iff
    {tau : StepPath → WithTop ℕ} {omega : StepPath} {n : ℕ}
    (htau : tau omega = n) (delta : ℝ) (m : ℕ) (x : Point) :
    postWithTopStoppingBlock tau (levelCutoffTime delta m) omega ∈
        freshCreationBlock delta m x ↔
      shiftSteps n omega ∈ freshCreationSteps delta m x := by
  have hblock : postWithTopStoppingBlock tau (levelCutoffTime delta m) omega =
      stepPrefix (levelCutoffTime delta m) (shiftSteps n omega) := by
    have hvalue : (tau omega).untopD 0 = n := by
      rw [htau]
      exact WithTop.untopD_coe (0 : ℕ) n
    funext j
    change omega ((tau omega).untopD 0 + (j : ℕ)) = omega (n + (j : ℕ))
    rw [hvalue]
  rw [hblock]
  exact mem_freshCreationBlock_stepPrefix_iff delta m x (shiftSteps n omega)

/-! ## Facts at a realized level clock -/

theorem thresholdCreation_of_levelTimeSteps_eq
    {omega : StepPath} {m k n : ℕ} (_hk : 0 < k)
    (htime : levelTimeSteps m k omega = n) :
    ThresholdCreation (trajectory omega) m k n := by
  constructor
  · exact (levelTimeSteps_le_iff m k n omega).mp (by rw [htime])
  · intro q hqn
    by_contra hnot
    have hle : levelTimeSteps m k omega ≤ q :=
      (levelTimeSteps_le_iff m k q omega).mpr (Nat.le_of_not_gt hnot)
    rw [htime] at hle
    exact (not_le_of_gt hqn) (by exact_mod_cast hle)

theorem levelEventSteps_at_value_thresholdCounts
    {omega : StepPath} {m k n : ℕ} (hk : 0 < k)
    (htime : levelTimeSteps m k omega = n)
    (hevent : omega ∈ levelEventSteps m k) :
    thresholdCount (trajectory omega) n m = k ∧
      thresholdCount (trajectory omega) n (m + 1) = 0 := by
  have hcreation := thresholdCreation_of_levelTimeSteps_eq hk htime
  refine ⟨thresholdCount_eq_of_creation hk hcreation, ?_⟩
  by_contra hne
  have hpositive : 1 ≤ thresholdCount (trajectory omega) n (m + 1) :=
    Nat.one_le_iff_ne_zero.mpr hne
  have hnextLe : levelTimeSteps (m + 1) 1 omega ≤ n :=
    (levelTimeSteps_le_iff (m + 1) 1 n omega).mpr hpositive
  have hlt : (n : WithTop ℕ) < levelTimeSteps (m + 1) 1 omega := by
    change levelTimeSteps m k omega < levelTimeSteps (m + 1) 1 omega at hevent
    simpa [htime] using hevent
  exact (not_lt_of_ge hnextLe) hlt

/-! ## The first-stage restart -/

/-- A fresh block avoiding the old first favorite and reaching a fresh
one-site threshold creates `M_m^2`. -/
theorem firstStage_freshCreation_subset_levelEventTwo
    (delta : ℝ) (m : ℕ) (hm : 2 ≤ m) :
    levelEventSteps m 1 ∩
        postWithTopStoppingBlock (levelTimeSteps m 1) (levelCutoffTime delta m) ⁻¹'
          freshCreationBlock delta m 0 ⊆
      levelEventSteps m 2 := by
  intro omega homega
  rcases homega with ⟨hM, hfreshBlock⟩
  have htfinite : levelTimeSteps m 1 omega < ⊤ := by
    exact hM.trans_le le_top
  have htne : levelTimeSteps m 1 omega ≠ ⊤ := WithTop.lt_top_iff_ne_top.mp htfinite
  lift levelTimeSteps m 1 omega to ℕ using htne with n htime
  have hcounts := levelEventSteps_at_value_thresholdCounts (by omega) htime.symm hM
  have hcreation := thresholdCreation_of_levelTimeSteps_eq (by omega) htime.symm
  have hcurrent : trajectory omega n ∈ thresholdSites (trajectory omega) n m :=
    position_mem_thresholdSites_of_creation (by omega) hcreation
  have hDcard : (thresholdSites (trajectory omega) n m).card = 1 := by
    simpa [thresholdCount] using hcounts.1
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hDcard
  have hacurrent : a = trajectory omega n := by
    have hcurrent' : trajectory omega n = a := by
      simpa [ha] using hcurrent
    exact hcurrent'.symm
  have hD : thresholdSites (trajectory omega) n m = {trajectory omega n} := by
    simpa [hacurrent] using ha
  have hfresh : shiftSteps n omega ∈ freshCreationSteps delta m 0 :=
    (postWithTopStoppingBlock_mem_freshCreationBlock_iff htime.symm delta m 0).mp hfreshBlock
  have havold : ∀ j, 0 < j → j ≤ levelCutoffTime delta m →
      trajectory omega n + trajectory (shiftSteps n omega) j ∉
        thresholdSites (trajectory omega) n m := by
    intro j hjpos hjN
    rw [hD, Finset.mem_singleton]
    intro heq
    have hzero : trajectory (shiftSteps n omega) j = 0 := by
      simpa only [add_eq_left] using heq
    exact (hfresh.1 j hjpos hjN).1 hzero
  have hlevel : levelFavorite (trajectory omega) m 2 :=
    levelFavorite_succ_of_fresh_restart omega m 1 n (levelCutoffTime delta m)
      hm hcounts.1 hcounts.2 havold hfresh.2
  rw [levelEventSteps_eq_preimage m 2 (by omega)]
  exact hlevel

/-! ## The second old favorite and its stopped-prefix measurability -/

/-- A canonical choice of an old threshold site different from the current
site.  The fallback value is irrelevant when the threshold set has cardinality
two and contains the current position. -/
noncomputable def otherThresholdSite (s : WalkPath) (n m : ℕ) : Point :=
  by
    classical
    exact if h : ∃ x, x ∈ (thresholdSites s n m).erase (s n) then h.choose else 0

theorem otherThresholdSite_mem_erase
    (s : WalkPath) (n m : ℕ)
    (hcard : (thresholdSites s n m).card = 2)
    (hcurrent : s n ∈ thresholdSites s n m) :
    otherThresholdSite s n m ∈ (thresholdSites s n m).erase (s n) := by
  have heraseCard : ((thresholdSites s n m).erase (s n)).card = 1 := by
    rw [Finset.card_erase_of_mem hcurrent, hcard]
  have hex : ∃ x, x ∈ (thresholdSites s n m).erase (s n) := by
    exact Finset.card_pos.mp (by omega)
  rw [otherThresholdSite, dif_pos hex]
  exact hex.choose_spec

theorem otherThresholdSite_mem
    (s : WalkPath) (n m : ℕ)
    (hcard : (thresholdSites s n m).card = 2)
    (hcurrent : s n ∈ thresholdSites s n m) :
    otherThresholdSite s n m ∈ thresholdSites s n m := by
  exact Finset.mem_of_mem_erase
    (otherThresholdSite_mem_erase s n m hcard hcurrent)

theorem otherThresholdSite_ne_current
    (s : WalkPath) (n m : ℕ)
    (hcard : (thresholdSites s n m).card = 2)
    (hcurrent : s n ∈ thresholdSites s n m) :
    otherThresholdSite s n m ≠ s n := by
  exact (Finset.mem_erase.mp
    (otherThresholdSite_mem_erase s n m hcard hcurrent)).1

/-- When there are exactly two threshold sites and the walk currently sits at
one of them, the threshold set is the pair consisting of the current site and
`otherThresholdSite`. -/
theorem thresholdSites_eq_current_insert_other
    (s : WalkPath) (n m : ℕ)
    (hcard : (thresholdSites s n m).card = 2)
    (hcurrent : s n ∈ thresholdSites s n m) :
    thresholdSites s n m = {s n, otherThresholdSite s n m} := by
  have hotherErase := otherThresholdSite_mem_erase s n m hcard hcurrent
  have hother := Finset.mem_of_mem_erase hotherErase
  have hne := (Finset.mem_erase.mp hotherErase).1
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    rw [Finset.mem_insert]
    by_cases hzc : z = s n
    · exact Or.inl hzc
    · right
      have hzErase : z ∈ (thresholdSites s n m).erase (s n) :=
        Finset.mem_erase.mpr ⟨hzc, hz⟩
      have heraseCard : ((thresholdSites s n m).erase (s n)).card = 1 := by
        rw [Finset.card_erase_of_mem hcurrent, hcard]
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp heraseCard
      have hza : z = a := by simpa [ha] using hzErase
      have hoa : otherThresholdSite s n m = a := by simpa [ha] using hotherErase
      simpa using hza.trans hoa.symm
  · rw [hcard]
    simp [hne.symm]

theorem thresholdSites_extendPrefix_stepPrefix (omega : StepPath) (n m : ℕ) :
    thresholdSites
        (trajectory (StoppedInsertion.extendPrefix (stepPrefix n omega))) n m =
      thresholdSites (trajectory omega) n m := by
  have hp := StoppedInsertion.trajectoryPrefix_stepPrefix omega n
  unfold thresholdSites visitedSites localTime
  rw [show pathPrefix
      (trajectory (StoppedInsertion.extendPrefix (stepPrefix n omega))) n =
      pathPrefix (trajectory omega) n by
    funext j
    exact congrFun hp j]

/-- The displacement from the current site to the canonical other threshold
site, expressed explicitly as a statistic of the first `n` increments. -/
noncomputable def secondFavoriteDisplacementAt (m n : ℕ) (omega : StepPath) : Point :=
  let w := StoppedInsertion.extendPrefix (stepPrefix n omega)
  otherThresholdSite (trajectory w) n m - trajectory w n

theorem secondFavoriteDisplacementAt_eq
    (m n : ℕ) (omega : StepPath) :
    secondFavoriteDisplacementAt m n omega =
      otherThresholdSite (trajectory omega) n m - trajectory omega n := by
  have hsite := thresholdSites_extendPrefix_stepPrefix omega n m
  have hend := trajectory_extendPrefix_stepPrefix_of_le omega n n le_rfl
  dsimp only [secondFavoriteDisplacementAt]
  unfold otherThresholdSite
  rw [hsite, hend]

theorem measurable_secondFavoriteDisplacementAt (m n : ℕ) :
    Measurable[incrementFiltration n]
      (secondFavoriteDisplacementAt m n) := by
  let F : (Fin n → Direction) → Point := fun u ↦
    otherThresholdSite (trajectory (StoppedInsertion.extendPrefix u)) n m -
      trajectory (StoppedInsertion.extendPrefix u) n
  have hF : Measurable[MeasurableSpace.comap (stepPrefix n) inferInstance]
      (fun omega : StepPath ↦ F (stepPrefix n omega)) :=
    (measurable_of_countable F).comp (comap_measurable (stepPrefix n))
  rw [incrementFiltration_apply]
  exact hF

/-- The same displacement evaluated at the second threshold-creation clock.
On the exceptional value `⊤` it uses the arbitrary prefix at time zero. -/
noncomputable def secondFavoriteDisplacement (m : ℕ) (omega : StepPath) : Point :=
  secondFavoriteDisplacementAt m ((levelTimeSteps m 2 omega).untopD 0) omega

theorem secondFavoriteDisplacement_at_levelTime_two
    {m n : ℕ} {omega : StepPath}
    (htime : levelTimeSteps m 2 omega = n) :
    secondFavoriteDisplacement m omega = secondFavoriteDisplacementAt m n omega := by
  have hvalue : (levelTimeSteps m 2 omega).untopD 0 = n := by
    rw [htime]
    exact WithTop.untopD_coe (0 : ℕ) n
  simp only [secondFavoriteDisplacement, hvalue]

/-- Each value fiber of the random second-favorite displacement is observable
at the clock `T_m^2`.  This atomwise formulation is exactly the one consumed by
the extended strong Markov theorem. -/
theorem isMeasurableAtWithTopStopping_secondFavoriteDisplacement_fiber
    (m : ℕ) (x : Point) :
    IsMeasurableAtWithTopStopping (levelTimeSteps m 2)
      {omega | secondFavoriteDisplacement m omega = x} := by
  intro n
  have heq :
      {omega | secondFavoriteDisplacement m omega = x} ∩
          {omega | levelTimeSteps m 2 omega = n} =
        {omega | secondFavoriteDisplacementAt m n omega = x} ∩
          {omega | levelTimeSteps m 2 omega = n} := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hdisp, htime⟩
      exact ⟨(secondFavoriteDisplacement_at_levelTime_two htime).symm.trans hdisp,
        htime⟩
    · rintro ⟨hdisp, htime⟩
      exact ⟨(secondFavoriteDisplacement_at_levelTime_two htime).trans hdisp,
        htime⟩
  rw [heq]
  exact (measurableSet_eq_fun (measurable_secondFavoriteDisplacementAt m n)
      measurable_const).inter
    ((isStoppingTime_levelTimeSteps m 2).measurableSet_eq n)

theorem isMeasurableAtWithTopStopping_levelEventTwo_displacement_fiber
    (m : ℕ) (x : Point) :
    IsMeasurableAtWithTopStopping (levelTimeSteps m 2)
      (levelEventSteps m 2 ∩ {omega | secondFavoriteDisplacement m omega = x}) := by
  have hM : IsMeasurableAtWithTopStopping (levelTimeSteps m 2)
      (levelEventSteps m 2) :=
    isMeasurableAtWithTopStopping_of_measurableSet_stopping
      (isStoppingTime_levelTimeSteps m 2)
      (measurableSet_levelEventSteps_at_current m 2)
  have hx := isMeasurableAtWithTopStopping_secondFavoriteDisplacement_fiber m x
  intro n
  have heq :
      (levelEventSteps m 2 ∩ {omega | secondFavoriteDisplacement m omega = x}) ∩
          {omega | levelTimeSteps m 2 omega = n} =
        (levelEventSteps m 2 ∩ {omega | levelTimeSteps m 2 omega = n}) ∩
          ({omega | secondFavoriteDisplacement m omega = x} ∩
            {omega | levelTimeSteps m 2 omega = n}) := by
    ext omega
    simp only [Set.mem_inter_iff]
    tauto
  rw [heq]
  exact (hM n).inter (hx n)

/-! ## The second-stage restart -/

/-- On the fiber where the random displacement is `x`, a fresh block avoiding
`0` and `x` creates the third favorite. -/
theorem secondStage_freshCreation_fiber_subset_levelEventThree
    (delta : ℝ) (m : ℕ) (hm : 2 ≤ m) (x : Point) :
    (levelEventSteps m 2 ∩ {omega | secondFavoriteDisplacement m omega = x}) ∩
        postWithTopStoppingBlock (levelTimeSteps m 2) (levelCutoffTime delta m) ⁻¹'
          freshCreationBlock delta m x ⊆
      levelEventSteps m 3 := by
  intro omega homega
  rcases homega with ⟨⟨hM, hdisp⟩, hfreshBlock⟩
  have htfinite : levelTimeSteps m 2 omega < ⊤ := hM.trans_le le_top
  have htne : levelTimeSteps m 2 omega ≠ ⊤ := WithTop.lt_top_iff_ne_top.mp htfinite
  lift levelTimeSteps m 2 omega to ℕ using htne with n htime
  have hcounts := levelEventSteps_at_value_thresholdCounts (by omega) htime.symm hM
  have hcreation := thresholdCreation_of_levelTimeSteps_eq (by omega) htime.symm
  have hcurrent : trajectory omega n ∈ thresholdSites (trajectory omega) n m :=
    position_mem_thresholdSites_of_creation (by omega) hcreation
  have hDcard : (thresholdSites (trajectory omega) n m).card = 2 := by
    simpa [thresholdCount] using hcounts.1
  have hD := thresholdSites_eq_current_insert_other
    (trajectory omega) n m hDcard hcurrent
  have hdispAt : secondFavoriteDisplacementAt m n omega = x :=
    (secondFavoriteDisplacement_at_levelTime_two htime.symm).symm.trans hdisp
  have hx : otherThresholdSite (trajectory omega) n m - trajectory omega n = x := by
    rw [← secondFavoriteDisplacementAt_eq m n omega]
    exact hdispAt
  have hfresh : shiftSteps n omega ∈ freshCreationSteps delta m x :=
    (postWithTopStoppingBlock_mem_freshCreationBlock_iff htime.symm delta m x).mp
      hfreshBlock
  have havold : ∀ j, 0 < j → j ≤ levelCutoffTime delta m →
      trajectory omega n + trajectory (shiftSteps n omega) j ∉
        thresholdSites (trajectory omega) n m := by
    intro j hjpos hjN
    rw [hD, Finset.mem_insert, Finset.mem_singleton]
    intro hold
    rcases hold with hcur | hother
    · have hzero : trajectory (shiftSteps n omega) j = 0 := by
        simpa only [add_eq_left] using hcur
      exact (hfresh.1 j hjpos hjN).1 hzero
    · have hoffset : trajectory (shiftSteps n omega) j = x := by
        rw [← hx]
        exact eq_sub_of_add_eq (by simpa [add_comm] using hother)
      exact (hfresh.1 j hjpos hjN).2 hoffset
  have hlevel : levelFavorite (trajectory omega) m 3 :=
    levelFavorite_succ_of_fresh_restart omega m 2 n (levelCutoffTime delta m)
      hm hcounts.1 hcounts.2 havold hfresh.2
  rw [levelEventSteps_eq_preimage m 3 (by omega)]
  exact hlevel

end Erdos1165.RestartBridge
