/-
Copyright 2026 The Lean-Proofs Authors.

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
import ErdosProblems.Erdos722.StoppedFreedman
import Mathlib

/-!
# Critical-interval stopped processes

Dynamic concentration only needs negative drift while a counter is close
enough to its upper barrier to threaten it.  This file implements that
critical-interval device on the same finite transition trees as
`StoppedFreedman`: a tracker is started at each possible time and is stopped
as soon as the counter leaves its critical interval.
-/

namespace Erdos722.CriticalFreedman

open Finset
open Erdos722.AdaptiveChernoff
open Erdos722.FiniteFreedman
open Erdos722.RandomGreedy
open Erdos722.StoppedFreedman

noncomputable section

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

/-- From time `start` through the current history, the designated counter
has remained in the closed lower half of its critical interval. -/
def CriticalSince (Y : β → List α → ℝ) (window : β → ℝ)
    (b : β) (start : ℕ) (history : List α) : Prop :=
  start ≤ history.length ∧
    ∀ j ∈ Finset.Icc start history.length,
      -window b ≤ Y b (history.take j)

lemma CriticalSince.current
    {Y : β → List α → ℝ} {window : β → ℝ}
    {b : β} {start : ℕ} {history : List α}
    (h : CriticalSince Y window b start history) :
    -window b ≤ Y b history := by
  have hj := h.2 history.length
    (Finset.mem_Icc.mpr ⟨h.1, le_rfl⟩)
  simpa using hj

lemma CriticalSince.take
    {Y : β → List α → ℝ} {window : β → ℝ}
    {b : β} {start j : ℕ} {history : List α}
    (h : CriticalSince Y window b start history)
    (hsj : start ≤ j) (hjl : j ≤ history.length) :
    CriticalSince Y window b start (history.take j) := by
  have htakeLen : (history.take j).length = j := by
    simp [List.length_take, Nat.min_eq_left hjl]
  refine ⟨by simpa [htakeLen] using hsj, ?_⟩
  intro i hi
  have hidata := Finset.mem_Icc.mp hi
  have hij : i ≤ j := by simpa [htakeLen] using hidata.2
  have hil : i ≤ history.length := hij.trans hjl
  have hmain := h.2 i (Finset.mem_Icc.mpr ⟨hidata.1, hil⟩)
  rw [List.take_take, Nat.min_eq_left hij]
  exact hmain

lemma CriticalSince.append_singleton
    {Y : β → List α → ℝ} {window : β → ℝ}
    {b : β} {start : ℕ} {history : List α} {a : α}
    (h : CriticalSince Y window b start history)
    (hnew : -window b ≤ Y b (history ++ [a])) :
    CriticalSince Y window b start (history ++ [a]) := by
  refine ⟨by simpa using h.1.trans (Nat.le_succ _), ?_⟩
  intro j hj
  have hjdata := Finset.mem_Icc.mp hj
  by_cases hjold : j ≤ history.length
  · have hold := h.2 j (Finset.mem_Icc.mpr ⟨hjdata.1, hjold⟩)
    simpa [List.take_append_of_le_length hjold] using hold
  · have hjnew : j = history.length + 1 := by
      have hjle : j ≤ history.length + 1 := by
        simpa using hjdata.2
      omega
    subst j
    have hlen : (history ++ [a]).length = history.length + 1 := by simp
    rw [← hlen, List.take_length]
    exact hnew

/-- The actual observable increment while the selected start-time tracker
is live; it is zero before that time, after leaving the critical interval,
or after any barrier has already failed. -/
noncomputable def criticalIncrement
    (good : List α → Prop) [DecidablePred good]
    (Y : β → List α → ℝ) (window : β → ℝ)
    (b : β) (start : ℕ) (history : List α) (a : α) : ℝ := by
  classical
  exact if AllGood good history ∧
      CriticalSince Y window b start history then
    observableIncrement Y b history a
  else 0

lemma criticalIncrement_eq_of_live
    (good : List α → Prop) [DecidablePred good]
    (Y : β → List α → ℝ) (window : β → ℝ)
    (b : β) (start : ℕ) (history : List α) (a : α)
    (hall : AllGood good history)
    (hcrit : CriticalSince Y window b start history) :
    criticalIncrement good Y window b start history a =
      observableIncrement Y b history a := by
  simp [criticalIncrement, hall, hcrit]

lemma criticalIncrement_eq_zero_of_not_live
    (good : List α → Prop) [DecidablePred good]
    (Y : β → List α → ℝ) (window : β → ℝ)
    (b : β) (start : ℕ) (history : List α) (a : α)
    (h : ¬ (AllGood good history ∧
      CriticalSince Y window b start history)) :
    criticalIncrement good Y window b start history a = 0 := by
  simp [criticalIncrement, h]

lemma pathSum_criticalIncrement_before_start
    (good : List α → Prop) [DecidablePred good]
    (Y : β → List α → ℝ) (window : β → ℝ)
    (b : β) (start : ℕ) {path : List α}
    (hlen : path.length ≤ start) :
    pathSum (criticalIncrement good Y window b start) [] path = 0 := by
  induction path using List.reverseRecOn with
  | nil => simp [pathSum]
  | append_singleton path a ih =>
      simp only [List.length_append, List.length_singleton] at hlen
      have hlenOld : path.length ≤ start := by omega
      rw [pathSum_append, ih hlenOld]
      have hnot : ¬ CriticalSince Y window b start path := by
        intro hcrit
        have hlt : path.length < start := by omega
        exact (not_le_of_gt hlt) hcrit.1
      simp [pathSum, criticalIncrement, hnot]

lemma pathSum_criticalIncrement_eq_sub
    (good : List α → Prop) [DecidablePred good]
    (Y : β → List α → ℝ) (window : β → ℝ)
    (b : β) (start : ℕ) {path : List α}
    (hall : AllGood good path)
    (hcrit : CriticalSince Y window b start path) :
    pathSum (criticalIncrement good Y window b start) [] path =
      Y b path - Y b (path.take start) := by
  induction path using List.reverseRecOn with
  | nil =>
      have hs : start = 0 := by simpa using hcrit.1
      subst start
      simp [pathSum]
  | append_singleton path a ih =>
      by_cases hstart : start ≤ path.length
      · have hcritOld := hcrit.take hstart (by simp)
        have hcritOld' : CriticalSince Y window b start path := by
          simpa using hcritOld
        have hallOld := hall.prefix (good := good)
          (show path <+: path ++ [a] from List.prefix_append path [a])
        rw [pathSum_append, ih hallOld hcritOld']
        have hlive := criticalIncrement_eq_of_live good Y window b start
          path a hallOld hcritOld'
        simp only [pathSum, List.nil_append]
        rw [hlive]
        unfold observableIncrement
        have htake : (path ++ [a]).take start = path.take start := by
          exact List.take_append_of_le_length hstart
        rw [htake]
        ring
      · have hstartEq : start = path.length + 1 := by
          have := hcrit.1
          simp only [List.length_append, List.length_singleton] at this
          omega
        have hbefore : path.length ≤ start := by omega
        rw [pathSum_append,
          pathSum_criticalIncrement_before_start good Y window b start hbefore]
        have hnot : ¬ CriticalSince Y window b start path := by
          intro hc
          exact hstart hc.1
        simp only [List.nil_append]
        rw [show pathSum (criticalIncrement good Y window b start)
          path [a] = criticalIncrement good Y window b start path a by
            simp [pathSum]]
        rw [criticalIncrement_eq_zero_of_not_live good Y window b start
          path a (by simp [hnot])]
        have hlen : (path ++ [a]).length = path.length + 1 := by simp
        rw [hstartEq, ← hlen, List.take_length]
        ring

lemma pathSum_criticalIncrement_eq_zero_of_not_allGood
    (good : List α → Prop) [DecidablePred good]
    (Y : β → List α → ℝ) (window : β → ℝ)
    (b : β) (start : ℕ) {history : List α}
    (hbad : ¬ AllGood good history) :
    ∀ tail : List α,
      pathSum (criticalIncrement good Y window b start) history tail = 0 := by
  intro tail
  induction tail generalizing history with
  | nil => simp [pathSum]
  | cons a rest ih =>
      have hbadNext : ¬ AllGood good (history ++ [a]) :=
        not_allGood_append good hbad [a]
      have hzero := criticalIncrement_eq_zero_of_not_live
        good Y window b start history a (by simp [hbad])
      simp [pathSum, hzero, ih hbadNext]

/-- Cutting an increment off at level `depth` does not alter its path sum
along a continuation which ends by that level. -/
lemma pathSum_cutoff_eq
    (inc : List α → α → ℝ) (depth : ℕ)
    (history path : List α)
    (hlen : history.length + path.length ≤ depth) :
    pathSum (fun h a ↦ if h.length < depth then inc h a else 0)
        history path =
      pathSum inc history path := by
  induction path generalizing history with
  | nil => simp [pathSum]
  | cons a rest ih =>
      have hhistory : history.length < depth := by
        simp only [List.length_cons] at hlen
        omega
      simp only [pathSum, if_pos hhistory]
      have htail : (history ++ [a]).length + rest.length ≤ depth := by
        simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hlen
      rw [ih (history ++ [a]) htail]

/-- Totalized increment used on the finite transition tree.  On a good
history it is active only when that history is a legal prefix; on a bad
history the underlying critical increment is already zero. -/
noncomputable def legalActiveIncrement
    (good : List α → Prop) (legal : List α → Finset α)
    (depth : ℕ) (inc : List α → α → ℝ) :
    List α → α → ℝ := by
  classical
  exact fun history a ↦
    if history.length < depth ∧
        (AllGood good history → FollowsLegal legal [] history) ∧
        a ∈ legal history then
      inc history a else 0

/-- Along a good legal path, the implication used to totalize the stopped
increment is true at every source history. -/
lemma pathSum_active_eq_of_allGood_follows
    (good : List α → Prop) [DecidablePred good]
    (legal : List α → Finset α)
    (inc : List α → α → ℝ) (depth : ℕ)
    (path : List α)
    (hall : AllGood good path)
    (hfollow : FollowsLegal legal [] path)
    (hlen : path.length ≤ depth) :
    pathSum (legalActiveIncrement good legal depth inc) [] path =
      pathSum inc [] path := by
  induction path using List.reverseRecOn with
  | nil => simp [pathSum]
  | append_singleton path a ih =>
      have hallOld := hall.prefix (good := good)
        (show path <+: path ++ [a] from List.prefix_append path [a])
      have hfollowOld := FollowsLegal.prefix legal hfollow
        (show path <+: path ++ [a] from List.prefix_append path [a])
      have ha : a ∈ legal path := by
        have hs := (FollowsLegal.append_iff legal [] path [a]).mp hfollow
        simpa [FollowsLegal] using hs.2
      have hlenLt : path.length < depth := by
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      have hlenOld : path.length ≤ depth := hlenLt.le
      rw [pathSum_append, pathSum_append, ih hallOld hfollowOld hlenOld]
      simp [pathSum, legalActiveIncrement, hlenLt, hallOld, hfollowOld, ha]

/-- Once a prefix is bad, the implication-totalized critical increment is
zero on every continuation. -/
lemma pathSum_activeCritical_eq_zero_of_not_allGood
    (good : List α → Prop) [DecidablePred good]
    (legal : List α → Finset α)
    (Y : β → List α → ℝ) (window : β → ℝ)
    (b : β) (start depth : ℕ) {history : List α}
    (hbad : ¬ AllGood good history) :
    ∀ tail : List α,
      pathSum (legalActiveIncrement good legal depth
          (criticalIncrement good Y window b start))
        history tail = 0 := by
  intro tail
  induction tail generalizing history with
  | nil => simp [pathSum]
  | cons a rest ih =>
      have hbadNext : ¬ AllGood good (history ++ [a]) :=
        not_allGood_append good hbad [a]
      have hzero := criticalIncrement_eq_zero_of_not_live
        good Y window b start history a (by simp [hbad])
      simp [pathSum, legalActiveIncrement, hzero, hbad, ih hbadNext]

/-- Simultaneous critical-interval concentration.  Negative drift and
variance estimates are required only while the counter lies in its critical
interval `[-window,0)`.  Starting a tracker at every possible time costs the
finite factor `depth+1` visible in `hsmall`. -/
theorem exists_legal_path_staying_below_zero_critical
    [Nonempty α]
    (legal : List α → Finset α)
    (Y : β → List α → ℝ)
    (window jump : β → ℝ)
    (v : β → ℕ → ℝ) (hv : ∀ b i, 0 ≤ v b i)
    {t : ℝ} (ht : 0 ≤ t)
    (hjumpNonneg : ∀ b, 0 ≤ jump b)
    (hjumpLt : ∀ b, jump b < window b)
    (hinitial : ∀ b,
      Y b [] < 0 ∧ Y b [] ≤ -window b + jump b)
    {depth : ℕ}
    (hnonempty : ∀ history,
      history.length < depth →
      FollowsLegal legal [] history →
      AllGood (fun h ↦ ∀ b, Y b h < 0) history →
        (legal history).Nonempty)
    (hjump : ∀ b history a,
      history.length < depth →
      FollowsLegal legal [] history →
      AllGood (fun h ↦ ∀ c, Y c h < 0) history →
      a ∈ legal history →
      |observableIncrement Y b history a| ≤ jump b)
    (hbound : ∀ b history a,
      history.length < depth →
      FollowsLegal legal [] history →
      AllGood (fun h ↦ ∀ c, Y c h < 0) history →
      a ∈ legal history →
      -window b ≤ Y b history →
      |t * observableIncrement Y b history a| ≤ 1)
    (hmean : ∀ b history,
      history.length < depth →
      FollowsLegal legal [] history →
      AllGood (fun h ↦ ∀ c, Y c h < 0) history →
      -window b ≤ Y b history →
      (∑ a : α, uniformStep legal history a *
        observableIncrement Y b history a) ≤ 0)
    (hvar : ∀ b history,
      history.length < depth →
      FollowsLegal legal [] history →
      AllGood (fun h ↦ ∀ c, Y c h < 0) history →
      -window b ≤ Y b history →
      (∑ a : α, uniformStep legal history a *
        (observableIncrement Y b history a) ^ 2) ≤
          v b history.length)
    (hsmall : (∑ z : β × Fin (depth + 1),
      Real.exp (-t * (window z.1 - jump z.1)) *
        Real.exp (t ^ 2 * varianceBudget (v z.1) 0 depth)) < 1) :
    ∃ path : List α, path.length = depth ∧
      FollowsLegal legal [] path ∧
      AllGood (fun h ↦ ∀ b, Y b h < 0) path := by
  classical
  let good : List α → Prop := fun h ↦ ∀ b, Y b h < 0
  let fallback : α := Classical.choice (inferInstance : Nonempty α)
  let live : List α → Prop := fun history ↦
    AllGood good history ∧ FollowsLegal legal [] history ∧
      history.length < depth
  let guarded := guardedLegal legal live fallback
  let inc : (β × Fin (depth + 1)) → List α → α → ℝ := fun z ↦
    legalActiveIncrement good legal depth
      (criticalIncrement good Y window z.1 z.2.1)
  let vv : (β × Fin (depth + 1)) → ℕ → ℝ := fun z ↦ v z.1
  have hvv : ∀ z i, 0 ≤ vv z i := by
    intro z i
    exact hv z.1 i
  have hguardedNonempty : ∀ history, (guarded history).Nonempty := by
    apply guardedLegal_nonempty legal live fallback
    intro history hlive
    exact hnonempty history hlive.2.2 hlive.2.1 hlive.1
  have hstepNonneg := uniformStep_nonneg guarded
  have hstepSum := sum_uniformStep guarded hguardedNonempty
  have hbound' : ∀ z history a, |t * inc z history a| ≤ 1 := by
    intro z history a
    by_cases hdepth : history.length < depth
    · by_cases ha : a ∈ legal history
      · by_cases helig : AllGood good history →
            FollowsLegal legal [] history
        · by_cases hlive : AllGood good history ∧
              CriticalSince Y window z.1 z.2.1 history
          · rw [show inc z history a = observableIncrement Y z.1 history a by
              simp [inc, legalActiveIncrement, hdepth, helig, ha,
                criticalIncrement, hlive]]
            exact hbound z.1 history a hdepth (helig hlive.1)
              hlive.1 ha hlive.2.current
          · simp [inc, legalActiveIncrement, hdepth, helig, ha,
              criticalIncrement, hlive]
        · simp [inc, legalActiveIncrement, hdepth, helig]
      · simp [inc, legalActiveIncrement, ha]
    · simp [inc, legalActiveIncrement, hdepth]
  have hmean' : ∀ z history,
      (∑ a : α, uniformStep guarded history a * inc z history a) ≤ 0 := by
    intro z history
    by_cases hdepth : history.length < depth
    · by_cases helig : AllGood good history →
          FollowsLegal legal [] history
      · by_cases hlive : AllGood good history ∧
            CriticalSince Y window z.1 z.2.1 history
        · have hfollow := helig hlive.1
          have hguardEq : guarded history = legal history := by
            simp [guarded, guardedLegal, live, hlive.1, hfollow, hdepth]
          have huniform : uniformStep guarded history =
              uniformStep legal history := by
            funext a
            simp [uniformStep, hguardEq]
          rw [huniform]
          simpa [inc, legalActiveIncrement, uniformStep, hdepth, helig,
            criticalIncrement, hlive] using
            hmean z.1 history hdepth hfollow hlive.1 hlive.2.current
        · simp [inc, legalActiveIncrement, hdepth, helig, criticalIncrement, hlive]
      · simp [inc, legalActiveIncrement, hdepth, helig]
    · simp [inc, legalActiveIncrement, hdepth]
  have hvar' : ∀ z history,
      (∑ a : α, uniformStep guarded history a * (inc z history a) ^ 2) ≤
        vv z history.length := by
    intro z history
    by_cases hdepth : history.length < depth
    · by_cases helig : AllGood good history →
          FollowsLegal legal [] history
      · by_cases hlive : AllGood good history ∧
            CriticalSince Y window z.1 z.2.1 history
        · have hfollow := helig hlive.1
          have hguardEq : guarded history = legal history := by
            simp [guarded, guardedLegal, live, hlive.1, hfollow, hdepth]
          have huniform : uniformStep guarded history =
              uniformStep legal history := by
            funext a
            simp [uniformStep, hguardEq]
          rw [huniform]
          simpa [inc, legalActiveIncrement, uniformStep, hdepth, helig, vv,
            criticalIncrement, hlive] using
            hvar z.1 history hdepth hfollow hlive.1 hlive.2.current
        · simpa [inc, legalActiveIncrement, hdepth, helig, vv, criticalIncrement, hlive] using
            hv z.1 history.length
      · simpa [inc, legalActiveIncrement, hdepth, helig, vv] using hv z.1 history.length
    · simpa [inc, legalActiveIncrement, hdepth, vv] using hv z.1 history.length
  obtain ⟨path, hlen, hpositive, hsums⟩ :=
    exists_path_of_sum_variance_lt_one (uniformStep guarded)
      hstepNonneg hstepSum inc vv hvv ht hbound' hmean' hvar'
      (history := []) (depth := depth)
      (threshold := fun z ↦ window z.1 - jump z.1) hsmall
  have hfollowGuarded : FollowsLegal guarded [] path :=
    (pathPositive_uniformStep_iff guarded hguardedNonempty [] path).mp hpositive
  have hprefix : ∀ pref : List α, pref <+: path →
      AllGood good pref ∧ FollowsLegal legal [] pref ∧
      ∀ b, -window b ≤ Y b pref →
        ∃ s : Fin (depth + 1), s.1 ≤ pref.length ∧
          CriticalSince Y window b s.1 pref ∧
          Y b (pref.take s.1) ≤ -window b + jump b := by
    intro pref hpref
    induction pref using List.reverseRecOn with
    | nil =>
        refine ⟨(AllGood.nil_iff good).mpr (fun b ↦ (hinitial b).1),
          by simp [FollowsLegal], ?_⟩
        intro b hb
        let s : Fin (depth + 1) := ⟨0, by omega⟩
        refine ⟨s, by simp [s], ?_, ?_⟩
        · refine ⟨by simp [s], ?_⟩
          intro j hj
          have hj0 : j = 0 := by simpa [s] using Finset.mem_Icc.mp hj |>.2
          subst j
          simpa using hb
        · simpa [s] using (hinitial b).2
    | append_singleton pref a ih =>
        have hprefOld : pref <+: path := by
          obtain ⟨tail, htail⟩ := hpref
          refine ⟨[a] ++ tail, ?_⟩
          simpa [List.append_assoc] using htail
        obtain ⟨hallOld, hfollowOld, hactiveOld⟩ := ih hprefOld
        have hguardedPref : FollowsLegal guarded [] (pref ++ [a]) :=
          FollowsLegal.prefix guarded hfollowGuarded hpref
        have hlastGuarded : a ∈ guarded pref := by
          have hs := (FollowsLegal.append_iff guarded [] pref [a]).mp
            hguardedPref
          simpa [FollowsLegal] using hs.2
        have hprefLength : pref.length < depth := by
          have hlength := hpref.length_le
          rw [hlen] at hlength
          simp only [List.length_append, List.length_singleton] at hlength
          omega
        have hguardEq : guarded pref = legal pref := by
          simp [guarded, guardedLegal, live, hallOld, hfollowOld, hprefLength]
        have hlastLegal : a ∈ legal pref := by
          rw [← hguardEq]
          exact hlastGuarded
        have hfollowNew : FollowsLegal legal [] (pref ++ [a]) :=
          (FollowsLegal.append_iff legal [] pref [a]).mpr
            ⟨hfollowOld, by simpa [FollowsLegal] using hlastLegal⟩
        have hgoodNew : good (pref ++ [a]) := by
          intro b
          by_contra hnot
          have hYnew : 0 ≤ Y b (pref ++ [a]) := le_of_not_gt hnot
          by_cases hcriticalOld : -window b ≤ Y b pref
          · obtain ⟨s, hslen, hscrit, hsvalue⟩ :=
              hactiveOld b hcriticalOld
            have hsumPref := pathSum_criticalIncrement_eq_sub
              good Y window b s.1 hallOld hscrit
            have hlive := criticalIncrement_eq_of_live good Y window b s.1
              pref a hallOld hscrit
            have hsumNew :
                pathSum (criticalIncrement good Y window b s.1) []
                    (pref ++ [a]) =
                  Y b (pref ++ [a]) - Y b (pref.take s.1) := by
              rw [pathSum_append, hsumPref]
              simp only [List.nil_append, pathSum, hlive, observableIncrement]
              ring
            have hbadNew : ¬ AllGood good (pref ++ [a]) := by
              intro hallNew
              exact hnot (hallNew.current good b)
            obtain ⟨tail, htail⟩ := hpref
            have hprefActive : pathSum (inc (b, s)) [] pref =
                pathSum (criticalIncrement good Y window b s.1) [] pref := by
              simpa [inc] using pathSum_active_eq_of_allGood_follows
                good legal (criticalIncrement good Y window b s.1) depth
                  pref hallOld hfollowOld hprefLength.le
            have hincLast : inc (b, s) pref a =
                criticalIncrement good Y window b s.1 pref a := by
              simp [inc, legalActiveIncrement, hprefLength, hallOld, hfollowOld,
                hlastLegal]
            have hincNew : pathSum (inc (b, s)) [] (pref ++ [a]) =
                pathSum (criticalIncrement good Y window b s.1) []
                  (pref ++ [a]) := by
              rw [pathSum_append, pathSum_append, hprefActive]
              simp [pathSum, hincLast]
            have htailIncZero : pathSum (inc (b, s)) (pref ++ [a]) tail = 0 := by
              simpa [inc] using
                pathSum_activeCritical_eq_zero_of_not_allGood
                  good legal Y window b s.1 depth hbadNew tail
            have hfull : pathSum (inc (b, s)) [] path =
                pathSum (criticalIncrement good Y window b s.1) []
                  (pref ++ [a]) := by
              rw [← htail, pathSum_append]
              simp only [List.nil_append]
              rw [hincNew, htailIncZero, add_zero]
            have hlt := hsums (b, s)
            rw [hfull, hsumNew] at hlt
            linarith
          · have hj := hjump b pref a hprefLength hfollowOld hallOld hlastLegal
            unfold observableIncrement at hj
            have hwin := hjumpLt b
            have habs := (abs_le.mp (hj.trans_eq (by rfl))).2
            linarith
        have hallNew : AllGood good (pref ++ [a]) :=
          (AllGood.append_singleton_iff good pref a).mpr
            ⟨hallOld, hgoodNew⟩
        refine ⟨hallNew, hfollowNew, ?_⟩
        intro b hcriticalNew
        by_cases hcriticalOld : -window b ≤ Y b pref
        · obtain ⟨s, hslen, hscrit, hsvalue⟩ :=
            hactiveOld b hcriticalOld
          exact ⟨s, by
              simp only [List.length_append, List.length_singleton]
              omega,
            hscrit.append_singleton hcriticalNew, by
              simpa [List.take_append_of_le_length hslen] using hsvalue⟩
        · have hnewLen : (pref ++ [a]).length ≤ depth := by
            rw [← hlen]
            exact hpref.length_le
          let s : Fin (depth + 1) :=
            ⟨(pref ++ [a]).length, by omega⟩
          refine ⟨s, by simp [s], ?_, ?_⟩
          · refine ⟨by simp [s], ?_⟩
            intro j hj
            have hjEq : j = (pref ++ [a]).length := by
              have hm := Finset.mem_Icc.mp hj
              simpa [s] using le_antisymm hm.2 hm.1
            subst j
            rw [List.take_length]
            exact hcriticalNew
          · have hj := hjump b pref a hprefLength hfollowOld hallOld hlastLegal
            unfold observableIncrement at hj
            have hupperJump := (abs_le.mp hj).2
            have htake : (pref ++ [a]).take s.1 = pref ++ [a] := by
              simp [s]
            rw [htake]
            linarith
  exact ⟨path, hlen, (hprefix path List.prefix_rfl).2.1,
    (hprefix path List.prefix_rfl).1⟩

/-- The critical-interval theorem with one exponential rate per observable.
This is obtained by scaling each observable and invoking the common-rate
theorem at rate one. -/
theorem exists_legal_path_staying_below_zero_critical_indexed
    [Nonempty α]
    (legal : List α → Finset α)
    (Y : β → List α → ℝ)
    (window jump rate : β → ℝ)
    (v : β → ℕ → ℝ) (hv : ∀ b i, 0 ≤ v b i)
    (hrate : ∀ b, 0 < rate b)
    (hjumpNonneg : ∀ b, 0 ≤ jump b)
    (hjumpLt : ∀ b, jump b < window b)
    (hinitial : ∀ b,
      Y b [] < 0 ∧ Y b [] ≤ -window b + jump b)
    {depth : ℕ}
    (hnonempty : ∀ history,
      history.length < depth →
      FollowsLegal legal [] history →
      AllGood (fun h ↦ ∀ b, Y b h < 0) history →
        (legal history).Nonempty)
    (hjump : ∀ b history a,
      history.length < depth →
      FollowsLegal legal [] history →
      AllGood (fun h ↦ ∀ c, Y c h < 0) history →
      a ∈ legal history →
      |observableIncrement Y b history a| ≤ jump b)
    (hbound : ∀ b history a,
      history.length < depth →
      FollowsLegal legal [] history →
      AllGood (fun h ↦ ∀ c, Y c h < 0) history →
      a ∈ legal history →
      -window b ≤ Y b history →
      |rate b * observableIncrement Y b history a| ≤ 1)
    (hmean : ∀ b history,
      history.length < depth →
      FollowsLegal legal [] history →
      AllGood (fun h ↦ ∀ c, Y c h < 0) history →
      -window b ≤ Y b history →
      (∑ a : α, uniformStep legal history a *
        observableIncrement Y b history a) ≤ 0)
    (hvar : ∀ b history,
      history.length < depth →
      FollowsLegal legal [] history →
      AllGood (fun h ↦ ∀ c, Y c h < 0) history →
      -window b ≤ Y b history →
      (∑ a : α, uniformStep legal history a *
        (observableIncrement Y b history a) ^ 2) ≤
          v b history.length)
    (hsmall : (∑ z : β × Fin (depth + 1),
      Real.exp (-rate z.1 * (window z.1 - jump z.1)) *
        Real.exp ((rate z.1) ^ 2 *
          varianceBudget (v z.1) 0 depth)) < 1) :
    ∃ path : List α, path.length = depth ∧
      FollowsLegal legal [] path ∧
      AllGood (fun h ↦ ∀ b, Y b h < 0) path := by
  classical
  let Y' : β → List α → ℝ := fun b history ↦ rate b * Y b history
  let window' : β → ℝ := fun b ↦ rate b * window b
  let jump' : β → ℝ := fun b ↦ rate b * jump b
  let v' : β → ℕ → ℝ := fun b i ↦ (rate b) ^ 2 * v b i
  have hgood : ∀ history,
      (∀ b, Y' b history < 0) → ∀ b, Y b history < 0 := by
    intro history h b
    by_contra hn
    have hnonneg : 0 ≤ Y b history := le_of_not_gt hn
    have := mul_nonneg (hrate b).le hnonneg
    exact (not_lt_of_ge this) (h b)
  have hgoodAlong : ∀ (base path : List α),
      GoodAlong (fun h ↦ ∀ b, Y' b h < 0) base path →
        GoodAlong (fun h ↦ ∀ b, Y b h < 0) base path := by
    intro base path hall
    induction path generalizing base with
    | nil => exact hgood base hall
    | cons a rest ih =>
        exact ⟨hgood base hall.1, ih (base ++ [a]) hall.2⟩
  have hallGood : ∀ history,
      AllGood (fun h ↦ ∀ b, Y' b h < 0) history →
        AllGood (fun h ↦ ∀ b, Y b h < 0) history := by
    exact fun history hall ↦ hgoodAlong [] history hall
  have hinc (b : β) (history : List α) (a : α) :
      observableIncrement Y' b history a =
        rate b * observableIncrement Y b history a := by
    simp only [observableIncrement, Y']
    ring
  have hvariance : ∀ b i, 0 ≤ v' b i := by
    intro b i
    exact mul_nonneg (sq_nonneg _) (hv b i)
  have hinitial' : ∀ b,
      Y' b [] < 0 ∧ Y' b [] ≤ -window' b + jump' b := by
    intro b
    constructor
    · exact mul_neg_of_pos_of_neg (hrate b) (hinitial b).1
    · dsimp [Y', window', jump']
      have := mul_le_mul_of_nonneg_left (hinitial b).2 (hrate b).le
      nlinarith
  have hnonempty' : ∀ history,
      history.length < depth → FollowsLegal legal [] history →
      AllGood (fun h ↦ ∀ b, Y' b h < 0) history →
        (legal history).Nonempty := by
    intro history hlen hfollow hall
    exact hnonempty history hlen hfollow (hallGood history hall)
  have hjump' : ∀ b history a,
      history.length < depth → FollowsLegal legal [] history →
      AllGood (fun h ↦ ∀ c, Y' c h < 0) history →
      a ∈ legal history →
      |observableIncrement Y' b history a| ≤ jump' b := by
    intro b history a hlen hfollow hall ha
    rw [hinc, abs_mul, abs_of_pos (hrate b)]
    exact mul_le_mul_of_nonneg_left
      (hjump b history a hlen hfollow (hallGood history hall) ha)
      (hrate b).le
  have hcritical {b : β} {history : List α}
      (h : -window' b ≤ Y' b history) : -window b ≤ Y b history := by
    dsimp [window', Y'] at h
    apply le_of_mul_le_mul_left
      (show rate b * (-window b) ≤ rate b * Y b history by nlinarith)
      (hrate b)
  have hbound' : ∀ b history a,
      history.length < depth → FollowsLegal legal [] history →
      AllGood (fun h ↦ ∀ c, Y' c h < 0) history →
      a ∈ legal history → -window' b ≤ Y' b history →
      |(1 : ℝ) * observableIncrement Y' b history a| ≤ 1 := by
    intro b history a hlen hfollow hall ha hcrit
    simpa [hinc] using hbound b history a hlen hfollow
      (hallGood history hall) ha (hcritical hcrit)
  have hmean' : ∀ b history,
      history.length < depth → FollowsLegal legal [] history →
      AllGood (fun h ↦ ∀ c, Y' c h < 0) history →
      -window' b ≤ Y' b history →
      (∑ a : α, uniformStep legal history a *
        observableIncrement Y' b history a) ≤ 0 := by
    intro b history hlen hfollow hall hcrit
    have hm := hmean b history hlen hfollow (hallGood history hall)
      (hcritical hcrit)
    rw [show (∑ a : α, uniformStep legal history a *
        observableIncrement Y' b history a) =
      rate b * (∑ a : α, uniformStep legal history a *
        observableIncrement Y b history a) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [hinc]
        ring]
    exact mul_nonpos_of_nonneg_of_nonpos (hrate b).le hm
  have hvar' : ∀ b history,
      history.length < depth → FollowsLegal legal [] history →
      AllGood (fun h ↦ ∀ c, Y' c h < 0) history →
      -window' b ≤ Y' b history →
      (∑ a : α, uniformStep legal history a *
        (observableIncrement Y' b history a) ^ 2) ≤
          v' b history.length := by
    intro b history hlen hfollow hall hcrit
    have hvb := hvar b history hlen hfollow (hallGood history hall)
      (hcritical hcrit)
    dsimp [v']
    rw [show (∑ a : α, uniformStep legal history a *
        (observableIncrement Y' b history a) ^ 2) =
      (rate b) ^ 2 * (∑ a : α, uniformStep legal history a *
        (observableIncrement Y b history a) ^ 2) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [hinc]
        ring]
    exact mul_le_mul_of_nonneg_left hvb (sq_nonneg _)
  have hsmall' : (∑ z : β × Fin (depth + 1),
      Real.exp (-(1 : ℝ) * (window' z.1 - jump' z.1)) *
        Real.exp ((1 : ℝ) ^ 2 *
          varianceBudget (v' z.1) 0 depth)) < 1 := by
    rw [show (∑ z : β × Fin (depth + 1),
        Real.exp (-(1 : ℝ) * (window' z.1 - jump' z.1)) *
          Real.exp ((1 : ℝ) ^ 2 * varianceBudget (v' z.1) 0 depth)) =
      ∑ z : β × Fin (depth + 1),
        Real.exp (-rate z.1 * (window z.1 - jump z.1)) *
          Real.exp ((rate z.1) ^ 2 * varianceBudget (v z.1) 0 depth) by
      apply Finset.sum_congr rfl
      intro z _hz
      have hvscale : varianceBudget (v' z.1) 0 depth =
          (rate z.1) ^ 2 * varianceBudget (v z.1) 0 depth := by
        simpa [v'] using varianceBudget_const_mul (rate z.1 ^ 2) (v z.1) 0 depth
      rw [hvscale]
      dsimp [window', jump']
      congr 2 <;> ring]
    exact hsmall
  obtain ⟨path, hlen, hfollow, hall⟩ :=
    exists_legal_path_staying_below_zero_critical legal Y' window' jump' v'
      hvariance (by norm_num : (0 : ℝ) ≤ 1)
      (fun b ↦ mul_nonneg (hrate b).le (hjumpNonneg b))
      (fun b ↦ mul_lt_mul_of_pos_left (hjumpLt b) (hrate b))
      hinitial' hnonempty' hjump' hbound' hmean' hvar' hsmall'
  exact ⟨path, hlen, hfollow, hallGood path hall⟩

end

end Erdos722.CriticalFreedman
