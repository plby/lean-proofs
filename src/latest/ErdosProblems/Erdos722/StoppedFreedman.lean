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
import ErdosProblems.Erdos722.FiniteFreedman
import ErdosProblems.Erdos722.RandomGreedy
import Mathlib

/-!
# Stopped finite variance processes

This module packages the stopping-time argument used by the clique-removal
analysis.  A family of barriers is guarded at the first history where any
barrier fails.  The transition-tree concentration theorem then extracts a
legal path on which no barrier ever fails.
-/

namespace Erdos722.StoppedFreedman

open Finset
open Erdos722.AdaptiveChernoff
open Erdos722.FiniteFreedman
open Erdos722.RandomGreedy

noncomputable section

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

/-- `GoodAlong good history path` says that `good` holds at the initial
history, after every selection, and at the terminal history. -/
def GoodAlong (good : List α → Prop) : List α → List α → Prop
  | history, [] => good history
  | history, a :: rest =>
      good history ∧ GoodAlong good (history ++ [a]) rest

/-- Every prefix of a history is good, expressed recursively from the root.
-/
def AllGood (good : List α → Prop) (history : List α) : Prop :=
  GoodAlong good [] history

lemma GoodAlong.initial (good : List α → Prop)
    {history path : List α} (h : GoodAlong good history path) :
    good history := by
  cases path with
  | nil => exact h
  | cons a rest => exact h.1

lemma GoodAlong.terminal (good : List α → Prop)
    {history path : List α} (h : GoodAlong good history path) :
    good (history ++ path) := by
  induction path generalizing history with
  | nil =>
      change good history at h
      simpa using h
  | cons a rest ih =>
      simpa [List.append_assoc] using ih h.2

lemma GoodAlong.append_iff (good : List α → Prop)
    (history xs ys : List α) :
    GoodAlong good history (xs ++ ys) ↔
      GoodAlong good history xs ∧ GoodAlong good (history ++ xs) ys := by
  induction xs generalizing history with
  | nil =>
      constructor
      · intro h
        exact ⟨h.initial good, by simpa using h⟩
      · exact fun h ↦ by simpa using h.2
  | cons a xs ih =>
      simp only [List.cons_append, GoodAlong]
      rw [ih]
      simp [List.append_assoc, and_assoc]

lemma AllGood.nil_iff (good : List α → Prop) :
    AllGood good [] ↔ good [] := by
  rfl

lemma AllGood.append_iff (good : List α → Prop)
    (xs ys : List α) :
    AllGood good (xs ++ ys) ↔
      AllGood good xs ∧ GoodAlong good xs ys := by
  simpa [AllGood] using GoodAlong.append_iff good [] xs ys

lemma AllGood.append_singleton_iff (good : List α → Prop)
    (history : List α) (a : α) :
    AllGood good (history ++ [a]) ↔
      AllGood good history ∧ good (history ++ [a]) := by
  constructor
  · intro h
    have hx := (AllGood.append_iff good history [a]).mp h
    have hga := hx.2
    change good history ∧ good (history ++ [a]) at hga
    exact ⟨hx.1, hga.2⟩
  · rintro ⟨hall, hnew⟩
    apply (AllGood.append_iff good history [a]).mpr
    refine ⟨hall, ?_⟩
    change good history ∧ good (history ++ [a])
    have hcurrent : good history := by
      simpa [AllGood] using (GoodAlong.terminal good hall)
    exact ⟨hcurrent, hnew⟩

lemma AllGood.current (good : List α → Prop) {history : List α}
    (h : AllGood good history) : good history := by
  simpa [AllGood] using (GoodAlong.terminal good h)

lemma AllGood.prefix (good : List α → Prop) {xs ys : List α}
    (h : AllGood good ys) (hp : xs <+: ys) : AllGood good xs := by
  obtain ⟨tail, rfl⟩ := hp
  exact (AllGood.append_iff good xs tail).mp h |>.1

lemma not_allGood_append (good : List α → Prop) {history : List α}
    (h : ¬ AllGood good history) (tail : List α) :
    ¬ AllGood good (history ++ tail) := by
  intro hall
  exact h ((AllGood.append_iff good history tail).mp hall).1

/-- One-step increment of a history observable. -/
def observableIncrement (Y : β → List α → ℝ) (b : β)
    (history : List α) (a : α) : ℝ :=
  Y b (history ++ [a]) - Y b history

/-- Stop every observable increment after the first bad prefix. -/
noncomputable def stoppedIncrement (good : List α → Prop) [DecidablePred good]
    (Y : β → List α → ℝ) (b : β)
    (history : List α) (a : α) : ℝ := by
  classical
  exact if AllGood good history then observableIncrement Y b history a else 0

lemma pathSum_stopped_eq_zero_of_not_allGood
    (good : List α → Prop) [DecidablePred good]
    (Y : β → List α → ℝ) (b : β)
    {history : List α} (hbad : ¬ AllGood good history) :
    ∀ tail : List α,
      pathSum (stoppedIncrement good Y b) history tail = 0 := by
  intro tail
  induction tail generalizing history with
  | nil => simp [pathSum]
  | cons a rest ih =>
      have hbadNext : ¬ AllGood good (history ++ [a]) :=
        not_allGood_append good hbad [a]
      simp [pathSum, stoppedIncrement, hbad, ih hbadNext]

/-- Simultaneous stopped-process theorem.  The observable itself defines the
good region `Y_b(history)<0`; conditional estimates are required only while
all earlier barriers hold. -/
theorem exists_legal_path_staying_below_zero
    [Nonempty α]
    (legal : List α → Finset α)
    (Y : β → List α → ℝ)
    (v : β → ℕ → ℝ) (hv : ∀ b i, 0 ≤ v b i)
    {t : ℝ} (ht : 0 ≤ t)
    (hinitial : ∀ b, Y b [] < 0)
    (hnonempty : ∀ history,
      AllGood (fun h ↦ ∀ b, Y b h < 0) history →
        (legal history).Nonempty)
    (hbound : ∀ b history a,
      AllGood (fun h ↦ ∀ c, Y c h < 0) history →
      |t * observableIncrement Y b history a| ≤ 1)
    (hmean : ∀ b history,
      AllGood (fun h ↦ ∀ c, Y c h < 0) history →
      (∑ a : α, uniformStep legal history a *
        observableIncrement Y b history a) ≤ 0)
    (hvar : ∀ b history,
      AllGood (fun h ↦ ∀ c, Y c h < 0) history →
      (∑ a : α, uniformStep legal history a *
        (observableIncrement Y b history a) ^ 2) ≤
          v b history.length)
    {depth : ℕ}
    (hsmall : (∑ b : β,
      Real.exp (-t * (-Y b [])) *
        Real.exp (t ^ 2 * varianceBudget (v b) 0 depth)) < 1) :
    ∃ path : List α, path.length = depth ∧
      FollowsLegal legal [] path ∧
      AllGood (fun h ↦ ∀ b, Y b h < 0) path := by
  classical
  let good : List α → Prop := fun h ↦ ∀ b, Y b h < 0
  let fallback : α := Classical.choice (inferInstance : Nonempty α)
  let guarded := guardedLegal legal (AllGood good) fallback
  let sinc : β → List α → α → ℝ := stoppedIncrement good Y
  have hguardedNonempty : ∀ history, (guarded history).Nonempty := by
    exact guardedLegal_nonempty legal (AllGood good) fallback hnonempty
  have hstepNonneg := uniformStep_nonneg guarded
  have hstepSum := sum_uniformStep guarded hguardedNonempty
  have hbound' : ∀ b history a, |t * sinc b history a| ≤ 1 := by
    intro b history a
    by_cases hall : AllGood good history
    · have hlegalEq : guarded history = legal history := by
        simp [guarded, guardedLegal, hall]
      simpa [sinc, stoppedIncrement, hall] using hbound b history a hall
    · simp [sinc, stoppedIncrement, hall]
  have hmean' : ∀ b history,
      (∑ a : α, uniformStep guarded history a * sinc b history a) ≤ 0 := by
    intro b history
    by_cases hall : AllGood good history
    · have hlegalEq : guarded history = legal history := by
        simp [guarded, guardedLegal, hall]
      have huniform : uniformStep guarded history =
          uniformStep legal history := by
        funext a
        simp [uniformStep, hlegalEq]
      rw [huniform]
      simpa [sinc, stoppedIncrement, hall] using hmean b history hall
    · simp [sinc, stoppedIncrement, hall]
  have hvar' : ∀ b history,
      (∑ a : α, uniformStep guarded history a * (sinc b history a) ^ 2) ≤
        v b history.length := by
    intro b history
    by_cases hall : AllGood good history
    · have hlegalEq : guarded history = legal history := by
        simp [guarded, guardedLegal, hall]
      have huniform : uniformStep guarded history =
          uniformStep legal history := by
        funext a
        simp [uniformStep, hlegalEq]
      rw [huniform]
      simpa [sinc, stoppedIncrement, hall] using hvar b history hall
    · simpa [sinc, stoppedIncrement, hall] using hv b history.length
  obtain ⟨path, hlen, hpositive, hsum⟩ :=
    exists_path_of_sum_variance_lt_one (uniformStep guarded)
      hstepNonneg hstepSum sinc v hv ht hbound' hmean' hvar'
      (history := []) (depth := depth) (threshold := fun b ↦ -Y b []) hsmall
  have hfollowGuarded : FollowsLegal guarded [] path :=
    (pathPositive_uniformStep_iff guarded hguardedNonempty [] path).mp hpositive
  have hprefix : ∀ pref : List α, pref <+: path →
      AllGood good pref ∧ FollowsLegal legal [] pref ∧
        ∀ b, pathSum (sinc b) [] pref = Y b pref - Y b [] := by
    intro pref hpref
    induction pref using List.reverseRecOn with
    | nil =>
        refine ⟨?_, by simp [FollowsLegal], ?_⟩
        · exact (AllGood.nil_iff good).mpr hinitial
        · intro b
          simp [pathSum]
    | append_singleton pref a ih =>
        have hprefOld : pref <+: path := by
          obtain ⟨tail, htail⟩ := hpref
          refine ⟨[a] ++ tail, ?_⟩
          simpa [List.append_assoc] using htail
        obtain ⟨hallOld, hfollowOld, hsumOld⟩ := ih hprefOld
        have hguardedPref : FollowsLegal guarded [] (pref ++ [a]) :=
          FollowsLegal.prefix guarded hfollowGuarded hpref
        have hlastGuarded : a ∈ guarded pref := by
          have hs := (FollowsLegal.append_iff guarded [] pref [a]).mp
            hguardedPref
          simpa [FollowsLegal] using hs.2
        have hguardEq : guarded pref = legal pref := by
          simp [guarded, guardedLegal, hallOld]
        have hlastLegal : a ∈ legal pref := by
          rw [← hguardEq]
          exact hlastGuarded
        have hfollowNew : FollowsLegal legal [] (pref ++ [a]) :=
          (FollowsLegal.append_iff legal [] pref [a]).mpr
            ⟨hfollowOld, by simpa [FollowsLegal] using hlastLegal⟩
        have hsumNew : ∀ b,
            pathSum (sinc b) [] (pref ++ [a]) =
              Y b (pref ++ [a]) - Y b [] := by
          intro b
          have hsinc : sinc b pref a = observableIncrement Y b pref a := by
            simp [sinc, stoppedIncrement, hallOld]
          rw [pathSum_append, hsumOld b]
          simp only [List.nil_append]
          rw [show pathSum (sinc b) pref [a] = sinc b pref a by
            simp [pathSum]]
          rw [hsinc]
          unfold observableIncrement
          ring
        have hgoodNew : good (pref ++ [a]) := by
          intro b
          by_contra hnot
          have hYnonneg : 0 ≤ Y b (pref ++ [a]) := le_of_not_gt hnot
          have hbadNew : ¬ AllGood good (pref ++ [a]) := by
            intro hallNew
            exact hnot (hallNew.current good b)
          obtain ⟨tail, htail⟩ := hpref
          have htailZero := pathSum_stopped_eq_zero_of_not_allGood
            good Y b hbadNew tail
          change pathSum (sinc b) (pref ++ [a]) tail = 0 at htailZero
          have hfull : pathSum (sinc b) [] path =
              pathSum (sinc b) [] (pref ++ [a]) := by
            rw [← htail, pathSum_append]
            simpa using congrArg
              (fun z ↦ pathSum (sinc b) [] (pref ++ [a]) + z) htailZero
          have hlt := hsum b
          rw [hfull, hsumNew b] at hlt
          linarith
        have hallNew : AllGood good (pref ++ [a]) :=
          (AllGood.append_singleton_iff good pref a).mpr
            ⟨hallOld, hgoodNew⟩
        exact ⟨hallNew, hfollowNew, hsumNew⟩
  exact ⟨path, hlen, (hprefix path List.prefix_rfl).2.1,
    (hprefix path List.prefix_rfl).1⟩

end

end Erdos722.StoppedFreedman
