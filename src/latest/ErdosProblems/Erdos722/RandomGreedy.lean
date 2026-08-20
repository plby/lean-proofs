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
import ErdosProblems.Erdos722.AdaptiveChernoff
import Mathlib

/-!
# Abstract finite random-greedy selection

This is the probability-to-existence core of the rooted extension lemma.
At each history the next object is chosen uniformly from a nonempty finite
legal set.  Conditional indicator bounds and one finite exponential union
bound produce a concrete legal path with every tracked load below its cap.
-/

namespace Erdos722.RandomGreedy

open Finset
open Erdos722.AdaptiveChernoff

noncomputable section

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

/-- Every successive element belongs to the legal set exposed by the
preceding history. -/
def FollowsLegal (legal : List α → Finset α) : List α → List α → Prop
  | _history, [] => True
  | history, a :: rest =>
      a ∈ legal history ∧ FollowsLegal legal (history ++ [a]) rest

/-- The element at position `i` is legal after precisely the preceding
prefix has been appended to the initial history. -/
theorem FollowsLegal.get_mem
    (legal : List α → Finset α) {history path : List α}
    (h : FollowsLegal legal history path) (i : Fin path.length) :
    path.get i ∈ legal (history ++ path.take i.1) := by
  induction path generalizing history with
  | nil => exact Fin.elim0 i
  | cons a rest ih =>
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa [FollowsLegal] using h.1
      · have hrest := ih h.2 j
        simpa [List.take, List.append_assoc] using hrest

theorem FollowsLegal.append_iff
    (legal : List α → Finset α) (history xs ys : List α) :
    FollowsLegal legal history (xs ++ ys) ↔
      FollowsLegal legal history xs ∧
        FollowsLegal legal (history ++ xs) ys := by
  induction xs generalizing history with
  | nil => simp [FollowsLegal]
  | cons a xs ih =>
      simp only [List.cons_append, FollowsLegal]
      rw [ih]
      simp [List.append_assoc, and_assoc]

theorem FollowsLegal.prefix
    (legal : List α → Finset α) {history path pref : List α}
    (h : FollowsLegal legal history path) (hpref : pref <+: path) :
    FollowsLegal legal history pref := by
  obtain ⟨tail, rfl⟩ := hpref
  exact (FollowsLegal.append_iff legal history pref tail).mp h |>.1

lemma pathPositive_uniformStep_iff
    (legal : List α → Finset α)
    (hnonempty : ∀ history, (legal history).Nonempty) :
    ∀ history path,
      PathPositive (uniformStep legal) history path ↔
        FollowsLegal legal history path := by
  intro history path
  induction path generalizing history with
  | nil => simp [PathPositive, FollowsLegal]
  | cons a rest ih =>
      simp only [PathPositive, FollowsLegal]
      rw [uniformStep_pos_iff legal hnonempty, ih]

/-- Under uniform choice, an indicator's conditional mean is the exact
fraction of legal choices on which it fires. -/
lemma sum_uniformStep_mul_hitBit
    (legal : List α → Finset α)
    (history : List α)
    (hnonempty : (legal history).Nonempty)
    (hit : List α → α → Bool) :
    (∑ a : α, uniformStep legal history a * hitBit hit history a) =
      (((legal history).filter fun a ↦ hit history a).card : ℝ) /
        (legal history).card := by
  have hcard : ((legal history).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hnonempty)
  rw [div_eq_mul_inv]
  calc
    (∑ a : α, uniformStep legal history a * hitBit hit history a) =
        ∑ a ∈ legal history, ((legal history).card : ℝ)⁻¹ *
          (if hit history a then 1 else 0) := by
      calc
        (∑ a : α, uniformStep legal history a * hitBit hit history a) =
            ∑ a : α, if a ∈ legal history then
              ((legal history).card : ℝ)⁻¹ *
                (if hit history a then 1 else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro a _ha
          by_cases hal : a ∈ legal history <;>
            by_cases hh : hit history a <;>
              simp [uniformStep, hitBit, hal, hh]
        _ = ∑ a ∈ legal history, ((legal history).card : ℝ)⁻¹ *
              (if hit history a then 1 else 0) := by
          rw [← Finset.sum_filter]
          simp
    _ = (∑ a ∈ legal history, (if hit history a then 1 else 0 : ℝ)) *
          ((legal history).card : ℝ)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = (((legal history).filter fun a ↦ hit history a).card : ℝ) *
          ((legal history).card : ℝ)⁻¹ := by
      congr 1
      rw [Finset.card_filter]
      push_cast
      rfl

/-- Simultaneous random-greedy load theorem in its exact finite form. -/
theorem exists_legal_path_with_load_caps
    (legal : List α → Finset α)
    (hnonempty : ∀ history, (legal history).Nonempty)
    (hit : β → List α → α → Bool)
    (p : β → ℕ → ℝ) (hp : ∀ b i, 0 ≤ p b i)
    {t : ℝ} (ht : 0 ≤ t)
    (hhit : ∀ b history,
      (∑ a : α, uniformStep legal history a *
          hitBit (hit b) history a) ≤ p b history.length)
    {history : List α} {depth : ℕ} {cap : β → ℕ}
    (hsmall : (∑ b : β,
      Real.exp (-t * cap b) *
        Real.exp ((Real.exp t - 1) *
          adaptiveBudget (p b) history.length depth)) < 1) :
    ∃ path : List α, path.length = depth ∧
      FollowsLegal legal history path ∧
      ∀ b : β, pathHits (hit b) history path < cap b := by
  have hstepNonneg := uniformStep_nonneg legal
  have hstepSum := sum_uniformStep legal hnonempty
  obtain ⟨path, hlen, hpositive, hloads⟩ :=
    exists_path_of_sum_chernoff_lt_one (uniformStep legal)
      hstepNonneg hstepSum hit p hp ht hhit hsmall
  exact ⟨path, hlen,
    (pathPositive_uniformStep_iff legal hnonempty _ _).mp hpositive, hloads⟩

/-- Constant conditional budgets give the usual `depth * p` exponent. -/
lemma adaptiveBudget_const (c : ℝ) (start depth : ℕ) :
    adaptiveBudget (fun _ ↦ c) start depth = depth * c := by
  induction depth generalizing start with
  | zero => simp [adaptiveBudget]
  | succ depth ih =>
      simp [adaptiveBudget, ih]
      ring

/-! ## Guarding the process at its first bad history -/

/-- Hits split over concatenated paths, with the second part evaluated after
the history has been extended by the first. -/
lemma pathHits_append (hit : List α → α → Bool)
    (history xs ys : List α) :
    pathHits hit history (xs ++ ys) =
      pathHits hit history xs + pathHits hit (history ++ xs) ys := by
  induction xs generalizing history with
  | nil => simp [pathHits]
  | cons a xs ih =>
      simp only [List.cons_append, pathHits]
      rw [ih]
      have hh : (history ++ [a]) ++ xs = history ++ (a :: xs) := by
        simp [List.append_assoc]
      rw [hh]
      omega

lemma pathHits_le_of_prefix (hit : List α → α → Bool)
    (history : List α) {xs ys : List α} (hprefix : xs <+: ys) :
    pathHits hit history xs ≤ pathHits hit history ys := by
  obtain ⟨tail, rfl⟩ := hprefix
  rw [pathHits_append]
  omega

/-- Outside the good-history region use a fixed fallback choice. -/
def guardedLegal (legal : List α → Finset α) (good : List α → Prop)
    [DecidablePred good] (fallback : α) (history : List α) : Finset α :=
  if good history then legal history else {fallback}

/-- Loads are only recorded before the stopping time. -/
def guardedHit (good : List α → Prop) [DecidablePred good]
    (hit : β → List α → α → Bool) (b : β)
    (history : List α) (a : α) : Bool :=
  if good history then hit b history a else false

lemma guardedLegal_nonempty
    (legal : List α → Finset α) (good : List α → Prop)
    [DecidablePred good] (fallback : α)
    (hnonempty : ∀ history, good history → (legal history).Nonempty) :
    ∀ history, (guardedLegal legal good fallback history).Nonempty := by
  intro history
  by_cases hgood : good history
  · simpa [guardedLegal, hgood] using hnonempty history hgood
  · simp [guardedLegal, hgood]

/-- Exact finite stopping-time form of random greedy. Count estimates are
required only at good histories. Every prefix whose original loads stay
below the caps is assumed good, so the extracted path never uses the
fallback branch. -/
theorem exists_legal_path_with_load_caps_until_bad
    [Nonempty α]
    (legal : List α → Finset α) (good : List α → Prop)
    [DecidablePred good]
    (hit : β → List α → α → Bool)
    (p : β → ℕ → ℝ) (hp : ∀ b i, 0 ≤ p b i)
    {t : ℝ} (ht : 0 ≤ t)
    (hnonempty : ∀ history, good history → (legal history).Nonempty)
    (hhit : ∀ b history, good history →
      (∑ a : α, uniformStep legal history a *
          hitBit (hit b) history a) ≤ p b history.length)
    {history : List α} {depth : ℕ} {cap : β → ℕ}
    (hgood : ∀ pref : List α, pref.length ≤ depth →
      (∀ b : β, pathHits (hit b) history pref < cap b) →
      FollowsLegal legal history pref →
        good (history ++ pref))
    (hsmall : (∑ b : β,
      Real.exp (-t * cap b) *
        Real.exp ((Real.exp t - 1) *
          adaptiveBudget (p b) history.length depth)) < 1) :
    ∃ path : List α, path.length = depth ∧
      FollowsLegal legal history path ∧
      ∀ b : β, pathHits (hit b) history path < cap b := by
  classical
  let fallback : α := Classical.choice (inferInstance : Nonempty α)
  let guarded := guardedLegal legal good fallback
  let ghit := guardedHit good hit
  have hguardedNonempty : ∀ hist, (guarded hist).Nonempty := by
    exact guardedLegal_nonempty legal good fallback hnonempty
  have hguardedMean : ∀ b hist,
      (∑ a : α, uniformStep guarded hist a *
          hitBit (ghit b) hist a) ≤ p b hist.length := by
    intro b hist
    by_cases hg : good hist
    · have heq : guarded hist = legal hist := by
        simp [guarded, guardedLegal, hg]
      have hhitEq : ∀ a, ghit b hist a = hit b hist a := by
        intro a
        simp [ghit, guardedHit, hg]
      have huniformEq : uniformStep guarded hist =
          uniformStep legal hist := by
        funext a
        simp [uniformStep, heq]
      have hbitEq : hitBit (ghit b) hist = hitBit (hit b) hist := by
        funext a
        simp [hitBit, hhitEq a]
      rw [huniformEq, hbitEq]
      exact hhit b hist hg
    · have hzero : ∀ a, hitBit (ghit b) hist a = 0 := by
        intro a
        simp [ghit, guardedHit, hg, hitBit]
      simpa [hzero] using hp b hist.length
  obtain ⟨path, hlen, hfollowGuarded, hloadsGuarded⟩ :=
    exists_legal_path_with_load_caps guarded hguardedNonempty ghit p hp ht
      hguardedMean hsmall
  have hprefix : ∀ pref : List α, pref <+: path →
      (∀ b : β,
        pathHits (hit b) history pref =
          pathHits (ghit b) history pref) ∧
      FollowsLegal legal history pref ∧
      good (history ++ pref) := by
    intro pref hprefixPath
    induction pref using List.reverseRecOn with
    | nil =>
        have hcaps : ∀ b : β, pathHits (hit b) history [] < cap b := by
          intro b
          have hpositive : 0 < cap b := by
            exact Nat.zero_lt_of_lt (hloadsGuarded b)
          simpa [pathHits] using hpositive
        have hfollowNil : FollowsLegal legal history [] := by
          simp [FollowsLegal]
        exact ⟨fun b ↦ by simp [pathHits], hfollowNil,
          hgood [] (by simp) hcaps hfollowNil⟩
    | append_singleton pref a ih =>
        obtain ⟨tail, htail⟩ := hprefixPath
        have hprefixNew : pref ++ [a] <+: path := ⟨tail, htail⟩
        have hprefixOld : pref <+: path := by
          refine ⟨[a] ++ tail, ?_⟩
          simpa [List.append_assoc] using htail
        obtain ⟨heqOld, hfollowOld, hgoodOld⟩ := ih hprefixOld
        have hlenPrefix : (pref ++ [a]).length ≤ depth := by
          rw [← hlen]
          have hlength := congrArg List.length htail
          simp only [List.length_append, List.length_singleton] at hlength ⊢
          omega
        have hghit : ∀ b,
            ghit b (history ++ pref) a =
              hit b (history ++ pref) a := by
          intro b
          simp [ghit, guardedHit, hgoodOld]
        have heqNew : ∀ b : β,
            pathHits (hit b) history (pref ++ [a]) =
              pathHits (ghit b) history (pref ++ [a]) := by
          intro b
          rw [pathHits_append, pathHits_append, heqOld b]
          simp only [pathHits, List.append_nil, Nat.add_zero]
          have hbit : hitBit (hit b) (history ++ pref) a =
              hitBit (ghit b) (history ++ pref) a := by
            unfold hitBit
            rw [hghit b]
          exact congrArg (fun z ↦
            pathHits (ghit b) history pref + z) hbit
        have hcapsNew : ∀ b : β,
            pathHits (hit b) history (pref ++ [a]) < cap b := by
          intro b
          rw [heqNew b]
          exact (pathHits_le_of_prefix (ghit b) history hprefixNew).trans_lt
            (hloadsGuarded b)
        have hfollowGuardedNew :
            FollowsLegal guarded history (pref ++ [a]) :=
          FollowsLegal.prefix guarded hfollowGuarded hprefixNew
        have hlastGuarded : a ∈ guarded (history ++ pref) := by
          have hs := (FollowsLegal.append_iff guarded history pref [a]).mp
            hfollowGuardedNew
          simpa [FollowsLegal] using hs.2
        have hguardEq : guarded (history ++ pref) =
            legal (history ++ pref) := by
          simp [guarded, guardedLegal, hgoodOld]
        have hlastLegal : a ∈ legal (history ++ pref) := by
          rw [← hguardEq]
          exact hlastGuarded
        have hfollowNew : FollowsLegal legal history (pref ++ [a]) :=
          (FollowsLegal.append_iff legal history pref [a]).mpr
            ⟨hfollowOld, by simpa [FollowsLegal] using hlastLegal⟩
        exact ⟨heqNew, hfollowNew,
          hgood (pref ++ [a]) hlenPrefix hcapsNew hfollowNew⟩
  have hfollow : FollowsLegal legal history path :=
    (hprefix path List.prefix_rfl).2.1
  have heqFull := (hprefix path List.prefix_rfl).1
  exact ⟨path, hlen, hfollow,
    fun b ↦ (heqFull b).trans_lt (hloadsGuarded b)⟩

/-- Constant-budget version used by the rooted extension count. -/
theorem exists_legal_path_with_constant_load_caps
    (legal : List α → Finset α)
    (hnonempty : ∀ history, (legal history).Nonempty)
    (hit : β → List α → α → Bool)
    (p : β → ℝ) (hp : ∀ b, 0 ≤ p b)
    {t : ℝ} (ht : 0 ≤ t)
    (hhit : ∀ b history,
      (∑ a : α, uniformStep legal history a *
          hitBit (hit b) history a) ≤ p b)
    {history : List α} {depth : ℕ} {cap : β → ℕ}
    (hsmall : (∑ b : β,
      Real.exp (-t * cap b) *
        Real.exp ((Real.exp t - 1) * (depth * p b))) < 1) :
    ∃ path : List α, path.length = depth ∧
      FollowsLegal legal history path ∧
      ∀ b : β, pathHits (hit b) history path < cap b := by
  apply exists_legal_path_with_load_caps legal hnonempty hit
    (fun b _ ↦ p b) (fun b _ ↦ hp b) ht
    (fun b h ↦ hhit b h)
  simpa [adaptiveBudget_const] using hsmall

end

end Erdos722.RandomGreedy
