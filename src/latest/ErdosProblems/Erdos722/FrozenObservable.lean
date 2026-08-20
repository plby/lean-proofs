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
import Mathlib

/-!
# Observables frozen when they become irrelevant

An edge-degree trajectory is only tracked until that edge is covered.  The
definitions below turn such a trajectory into an ordinary history observable
whose increments are exactly zero from the covering transition onward.
-/

namespace Erdos722.FrozenObservable

noncomputable section

variable {α : Type*}

/-- Evaluate `raw` until the next history is no longer relevant, then retain
the last relevant value forever. -/
def freezeAux (raw : List α → ℝ) (relevant : List α → Bool) :
    List α → List α → ℝ
  | history, [] => raw history
  | history, a :: rest =>
      if relevant (history ++ [a]) then
        freezeAux raw relevant (history ++ [a]) rest
      else raw history

/-- Rooted frozen observable. -/
def freezeValue (raw : List α → ℝ) (relevant : List α → Bool)
    (history : List α) : ℝ :=
  freezeAux raw relevant [] history

/-- Once relevance is lost it never returns. -/
def RelevanceMonotone (relevant : List α → Bool) : Prop :=
  ∀ history a, relevant (history ++ [a]) → relevant history

lemma relevant_prefix_of_append
    (relevant : List α → Bool) (hmono : RelevanceMonotone relevant) :
    ∀ history path, relevant (history ++ path) → relevant history := by
  intro history path
  induction path using List.reverseRecOn with
  | nil => simp
  | append_singleton path a ih =>
      intro hrel
      apply ih
      exact hmono (history ++ path) a (by
        simpa [List.append_assoc] using hrel)

lemma freezeAux_eq_raw_of_relevant
    (raw : List α → ℝ) (relevant : List α → Bool)
    (hmono : RelevanceMonotone relevant) :
    ∀ history path, relevant (history ++ path) →
      freezeAux raw relevant history path = raw (history ++ path) := by
  intro history path
  induction path generalizing history with
  | nil => simp [freezeAux]
  | cons a rest ih =>
      intro hrel
      have hrelNext : relevant (history ++ [a]) := by
        apply relevant_prefix_of_append relevant hmono (history ++ [a]) rest
        simpa [List.append_assoc] using hrel
      simp only [freezeAux, hrelNext, if_true]
      have htail : relevant ((history ++ [a]) ++ rest) := by
        simpa [List.append_assoc] using hrel
      simpa [List.append_assoc] using ih (history ++ [a]) htail

lemma freezeValue_eq_raw_of_relevant
    (raw : List α → ℝ) (relevant : List α → Bool)
    (hmono : RelevanceMonotone relevant)
    {history : List α} (hrel : relevant history) :
    freezeValue raw relevant history = raw history := by
  simpa [freezeValue] using
    freezeAux_eq_raw_of_relevant raw relevant hmono [] history hrel

lemma freezeAux_append_singleton
    (raw : List α → ℝ) (relevant : List α → Bool)
    (hmono : RelevanceMonotone relevant) :
    ∀ history path a,
      freezeAux raw relevant history (path ++ [a]) =
        if relevant (history ++ path) then
          if relevant (history ++ path ++ [a]) then
            raw (history ++ path ++ [a])
          else raw (history ++ path)
        else freezeAux raw relevant history path := by
  intro history path
  induction path generalizing history with
  | nil =>
      intro a
      by_cases hrel : relevant history
      · simp [freezeAux, hrel]
      · have hnext : ¬ relevant (history ++ [a]) := by
          intro h
          exact hrel (hmono history a h)
        simp [freezeAux, hrel, hnext]
  | cons b rest ih =>
      intro a
      by_cases hnext : relevant (history ++ [b])
      · simp only [List.cons_append, freezeAux, hnext, if_true]
        simpa [List.append_assoc] using ih (history ++ [b]) a
      · have hnotFinal : ¬ relevant (history ++ (b :: rest)) := by
          intro hfinal
          apply hnext
          apply relevant_prefix_of_append relevant hmono (history ++ [b]) rest
          simpa [List.append_assoc] using hfinal
        simp [freezeAux, hnext, hnotFinal]

/-- Exact one-step update of the frozen observable. -/
theorem freezeValue_append_singleton
    (raw : List α → ℝ) (relevant : List α → Bool)
    (hmono : RelevanceMonotone relevant) (history : List α) (a : α) :
    freezeValue raw relevant (history ++ [a]) =
      if relevant history then
        if relevant (history ++ [a]) then raw (history ++ [a])
        else raw history
      else freezeValue raw relevant history := by
  simpa [freezeValue] using
    freezeAux_append_singleton raw relevant hmono [] history a

theorem freezeValue_increment
    (raw : List α → ℝ) (relevant : List α → Bool)
    (hmono : RelevanceMonotone relevant) (history : List α) (a : α) :
    freezeValue raw relevant (history ++ [a]) -
        freezeValue raw relevant history =
      if relevant history ∧ relevant (history ++ [a]) then
        raw (history ++ [a]) - raw history
      else 0 := by
  rw [freezeValue_append_singleton raw relevant hmono]
  by_cases hrel : relevant history
  · have hcurrent := freezeValue_eq_raw_of_relevant raw relevant hmono hrel
    by_cases hnext : relevant (history ++ [a]) <;>
      simp [hrel, hnext, hcurrent]
  · simp [hrel]

end

end Erdos722.FrozenObservable
