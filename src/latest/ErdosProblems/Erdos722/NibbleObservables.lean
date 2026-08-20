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
import ErdosProblems.Erdos722.FrozenObservable
import ErdosProblems.Erdos722.NibbleDrift
import Mathlib

/-!
# Real-valued clique-removal observables

This file converts the exact natural-number update identities into the
frozen real observables used by the stopped finite-variance theorem.  Edge
counters stop on the transition which covers their edge; face counters keep
running until the prescribed terminal depth.
-/

namespace Erdos722.NibbleObservables

open Finset
open Erdos722.NibbleBasics
open Erdos722.NibbleProcess
open Erdos722.NibbleCounters
open Erdos722.NibbleDrift
open Erdos722.FrozenObservable
open Erdos722.AdaptiveChernoff

noncomputable section

variable {n q r : ℕ}

/-- Whether an edge is still a vertex of the residual design hypergraph. -/
def edgeRelevant (host : Finset (Finset (Fin n))) (r : ℕ)
    (e : Finset (Fin n)) (history : List (Finset (Fin n))) : Bool :=
  decide (e ∈ residualHost host r history)

lemma edgeRelevant_iff
    {host : Finset (Finset (Fin n))} {r : ℕ}
    {e : Finset (Fin n)} {history : List (Finset (Fin n))} :
    edgeRelevant host r e history ↔ e ∈ residualHost host r history := by
  simp [edgeRelevant]

lemma edgeRelevant_monotone
    (host : Finset (Finset (Fin n))) (r : ℕ) (e : Finset (Fin n)) :
    RelevanceMonotone (edgeRelevant host r e) := by
  intro history Q hnext
  rw [edgeRelevant_iff] at hnext ⊢
  rw [residualHost_update] at hnext
  exact Finset.mem_sdiff.mp hnext |>.1

/-- Frozen upper edge-degree deviation. -/
def upperDegreeObservable
    (host H : Finset (Finset (Fin n))) (r : ℕ)
    (upper : ℕ → ℝ) (e : Finset (Fin n))
    (history : List (Finset (Fin n))) : ℝ :=
  freezeValue
    (fun h ↦ (availableDegree H r h e : ℝ) - upper h.length)
    (edgeRelevant host r e) history

/-- Frozen lower edge-degree deviation. -/
def lowerDegreeObservable
    (host H : Finset (Finset (Fin n))) (r : ℕ)
    (lower : ℕ → ℝ) (e : Finset (Fin n))
    (history : List (Finset (Fin n))) : ℝ :=
  freezeValue
    (fun h ↦ lower h.length - (availableDegree H r h e : ℝ))
    (edgeRelevant host r e) history

/-- Upper residual lower-face-degree deviation. -/
def faceObservable
    (host : Finset (Finset (Fin n))) (r : ℕ)
    (cap : ℕ → ℝ) (f : Finset (Fin n))
    (history : List (Finset (Fin n))) : ℝ :=
  (residualFaceDegree host r history f : ℝ) - cap history.length

/-- Total available-clique deviation. -/
def cliqueObservable
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (profile : ℕ → ℝ) (history : List (Finset (Fin n))) : ℝ :=
  ((availableCliques H r history).card : ℝ) - profile history.length

/-- Weighted residual face-degree deviation.  Taking an increasing weight
is the source-faithful way to obtain negative drift at every face degree,
without assuming the face is itself close to its barrier. -/
def weightedFaceObservable
    (host : Finset (Finset (Fin n))) (r : ℕ)
    (weight cap : ℕ → ℝ) (f : Finset (Fin n))
    (history : List (Finset (Fin n))) : ℝ :=
  weight history.length * (residualFaceDegree host r history f : ℝ) -
    cap history.length

lemma upperDegreeObservable_eq_of_relevant
    {host H : Finset (Finset (Fin n))} {upper : ℕ → ℝ}
    {e : Finset (Fin n)} {history : List (Finset (Fin n))}
    (he : e ∈ residualHost host r history) :
    upperDegreeObservable host H r upper e history =
      (availableDegree H r history e : ℝ) - upper history.length := by
  apply freezeValue_eq_raw_of_relevant
    (hmono := edgeRelevant_monotone host r e)
  simpa [edgeRelevant] using he

lemma lowerDegreeObservable_eq_of_relevant
    {host H : Finset (Finset (Fin n))} {lower : ℕ → ℝ}
    {e : Finset (Fin n)} {history : List (Finset (Fin n))}
    (he : e ∈ residualHost host r history) :
    lowerDegreeObservable host H r lower e history =
      lower history.length - (availableDegree H r history e : ℝ) := by
  apply freezeValue_eq_raw_of_relevant
    (hmono := edgeRelevant_monotone host r e)
  simpa [edgeRelevant] using he

/-- Exact upper-observable increment.  Covering choices and all later
choices have increment zero. -/
theorem upperDegreeObservable_increment
    (host H : Finset (Finset (Fin n))) (r : ℕ)
    (upper : ℕ → ℝ) (e : Finset (Fin n))
    (history : List (Finset (Fin n))) (Q : Finset (Fin n)) :
    upperDegreeObservable host H r upper e (history ++ [Q]) -
        upperDegreeObservable host H r upper e history =
      if e ∈ residualHost host r history ∧
          e ∈ residualHost host r (history ++ [Q]) then
        -(deletedAtEdge H r history e Q).card -
          (upper (history.length + 1) - upper history.length)
      else 0 := by
  unfold upperDegreeObservable
  rw [freezeValue_increment
    (hmono := edgeRelevant_monotone host r e)]
  simp only [edgeRelevant, Bool.decide_coe, decide_eq_true_eq,
    List.length_append, List.length_singleton, Nat.add_comm]
  by_cases hrel : e ∈ residualHost host r history ∧
      e ∈ residualHost host r (history ++ [Q])
  · rw [if_pos hrel]
    rw [availableDegree_update, Nat.cast_sub
      (card_deletedAtEdge_le_availableDegree H r history e Q)]
    push_cast
    simp only [if_pos hrel]
    ring
  · simp [hrel]

/-- Exact lower-observable increment. -/
theorem lowerDegreeObservable_increment
    (host H : Finset (Finset (Fin n))) (r : ℕ)
    (lower : ℕ → ℝ) (e : Finset (Fin n))
    (history : List (Finset (Fin n))) (Q : Finset (Fin n)) :
    lowerDegreeObservable host H r lower e (history ++ [Q]) -
        lowerDegreeObservable host H r lower e history =
      if e ∈ residualHost host r history ∧
          e ∈ residualHost host r (history ++ [Q]) then
        (deletedAtEdge H r history e Q).card +
          (lower (history.length + 1) - lower history.length)
      else 0 := by
  unfold lowerDegreeObservable
  rw [freezeValue_increment
    (hmono := edgeRelevant_monotone host r e)]
  simp only [edgeRelevant, Bool.decide_coe, decide_eq_true_eq,
    List.length_append, List.length_singleton, Nat.add_comm]
  by_cases hrel : e ∈ residualHost host r history ∧
      e ∈ residualHost host r (history ++ [Q])
  · rw [if_pos hrel]
    rw [availableDegree_update, Nat.cast_sub
      (card_deletedAtEdge_le_availableDegree H r history e Q)]
    push_cast
    simp only [if_pos hrel]
    ring
  · simp [hrel]

/-- Exact face-observable increment on a legal choice. -/
theorem faceObservable_increment
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, blockEdges r Q ⊆ host)
    (cap : ℕ → ℝ) (f : Finset (Fin n))
    {history : List (Finset (Fin n))} {Q : Finset (Fin n)}
    (hQ : Q ∈ availableCliques H r history) :
    faceObservable host r cap f (history ++ [Q]) -
        faceObservable host r cap f history =
      -(faceLoss r Q f : ℝ) -
        (cap (history.length + 1) - cap history.length) := by
  unfold faceObservable
  rw [residualFaceDegree_update hH hQ,
    Nat.cast_sub (faceLoss_le_residualFaceDegree hH hQ)]
  simp only [List.length_append, List.length_singleton]
  push_cast
  ring

/-- Exact total-clique observable increment. -/
theorem cliqueObservable_increment
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (profile : ℕ → ℝ) (history : List (Finset (Fin n)))
    (Q : Finset (Fin n)) :
    cliqueObservable H r profile (history ++ [Q]) -
        cliqueObservable H r profile history =
      -(deletedCliques H r history Q).card -
        (profile (history.length + 1) - profile history.length) := by
  have hle : (deletedCliques H r history Q).card ≤
      (availableCliques H r history).card := by
    apply Finset.card_le_card
    intro P hP
    exact (Finset.mem_sdiff.mp hP).1
  unfold cliqueObservable
  rw [card_availableCliques_update, Nat.cast_sub hle]
  simp only [List.length_append, List.length_singleton]
  ring

theorem weightedFaceObservable_increment
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, blockEdges r Q ⊆ host)
    (weight cap : ℕ → ℝ) (f : Finset (Fin n))
    {history : List (Finset (Fin n))} {Q : Finset (Fin n)}
    (hQ : Q ∈ availableCliques H r history) :
    weightedFaceObservable host r weight cap f (history ++ [Q]) -
        weightedFaceObservable host r weight cap f history =
      (weight (history.length + 1) - weight history.length) *
          (residualFaceDegree host r history f : ℝ) -
        weight (history.length + 1) * faceLoss r Q f -
        (cap (history.length + 1) - cap history.length) := by
  unfold weightedFaceObservable
  rw [residualFaceDegree_update hH hQ,
    Nat.cast_sub (faceLoss_le_residualFaceDegree hH hQ)]
  simp only [List.length_append, List.length_singleton]
  ring

/-- Conditional mean of the frozen upper-degree increment. -/
theorem sum_uniformStep_mul_upperDegreeIncrement
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, blockEdges r Q ⊆ host)
    (upper : ℕ → ℝ) {e : Finset (Fin n)}
    {history : List (Finset (Fin n))}
    (he : e ∈ residualHost host r history)
    (hne : (availableCliques H r history).Nonempty) :
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        (upperDegreeObservable host H r upper e (history ++ [Q]) -
          upperDegreeObservable host H r upper e history)) =
      -((∑ Q ∈ availableCliques H r history,
          if e ∈ blockEdges r Q then 0
          else (deletedAtEdge H r history e Q).card +
            (upper (history.length + 1) - upper history.length) : ℝ) /
        (availableCliques H r history).card) := by
  have hcard : ((availableCliques H r history).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  -- On a legal choice, `e` survives precisely when the choice does not
  -- contain it.
  have hsurvive : ∀ Q ∈ availableCliques H r history,
      (e ∈ residualHost host r (history ++ [Q]) ↔
        e ∉ blockEdges r Q) := by
    intro Q hQ
    rw [residualHost_update]
    simp [he]
  calc
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        (upperDegreeObservable host H r upper e (history ++ [Q]) -
          upperDegreeObservable host H r upper e history)) =
        ∑ Q ∈ availableCliques H r history,
          ((availableCliques H r history).card : ℝ)⁻¹ *
            (if e ∈ blockEdges r Q then 0 else
              -(deletedAtEdge H r history e Q).card -
                (upper (history.length + 1) - upper history.length)) := by
      calc
        _ = ∑ Q : Finset (Fin n),
            if Q ∈ availableCliques H r history then
              ((availableCliques H r history).card : ℝ)⁻¹ *
                (if e ∈ blockEdges r Q then 0 else
                  -(deletedAtEdge H r history e Q).card -
                    (upper (history.length + 1) - upper history.length))
            else 0 := by
              apply Finset.sum_congr rfl
              intro Q _hQ
              by_cases hQa : Q ∈ availableCliques H r history
              · rw [upperDegreeObservable_increment]
                have hs := hsurvive Q hQa
                by_cases heQ : e ∈ blockEdges r Q
                · simp [uniformStep, hQa, heQ, he, hs]
                · simp [uniformStep, hQa, heQ, he, hs]
              · simp [uniformStep, hQa]
        _ = _ := by
          rw [← Finset.sum_filter]
          rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ = -((∑ Q ∈ availableCliques H r history,
          if e ∈ blockEdges r Q then 0
          else (deletedAtEdge H r history e Q).card +
            (upper (history.length + 1) - upper history.length) : ℝ) /
        (availableCliques H r history).card) := by
      rw [div_eq_mul_inv]
      calc
        (∑ Q ∈ availableCliques H r history,
          ((availableCliques H r history).card : ℝ)⁻¹ *
            (if e ∈ blockEdges r Q then 0 else
              -(deletedAtEdge H r history e Q).card -
                (upper (history.length + 1) - upper history.length))) =
            ((availableCliques H r history).card : ℝ)⁻¹ *
              ∑ Q ∈ availableCliques H r history,
                (if e ∈ blockEdges r Q then 0 else
                  -(deletedAtEdge H r history e Q).card -
                    (upper (history.length + 1) - upper history.length)) := by
                      rw [Finset.mul_sum]
        _ = _ := by
          have hsum :
              (∑ Q ∈ availableCliques H r history,
                (if e ∈ blockEdges r Q then 0 else
                  -(deletedAtEdge H r history e Q).card -
                    (upper (history.length + 1) - upper history.length))) =
                -(∑ Q ∈ availableCliques H r history,
                  (if e ∈ blockEdges r Q then 0 else
                    (deletedAtEdge H r history e Q).card +
                      (upper (history.length + 1) - upper history.length))) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro Q hQ
            by_cases heQ : e ∈ blockEdges r Q <;> simp [heQ] <;> ring
          rw [hsum]
          ring

/-- Conditional mean of the frozen lower-degree increment. -/
theorem sum_uniformStep_mul_lowerDegreeIncrement
    {host H : Finset (Finset (Fin n))}
    (lower : ℕ → ℝ) {e : Finset (Fin n)}
    {history : List (Finset (Fin n))}
    (he : e ∈ residualHost host r history)
    (hne : (availableCliques H r history).Nonempty) :
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        (lowerDegreeObservable host H r lower e (history ++ [Q]) -
          lowerDegreeObservable host H r lower e history)) =
      ((∑ Q ∈ availableCliques H r history,
          if e ∈ blockEdges r Q then 0
          else (deletedAtEdge H r history e Q).card +
            (lower (history.length + 1) - lower history.length) : ℝ) /
        (availableCliques H r history).card) := by
  have hsurvive : ∀ Q ∈ availableCliques H r history,
      (e ∈ residualHost host r (history ++ [Q]) ↔
        e ∉ blockEdges r Q) := by
    intro Q hQ
    rw [residualHost_update]
    simp [he]
  calc
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        (lowerDegreeObservable host H r lower e (history ++ [Q]) -
          lowerDegreeObservable host H r lower e history)) =
        ∑ Q ∈ availableCliques H r history,
          ((availableCliques H r history).card : ℝ)⁻¹ *
            (if e ∈ blockEdges r Q then 0 else
              (deletedAtEdge H r history e Q).card +
                (lower (history.length + 1) - lower history.length)) := by
      calc
        _ = ∑ Q : Finset (Fin n),
            if Q ∈ availableCliques H r history then
              ((availableCliques H r history).card : ℝ)⁻¹ *
                (if e ∈ blockEdges r Q then 0 else
                  (deletedAtEdge H r history e Q).card +
                    (lower (history.length + 1) - lower history.length))
            else 0 := by
              apply Finset.sum_congr rfl
              intro Q _hQ
              by_cases hQa : Q ∈ availableCliques H r history
              · rw [lowerDegreeObservable_increment]
                have hs := hsurvive Q hQa
                by_cases heQ : e ∈ blockEdges r Q
                · simp [uniformStep, hQa, heQ, he, hs]
                · simp [uniformStep, hQa, heQ, he, hs]
              · simp [uniformStep, hQa]
        _ = _ := by
          rw [← Finset.sum_filter]
          rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ = ((∑ Q ∈ availableCliques H r history,
          if e ∈ blockEdges r Q then 0
          else (deletedAtEdge H r history e Q).card +
            (lower (history.length + 1) - lower history.length) : ℝ) /
        (availableCliques H r history).card) := by
      rw [div_eq_mul_inv]
      rw [← Finset.mul_sum]
      ring

/-- Conditional mean of a face deviation. -/
theorem sum_uniformStep_mul_faceIncrement
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, blockEdges r Q ⊆ host)
    (cap : ℕ → ℝ) (f : Finset (Fin n))
    {history : List (Finset (Fin n))}
    (hne : (availableCliques H r history).Nonempty) :
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        (faceObservable host r cap f (history ++ [Q]) -
          faceObservable host r cap f history)) =
      -((∑ Q ∈ availableCliques H r history,
          faceLoss r Q f : ℝ) /
        (availableCliques H r history).card) -
      (cap (history.length + 1) - cap history.length) := by
  have hcard : ((availableCliques H r history).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  calc
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        (faceObservable host r cap f (history ++ [Q]) -
          faceObservable host r cap f history)) =
        ∑ Q ∈ availableCliques H r history,
          ((availableCliques H r history).card : ℝ)⁻¹ *
            (-(faceLoss r Q f : ℝ) -
              (cap (history.length + 1) - cap history.length)) := by
      calc
        _ = ∑ Q : Finset (Fin n),
            if Q ∈ availableCliques H r history then
              ((availableCliques H r history).card : ℝ)⁻¹ *
                (-(faceLoss r Q f : ℝ) -
                  (cap (history.length + 1) - cap history.length))
            else 0 := by
              apply Finset.sum_congr rfl
              intro Q _hQ
              by_cases hQa : Q ∈ availableCliques H r history
              · rw [faceObservable_increment hH cap f hQa]
                simp [uniformStep, hQa]
              · simp [uniformStep, hQa]
        _ = _ := by
          rw [← Finset.sum_filter]
          rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ = -((∑ Q ∈ availableCliques H r history,
          faceLoss r Q f : ℝ) /
        (availableCliques H r history).card) -
      (cap (history.length + 1) - cap history.length) := by
      rw [div_eq_mul_inv, ← Finset.mul_sum]
      have hcount :
          (∑ _Q ∈ availableCliques H r history,
            (cap (history.length + 1) - cap history.length)) =
            (availableCliques H r history).card *
              (cap (history.length + 1) - cap history.length) := by
                simp
                ring
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, hcount]
      field_simp

/-- Conditional mean of the total-clique deviation. -/
theorem sum_uniformStep_mul_cliqueIncrement
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (profile : ℕ → ℝ) {history : List (Finset (Fin n))}
    (hne : (availableCliques H r history).Nonempty) :
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        (cliqueObservable H r profile (history ++ [Q]) -
          cliqueObservable H r profile history)) =
      -((∑ Q ∈ availableCliques H r history,
          (deletedCliques H r history Q).card : ℝ) /
        (availableCliques H r history).card) -
      (profile (history.length + 1) - profile history.length) := by
  have hcard : ((availableCliques H r history).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  calc
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        (cliqueObservable H r profile (history ++ [Q]) -
          cliqueObservable H r profile history)) =
        ∑ Q ∈ availableCliques H r history,
          ((availableCliques H r history).card : ℝ)⁻¹ *
            (-(deletedCliques H r history Q).card -
              (profile (history.length + 1) - profile history.length)) := by
      calc
        _ = ∑ Q : Finset (Fin n),
            if Q ∈ availableCliques H r history then
              ((availableCliques H r history).card : ℝ)⁻¹ *
                (-(deletedCliques H r history Q).card -
                  (profile (history.length + 1) - profile history.length))
            else 0 := by
              apply Finset.sum_congr rfl
              intro Q _hQ
              by_cases hQa : Q ∈ availableCliques H r history
              · rw [cliqueObservable_increment]
                simp [uniformStep, hQa]
              · simp [uniformStep, hQa]
        _ = _ := by
          rw [← Finset.sum_filter]
          rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ = -((∑ Q ∈ availableCliques H r history,
          (deletedCliques H r history Q).card : ℝ) /
        (availableCliques H r history).card) -
      (profile (history.length + 1) - profile history.length) := by
      rw [div_eq_mul_inv, ← Finset.mul_sum]
      have hcount :
          (∑ _Q ∈ availableCliques H r history,
            (profile (history.length + 1) - profile history.length)) =
            (availableCliques H r history).card *
              (profile (history.length + 1) - profile history.length) := by
                simp
                ring
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, hcount]
      field_simp

/-- Conditional mean of the weighted face deviation. -/
theorem sum_uniformStep_mul_weightedFaceIncrement
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, blockEdges r Q ⊆ host)
    (weight cap : ℕ → ℝ) (f : Finset (Fin n))
    {history : List (Finset (Fin n))}
    (hne : (availableCliques H r history).Nonempty) :
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        (weightedFaceObservable host r weight cap f (history ++ [Q]) -
          weightedFaceObservable host r weight cap f history)) =
      (weight (history.length + 1) - weight history.length) *
          (residualFaceDegree host r history f : ℝ) -
        weight (history.length + 1) *
          ((∑ Q ∈ availableCliques H r history,
              faceLoss r Q f : ℝ) /
            (availableCliques H r history).card) -
        (cap (history.length + 1) - cap history.length) := by
  have hface := sum_uniformStep_mul_faceLoss H r history hne f
  calc
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        (weightedFaceObservable host r weight cap f (history ++ [Q]) -
          weightedFaceObservable host r weight cap f history)) =
        ∑ Q : Finset (Fin n),
          uniformStep (availableCliques H r) history Q *
            ((weight (history.length + 1) - weight history.length) *
                (residualFaceDegree host r history f : ℝ) -
              weight (history.length + 1) * faceLoss r Q f -
              (cap (history.length + 1) - cap history.length)) := by
      apply Finset.sum_congr rfl
      intro Q hQuniv
      by_cases hQa : Q ∈ availableCliques H r history
      · rw [weightedFaceObservable_increment hH weight cap f hQa]
      · have hzero : uniformStep (availableCliques H r) history Q = 0 := by
          simp [uniformStep, hQa]
        simp [hzero]
    _ = (weight (history.length + 1) - weight history.length) *
          (residualFaceDegree host r history f : ℝ) -
        weight (history.length + 1) *
          ((∑ Q ∈ availableCliques H r history,
              faceLoss r Q f : ℝ) /
            (availableCliques H r history).card) -
        (cap (history.length + 1) - cap history.length) := by
      rw [← hface]
      have hone : (∑ Q : Finset (Fin n),
          uniformStep (availableCliques H r) history Q) = 1 := by
        have hcard : (0 : ℝ) < (availableCliques H r history).card := by
          exact_mod_cast Finset.card_pos.mpr hne
        calc
          (∑ Q : Finset (Fin n),
              uniformStep (availableCliques H r) history Q) =
              ∑ Q : Finset (Fin n),
                if Q ∈ availableCliques H r history then
                  ((availableCliques H r history).card : ℝ)⁻¹ else 0 := by
                  apply Finset.sum_congr rfl
                  intro Q hQ
                  by_cases hQa : Q ∈ availableCliques H r history <;>
                    simp [uniformStep, hQa]
          _ =
              ∑ Q ∈ availableCliques H r history,
                ((availableCliques H r history).card : ℝ)⁻¹ := by
                  rw [← Finset.sum_filter]
                  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
          _ = 1 := by simp [hcard.ne']
      have hconst (c : ℝ) :
          (∑ Q : Finset (Fin n),
            uniformStep (availableCliques H r) history Q * c) = c := by
        change (∑ Q ∈ (Finset.univ : Finset (Finset (Fin n))),
          uniformStep (availableCliques H r) history Q * c) = c
        rw [← Finset.sum_mul]
        change (∑ Q : Finset (Fin n),
          uniformStep (availableCliques H r) history Q) * c = c
        rw [hone, one_mul]
      have hloss :
          (∑ Q : Finset (Fin n),
            uniformStep (availableCliques H r) history Q *
              (weight (history.length + 1) * faceLoss r Q f)) =
            weight (history.length + 1) *
              ∑ Q : Finset (Fin n),
                uniformStep (availableCliques H r) history Q *
                  faceLoss r Q f := by
        calc
          (∑ Q : Finset (Fin n),
              uniformStep (availableCliques H r) history Q *
                (weight (history.length + 1) * faceLoss r Q f)) =
              ∑ Q : Finset (Fin n),
                weight (history.length + 1) *
                  (uniformStep (availableCliques H r) history Q *
                    faceLoss r Q f) := by
                      apply Finset.sum_congr rfl
                      intro Q hQ
                      ring
          _ = _ := by
            change (∑ Q ∈ (Finset.univ : Finset (Finset (Fin n))),
              weight (history.length + 1) *
                (uniformStep (availableCliques H r) history Q *
                  faceLoss r Q f)) = _
            rw [← Finset.mul_sum]
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [hloss, hconst, hconst, hconst]

end

end Erdos722.NibbleObservables
