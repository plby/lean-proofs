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
import ErdosProblems.Erdos722.NibbleFaceDrift
import Mathlib

/-!
# Finite drift interfaces for the clique-removal counters

The combinatorial Bonferroni estimates in `NibbleDrift` bound the deletion
numerators.  This file converts those bounds, without asymptotic notation,
into nonpositive conditional means for the upper/lower edge and total-clique
observables.  Each theorem ends in one displayed scalar inequality; the
polynomial profiles discharge those inequalities in the next layer.
-/

namespace Erdos722.NibbleEdgeDrift

open Finset
open Erdos722.NibbleBasics
open Erdos722.NibbleProcess
open Erdos722.NibbleCounters
open Erdos722.NibbleDrift
open Erdos722.NibbleObservables
open Erdos722.AdaptiveChernoff

noncomputable section

variable {n q r : ℕ}

lemma sum_if_not_add_const
    {A : Finset (Finset (Fin n))} (p : Finset (Fin n) → Prop)
    [DecidablePred p] (d : Finset (Fin n) → ℕ) (c : ℝ) :
    (∑ Q ∈ A, if p Q then 0 else (d Q : ℝ) + c) =
      (∑ Q ∈ A, if p Q then 0 else (d Q : ℝ)) +
        ((A.filter fun Q ↦ ¬ p Q).card : ℝ) * c := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert Q A hQA ih =>
      by_cases hp : p Q
      · simp only [Finset.sum_insert hQA, if_pos hp, zero_add]
        rw [ih]
        simp [Finset.filter_insert, hQA, hp]
      · simp only [Finset.sum_insert hQA, if_neg hp]
        rw [ih]
        simp [Finset.filter_insert, hQA, hp]
        ring

lemma card_filter_not_eq_sub
    {A : Finset (Finset (Fin n))} (p : Finset (Fin n) → Prop)
    [DecidablePred p] :
    (A.filter fun Q ↦ ¬ p Q).card = A.card - (A.filter p).card := by
  have h := Finset.card_filter_add_card_filter_not (s := A) p
  omega

lemma sum_deletedAtEdge_add_delta
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (e : Finset (Fin n)) (δ : ℝ) :
    (∑ Q ∈ availableCliques H r history,
      if e ∈ blockEdges r Q then 0
      else (deletedAtEdge H r history e Q).card + δ) =
      (∑ Q ∈ availableCliques H r history,
        if e ∈ blockEdges r Q then 0
        else (deletedAtEdge H r history e Q).card : ℝ) +
      ((availableCliques H r history).card -
        availableDegree H r history e : ℕ) * δ := by
  rw [sum_if_not_add_const]
  rw [card_filter_not_eq_sub]
  rfl

/-- Lower deletion estimate plus one scalar inequality gives upper-degree
negative drift. -/
theorem sum_uniformStep_mul_upperDegreeIncrement_nonpos
    (hr : 0 < r) (hrq : r < q)
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    {history : List (Finset (Fin n))} {e : Finset (Fin n)}
    (he : e ∈ residualHost host r history) (hecard : e.card = r)
    (hne : (availableCliques H r history).Nonempty)
    (upper : ℕ → ℝ) (L : ℕ)
    (hlower : ∀ f ∈ residualHost host r history,
      L ≤ availableDegree H r history f)
    (hscalar : (0 : ℝ) ≤
      ((availableDegree H r history e * (Nat.choose q r - 1) *
          (L - n ^ (q - r - 1)) : ℕ) : ℝ) -
        ((availableDegree H r history e * (Nat.choose q r - 1) ^ 2 *
          n ^ (q - r - 1) : ℕ) : ℝ) +
        ((availableCliques H r history).card -
          availableDegree H r history e : ℕ) *
          (upper (history.length + 1) - upper history.length)) :
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        (upperDegreeObservable host H r upper e (history ++ [Q]) -
          upperDegreeObservable host H r upper e history)) ≤ 0 := by
  rw [sum_uniformStep_mul_upperDegreeIncrement
    (fun Q hQ ↦ (hH Q hQ).2) upper he hne]
  rw [sum_deletedAtEdge_add_delta]
  let S : ℕ := ∑ Q ∈ availableCliques H r history,
    if e ∈ blockEdges r Q then 0
    else (deletedAtEdge H r history e Q).card
  have hdel := degree_mul_other_mul_lower_le_sum_deleted_add_error
    hr hrq hH history hecard L hlower
  have hdelReal :
      ((availableDegree H r history e * (Nat.choose q r - 1) *
          (L - n ^ (q - r - 1)) : ℕ) : ℝ) ≤
        (S : ℝ) +
          ((availableDegree H r history e *
            (Nat.choose q r - 1) ^ 2 * n ^ (q - r - 1) : ℕ) : ℝ) := by
    dsimp [S]
    exact_mod_cast hdel
  have hnum : 0 ≤
      (S : ℝ) +
        ((availableCliques H r history).card -
          availableDegree H r history e : ℕ) *
          (upper (history.length + 1) - upper history.length) := by
    dsimp [S] at hscalar ⊢
    linarith
  have hcard : (0 : ℝ) < (availableCliques H r history).card := by
    exact_mod_cast Finset.card_pos.mpr hne
  apply neg_nonpos.mpr
  apply div_nonneg
  · simpa [S] using hnum
  · exact hcard.le

/-- Upper deletion estimate plus one scalar inequality gives lower-degree
negative drift. -/
theorem sum_uniformStep_mul_lowerDegreeIncrement_nonpos
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    {history : List (Finset (Fin n))} {e : Finset (Fin n)}
    (he : e ∈ residualHost host r history)
    (hne : (availableCliques H r history).Nonempty)
    (lower : ℕ → ℝ) (U : ℕ)
    (hupper : ∀ f ∈ residualHost host r history,
      availableDegree H r history f ≤ U)
    (hscalar :
      ((availableDegree H r history e * (Nat.choose q r - 1) * U : ℕ) : ℝ) +
        ((availableCliques H r history).card -
          availableDegree H r history e : ℕ) *
          (lower (history.length + 1) - lower history.length) ≤ 0) :
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        (lowerDegreeObservable host H r lower e (history ++ [Q]) -
          lowerDegreeObservable host H r lower e history)) ≤ 0 := by
  rw [sum_uniformStep_mul_lowerDegreeIncrement lower he hne]
  rw [sum_deletedAtEdge_add_delta]
  have hdel := sum_surviving_deletedAtEdge_le hH history e U hupper
  let S : ℕ := ∑ Q ∈ availableCliques H r history,
    if e ∈ blockEdges r Q then 0
    else (deletedAtEdge H r history e Q).card
  have hdelReal : (S : ℝ) ≤
      ((availableDegree H r history e * (Nat.choose q r - 1) * U : ℕ) : ℝ) := by
    dsimp [S]
    exact_mod_cast hdel
  have hnum : (S : ℝ) +
      ((availableCliques H r history).card -
        availableDegree H r history e : ℕ) *
        (lower (history.length + 1) - lower history.length) ≤ 0 := by
    linarith
  apply div_nonpos_of_nonpos_of_nonneg
  · simpa [S] using hnum
  · positivity

/-- Lower total-deletion estimate gives upper total-clique drift. -/
theorem sum_uniformStep_mul_cliqueUpperIncrement_nonpos
    (hr : 0 < r) (hrq : r < q)
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    {history : List (Finset (Fin n))}
    (hne : (availableCliques H r history).Nonempty)
    (profile : ℕ → ℝ) (L : ℕ)
    (hlower : ∀ e ∈ residualHost host r history,
      L ≤ availableDegree H r history e)
    (hscalar : (0 : ℝ) ≤
      ((Nat.choose q r * L : ℕ) : ℝ) -
        (((Nat.choose q r) ^ 2 * n ^ (q - r - 1) : ℕ) : ℝ) +
        (profile (history.length + 1) - profile history.length)) :
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        (cliqueObservable H r profile (history ++ [Q]) -
          cliqueObservable H r profile history)) ≤ 0 := by
  rw [sum_uniformStep_mul_cliqueIncrement H r profile hne]
  let M := (availableCliques H r history).card
  let S := ∑ Q ∈ availableCliques H r history,
    (deletedCliques H r history Q).card
  have hdel := card_available_mul_choose_mul_lower_le_sum_deleted_add_error
    hr hrq hH history L hlower
  have hMpos : (0 : ℝ) < M := by
    dsimp [M]
    exact_mod_cast Finset.card_pos.mpr hne
  have hdelReal :
      ((M * Nat.choose q r * L : ℕ) : ℝ) ≤
        ((S + M * (Nat.choose q r) ^ 2 * n ^ (q - r - 1) : ℕ) : ℝ) := by
    exact_mod_cast hdel
  have havg : (0 : ℝ) ≤ (S : ℝ) / M +
      (profile (history.length + 1) - profile history.length) := by
    have hM0 : (0 : ℝ) ≤ M := hMpos.le
    have hprofileMul : 0 ≤ (M : ℝ) *
        (((Nat.choose q r * L : ℕ) : ℝ) -
          (((Nat.choose q r) ^ 2 * n ^ (q - r - 1) : ℕ) : ℝ) +
          (profile (history.length + 1) - profile history.length)) :=
      mul_nonneg hM0 hscalar
    have hmul : -(profile (history.length + 1) - profile history.length) * M ≤
        (S : ℝ) := by
      push_cast at hdelReal
      push_cast at hprofileMul
      nlinarith
    have hdiv : -(profile (history.length + 1) - profile history.length) ≤
        (S : ℝ) / M := (le_div_iff₀ hMpos).2 (by
          simpa [mul_comm] using hmul)
    linarith
  simpa [S, M] using (show
    -((S : ℝ) / M) -
      (profile (history.length + 1) - profile history.length) ≤ 0 by
        linarith)

/-- Upper total-deletion estimate gives lower total-clique drift. -/
theorem sum_uniformStep_mul_cliqueLowerIncrement_nonpos
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    {history : List (Finset (Fin n))}
    (hne : (availableCliques H r history).Nonempty)
    (profile : ℕ → ℝ) (U : ℕ)
    (hupper : ∀ e ∈ residualHost host r history,
      availableDegree H r history e ≤ U)
    (hscalar : (Nat.choose q r * U : ℝ) +
      (profile (history.length + 1) - profile history.length) ≤ 0) :
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        ((-cliqueObservable H r profile) (history ++ [Q]) -
          (-cliqueObservable H r profile) history)) ≤ 0 := by
  have hmean := sum_uniformStep_mul_cliqueIncrement H r profile hne
  have hdel := sum_card_deletedCliques_le hH history U hupper
  let M := (availableCliques H r history).card
  let S := ∑ Q ∈ availableCliques H r history,
    (deletedCliques H r history Q).card
  have hMpos : (0 : ℝ) < M := by
    dsimp [M]
    exact_mod_cast Finset.card_pos.mpr hne
  have hdelReal : (S : ℝ) ≤ M * Nat.choose q r * U := by
    dsimp [S, M]
    exact_mod_cast hdel
  have havg : (S : ℝ) / M ≤ Nat.choose q r * U := by
    apply (div_le_iff₀ hMpos).2
    nlinarith
  rw [show (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        ((-cliqueObservable H r profile) (history ++ [Q]) -
          (-cliqueObservable H r profile) history)) =
      -(∑ Q : Finset (Fin n),
        uniformStep (availableCliques H r) history Q *
          (cliqueObservable H r profile (history ++ [Q]) -
            cliqueObservable H r profile history)) by
        calc
          _ = ∑ Q : Finset (Fin n),
              -(uniformStep (availableCliques H r) history Q *
                (cliqueObservable H r profile (history ++ [Q]) -
                  cliqueObservable H r profile history)) := by
                apply Finset.sum_congr rfl
                intro Q hQ
                change
                  uniformStep (availableCliques H r) history Q *
                      (-cliqueObservable H r profile (history ++ [Q]) -
                        -cliqueObservable H r profile history) = _
                ring
          _ = _ := by rw [Finset.sum_neg_distrib]]
  rw [hmean]
  have htarget :
      -(-((S : ℝ) / M) -
        (profile (history.length + 1) - profile history.length)) ≤ 0 := by
    linarith
  simpa [S, M] using htarget

end

end Erdos722.NibbleEdgeDrift
