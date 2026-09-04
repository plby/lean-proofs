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
import ErdosProblems.Erdos722.NibbleVariance
import ErdosProblems.Erdos722.NibbleCodegree
import Mathlib

/-!
# Jump and first-moment estimates for clique removal

This file supplies the bounded-increment part of the finite Freedman
argument.  The important point is that increments only have to be bounded
on legal actions.  An edge-degree changes by at most one design-hypergraph
codegree for each edge of the selected clique; the total clique count
changes by at most the clique size times the current maximum degree; and a
lower-face counter loses at most all the edges of the selected clique.
-/

namespace Erdos722.NibbleMoments

open Finset
open Erdos722.NibbleBasics
open Erdos722.NibbleProcess
open Erdos722.NibbleCounters
open Erdos722.NibbleObservables
open Erdos722.NibbleCodegree
open Erdos722.NibbleDrift
open Erdos722.NibbleBarrier
open Erdos722.NibbleVariance
open Erdos722.StoppedFreedman
open Erdos722.AdaptiveChernoff
open Erdos722.Typicality

noncomputable section

variable {n q r : ℕ}

/-- The deterministic codegree jump used by every edge counter. -/
def edgeDeletionJump (n q r : ℕ) : ℝ :=
  Nat.choose q r * n ^ (q - r - 1)

/-- A common pointwise jump envelope for the complete barrier family. -/
def barrierJump
    (host : Finset (Finset (Fin n))) (q r : ℕ)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (faceWeight faceCap : ℕ → ℝ) (U : ℕ → ℕ) :
    BarrierIndex host r → ℕ → ℝ
  | Sum.inl (Sum.inl (_e, false)), i =>
      edgeDeletionJump n q r + |degreeUpper (i + 1) - degreeUpper i|
  | Sum.inl (Sum.inl (_e, true)), i =>
      edgeDeletionJump n q r + |degreeLower (i + 1) - degreeLower i|
  | Sum.inl (Sum.inr false), i =>
      Nat.choose q r * U i + |cliqueUpper (i + 1) - cliqueUpper i|
  | Sum.inl (Sum.inr true), i =>
      Nat.choose q r * U i + |cliqueLower (i + 1) - cliqueLower i|
  | Sum.inr _f, i =>
      |faceWeight (i + 1) - faceWeight i| * n +
        |faceWeight (i + 1)| * Nat.choose q r +
        |faceCap (i + 1) - faceCap i|

lemma abs_sub_sub_le (a b c : ℝ) :
    |a - b - c| ≤ |a| + |b| + |c| := by
  calc
    |a - b - c| ≤ |a - b| + |c| := abs_sub _ _
    _ ≤ |a| + |b| + |c| := by linarith [abs_sub a b]

lemma abs_natCast_add_le {a : ℕ} (b A : ℝ) (ha : (a : ℝ) ≤ A) :
    |(a : ℝ) + b| ≤ A + |b| := by
  calc
    |(a : ℝ) + b| ≤ |(a : ℝ)| + |b| := abs_add_le _ _
    _ = (a : ℝ) + |b| := by simp
    _ ≤ A + |b| := by gcongr

lemma abs_neg_natCast_sub_le {a : ℕ} (b A : ℝ) (ha : (a : ℝ) ≤ A) :
    |-(a : ℝ) - b| ≤ A + |b| := by
  calc
    |-(a : ℝ) - b| ≤ |-(a : ℝ)| + |b| := abs_sub _ _
    _ = (a : ℝ) + |b| := by simp
    _ ≤ A + |b| := by gcongr

lemma sum_uniformStep_mul_eq_average
    {α : Type*} [Fintype α] [DecidableEq α]
    (legal : List α → Finset α) (history : List α)
    (hne : (legal history).Nonempty) (b : α → ℝ) :
    (∑ a : α, uniformStep legal history a * b a) =
      (∑ a ∈ legal history, b a) / (legal history).card := by
  have hcard : ((legal history).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  rw [div_eq_mul_inv]
  calc
    (∑ a : α, uniformStep legal history a * b a) =
        ∑ a ∈ legal history, ((legal history).card : ℝ)⁻¹ * b a := by
      calc
        _ = ∑ a : α, if a ∈ legal history then
              ((legal history).card : ℝ)⁻¹ * b a else 0 := by
                apply Finset.sum_congr rfl
                intro a _ha
                simp [uniformStep]
        _ = _ := by rw [← Finset.sum_filter]; simp
    _ = ((legal history).card : ℝ)⁻¹ *
          ∑ a ∈ legal history, b a := by rw [Finset.mul_sum]
    _ = (∑ a ∈ legal history, b a) *
          ((legal history).card : ℝ)⁻¹ := by ring

/-- A pointwise absolute bound by `b + c` converts to the corresponding
uniform average bound. -/
lemma sum_uniformStep_mul_abs_le_average
    {α : Type*} [Fintype α] [DecidableEq α]
    (legal : List α → Finset α) (history : List α)
    (hne : (legal history).Nonempty) (x b : α → ℝ) (c : ℝ)
    (hx : ∀ a ∈ legal history, |x a| ≤ b a + c) :
    (∑ a : α, uniformStep legal history a * |x a|) ≤
      (∑ a ∈ legal history, b a) / (legal history).card + c := by
  have hsum : ∑ a : α, uniformStep legal history a = 1 := by
    have hcard : (0 : ℝ) < (legal history).card := by
      exact_mod_cast Finset.card_pos.mpr hne
    simp [uniformStep, hcard.ne']
  calc
    (∑ a : α, uniformStep legal history a * |x a|) ≤
        ∑ a : α, uniformStep legal history a * (b a + c) := by
      apply Finset.sum_le_sum
      intro a _ha
      by_cases hal : a ∈ legal history
      · exact mul_le_mul_of_nonneg_left (hx a hal)
          (uniformStep_nonneg legal history a)
      · simp [uniformStep, hal]
    _ = (∑ a : α, uniformStep legal history a * b a) + c := by
      calc
        (∑ a : α, uniformStep legal history a * (b a + c)) =
            ∑ a : α, (uniformStep legal history a * b a +
              uniformStep legal history a * c) := by
                apply Finset.sum_congr rfl
                intro a _ha
                ring
        _ = (∑ a : α, uniformStep legal history a * b a) +
              ∑ a : α, uniformStep legal history a * c :=
                Finset.sum_add_distrib
        _ = (∑ a : α, uniformStep legal history a * b a) +
              (∑ a : α, uniformStep legal history a) * c := by
                rw [Finset.sum_mul]
        _ = _ := by rw [hsum]; ring
    _ = _ := by rw [sum_uniformStep_mul_eq_average legal history hne b]

lemma sum_uniformStep_mul_abs_le_constant
    {α : Type*} [Fintype α] [DecidableEq α]
    (legal : List α → Finset α) (history : List α)
    (hne : (legal history).Nonempty) (x : α → ℝ) (J : ℝ)
    (hx : ∀ a ∈ legal history, |x a| ≤ J) :
    (∑ a : α, uniformStep legal history a * |x a|) ≤ J := by
  have hsum : ∑ a : α, uniformStep legal history a = 1 := by
    have hcard : (0 : ℝ) < (legal history).card := by
      exact_mod_cast Finset.card_pos.mpr hne
    simp [uniformStep, hcard.ne']
  calc
    (∑ a : α, uniformStep legal history a * |x a|) ≤
        ∑ a : α, uniformStep legal history a * J := by
      apply Finset.sum_le_sum
      intro a _ha
      by_cases hal : a ∈ legal history
      · exact mul_le_mul_of_nonneg_left (hx a hal)
          (uniformStep_nonneg legal history a)
      · simp [uniformStep, hal]
    _ = (∑ a : α, uniformStep legal history a) * J := by
      rw [Finset.sum_mul]
    _ = J := by rw [hsum]; ring

theorem sum_uniformStep_mul_abs_upperDegreeIncrement_le
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (upper : ℕ → ℝ) {history : List (Finset (Fin n))}
    {e : Finset (Fin n)} (he : e ∈ residualHost host r history)
    (hne : (availableCliques H r history).Nonempty)
    (U : ℕ) (hupper : ∀ f ∈ residualHost host r history,
      availableDegree H r history f ≤ U)
    (C : ℝ) (hC : 0 < C)
    (hCM : C ≤ (availableCliques H r history).card) :
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        |upperDegreeObservable host H r upper e (history ++ [Q]) -
          upperDegreeObservable host H r upper e history|) ≤
      ((U * (Nat.choose q r - 1) * U : ℕ) : ℝ) / C +
        |upper (history.length + 1) - upper history.length| := by
  let A := availableCliques H r history
  let b : Finset (Fin n) → ℝ := fun Q ↦
    if e ∈ blockEdges r Q then 0
    else (deletedAtEdge H r history e Q).card
  have havg := sum_uniformStep_mul_abs_le_average
    (availableCliques H r) history hne
    (fun Q ↦ upperDegreeObservable host H r upper e (history ++ [Q]) -
      upperDegreeObservable host H r upper e history)
    b |upper (history.length + 1) - upper history.length| (by
      intro Q hQA
      rw [upperDegreeObservable_increment]
      by_cases heQ : e ∈ blockEdges r Q
      · have hnotrel : ¬(e ∈ residualHost host r history ∧
            e ∈ residualHost host r (history ++ [Q])) := by
          intro hrel
          rw [residualHost_update] at hrel
          exact (Finset.mem_sdiff.mp hrel.2).2 heQ
        simp [hnotrel, b, heQ]
      · have hrel : e ∈ residualHost host r history ∧
            e ∈ residualHost host r (history ++ [Q]) := by
          refine ⟨he, ?_⟩
          rw [residualHost_update]
          exact Finset.mem_sdiff.mpr ⟨he, heQ⟩
        rw [if_pos hrel]
        simp only [b, if_neg heQ]
        exact abs_neg_natCast_sub_le _ _ le_rfl)
  have hdelNat := sum_surviving_deletedAtEdge_le hH history e U hupper
  have hdeg : availableDegree H r history e ≤ U := hupper e he
  have hprod : availableDegree H r history e * (Nat.choose q r - 1) * U ≤
      U * (Nat.choose q r - 1) * U := by
    exact Nat.mul_le_mul_right U
      (Nat.mul_le_mul_right (Nat.choose q r - 1) hdeg)
  have hsumNat : (∑ Q ∈ A,
        if e ∈ blockEdges r Q then 0
        else (deletedAtEdge H r history e Q).card) ≤
      U * (Nat.choose q r - 1) * U := by
    exact hdelNat.trans hprod
  have hsumReal : (∑ Q ∈ A, b Q) ≤
      ((U * (Nat.choose q r - 1) * U : ℕ) : ℝ) := by
    dsimp [A, b]
    exact_mod_cast hsumNat
  have hM : (0 : ℝ) < A.card := by
    dsimp [A]
    exact_mod_cast Finset.card_pos.mpr hne
  have hnum : (0 : ℝ) ≤ ((U * (Nat.choose q r - 1) * U : ℕ) : ℝ) := by
    positivity
  have hratio : (∑ Q ∈ A, b Q) / A.card ≤
      ((U * (Nat.choose q r - 1) * U : ℕ) : ℝ) / C := by
    calc
      (∑ Q ∈ A, b Q) / A.card ≤
          ((U * (Nat.choose q r - 1) * U : ℕ) : ℝ) / A.card :=
            div_le_div_of_nonneg_right hsumReal hM.le
      _ ≤ ((U * (Nat.choose q r - 1) * U : ℕ) : ℝ) / C :=
            div_le_div_of_nonneg_left hnum hC hCM
  calc
    _ ≤ (∑ Q ∈ availableCliques H r history, b Q) /
          (availableCliques H r history).card +
          |upper (history.length + 1) - upper history.length| := havg
    _ ≤ _ := by
      dsimp [A] at hratio
      gcongr

theorem sum_uniformStep_mul_abs_lowerDegreeIncrement_le
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (lower : ℕ → ℝ) {history : List (Finset (Fin n))}
    {e : Finset (Fin n)} (he : e ∈ residualHost host r history)
    (hne : (availableCliques H r history).Nonempty)
    (U : ℕ) (hupper : ∀ f ∈ residualHost host r history,
      availableDegree H r history f ≤ U)
    (C : ℝ) (hC : 0 < C)
    (hCM : C ≤ (availableCliques H r history).card) :
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        |lowerDegreeObservable host H r lower e (history ++ [Q]) -
          lowerDegreeObservable host H r lower e history|) ≤
      ((U * (Nat.choose q r - 1) * U : ℕ) : ℝ) / C +
        |lower (history.length + 1) - lower history.length| := by
  let A := availableCliques H r history
  let b : Finset (Fin n) → ℝ := fun Q ↦
    if e ∈ blockEdges r Q then 0
    else (deletedAtEdge H r history e Q).card
  have havg := sum_uniformStep_mul_abs_le_average
    (availableCliques H r) history hne
    (fun Q ↦ lowerDegreeObservable host H r lower e (history ++ [Q]) -
      lowerDegreeObservable host H r lower e history)
    b |lower (history.length + 1) - lower history.length| (by
      intro Q hQA
      rw [lowerDegreeObservable_increment]
      by_cases heQ : e ∈ blockEdges r Q
      · have hnotrel : ¬(e ∈ residualHost host r history ∧
            e ∈ residualHost host r (history ++ [Q])) := by
          intro hrel
          rw [residualHost_update] at hrel
          exact (Finset.mem_sdiff.mp hrel.2).2 heQ
        simp [hnotrel, b, heQ]
      · have hrel : e ∈ residualHost host r history ∧
            e ∈ residualHost host r (history ++ [Q]) := by
          refine ⟨he, ?_⟩
          rw [residualHost_update]
          exact Finset.mem_sdiff.mpr ⟨he, heQ⟩
        rw [if_pos hrel]
        simp only [b, if_neg heQ]
        exact abs_natCast_add_le _ _ le_rfl)
  have hdelNat := sum_surviving_deletedAtEdge_le hH history e U hupper
  have hdeg : availableDegree H r history e ≤ U := hupper e he
  have hprod : availableDegree H r history e * (Nat.choose q r - 1) * U ≤
      U * (Nat.choose q r - 1) * U := by
    exact Nat.mul_le_mul_right U
      (Nat.mul_le_mul_right (Nat.choose q r - 1) hdeg)
  have hsumNat : (∑ Q ∈ A,
        if e ∈ blockEdges r Q then 0
        else (deletedAtEdge H r history e Q).card) ≤
      U * (Nat.choose q r - 1) * U := hdelNat.trans hprod
  have hsumReal : (∑ Q ∈ A, b Q) ≤
      ((U * (Nat.choose q r - 1) * U : ℕ) : ℝ) := by
    dsimp [A, b]
    exact_mod_cast hsumNat
  have hM : (0 : ℝ) < A.card := by
    dsimp [A]
    exact_mod_cast Finset.card_pos.mpr hne
  have hnum : (0 : ℝ) ≤ ((U * (Nat.choose q r - 1) * U : ℕ) : ℝ) := by
    positivity
  have hratio : (∑ Q ∈ A, b Q) / A.card ≤
      ((U * (Nat.choose q r - 1) * U : ℕ) : ℝ) / C := by
    calc
      (∑ Q ∈ A, b Q) / A.card ≤
          ((U * (Nat.choose q r - 1) * U : ℕ) : ℝ) / A.card :=
            div_le_div_of_nonneg_right hsumReal hM.le
      _ ≤ ((U * (Nat.choose q r - 1) * U : ℕ) : ℝ) / C :=
            div_le_div_of_nonneg_left hnum hC hCM
  calc
    _ ≤ (∑ Q ∈ availableCliques H r history, b Q) /
          (availableCliques H r history).card +
          |lower (history.length + 1) - lower history.length| := havg
    _ ≤ _ := by
      dsimp [A] at hratio
      gcongr

theorem sum_uniformStep_mul_abs_weightedFaceIncrement_le
    (hr : 0 < r)
    {host H : Finset (Finset (Fin n))}
    (hhost : host ⊆ uniformEdges n r)
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (weight cap : ℕ → ℝ) {history : List (Finset (Fin n))}
    {f : Finset (Fin n)} (hf : f.card = r - 1)
    (hne : (availableCliques H r history).Nonempty)
    (U : ℕ) (hupper : ∀ e ∈ residualHost host r history,
      availableDegree H r history e ≤ U)
    (C : ℝ) (hC : 0 < C)
    (hCM : C ≤ (availableCliques H r history).card) :
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        |weightedFaceObservable host r weight cap f (history ++ [Q]) -
          weightedFaceObservable host r weight cap f history|) ≤
      |weight (history.length + 1) - weight history.length| * n +
        |weight (history.length + 1)| *
          (((n * U : ℕ) : ℝ) / C) +
        |cap (history.length + 1) - cap history.length| := by
  let A := availableCliques H r history
  let b : Finset (Fin n) → ℝ := fun Q ↦
    |weight (history.length + 1)| * faceLoss r Q f
  let c : ℝ :=
    |weight (history.length + 1) - weight history.length| *
        residualFaceDegree host r history f +
      |cap (history.length + 1) - cap history.length|
  have havg := sum_uniformStep_mul_abs_le_average
    (availableCliques H r) history hne
    (fun Q ↦ weightedFaceObservable host r weight cap f (history ++ [Q]) -
      weightedFaceObservable host r weight cap f history)
    b c (by
      intro Q hQA
      rw [weightedFaceObservable_increment
        (fun P hP ↦ (hH P hP).2) weight cap f hQA]
      calc
        |(weight (history.length + 1) - weight history.length) *
              (residualFaceDegree host r history f : ℝ) -
            weight (history.length + 1) * faceLoss r Q f -
            (cap (history.length + 1) - cap history.length)| ≤
            |(weight (history.length + 1) - weight history.length) *
              (residualFaceDegree host r history f : ℝ)| +
            |weight (history.length + 1) * faceLoss r Q f| +
            |cap (history.length + 1) - cap history.length| :=
              abs_sub_sub_le _ _ _
        _ = b Q + c := by simp [b, c, abs_mul]; ring)
  have hfaceNat := sum_faceLoss_le_faceDegree_mul_degreeUpper
    (fun P hP ↦ (hH P hP).2) history f U hupper
  have hFN : residualFaceDegree host r history f ≤ n :=
    residualFaceDegree_le_n hr hhost history hf
  have hnumNat : (∑ Q ∈ A, faceLoss r Q f) ≤ n * U := by
    exact hfaceNat.trans (Nat.mul_le_mul_right U hFN)
  have hnumReal : (∑ Q ∈ A, (faceLoss r Q f : ℝ)) ≤
      ((n * U : ℕ) : ℝ) := by
    exact_mod_cast hnumNat
  have hbSum : (∑ Q ∈ A, b Q) ≤
      |weight (history.length + 1)| * ((n * U : ℕ) : ℝ) := by
    dsimp [b]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hnumReal (abs_nonneg _)
  have hM : (0 : ℝ) < A.card := by
    dsimp [A]
    exact_mod_cast Finset.card_pos.mpr hne
  have hratio : (∑ Q ∈ A, b Q) / A.card ≤
      |weight (history.length + 1)| * (((n * U : ℕ) : ℝ) / C) := by
    calc
      (∑ Q ∈ A, b Q) / A.card ≤
          (|weight (history.length + 1)| * ((n * U : ℕ) : ℝ)) /
            A.card := div_le_div_of_nonneg_right hbSum hM.le
      _ ≤ (|weight (history.length + 1)| * ((n * U : ℕ) : ℝ)) / C := by
            exact div_le_div_of_nonneg_left
              (mul_nonneg (abs_nonneg _) (by positivity)) hC hCM
      _ = |weight (history.length + 1)| *
          (((n * U : ℕ) : ℝ) / C) := by ring
  have hcBound : c ≤
      |weight (history.length + 1) - weight history.length| * n +
        |cap (history.length + 1) - cap history.length| := by
    dsimp [c]
    have hcast : (residualFaceDegree host r history f : ℝ) ≤ n := by
      exact_mod_cast hFN
    gcongr
  calc
    _ ≤ (∑ Q ∈ availableCliques H r history, b Q) /
          (availableCliques H r history).card + c := havg
    _ ≤ |weight (history.length + 1)| * (((n * U : ℕ) : ℝ) / C) +
          (|weight (history.length + 1) - weight history.length| * n +
            |cap (history.length + 1) - cap history.length|) := by
      dsimp [A] at hratio
      linarith
    _ = _ := by ring

/-- Conditional absolute-first-moment budgets.  The edge and face entries
use the tracked lower clique-count profile `C` as a deterministic
denominator. -/
def barrierAbsBudget
    (host : Finset (Finset (Fin n))) (q r : ℕ)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (faceWeight faceCap : ℕ → ℝ) (U : ℕ → ℕ) (C : ℕ → ℝ) :
    BarrierIndex host r → ℕ → ℝ
  | Sum.inl (Sum.inl (_e, false)), i =>
      ((U i * (Nat.choose q r - 1) * U i : ℕ) : ℝ) / C i +
        |degreeUpper (i + 1) - degreeUpper i|
  | Sum.inl (Sum.inl (_e, true)), i =>
      ((U i * (Nat.choose q r - 1) * U i : ℕ) : ℝ) / C i +
        |degreeLower (i + 1) - degreeLower i|
  | Sum.inl (Sum.inr false), i =>
      Nat.choose q r * U i + |cliqueUpper (i + 1) - cliqueUpper i|
  | Sum.inl (Sum.inr true), i =>
      Nat.choose q r * U i + |cliqueLower (i + 1) - cliqueLower i|
  | Sum.inr _f, i =>
      |faceWeight (i + 1) - faceWeight i| * n +
        |faceWeight (i + 1)| * (((n * U i : ℕ) : ℝ) / C i) +
        |faceCap (i + 1) - faceCap i|

/-- Simultaneous conditional absolute-first-moment bounds, assuming the
current state has maximum available degree `U i` and at least `C i`
available cliques. -/
theorem barrierObservable_absMoment_le_of_state
    (hr : 0 < r) (hrq : r < q)
    {host H : Finset (Finset (Fin n))}
    (hhost : host ⊆ uniformEdges n r)
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (faceWeight faceCap : ℕ → ℝ) (U : ℕ → ℕ) (C : ℕ → ℝ)
    {history : List (Finset (Fin n))}
    (hne : (availableCliques H r history).Nonempty)
    (hupper : ∀ e ∈ residualHost host r history,
      availableDegree H r history e ≤ U history.length)
    (hC : 0 < C history.length)
    (hCM : C history.length ≤ (availableCliques H r history).card) :
    ∀ z : BarrierIndex host r,
      (∑ Q : Finset (Fin n),
        uniformStep (availableCliques H r) history Q *
          |observableIncrement
            (barrierObservable host H r degreeUpper degreeLower
              cliqueUpper cliqueLower faceWeight faceCap) z history Q|) ≤
        barrierAbsBudget host q r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap U C z history.length := by
  intro z
  rcases z with (⟨⟨e, heHost⟩, isLower⟩ | isClique) | ⟨f, hf⟩
  · cases isLower with
    | false =>
        by_cases he : e ∈ residualHost host r history
        · simpa [observableIncrement, barrierObservable_edgeUpper_eq,
            barrierAbsBudget] using
            sum_uniformStep_mul_abs_upperDegreeIncrement_le
              hH degreeUpper he hne (U history.length) hupper
              (C history.length) hC hCM
        · have hzero : ∀ Q : Finset (Fin n),
              observableIncrement
                (barrierObservable host H r degreeUpper degreeLower
                  cliqueUpper cliqueLower faceWeight faceCap)
                (Sum.inl (Sum.inl (⟨e, heHost⟩, false))) history Q = 0 := by
            intro Q
            simp only [observableIncrement, barrierObservable_edgeUpper_eq]
            rw [upperDegreeObservable_increment]
            simp [he]
          rw [show (∑ Q : Finset (Fin n),
              uniformStep (availableCliques H r) history Q *
                |observableIncrement
                  (barrierObservable host H r degreeUpper degreeLower
                    cliqueUpper cliqueLower faceWeight faceCap)
                  (Sum.inl (Sum.inl (⟨e, heHost⟩, false))) history Q|) = 0 by
                apply Finset.sum_eq_zero
                intro Q _hQ
                simp [hzero Q]]
          simp only [barrierAbsBudget]
          positivity
    | true =>
        by_cases he : e ∈ residualHost host r history
        · simpa [observableIncrement, barrierObservable_edgeLower_eq,
            barrierAbsBudget] using
            sum_uniformStep_mul_abs_lowerDegreeIncrement_le
              hH degreeLower he hne (U history.length) hupper
              (C history.length) hC hCM
        · have hzero : ∀ Q : Finset (Fin n),
              observableIncrement
                (barrierObservable host H r degreeUpper degreeLower
                  cliqueUpper cliqueLower faceWeight faceCap)
                (Sum.inl (Sum.inl (⟨e, heHost⟩, true))) history Q = 0 := by
            intro Q
            simp only [observableIncrement, barrierObservable_edgeLower_eq]
            rw [lowerDegreeObservable_increment]
            simp [he]
          rw [show (∑ Q : Finset (Fin n),
              uniformStep (availableCliques H r) history Q *
                |observableIncrement
                  (barrierObservable host H r degreeUpper degreeLower
                    cliqueUpper cliqueLower faceWeight faceCap)
                  (Sum.inl (Sum.inl (⟨e, heHost⟩, true))) history Q|) = 0 by
                apply Finset.sum_eq_zero
                intro Q _hQ
                simp [hzero Q]]
          simp only [barrierAbsBudget]
          positivity
  · apply sum_uniformStep_mul_abs_le_constant
      (availableCliques H r) history hne
    intro Q hQ
    have hQH : Q ∈ H := availableCliques_subset H r history hQ
    have hQcard : Q.card = q := (hH Q hQH).1
    have hQedges : blockEdges r Q ⊆ residualHost host r history :=
      blockEdges_subset_residual_of_available
        (fun P hP ↦ (hH P hP).2) hQ
    have hdeleted : ((deletedCliques H r history Q).card : ℝ) ≤
        Nat.choose q r * U history.length := by
      have hnat := card_deletedCliques_le (U history.length)
        (fun e he ↦ hupper e (hQedges he))
      rw [card_blockEdges, hQcard] at hnat
      exact_mod_cast hnat
    cases isClique with
    | false =>
        simp only [observableIncrement, barrierObservable]
        rw [cliqueObservable_increment]
        exact abs_neg_natCast_sub_le _ _ hdeleted
    | true =>
        simp only [observableIncrement, barrierObservable]
        rw [show
          -(cliqueObservable H r cliqueLower (history ++ [Q])) -
              -cliqueObservable H r cliqueLower history =
            -(cliqueObservable H r cliqueLower (history ++ [Q]) -
              cliqueObservable H r cliqueLower history) by ring,
          abs_neg, cliqueObservable_increment]
        exact abs_neg_natCast_sub_le _ _ hdeleted
  · have hfcard : f.card = r - 1 := mem_uniformEdges.mp hf
    simpa [observableIncrement, barrierObservable_face_eq,
      barrierAbsBudget] using
      sum_uniformStep_mul_abs_weightedFaceIncrement_le
        hr hhost hH faceWeight faceCap hfcard hne
        (U history.length) hupper (C history.length) hC hCM

/-- Pointwise bounded increments for all five kinds of barrier. -/
theorem barrierObservable_increment_abs_le
    (hr : 0 < r) (hrq : r < q)
    {host H : Finset (Finset (Fin n))}
    (hhost : host ⊆ uniformEdges n r)
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (faceWeight faceCap : ℕ → ℝ) (U : ℕ → ℕ)
    {history : List (Finset (Fin n))} {Q : Finset (Fin n)}
    (hQ : Q ∈ availableCliques H r history)
    (hupper : ∀ e ∈ residualHost host r history,
      availableDegree H r history e ≤ U history.length) :
    ∀ z : BarrierIndex host r,
      |observableIncrement
        (barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap) z history Q| ≤
        barrierJump host q r degreeUpper degreeLower cliqueUpper cliqueLower
          faceWeight faceCap U z history.length := by
  have hQH : Q ∈ H := availableCliques_subset H r history hQ
  have hQcard : Q.card = q := (hH Q hQH).1
  have hQedges : blockEdges r Q ⊆ residualHost host r history :=
    blockEdges_subset_residual_of_available (fun P hP ↦ (hH P hP).2) hQ
  intro z
  rcases z with (⟨⟨e, heHost⟩, isLower⟩ | isClique) | ⟨f, hf⟩
  · have hecard : e.card = r := mem_uniformEdges.mp (hhost heHost)
    cases isLower with
    | false =>
        simp only [observableIncrement, barrierObservable_edgeUpper_eq]
        rw [upperDegreeObservable_increment]
        by_cases hrel : e ∈ residualHost host r history ∧
            e ∈ residualHost host r (history ++ [Q])
        · rw [if_pos hrel]
          apply abs_neg_natCast_sub_le
          unfold edgeDeletionJump
          exact_mod_cast card_deletedAtEdge_le hr hrq
            (history := history) (fun P hP ↦ (hH P hP).1)
            hecard hQcard (by
              intro heQ
              rw [residualHost_update] at hrel
              exact (Finset.mem_sdiff.mp hrel.2).2 heQ)
        · rw [if_neg hrel]
          simp only [abs_zero, barrierJump]
          apply add_nonneg
          · unfold edgeDeletionJump
            positivity
          · exact abs_nonneg _
    | true =>
        simp only [observableIncrement, barrierObservable_edgeLower_eq]
        rw [lowerDegreeObservable_increment]
        by_cases hrel : e ∈ residualHost host r history ∧
            e ∈ residualHost host r (history ++ [Q])
        · rw [if_pos hrel]
          apply abs_natCast_add_le
          unfold edgeDeletionJump
          exact_mod_cast card_deletedAtEdge_le hr hrq
            (history := history) (fun P hP ↦ (hH P hP).1)
            hecard hQcard (by
              intro heQ
              rw [residualHost_update] at hrel
              exact (Finset.mem_sdiff.mp hrel.2).2 heQ)
        · rw [if_neg hrel]
          simp only [abs_zero, barrierJump]
          apply add_nonneg
          · unfold edgeDeletionJump
            positivity
          · exact abs_nonneg _
  · have hdeleted : ((deletedCliques H r history Q).card : ℝ) ≤
        Nat.choose q r * U history.length := by
      have hnat := card_deletedCliques_le (U history.length)
        (fun e he ↦ hupper e (hQedges he))
      rw [card_blockEdges, hQcard] at hnat
      exact_mod_cast hnat
    cases isClique with
    | false =>
        simp only [observableIncrement, barrierObservable]
        rw [cliqueObservable_increment]
        exact abs_neg_natCast_sub_le _ _ hdeleted
    | true =>
        simp only [observableIncrement, barrierObservable]
        rw [show
          -(cliqueObservable H r cliqueLower (history ++ [Q])) -
              -cliqueObservable H r cliqueLower history =
            -(cliqueObservable H r cliqueLower (history ++ [Q]) -
              cliqueObservable H r cliqueLower history) by ring,
          abs_neg, cliqueObservable_increment]
        exact abs_neg_natCast_sub_le _ _ hdeleted
  · have hfcard : f.card = r - 1 := mem_uniformEdges.mp hf
    have hface : (residualFaceDegree host r history f : ℝ) ≤ n := by
      exact_mod_cast residualFaceDegree_le_n hr hhost history hfcard
    have hloss : (faceLoss r Q f : ℝ) ≤ Nat.choose q r := by
      exact_mod_cast faceLoss_le_choose Q f hQcard
    simp only [observableIncrement, barrierObservable_face_eq]
    rw [weightedFaceObservable_increment
      (fun P hP ↦ (hH P hP).2) faceWeight faceCap f hQ]
    calc
      |(faceWeight (history.length + 1) - faceWeight history.length) *
            (residualFaceDegree host r history f : ℝ) -
          faceWeight (history.length + 1) * faceLoss r Q f -
          (faceCap (history.length + 1) - faceCap history.length)| ≤
          |faceWeight (history.length + 1) - faceWeight history.length| *
              (residualFaceDegree host r history f : ℝ) +
            |faceWeight (history.length + 1)| * faceLoss r Q f +
            |faceCap (history.length + 1) - faceCap history.length| := by
              calc
                _ ≤ |(faceWeight (history.length + 1) - faceWeight history.length) *
                      (residualFaceDegree host r history f : ℝ)| +
                    |faceWeight (history.length + 1) * faceLoss r Q f| +
                    |faceCap (history.length + 1) - faceCap history.length| :=
                      abs_sub_sub_le _ _ _
                _ = _ := by simp [abs_mul]
      _ ≤ |faceWeight (history.length + 1) - faceWeight history.length| * n +
            |faceWeight (history.length + 1)| * Nat.choose q r +
            |faceCap (history.length + 1) - faceCap history.length| := by
              gcongr
      _ = _ := by rfl

/-- Good upper-degree and lower-clique barriers provide both pointwise
jump and conditional absolute-first-moment estimates. -/
theorem barrierObservable_jump_absMoment_of_good
    (hr : 0 < r) (hrq : r < q)
    {host H : Finset (Finset (Fin n))}
    (hhost : host ⊆ uniformEdges n r)
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (faceWeight faceCap : ℕ → ℝ) (U : ℕ → ℕ)
    {depth : ℕ}
    (hUEnvelope : ∀ i < depth, degreeUpper i ≤ U i)
    (hcliqueLowerPos : ∀ i < depth, 0 < cliqueLower i)
    {history : List (Finset (Fin n))}
    (hlen : history.length < depth)
    (hall : AllGood (fun h ↦ ∀ c,
      barrierObservable host H r degreeUpper degreeLower
        cliqueUpper cliqueLower faceWeight faceCap c h < 0) history) :
    (∀ z : BarrierIndex host r, ∀ Q ∈ availableCliques H r history,
      |observableIncrement
        (barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap) z history Q| ≤
        barrierJump host q r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap U z history.length) ∧
    (∀ z : BarrierIndex host r,
      (∑ Q : Finset (Fin n),
        uniformStep (availableCliques H r) history Q *
          |observableIncrement
            (barrierObservable host H r degreeUpper degreeLower
              cliqueUpper cliqueLower faceWeight faceCap) z history Q|) ≤
        barrierAbsBudget host q r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap U cliqueLower
          z history.length) := by
  have hupper : ∀ e ∈ residualHost host r history,
      availableDegree H r history e ≤ U history.length := by
    intro e he
    let ei : HostEdge host := ⟨e, (Finset.mem_sdiff.mp he).1⟩
    have hu := hall.current
      (good := fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap c h < 0)
      (Sum.inl (Sum.inl (ei, false)))
    rw [barrierObservable_edgeUpper_eq,
      upperDegreeObservable_eq_of_relevant he] at hu
    change (availableDegree H r history e : ℝ) -
      degreeUpper history.length < 0 at hu
    have hreal : (availableDegree H r history e : ℝ) < U history.length :=
      (by linarith : (availableDegree H r history e : ℝ) <
        degreeUpper history.length).trans_le
          (hUEnvelope history.length hlen)
    have hnat : availableDegree H r history e < U history.length := by
      exact_mod_cast hreal
    omega
  have hlo := hall.current
    (good := fun h ↦ ∀ c,
      barrierObservable host H r degreeUpper degreeLower
        cliqueUpper cliqueLower faceWeight faceCap c h < 0)
    (Sum.inl (Sum.inr true))
  rw [barrierObservable_cliqueLower_eq] at hlo
  have hC : 0 < cliqueLower history.length :=
    hcliqueLowerPos history.length hlen
  have hMreal : cliqueLower history.length <
      ((availableCliques H r history).card : ℝ) := by linarith
  have hMnat : 0 < (availableCliques H r history).card := by
    exact_mod_cast hC.trans hMreal
  have hne : (availableCliques H r history).Nonempty :=
    Finset.card_pos.mp hMnat
  refine ⟨?_, ?_⟩
  · intro z Q hQ
    exact barrierObservable_increment_abs_le hr hrq hhost hH
      degreeUpper degreeLower cliqueUpper cliqueLower faceWeight faceCap U
      hQ hupper z
  · intro z
    exact barrierObservable_absMoment_le_of_state hr hrq hhost hH
      degreeUpper degreeLower cliqueUpper cliqueLower faceWeight faceCap
      U cliqueLower hne hupper hC hMreal.le z

lemma barrierJump_nonneg
    (host : Finset (Finset (Fin n))) (q r : ℕ)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (faceWeight faceCap : ℕ → ℝ) (U : ℕ → ℕ)
    (z : BarrierIndex host r) (i : ℕ) :
    0 ≤ barrierJump host q r degreeUpper degreeLower
      cliqueUpper cliqueLower faceWeight faceCap U z i := by
  rcases z with (x | b) | f
  · rcases x with ⟨e, b⟩
    cases b <;> simp [barrierJump, edgeDeletionJump] <;> positivity
  · cases b <;> simp [barrierJump] <;> positivity
  · simp [barrierJump]
    positivity

lemma barrierAbsBudget_nonneg
    (host : Finset (Finset (Fin n))) (q r : ℕ)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (faceWeight faceCap : ℕ → ℝ) (U : ℕ → ℕ) (C : ℕ → ℝ)
    (z : BarrierIndex host r) (i : ℕ) (hC : 0 < C i) :
    0 ≤ barrierAbsBudget host q r degreeUpper degreeLower
      cliqueUpper cliqueLower faceWeight faceCap U C z i := by
  rcases z with (x | b) | f
  · rcases x with ⟨e, b⟩
    cases b <;> simp [barrierAbsBudget] <;> positivity
  · cases b <;> simp [barrierAbsBudget] <;> positivity
  · simp [barrierAbsBudget]
    positivity

end

end Erdos722.NibbleMoments
