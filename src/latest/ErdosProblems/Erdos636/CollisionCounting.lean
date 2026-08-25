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

import ErdosProblems.Erdos88.Concentration

/-!
# Collision counting on finite probability spaces

This file records the elementary first-moment argument used in the
profile-selection part of the proof of Erdős Problem 636.  The basic object
is the number of events from a finite family which occur at a point of a
finite uniform probability space.  Its uniform expectation is the sum of
the individual probabilities.  Markov's inequality then simultaneously
controls collision edges and the number of bad indices.
-/

open scoped BigOperators

namespace Erdos636
namespace CollisionCounting

open Classical Finset
open Erdos88.Concentration

variable {Omega : Type*} [Fintype Omega] [Nonempty Omega]

/-- The number of events in a finite family which occur at `omega`. -/
noncomputable def eventCount {iota : Type*} (I : Finset iota)
    (bad : iota → Omega → Prop) (omega : Omega) : Nat :=
  (I.filter fun i ↦ bad i omega).card

@[simp] lemma eventCount_empty {iota : Type*} (bad : iota → Omega → Prop)
    (omega : Omega) : eventCount ∅ bad omega = 0 := by
  simp [eventCount]

lemma eventCount_nonneg {iota : Type*} (I : Finset iota)
    (bad : iota → Omega → Prop) (omega : Omega) :
    0 ≤ (eventCount I bad omega : Real) := by
  positivity

/-- The normalized expected number of occurring events is the sum of their
individual normalized probabilities. -/
lemma uniformExpectation_eventCount {iota : Type*} (I : Finset iota)
    (bad : iota → Omega → Prop) :
    uniformExpectation (fun omega ↦ (eventCount I bad omega : Real)) =
      ∑ i ∈ I, uniformProbability (bad i) := by
  classical
  unfold uniformExpectation uniformProbability
  rw [← sum_div]
  congr 1
  calc
    ∑ omega, (eventCount I bad omega : Real) =
        ∑ omega, ∑ i ∈ I, if bad i omega then (1 : Real) else 0 := by
      apply sum_congr rfl
      intro omega _
      simp [eventCount]
    _ = ∑ i ∈ I, ∑ omega, if bad i omega then (1 : Real) else 0 := by
      rw [sum_comm]
    _ = ∑ i ∈ I, ((Finset.univ.filter (bad i)).card : Real) := by
      simp

/-- First-moment bound for a finite family of events. -/
lemma uniformExpectation_eventCount_le {iota : Type*} (I : Finset iota)
    (bad : iota → Omega → Prop) (p : Real)
    (hbad : ∀ i ∈ I, uniformProbability (bad i) ≤ p) :
    uniformExpectation (fun omega ↦ (eventCount I bad omega : Real)) ≤
      I.card * p := by
  rw [uniformExpectation_eventCount]
  calc
    ∑ i ∈ I, uniformProbability (bad i) ≤ ∑ _i ∈ I, p :=
      sum_le_sum fun i hi ↦ hbad i hi
    _ = I.card * p := by simp

/-- Markov's inequality for the number of occurring events. -/
lemma uniformProbability_eventCount_ge_le {iota : Type*} (I : Finset iota)
    (bad : iota → Omega → Prop) (p t : Real) (ht : 0 < t)
    (hbad : ∀ i ∈ I, uniformProbability (bad i) ≤ p) :
    uniformProbability (fun omega ↦ t ≤ eventCount I bad omega) ≤
      I.card * p / t := by
  classical
  rw [uniformProbability]
  have hmarkov := counting_markov
    (fun omega ↦ (eventCount I bad omega : Real)) t ht
    (eventCount_nonneg I bad)
  have hexpect := uniformExpectation_eventCount_le I bad p hbad
  have hcardOmega : (0 : Real) < Fintype.card Omega := by
    exact_mod_cast Fintype.card_pos
  rw [uniformExpectation] at hexpect
  calc
    ((Finset.univ.filter fun omega ↦
          t ≤ (eventCount I bad omega : Real)).card : Real) /
          Fintype.card Omega ≤
        ((∑ omega, (eventCount I bad omega : Real)) / t) /
          Fintype.card Omega := by
      apply div_le_div_of_nonneg_right _ hcardOmega.le
      exact (le_div_iff₀ ht).2 hmarkov
    _ = ((∑ omega, (eventCount I bad omega : Real)) /
          Fintype.card Omega) / t := by
      field_simp
    _ ≤ I.card * p / t :=
      div_le_div_of_nonneg_right hexpect ht.le

/-- If the Markov upper bound is strictly smaller than one, some outcome has
fewer than `t` bad events. -/
lemma exists_eventCount_lt {iota : Type*} (I : Finset iota)
    (bad : iota → Omega → Prop) (p t : Real) (ht : 0 < t)
    (hbad : ∀ i ∈ I, uniformProbability (bad i) ≤ p)
    (hsmall : I.card * p < t) :
    ∃ omega, (eventCount I bad omega : Real) < t := by
  by_contra h
  push Not at h
  have hprob : uniformProbability
      (fun omega ↦ t ≤ (eventCount I bad omega : Real)) = 1 := by
    classical
    have hcardOmega : (Fintype.card Omega : Real) ≠ 0 := by positivity
    simp [uniformProbability, h, hcardOmega]
  have hbound := uniformProbability_eventCount_ge_le I bad p t ht hbad
  rw [hprob] at hbound
  have : I.card * p / t < 1 := (div_lt_one ht).mpr hsmall
  linarith

/-- A direct averaging form: if the expected number of events is at most
`B`, then some outcome has event count at most `B`. -/
lemma exists_eventCount_le_of_expectation_le {iota : Type*} (I : Finset iota)
    (bad : iota → Omega → Prop) (B : Real)
    (hmean : uniformExpectation
      (fun omega ↦ (eventCount I bad omega : Real)) ≤ B) :
    ∃ omega, (eventCount I bad omega : Real) ≤ B := by
  have hcardOmega : (0 : Real) < Fintype.card Omega := by
    exact_mod_cast Fintype.card_pos
  rw [uniformExpectation] at hmean
  have hsum : ∑ omega, (eventCount I bad omega : Real) ≤
      ∑ _omega : Omega, B := by
    simpa [nsmul_eq_mul, mul_comm] using (div_le_iff₀ hcardOmega).1 hmean
  obtain ⟨omega, _homega, hle⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset Omega)) (by simp) hsum
  exact ⟨omega, hle⟩

/-- If every event has probability at most `p`, some outcome has at most
`|I| p` occurring events. -/
lemma exists_eventCount_le {iota : Type*} (I : Finset iota)
    (bad : iota → Omega → Prop) (p : Real)
    (hbad : ∀ i ∈ I, uniformProbability (bad i) ≤ p) :
    ∃ omega, (eventCount I bad omega : Real) ≤ I.card * p := by
  exact exists_eventCount_le_of_expectation_le I bad (I.card * p)
    (uniformExpectation_eventCount_le I bad p hbad)

section Collisions

variable {iota kappa : Type*} [LinearOrder iota] [DecidableEq kappa]

/-- The possible (unordered) edges among the indices in `I`, represented by
the increasing orientation. -/
def possibleEdges (I : Finset iota) : Finset (iota × iota) :=
  I.offDiag.filter fun ij ↦ ij.1 < ij.2

@[simp] lemma card_possibleEdges (I : Finset iota) :
    (possibleEdges I).card = I.card.choose 2 := by
  have hpossible : possibleEdges I =
      (I ×ˢ I).filter fun ij ↦ ij.1 < ij.2 := by
    ext ij
    simp [possibleEdges]
    grind
  rw [hpossible, Finset.card_product_filter_lt]

/-- The collision graph at an outcome.  An edge joins two indices whose
associated values agree. -/
def collisionEdges (I : Finset iota) (X : iota → Omega → kappa)
    (omega : Omega) : Finset (iota × iota) :=
  (possibleEdges I).filter fun ij ↦ X ij.1 omega = X ij.2 omega

@[simp] lemma mem_collisionEdges {I : Finset iota}
    {X : iota → Omega → kappa} {omega : Omega} {i j : iota} :
    (i, j) ∈ collisionEdges I X omega ↔
      i ∈ I ∧ j ∈ I ∧ i ≠ j ∧ i < j ∧ X i omega = X j omega := by
  simp [collisionEdges, possibleEdges, and_assoc]

lemma card_collisionEdges_eq_eventCount (I : Finset iota)
    (X : iota → Omega → kappa) (omega : Omega) :
    (collisionEdges I X omega).card =
      eventCount (possibleEdges I)
        (fun ij omega ↦ X ij.1 omega = X ij.2 omega) omega := by
  simp [collisionEdges, eventCount]

/-- Expected-edge bound for the collision graph. -/
lemma uniformExpectation_card_collisionEdges_le (I : Finset iota)
    (X : iota → Omega → kappa) (p : Real)
    (hcollision : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      uniformProbability (fun omega ↦ X i omega = X j omega) ≤ p) :
    uniformExpectation (fun omega ↦ ((collisionEdges I X omega).card : Real)) ≤
      I.card.choose 2 * p := by
  simp_rw [card_collisionEdges_eq_eventCount]
  rw [← card_possibleEdges]
  apply uniformExpectation_eventCount_le
  rintro ⟨i, j⟩ hij
  simp only [possibleEdges, mem_filter, mem_offDiag] at hij
  exact hcollision i hij.1.1 j hij.1.2.1 hij.1.2.2

/-- Collision-graph Markov bound: with high probability its total number of
edges is at most the displayed threshold. -/
lemma uniformProbability_card_collisionEdges_ge_le (I : Finset iota)
    (X : iota → Omega → kappa) (p t : Real) (ht : 0 < t)
    (hcollision : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      uniformProbability (fun omega ↦ X i omega = X j omega) ≤ p) :
    uniformProbability
        (fun omega ↦ t ≤ (collisionEdges I X omega).card) ≤
      I.card.choose 2 * p / t := by
  simp_rw [card_collisionEdges_eq_eventCount]
  rw [← card_possibleEdges]
  apply uniformProbability_eventCount_ge_le _ _ p t ht
  rintro ⟨i, j⟩ hij
  simp only [possibleEdges, mem_filter, mem_offDiag] at hij
  exact hcollision i hij.1.1 j hij.1.2.1 hij.1.2.2

/-- There is an outcome whose collision graph has at most its first-moment
edge budget. -/
lemma exists_card_collisionEdges_le (I : Finset iota)
    (X : iota → Omega → kappa) (p : Real)
    (hcollision : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      uniformProbability (fun omega ↦ X i omega = X j omega) ≤ p) :
    ∃ omega, ((collisionEdges I X omega).card : Real) ≤
      I.card.choose 2 * p := by
  simp_rw [card_collisionEdges_eq_eventCount]
  rw [← card_possibleEdges]
  apply exists_eventCount_le
  rintro ⟨i, j⟩ hij
  simp only [possibleEdges, mem_filter, mem_offDiag] at hij
  exact hcollision i hij.1.1 j hij.1.2.1 hij.1.2.2

end Collisions

end CollisionCounting
end Erdos636
