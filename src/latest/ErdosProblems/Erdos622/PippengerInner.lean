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
import ErdosProblems.Erdos76.PippengerSpencerInnerSurvival

/-!
# The finite joint-survival step in the Pippenger--Spencer nibble

This file supplies two estimates needed to propagate the sharp inner
marginal.  First, conditional acceptance of a live edge is squeezed between
`p * (1 - k * D * p)` and `p`.  Second, the probability that a finite set of
currently uncovered vertices remains uncovered is squeezed by the first two
Bonferroni bounds, with an explicit quadratic error.

Both results are completely finite.  In particular, they use the exact
finite-product probability masses from `Erdos76`, rather than a separate
measure-theoretic probability space.
-/

open Finset
open scoped BigOperators

namespace Erdos622

noncomputable section

attribute [local instance] Classical.propDecidable

namespace PippengerInner

open Erdos76

universe uV uE

variable {V : Type uV} {E : Type uE}
  [DecidableEq V] [Fintype E] [DecidableEq E]

namespace FiniteHypergraph

lemma one_sub_sum_le_prod_one_sub_local
    {I : Type*} [DecidableEq I] (s : Finset I) (p : I → ℝ)
    (hp₀ : ∀ i ∈ s, 0 ≤ p i) (hp₁ : ∀ i ∈ s, p i ≤ 1) :
    1 - ∑ i ∈ s, p i ≤ ∏ i ∈ s, (1 - p i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hpa₀ : 0 ≤ p a := hp₀ a (mem_insert_self a s)
      have hpa₁ : p a ≤ 1 := hp₁ a (mem_insert_self a s)
      have hs₀ : 0 ≤ ∑ i ∈ s, p i :=
        sum_nonneg fun i hi ↦ hp₀ i (mem_insert_of_mem hi)
      have hih := ih
        (fun i hi ↦ hp₀ i (mem_insert_of_mem hi))
        (fun i hi ↦ hp₁ i (mem_insert_of_mem hi))
      rw [sum_insert ha, prod_insert ha]
      calc
        1 - (p a + ∑ i ∈ s, p i) ≤
            (1 - p a) * (1 - ∑ i ∈ s, p i) := by nlinarith
        _ ≤ (1 - p a) * ∏ i ∈ s, (1 - p i) :=
          mul_le_mul_of_nonneg_left hih (sub_nonneg.mpr hpa₁)

lemma prod_one_sub_mem_Icc_local
    {I : Type*} [DecidableEq I] (s : Finset I) (p : I → ℝ)
    (hp₀ : ∀ i ∈ s, 0 ≤ p i) (hp₁ : ∀ i ∈ s, p i ≤ 1) :
    (∏ i ∈ s, (1 - p i)) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact prod_nonneg fun i hi ↦ sub_nonneg.mpr (hp₁ i hi)
  · exact prod_le_one (fun i hi ↦ sub_nonneg.mpr (hp₁ i hi))
      (fun i hi ↦ by linarith [hp₀ i hi])

lemma one_sub_natCast_le_indicator_eq_zero_local (n : ℕ) :
    1 - (n : ℝ) ≤ if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n =>
      rw [if_neg (Nat.succ_ne_zero n)]
      push_cast
      linarith [Nat.cast_nonneg n]

lemma indicator_eq_zero_le_one_sub_add_pairCount_local (n : ℕ) :
    (if n = 0 then (1 : ℝ) else 0) ≤
      1 - (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  by_cases h₀ : n = 0
  · simp [h₀]
  by_cases h₁ : n = 1
  · simp [h₁]
  rw [if_neg h₀]
  have hnNat : 2 ≤ n := by omega
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hprod : 0 ≤ ((n : ℝ) - 1) * ((n : ℝ) - 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- The currently live conflict neighbourhood is contained in the full
conflict neighbourhood of the distinguished edge. -/
lemma innerLiveConflictNeighbors_subset_conflicts
    (H : Erdos76.FiniteHypergraph V E) (M : Finset E) (e : E) :
    H.innerLiveConflictNeighbors M e ⊆
      (univ : Finset E).filter fun f ↦ H.Conflicts e f := by
  intro f hf
  have hf' := (H.mem_innerLiveConflictNeighbors M e f).1 hf
  exact mem_filter.mpr ⟨mem_univ f, hf'.1.symm, hf'.2.2⟩

/-- A live conflict neighbourhood has at most `k * D` indexed edges. -/
lemma innerLiveConflictNeighbors_card_le
    {H : Erdos76.FiniteHypergraph V E} {k D : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (M : Finset E) (e : E) :
    (H.innerLiveConflictNeighbors M e).card ≤ k * D := by
  calc
    (H.innerLiveConflictNeighbors M e).card ≤
        ((univ : Finset E).filter fun f ↦ H.Conflicts e f).card :=
      card_le_card (innerLiveConflictNeighbors_subset_conflicts H M e)
    _ = H.conflictDegree e := rfl
    _ ≤ k * D := H.conflictDegree_le_uniform_mul hunif hdeg e

/-- Conditional one-round acceptance of a live edge is at most its sampling
probability. -/
lemma innerNewAcceptanceMass_const_le
    (H : Erdos76.FiniteHypergraph V E) (M : Finset E) (p : ℝ) (e : E)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    H.innerNewAcceptanceMass M (fun _ ↦ p) e ≤
      p * (if H.InnerLive M e then 1 else 0) := by
  rw [H.innerNewAcceptanceMass_eq]
  by_cases hlive : H.InnerLive M e
  · rw [if_pos hlive, if_pos hlive, mul_one]
    exact mul_le_of_le_one_right hp₀
      (prod_one_sub_mem_Icc_local
        (H.innerLiveConflictNeighbors M e) (fun _ ↦ p)
        (fun _ _ ↦ hp₀) (fun _ _ ↦ hp₁)).2
  · simp [hlive]

/-- Conditional one-round acceptance of a live edge loses at most the union
bound for its full conflict neighbourhood. -/
lemma innerNewAcceptanceMass_const_ge
    {H : Erdos76.FiniteHypergraph V E} {k D : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (M : Finset E) (p : ℝ) (e : E)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    p * (1 - ((k * D : ℕ) : ℝ) * p) *
        (if H.InnerLive M e then 1 else 0) ≤
      H.innerNewAcceptanceMass M (fun _ ↦ p) e := by
  rw [H.innerNewAcceptanceMass_eq]
  by_cases hlive : H.InnerLive M e
  · rw [if_pos hlive, if_pos hlive, mul_one]
    let B := H.innerLiveConflictNeighbors M e
    have hprod : 1 - ∑ f ∈ B, p ≤ ∏ f ∈ B, (1 - p) :=
      one_sub_sum_le_prod_one_sub_local B (fun _ ↦ p)
        (fun _ _ ↦ hp₀) (fun _ _ ↦ hp₁)
    have hcard : (B.card : ℝ) ≤ ((k * D : ℕ) : ℝ) := by
      exact_mod_cast innerLiveConflictNeighbors_card_le hunif hdeg M e
    have hsum : (∑ _f ∈ B, p) = (B.card : ℝ) * p := by simp
    rw [hsum] at hprod
    have hlower : 1 - ((k * D : ℕ) : ℝ) * p ≤
        ∏ f ∈ B, (1 - p) := by
      exact (sub_le_sub_left
        (mul_le_mul_of_nonneg_right hcard hp₀) 1).trans hprod
    exact mul_le_mul_of_nonneg_left hlower hp₀
  · simp [hlive]

/-- The finite conditional mass that all vertices of `A` remain uncovered
after one inner step. -/
def jointUncoveredAfterStepMass
    (H : Erdos76.FiniteHypergraph V E) (M : Finset E)
    (p : E → ℝ) (A : Finset V) : ℝ :=
  ∑ S : Finset E, Erdos76.FiniteNibble.bernoulliMass univ p S *
    if ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v then 1 else 0

/-- First Bonferroni bound for joint one-step survival. -/
lemma one_sub_sum_innerNewAcceptanceMass_le_jointUncoveredAfterStepMass
    (H : Erdos76.FiniteHypergraph V E) (M : Finset E)
    (p : E → ℝ) (A : Finset V)
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    (hunc : ∀ v ∈ A, H.UncoveredBy M v) :
    1 - ∑ e ∈ H.edgesMeeting A, H.innerNewAcceptanceMass M p e ≤
      jointUncoveredAfterStepMass H M p A := by
  have hmass₀ (S : Finset E) :
      0 ≤ Erdos76.FiniteNibble.bernoulliMass univ p S :=
    Erdos76.FiniteNibble.bernoulliMass_nonneg (subset_univ S)
      (fun e _ ↦ hp₀ e) (fun e _ ↦ hp₁ e)
  have hpoint (S : Finset E) :
      1 - ((H.innerNewAcceptedMeeting M S A).card : ℝ) ≤
        if ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v then 1 else 0 := by
    by_cases h : ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v
    · have hzero : H.innerNewAcceptedMeeting M S A = ∅ :=
        (H.jointUncovered_innerStep_iff_innerNewAcceptedMeeting_eq_empty hunc).1 h
      rw [if_pos h]
      simp [hzero]
    · have hne : H.innerNewAcceptedMeeting M S A ≠ ∅ := fun hzero ↦
        h ((H.jointUncovered_innerStep_iff_innerNewAcceptedMeeting_eq_empty hunc).2 hzero)
      have hcard : (H.innerNewAcceptedMeeting M S A).card ≠ 0 :=
        card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hne)
      simpa [h, hcard] using
        one_sub_natCast_le_indicator_eq_zero_local
          (H.innerNewAcceptedMeeting M S A).card
  have hmass :
      (∑ S : Finset E, Erdos76.FiniteNibble.bernoulliMass univ p S) = 1 := by
    simpa using Erdos76.FiniteNibble.sum_bernoulliMass
      (univ : Finset E) p
  have hfirst :
      (∑ S : Finset E, Erdos76.FiniteNibble.bernoulliMass univ p S *
          ((H.innerNewAcceptedMeeting M S A).card : ℝ)) =
        ∑ e ∈ H.edgesMeeting A, H.innerNewAcceptanceMass M p e := by
    rw [show (∑ e ∈ H.edgesMeeting A,
        H.innerNewAcceptanceMass M p e) =
      ∑ e with ¬Disjoint (H.support e) A,
        H.innerNewAcceptanceMass M p e by rfl]
    exact H.sum_bernoulliMass_mul_innerNewAcceptedMeeting_card M p A
  calc
    1 - ∑ e ∈ H.edgesMeeting A, H.innerNewAcceptanceMass M p e =
        (∑ S : Finset E, Erdos76.FiniteNibble.bernoulliMass univ p S) -
          ∑ S : Finset E, Erdos76.FiniteNibble.bernoulliMass univ p S *
            ((H.innerNewAcceptedMeeting M S A).card : ℝ) := by
      rw [hmass, hfirst]
    _ =
        ∑ S : Finset E, Erdos76.FiniteNibble.bernoulliMass univ p S *
          (1 - ((H.innerNewAcceptedMeeting M S A).card : ℝ)) := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro S _
      ring
    _ ≤ ∑ S : Finset E, Erdos76.FiniteNibble.bernoulliMass univ p S *
          (if ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v then 1 else 0) := by
      exact sum_le_sum fun S _ ↦ mul_le_mul_of_nonneg_left (hpoint S) (hmass₀ S)
    _ = jointUncoveredAfterStepMass H M p A := rfl

/-- Second Bonferroni bound for joint one-step survival.  The error only
uses the size of `A`, the maximum degree, and the sampling probability. -/
lemma jointUncoveredAfterStepMass_le_one_sub_sum_add_quadratic
    (H : Erdos76.FiniteHypergraph V E) (M : Finset E)
    (A : Finset V) (D : ℕ) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hunc : ∀ v ∈ A, H.UncoveredBy M v) :
    jointUncoveredAfterStepMass H M (fun _ ↦ p) A ≤
      1 - ∑ e ∈ H.edgesMeeting A,
          H.innerNewAcceptanceMass M (fun _ ↦ p) e +
        ((((A.card * D : ℕ) : ℝ) * p) ^ 2) / 2 := by
  have hmass₀ (S : Finset E) :
      0 ≤ Erdos76.FiniteNibble.bernoulliMass univ (fun _ : E ↦ p) S :=
    Erdos76.FiniteNibble.bernoulliMass_nonneg (subset_univ S)
      (fun _ _ ↦ hp₀) (fun _ _ ↦ hp₁)
  have hpoint (S : Finset E) :
      (if ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v then (1 : ℝ) else 0) ≤
        1 - ((H.innerNewAcceptedMeeting M S A).card : ℝ) +
          ((H.innerNewAcceptedMeeting M S A).card : ℝ) *
            (((H.innerNewAcceptedMeeting M S A).card : ℝ) - 1) / 2 := by
    by_cases h : ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v
    · have hzero : H.innerNewAcceptedMeeting M S A = ∅ :=
        (H.jointUncovered_innerStep_iff_innerNewAcceptedMeeting_eq_empty hunc).1 h
      rw [if_pos h]
      simp [hzero]
    · have hne : H.innerNewAcceptedMeeting M S A ≠ ∅ := fun hzero ↦
        h ((H.jointUncovered_innerStep_iff_innerNewAcceptedMeeting_eq_empty hunc).2 hzero)
      have hcard : (H.innerNewAcceptedMeeting M S A).card ≠ 0 :=
        card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hne)
      simpa [h, hcard] using
        indicator_eq_zero_le_one_sub_add_pairCount_local
          (H.innerNewAcceptedMeeting M S A).card
  have hmass :
      (∑ S : Finset E,
        Erdos76.FiniteNibble.bernoulliMass univ (fun _ : E ↦ p) S) = 1 := by
    simpa using Erdos76.FiniteNibble.sum_bernoulliMass
      (univ : Finset E) (fun _ : E ↦ p)
  have hfirst :
      (∑ S : Finset E,
        Erdos76.FiniteNibble.bernoulliMass univ (fun _ : E ↦ p) S *
          ((H.innerNewAcceptedMeeting M S A).card : ℝ)) =
        ∑ e ∈ H.edgesMeeting A,
          H.innerNewAcceptanceMass M (fun _ ↦ p) e := by
    rw [show (∑ e ∈ H.edgesMeeting A,
        H.innerNewAcceptanceMass M (fun _ ↦ p) e) =
      ∑ e with ¬Disjoint (H.support e) A,
        H.innerNewAcceptanceMass M (fun _ ↦ p) e by rfl]
    exact H.sum_bernoulliMass_mul_innerNewAcceptedMeeting_card
      M (fun _ ↦ p) A
  have hlinear :
      (∑ S : Finset E,
        Erdos76.FiniteNibble.bernoulliMass univ (fun _ : E ↦ p) S *
          (1 - ((H.innerNewAcceptedMeeting M S A).card : ℝ))) =
        1 - ∑ e ∈ H.edgesMeeting A,
          H.innerNewAcceptanceMass M (fun _ ↦ p) e := by
    calc
      (∑ S : Finset E,
          Erdos76.FiniteNibble.bernoulliMass univ (fun _ : E ↦ p) S *
            (1 - ((H.innerNewAcceptedMeeting M S A).card : ℝ))) =
          (∑ S : Finset E,
            Erdos76.FiniteNibble.bernoulliMass univ (fun _ : E ↦ p) S) -
            ∑ S : Finset E,
              Erdos76.FiniteNibble.bernoulliMass univ (fun _ : E ↦ p) S *
                ((H.innerNewAcceptedMeeting M S A).card : ℝ) := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro S _
        ring
      _ = _ := by rw [hmass, hfirst]
  unfold jointUncoveredAfterStepMass
  calc
    (∑ S : Finset E, Erdos76.FiniteNibble.bernoulliMass univ (fun _ ↦ p) S *
        if ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v then 1 else 0) ≤
        ∑ S : Finset E, Erdos76.FiniteNibble.bernoulliMass univ (fun _ ↦ p) S *
          (1 - ((H.innerNewAcceptedMeeting M S A).card : ℝ) +
            ((H.innerNewAcceptedMeeting M S A).card : ℝ) *
              (((H.innerNewAcceptedMeeting M S A).card : ℝ) - 1) / 2) := by
      exact sum_le_sum fun S _ ↦ mul_le_mul_of_nonneg_left (hpoint S) (hmass₀ S)
    _ = 1 - ∑ e ∈ H.edgesMeeting A,
          H.innerNewAcceptanceMass M (fun _ ↦ p) e +
        ∑ S : Finset E, Erdos76.FiniteNibble.bernoulliMass univ (fun _ ↦ p) S *
          ((H.innerNewAcceptedMeeting M S A).card : ℝ) *
          (((H.innerNewAcceptedMeeting M S A).card : ℝ) - 1) / 2 := by
      calc
        (∑ S : Finset E,
            Erdos76.FiniteNibble.bernoulliMass univ (fun _ ↦ p) S *
              (1 - ((H.innerNewAcceptedMeeting M S A).card : ℝ) +
                ((H.innerNewAcceptedMeeting M S A).card : ℝ) *
                  (((H.innerNewAcceptedMeeting M S A).card : ℝ) - 1) / 2)) =
            (∑ S : Finset E,
              Erdos76.FiniteNibble.bernoulliMass univ (fun _ ↦ p) S *
                (1 - ((H.innerNewAcceptedMeeting M S A).card : ℝ))) +
              ∑ S : Finset E,
                Erdos76.FiniteNibble.bernoulliMass univ (fun _ ↦ p) S *
                  ((H.innerNewAcceptedMeeting M S A).card : ℝ) *
                  (((H.innerNewAcceptedMeeting M S A).card : ℝ) - 1) / 2 := by
          rw [← sum_add_distrib]
          apply sum_congr rfl
          intro S _
          ring
        _ = _ := by rw [hlinear]
    _ ≤ 1 - ∑ e ∈ H.edgesMeeting A,
          H.innerNewAcceptanceMass M (fun _ ↦ p) e +
        ((((A.card * D : ℕ) : ℝ) * p) ^ 2) / 2 := by
      gcongr
      exact H.sum_bernoulliMass_mul_innerNewAcceptedMeeting_pairCount_le
        M A D p hp₀ hp₁ hdeg

/-- The lower one-step bound with its current-state indicator made
explicit.  This form remains valid when `A` was already covered. -/
lemma indicator_sub_indicator_mul_sum_le_jointUncoveredAfterStepMass
    (H : Erdos76.FiniteHypergraph V E) (M : Finset E)
    (p : E → ℝ) (A : Finset V)
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1) :
    (if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) -
        (if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) *
          (∑ e ∈ H.edgesMeeting A, H.innerNewAcceptanceMass M p e) ≤
      jointUncoveredAfterStepMass H M p A := by
  by_cases hunc : ∀ v ∈ A, H.UncoveredBy M v
  · rw [if_pos hunc]
    simpa using
      one_sub_sum_innerNewAcceptanceMass_le_jointUncoveredAfterStepMass
        H M p A hp₀ hp₁ hunc
  · have hstep (S : Finset E) :
        ¬∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v :=
      H.not_jointUncovered_innerStep hunc
    have hzero : jointUncoveredAfterStepMass H M p A = 0 := by
      unfold jointUncoveredAfterStepMass
      apply sum_eq_zero
      intro S _
      rw [if_neg (hstep S)]
      ring
    simp [hunc, hzero]

/-- The upper one-step bound with its current-state indicator made
explicit. -/
lemma jointUncoveredAfterStepMass_le_indicator_sub_sum_add_quadratic
    (H : Erdos76.FiniteHypergraph V E) (M : Finset E)
    (A : Finset V) (D : ℕ) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) :
    jointUncoveredAfterStepMass H M (fun _ ↦ p) A ≤
      (if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) -
        (if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) *
          (∑ e ∈ H.edgesMeeting A,
            H.innerNewAcceptanceMass M (fun _ ↦ p) e) +
        (if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) *
          ((((A.card * D : ℕ) : ℝ) * p) ^ 2 / 2) := by
  by_cases hunc : ∀ v ∈ A, H.UncoveredBy M v
  · rw [if_pos hunc]
    simpa using
      jointUncoveredAfterStepMass_le_one_sub_sum_add_quadratic
        H M A D p hp₀ hp₁ hdeg hunc
  · have hstep (S : Finset E) :
        ¬∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v :=
      H.not_jointUncovered_innerStep hunc
    have hzero : jointUncoveredAfterStepMass H M (fun _ ↦ p) A = 0 := by
      unfold jointUncoveredAfterStepMass
      apply sum_eq_zero
      intro S _
      rw [if_neg (hstep S)]
      ring
    simp [hunc, hzero]

/-- The current joint-uncovered indicator times the total conditional new
acceptance mass is bounded above by raw sampling of all currently live
meeting edges. -/
lemma indicator_mul_sum_innerNewAcceptanceMass_le
    {H : Erdos76.FiniteHypergraph V E} {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (M : Finset E) (A : Finset V)
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) *
        (∑ e ∈ H.edgesMeeting A,
          H.innerNewAcceptanceMass M (fun _ ↦ p) e) ≤
      p * ∑ e ∈ H.edgesMeeting A,
        (if ∀ v ∈ A ∪ H.support e, H.UncoveredBy M v then 1 else 0) := by
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro e he
  have hindicator :
      0 ≤ (if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) := by
    split <;> norm_num
  calc
    (if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) *
        H.innerNewAcceptanceMass M (fun _ ↦ p) e ≤
      (if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) *
        (p * (if H.InnerLive M e then 1 else 0)) :=
      mul_le_mul_of_nonneg_left
        (innerNewAcceptanceMass_const_le H M p e hp₀ hp₁) hindicator
    _ = p * (if ∀ v ∈ A ∪ H.support e,
          H.UncoveredBy M v then 1 else 0) := by
      rw [← H.jointUncovered_indicator_mul_innerLive_indicator hk hunif M A e]
      ring

/-- The alteration lower coefficient supplies the reverse comparison. -/
lemma sub_mul_sum_indicator_le_indicator_mul_sum_innerNewAcceptanceMass
    {H : Erdos76.FiniteHypergraph V E} {k D : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (M : Finset E) (A : Finset V) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (p - ((k * D : ℕ) : ℝ) * p ^ 2) *
        (∑ e ∈ H.edgesMeeting A,
          (if ∀ v ∈ A ∪ H.support e, H.UncoveredBy M v then 1 else 0)) ≤
      (if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) *
        (∑ e ∈ H.edgesMeeting A,
          H.innerNewAcceptanceMass M (fun _ ↦ p) e) := by
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro e _
  have hindicator :
      0 ≤ (if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) := by
    split <;> norm_num
  calc
    (p - ((k * D : ℕ) : ℝ) * p ^ 2) *
        (if ∀ v ∈ A ∪ H.support e, H.UncoveredBy M v then 1 else 0) =
      (if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) *
        (p * (1 - ((k * D : ℕ) : ℝ) * p) *
          (if H.InnerLive M e then 1 else 0)) := by
      rw [← H.jointUncovered_indicator_mul_innerLive_indicator hk hunif M A e]
      ring
    _ ≤ (if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) *
        H.innerNewAcceptanceMass M (fun _ ↦ p) e :=
      mul_le_mul_of_nonneg_left
        (innerNewAcceptanceMass_const_ge hunif hdeg M p e hp₀ hp₁)
        hindicator

/-- Exchange the trajectory sum with an arbitrary finite edge sum of joint
uncovered indicators. -/
lemma sum_productMass_mul_sum_jointUncoveredIndicator
    (H : Erdos76.FiniteHypergraph V E) (w : Finset E → ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V) (B : Finset E) :
    (∑ X : Fin r → Finset E, Erdos76.FiniteProduct.productMass w X *
        ∑ e ∈ B,
          (if ∀ v ∈ A ∪ H.support e,
              H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
            then 1 else 0)) =
      ∑ e ∈ B, H.innerJointUncoveredMass w r M (A ∪ H.support e) := by
  simp_rw [Finset.mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  rfl

/-- Explicit forward recurrence for all finite joint-uncovered moments.
This is the finite combinatorial input for the later comparison with the
mean-field Euler trajectory. -/
theorem innerJointUncoveredMass_succ_mem_Icc
    {H : Erdos76.FiniteHypergraph V E} {k D : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (M : Finset E) (A : Finset V) (r : ℕ) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    H.innerJointUncoveredMass
        (Erdos76.FiniteNibble.bernoulliMass univ (fun _ ↦ p)) (r + 1) M A ∈
      Set.Icc
        (H.innerJointUncoveredMass
            (Erdos76.FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A -
          p * ∑ e ∈ H.edgesMeeting A,
            H.innerJointUncoveredMass
              (Erdos76.FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M
              (A ∪ H.support e))
        (H.innerJointUncoveredMass
            (Erdos76.FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A -
          (p - ((k * D : ℕ) : ℝ) * p ^ 2) *
            ∑ e ∈ H.edgesMeeting A,
              H.innerJointUncoveredMass
                (Erdos76.FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M
                (A ∪ H.support e) +
          ((((A.card * D : ℕ) : ℝ) * p) ^ 2 / 2) *
            H.innerJointUncoveredMass
              (Erdos76.FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A) := by
  let w : Finset E → ℝ :=
    Erdos76.FiniteNibble.bernoulliMass univ (fun _ ↦ p)
  let state : (Fin r → Finset E) → Finset E := fun X ↦
    (List.ofFn X).foldl H.innerStep M
  let current : (Fin r → Finset E) → ℝ := fun X ↦
    if ∀ v ∈ A, H.UncoveredBy (state X) v then 1 else 0
  let enlarged : (Fin r → Finset E) → E → ℝ := fun X e ↦
    if ∀ v ∈ A ∪ H.support e, H.UncoveredBy (state X) v then 1 else 0
  let error : ℝ := ((((A.card * D : ℕ) : ℝ) * p) ^ 2) / 2
  have hmass₀ (X : Fin r → Finset E) :
      0 ≤ Erdos76.FiniteProduct.productMass w X := by
    unfold Erdos76.FiniteProduct.productMass
    exact prod_nonneg fun i _ ↦
      Erdos76.FiniteNibble.bernoulliMass_nonneg (subset_univ (X i))
        (fun _ _ ↦ hp₀) (fun _ _ ↦ hp₁)
  have hcurrent :
      (∑ X : Fin r → Finset E,
        Erdos76.FiniteProduct.productMass w X * current X) =
        H.innerJointUncoveredMass w r M A := by
    rfl
  have henlarged :
      (∑ X : Fin r → Finset E,
        Erdos76.FiniteProduct.productMass w X *
          ∑ e ∈ H.edgesMeeting A, enlarged X e) =
        ∑ e ∈ H.edgesMeeting A,
          H.innerJointUncoveredMass w r M (A ∪ H.support e) := by
    simpa [enlarged, state] using
      sum_productMass_mul_sum_jointUncoveredIndicator
        H w r M A (H.edgesMeeting A)
  have hlowerPoint (X : Fin r → Finset E) :
      current X - p * ∑ e ∈ H.edgesMeeting A, enlarged X e ≤
        jointUncoveredAfterStepMass H (state X) (fun _ ↦ p) A := by
    have hbase :=
      indicator_sub_indicator_mul_sum_le_jointUncoveredAfterStepMass
        H (state X) (fun _ ↦ p) A (fun _ ↦ hp₀) (fun _ ↦ hp₁)
    have hnew := indicator_mul_sum_innerNewAcceptanceMass_le
      hk hunif (state X) A p hp₀ hp₁
    dsimp only [current, enlarged, state] at hbase hnew ⊢
    linarith
  have hupperPoint (X : Fin r → Finset E) :
      jointUncoveredAfterStepMass H (state X) (fun _ ↦ p) A ≤
        current X - (p - ((k * D : ℕ) : ℝ) * p ^ 2) *
            ∑ e ∈ H.edgesMeeting A, enlarged X e + error * current X := by
    have hbase :=
      jointUncoveredAfterStepMass_le_indicator_sub_sum_add_quadratic
        H (state X) A D p hp₀ hp₁ hdeg
    have hnew := sub_mul_sum_indicator_le_indicator_mul_sum_innerNewAcceptanceMass
      hk hunif hdeg (state X) A p hp₀ hp₁
    dsimp only [current, enlarged, error, state] at hbase hnew ⊢
    linarith
  have hstep :
      H.innerJointUncoveredMass w (r + 1) M A =
        ∑ X : Fin r → Finset E,
          Erdos76.FiniteProduct.productMass w X *
            jointUncoveredAfterStepMass H (state X) (fun _ ↦ p) A := by
    rw [H.innerJointUncoveredMass_bernoulli_succ_last]
    rfl
  change H.innerJointUncoveredMass w (r + 1) M A ∈ _
  constructor
  · rw [hstep]
    calc
      H.innerJointUncoveredMass w r M A -
          p * ∑ e ∈ H.edgesMeeting A,
            H.innerJointUncoveredMass w r M (A ∪ H.support e) =
        ∑ X : Fin r → Finset E,
          Erdos76.FiniteProduct.productMass w X *
            (current X - p * ∑ e ∈ H.edgesMeeting A, enlarged X e) := by
        rw [← hcurrent, ← henlarged]
        symm
        calc
          (∑ X : Fin r → Finset E,
              Erdos76.FiniteProduct.productMass w X *
                (current X - p * ∑ e ∈ H.edgesMeeting A, enlarged X e)) =
              ∑ X : Fin r → Finset E,
                (Erdos76.FiniteProduct.productMass w X * current X -
                  p * (Erdos76.FiniteProduct.productMass w X *
                    ∑ e ∈ H.edgesMeeting A, enlarged X e)) := by
            apply sum_congr rfl
            intro X _
            ring
          _ = _ := by rw [sum_sub_distrib, ← mul_sum]
      _ ≤ ∑ X : Fin r → Finset E,
          Erdos76.FiniteProduct.productMass w X *
            jointUncoveredAfterStepMass H (state X) (fun _ ↦ p) A := by
        exact sum_le_sum fun X _ ↦
          mul_le_mul_of_nonneg_left (hlowerPoint X) (hmass₀ X)
  · rw [hstep]
    calc
      (∑ X : Fin r → Finset E,
          Erdos76.FiniteProduct.productMass w X *
            jointUncoveredAfterStepMass H (state X) (fun _ ↦ p) A) ≤
        ∑ X : Fin r → Finset E,
          Erdos76.FiniteProduct.productMass w X *
            (current X - (p - ((k * D : ℕ) : ℝ) * p ^ 2) *
              ∑ e ∈ H.edgesMeeting A, enlarged X e + error * current X) := by
        exact sum_le_sum fun X _ ↦
          mul_le_mul_of_nonneg_left (hupperPoint X) (hmass₀ X)
      _ = H.innerJointUncoveredMass w r M A -
          (p - ((k * D : ℕ) : ℝ) * p ^ 2) *
            ∑ e ∈ H.edgesMeeting A,
              H.innerJointUncoveredMass w r M (A ∪ H.support e) +
          error * H.innerJointUncoveredMass w r M A := by
        rw [← hcurrent, ← henlarged]
        calc
          (∑ X : Fin r → Finset E,
              Erdos76.FiniteProduct.productMass w X *
                (current X - (p - ((k * D : ℕ) : ℝ) * p ^ 2) *
                  ∑ e ∈ H.edgesMeeting A, enlarged X e +
                  error * current X)) =
              ∑ X : Fin r → Finset E,
                (Erdos76.FiniteProduct.productMass w X * current X -
                  (p - ((k * D : ℕ) : ℝ) * p ^ 2) *
                    (Erdos76.FiniteProduct.productMass w X *
                      ∑ e ∈ H.edgesMeeting A, enlarged X e) +
                  error * (Erdos76.FiniteProduct.productMass w X * current X)) := by
            apply sum_congr rfl
            intro X _
            ring
          _ = (∑ X : Fin r → Finset E,
                Erdos76.FiniteProduct.productMass w X * current X) -
              (p - ((k * D : ℕ) : ℝ) * p ^ 2) *
                (∑ X : Fin r → Finset E,
                  Erdos76.FiniteProduct.productMass w X *
                    ∑ e ∈ H.edgesMeeting A, enlarged X e) +
              error * (∑ X : Fin r → Finset E,
                Erdos76.FiniteProduct.productMass w X * current X) := by
            rw [sum_add_distrib, sum_sub_distrib]
            congr 1
            · rw [← mul_sum]
            · rw [← mul_sum]

/-! ### Rank-two meeting-sum comparison -/

/-- A convenient abbreviation for the homogeneous Bernoulli joint moment. -/
def rankTwoJointMoment (H : Erdos76.FiniteHypergraph V E)
    (beta : ℝ) (D r : ℕ) (A : Finset V) : ℝ :=
  H.innerJointUncoveredMass
    (Erdos76.FiniteNibble.bernoulliMass univ
      (fun _ ↦ beta / (D : ℝ))) r ∅ A

/-- The rank-two Euler survival trajectory, isolated here so the graph
specialization does not depend on the general sharp-analysis module. -/
def rankTwoMeanFieldSurvival (beta : ℝ) : ℕ → ℝ
  | 0 => 1
  | r + 1 => rankTwoMeanFieldSurvival beta r -
      beta * rankTwoMeanFieldSurvival beta r ^ 2

@[simp] lemma rankTwoMeanFieldSurvival_zero (beta : ℝ) :
    rankTwoMeanFieldSurvival beta 0 = 1 := rfl

@[simp] lemma rankTwoMeanFieldSurvival_succ (beta : ℝ) (r : ℕ) :
    rankTwoMeanFieldSurvival beta (r + 1) = rankTwoMeanFieldSurvival beta r -
      beta * rankTwoMeanFieldSurvival beta r ^ 2 := rfl

lemma rankTwoMeanFieldSurvival_mem_Icc
    {beta : ℝ} (hbeta₀ : 0 ≤ beta) (hbeta₁ : beta ≤ 1) (r : ℕ) :
    rankTwoMeanFieldSurvival beta r ∈ Set.Icc (0 : ℝ) 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [rankTwoMeanFieldSurvival_succ]
      have hySq₀ : 0 ≤ rankTwoMeanFieldSurvival beta r ^ 2 := sq_nonneg _
      have hfactor : 0 ≤ 1 - beta * rankTwoMeanFieldSurvival beta r := by
        exact sub_nonneg.mpr (mul_le_one₀ hbeta₁ ih.1 ih.2)
      constructor
      · rw [show rankTwoMeanFieldSurvival beta r -
            beta * rankTwoMeanFieldSurvival beta r ^ 2 =
          rankTwoMeanFieldSurvival beta r *
            (1 - beta * rankTwoMeanFieldSurvival beta r) by ring]
        exact mul_nonneg ih.1 hfactor
      · rw [show rankTwoMeanFieldSurvival beta r -
            beta * rankTwoMeanFieldSurvival beta r ^ 2 =
          rankTwoMeanFieldSurvival beta r *
            (1 - beta * rankTwoMeanFieldSurvival beta r) by ring]
        have hfactorOne : 1 - beta * rankTwoMeanFieldSurvival beta r ≤ 1 :=
          sub_le_self _ (mul_nonneg hbeta₀ ih.1)
        exact (mul_le_mul_of_nonneg_left hfactorOne ih.1).trans ih.2

/-- Error after linearizing the power map across one Euler decrement. -/
def rankTwoPowerLinearizationError (a : ℕ) (x y d : ℝ) : ℝ :=
  x ^ a - y ^ a + (a : ℝ) * d * y ^ (a - 1)

/-- Coarse second-order bound for the power-map linearization on `[0,1]`. -/
lemma rankTwoPowerLinearizationError_mem_Icc
    (a : ℕ) {x y d : ℝ}
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (hy₁ : y ≤ 1)
    (hd₀ : 0 ≤ d) (hxy : x = y - d) :
    rankTwoPowerLinearizationError a x y d ∈
      Set.Icc 0 (((a : ℝ) ^ 2) * d ^ 2) := by
  induction a with
  | zero => simp [rankTwoPowerLinearizationError]
  | succ a ih =>
      by_cases ha : a = 0
      · subst a
        constructor
        · simp [rankTwoPowerLinearizationError, hxy]
        · simp [rankTwoPowerLinearizationError, hxy, sq_nonneg]
      · have ha₁ : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
        have hy₀ : 0 ≤ y := by linarith [hxy]
        have hrec :
            rankTwoPowerLinearizationError (a + 1) x y d =
              x * rankTwoPowerLinearizationError a x y d +
                (a : ℝ) * d ^ 2 * y ^ (a - 1) := by
          unfold rankTwoPowerLinearizationError
          rw [pow_succ, show a + 1 - 1 = a by omega]
          have hpow : y ^ a = y ^ (a - 1) * y := by
            conv_lhs => rw [← Nat.sub_add_cancel ha₁]
            rw [pow_add, pow_one]
          simp_rw [hpow]
          rw [hxy]
          push_cast
          ring_nf
          rw [hpow]
          ring
        rw [hrec]
        constructor
        · exact add_nonneg
            (mul_nonneg hx₀ ih.1)
            (mul_nonneg
              (mul_nonneg (Nat.cast_nonneg a) (sq_nonneg d))
              (pow_nonneg hy₀ _))
        · have hpow₁ : y ^ (a - 1) ≤ 1 := pow_le_one₀ hy₀ hy₁
          have hfirst :
              x * rankTwoPowerLinearizationError a x y d ≤
                1 * (((a : ℝ) ^ 2) * d ^ 2) :=
            mul_le_mul hx₁ ih.2 ih.1 (by norm_num)
          have hsecond :
              (a : ℝ) * d ^ 2 * y ^ (a - 1) ≤
                (a : ℝ) * d ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hpow₁
              (mul_nonneg (Nat.cast_nonneg a) (sq_nonneg d))
          calc
            x * rankTwoPowerLinearizationError a x y d +
                (a : ℝ) * d ^ 2 * y ^ (a - 1) ≤
              1 * (((a : ℝ) ^ 2) * d ^ 2) +
                (a : ℝ) * d ^ 2 * 1 := add_le_add hfirst hsecond
            _ ≤ (((a + 1 : ℕ) : ℝ) ^ 2) * d ^ 2 := by
              push_cast
              have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
              have haPlus : 0 ≤ (a : ℝ) + 1 := by positivity
              nlinarith [mul_nonneg haPlus hd2]

/-- The error budget propagated by the rank-two joint-moment induction. -/
def rankTwoMomentError (K D s C : ℕ) (beta : ℝ) : ℕ → ℝ
  | 0 => 0
  | r + 1 =>
      (1 + beta * (K : ℝ)) * rankTwoMomentError K D s C beta r +
        beta * (((K * s + 3 * K ^ 2 * C : ℕ) : ℝ) / (D : ℝ)) +
        (((3 : ℝ) / 2) * (K : ℝ) ^ 2 + 2 * (K : ℝ)) * beta ^ 2

@[simp] lemma rankTwoMomentError_zero (K D s C : ℕ) (beta : ℝ) :
    rankTwoMomentError K D s C beta 0 = 0 := rfl

@[simp] lemma rankTwoMomentError_succ (K D s C r : ℕ) (beta : ℝ) :
    rankTwoMomentError K D s C beta (r + 1) =
      (1 + beta * (K : ℝ)) * rankTwoMomentError K D s C beta r +
        beta * (((K * s + 3 * K ^ 2 * C : ℕ) : ℝ) / (D : ℝ)) +
        (((3 : ℝ) / 2) * (K : ℝ) ^ 2 + 2 * (K : ℝ)) * beta ^ 2 := rfl

/-- In a rank-two near-regular hypergraph, uniform control of enlarged joint
moments controls their sum over the edges meeting `A`. -/
lemma rankTwo_sum_jointMoment_meeting_sub_le
    {H : Erdos76.FiniteHypergraph V E} {D s C r : ℕ}
    (hunif : H.IsUniform 2)
    (hsD : s ≤ D)
    (hdegUpper : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hdegLower : ∀ v ∈ H.vertexSet, D - s ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {beta y epsilon : ℝ}
    (hp₀ : 0 ≤ beta / (D : ℝ)) (hp₁ : beta / (D : ℝ) ≤ 1)
    (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1) (hepsilon₀ : 0 ≤ epsilon)
    (A : Finset V) (hAsub : A ⊆ H.vertexSet)
    (hclose : ∀ B : Finset V, B ⊆ H.vertexSet → B.card ≤ A.card + 2 →
      |rankTwoJointMoment H beta D r B - y ^ B.card| ≤ epsilon) :
    |∑ e ∈ H.edgesMeeting A, rankTwoJointMoment H beta D r (A ∪ H.support e) -
        ((A.card * D : ℕ) : ℝ) * y ^ (A.card + 1)| ≤
      ((A.card * D : ℕ) : ℝ) * epsilon +
        ((A.card * s + 3 * A.card ^ 2 * C : ℕ) : ℝ) := by
  let t : ℝ := y ^ (A.card + 1)
  let J : E → ℝ := fun e ↦
    rankTwoJointMoment H beta D r (A ∪ H.support e)
  have ht₀ : 0 ≤ t := pow_nonneg hy₀ _
  have ht₁ : t ≤ 1 := pow_le_one₀ hy₀ hy₁
  have hJmem (e : E) : J e ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [J, rankTwoJointMoment] using
      (H.innerJointUncoveredMass_bernoulli_mem_Icc
        (p := fun _ ↦ beta / (D : ℝ)) (fun _ ↦ hp₀) (fun _ ↦ hp₁)
        r ∅ (A ∪ H.support e))
  have hcap (e : E) : (A ∪ H.support e).card ≤ A.card + 2 := by
    calc
      (A ∪ H.support e).card ≤ A.card + (H.support e).card :=
        Finset.card_union_le A (H.support e)
      _ = A.card + 2 := by rw [hunif e]
  have hterm (e : E) (he : e ∈ H.edgesMeeting A) :
      |J e - t| ≤
        if e ∈ H.multiMeetingEdges A then 1 else epsilon := by
    by_cases hmulti : e ∈ H.multiMeetingEdges A
    · rw [if_pos hmulti, abs_le]
      exact ⟨by linarith [(hJmem e).1, ht₁],
        by linarith [(hJmem e).2, ht₀]⟩
    · rw [if_neg hmulti]
      have hcard := H.card_union_support_eq_of_mem_edgesMeeting_not_multi
        A hunif he hmulti
      have hsub : A ∪ H.support e ⊆ H.vertexSet :=
        union_subset hAsub (H.support_subset_vertexSet e)
      have h := hclose (A ∪ H.support e) hsub (hcap e)
      simpa [J, t, hcard] using h
  have hmeetingCard : (H.edgesMeeting A).card ≤ A.card * D :=
    H.edgesMeeting_card_le_mul_degree A D hdegUpper
  have hmultiCard : (H.multiMeetingEdges A).card ≤ A.card ^ 2 * C :=
    H.multiMeetingEdges_card_le_sq_mul_pairDegree A C hpair
  have hdegreeLowOnA : ∀ v ∈ A, D - s ≤ H.edgeDegree v := by
    intro v hv
    exact hdegLower v (hAsub hv)
  have hmeetingLow : A.card * (D - s) ≤
      (H.edgesMeeting A).card + A.card ^ 2 * C * 2 :=
    H.card_mul_degreeLower_le_edgesMeeting_add_pairError
      A hunif hdegreeLowOnA hpair
  have hdeficitNat : A.card * D - (H.edgesMeeting A).card ≤
      A.card * s + 2 * A.card ^ 2 * C := by
    have hsplit : A.card * D = A.card * (D - s) + A.card * s := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hsD]
    have hmeetingLow' : A.card * (D - s) ≤
        (H.edgesMeeting A).card + 2 * (A.card ^ 2 * C) := by
      omega
    apply Nat.sub_le_iff_le_add.mpr
    calc
      A.card * D = A.card * (D - s) + A.card * s := hsplit
      _ ≤ ((H.edgesMeeting A).card + 2 * (A.card ^ 2 * C)) +
          A.card * s := Nat.add_le_add_right hmeetingLow' _
      _ = (H.edgesMeeting A).card +
          (A.card * s + 2 * A.card ^ 2 * C) := by
        simp only [Nat.mul_assoc]
        ac_rfl
      _ = (A.card * s + 2 * A.card ^ 2 * C) +
          (H.edgesMeeting A).card := Nat.add_comm _ _
  have hsumAroundCard :
      |∑ e ∈ H.edgesMeeting A, J e -
          ((H.edgesMeeting A).card : ℝ) * t| ≤
        ((A.card * D : ℕ) : ℝ) * epsilon +
          ((A.card ^ 2 * C : ℕ) : ℝ) := by
    have hcardSum : ((H.edgesMeeting A).card : ℝ) * t =
        ∑ _e ∈ H.edgesMeeting A, t := by simp
    rw [hcardSum, ← Finset.sum_sub_distrib]
    calc
      |∑ e ∈ H.edgesMeeting A, (J e - t)| ≤
          ∑ e ∈ H.edgesMeeting A, |J e - t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ H.edgesMeeting A,
          if e ∈ H.multiMeetingEdges A then 1 else epsilon := by
        exact sum_le_sum fun e he ↦ hterm e he
      _ ≤ ((A.card * D : ℕ) : ℝ) * epsilon +
          ((A.card ^ 2 * C : ℕ) : ℝ) := by
        have hfilter :
            (H.edgesMeeting A).filter (fun e ↦ e ∈ H.multiMeetingEdges A) =
              H.multiMeetingEdges A := by
          ext e
          simp [Erdos76.FiniteHypergraph.multiMeetingEdges]
        calc
          (∑ e ∈ H.edgesMeeting A,
              if e ∈ H.multiMeetingEdges A then 1 else epsilon) ≤
              ∑ e ∈ H.edgesMeeting A,
                (epsilon + if e ∈ H.multiMeetingEdges A then 1 else 0) := by
            apply sum_le_sum
            intro e he
            by_cases h : e ∈ H.multiMeetingEdges A <;> simp [h, hepsilon₀]
          _ = ((H.edgesMeeting A).card : ℝ) * epsilon +
              ((H.multiMeetingEdges A).card : ℝ) := by
            rw [sum_add_distrib]
            simp only [sum_const, nsmul_eq_mul]
            have hindicator :
                (∑ e ∈ H.edgesMeeting A,
                    if e ∈ H.multiMeetingEdges A then (1 : ℝ) else 0) =
                  ((H.multiMeetingEdges A).card : ℝ) := by
              rw [← sum_filter]
              rw [hfilter]
              simp
            rw [hindicator]
          _ ≤ ((A.card * D : ℕ) : ℝ) * epsilon +
              ((A.card ^ 2 * C : ℕ) : ℝ) := by
            have hmeetingR : ((H.edgesMeeting A).card : ℝ) * epsilon ≤
                ((A.card * D : ℕ) : ℝ) * epsilon :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hmeetingCard) hepsilon₀
            have hmultiR : ((H.multiMeetingEdges A).card : ℝ) ≤
                ((A.card ^ 2 * C : ℕ) : ℝ) := by exact_mod_cast hmultiCard
            exact add_le_add hmeetingR hmultiR
  have hcardAroundIdeal :
      |((H.edgesMeeting A).card : ℝ) * t -
          ((A.card * D : ℕ) : ℝ) * t| ≤
        ((A.card * s + 2 * A.card ^ 2 * C : ℕ) : ℝ) := by
    rw [← sub_mul, abs_mul, abs_of_nonneg ht₀]
    have hcardR : ((H.edgesMeeting A).card : ℝ) ≤
        ((A.card * D : ℕ) : ℝ) := by exact_mod_cast hmeetingCard
    rw [abs_of_nonpos (sub_nonpos.mpr hcardR), neg_sub]
    have hdeficitR :
        ((A.card * D : ℕ) : ℝ) - ((H.edgesMeeting A).card : ℝ) ≤
          ((A.card * s + 2 * A.card ^ 2 * C : ℕ) : ℝ) := by
      exact_mod_cast hdeficitNat
    have hnonneg : 0 ≤
        ((A.card * D : ℕ) : ℝ) - ((H.edgesMeeting A).card : ℝ) := by
      linarith
    calc
      (((A.card * D : ℕ) : ℝ) - ((H.edgesMeeting A).card : ℝ)) * t ≤
          (((A.card * D : ℕ) : ℝ) - ((H.edgesMeeting A).card : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left ht₁ hnonneg
      _ ≤ ((A.card * s + 2 * A.card ^ 2 * C : ℕ) : ℝ) := by
        simpa using hdeficitR
  change |∑ e ∈ H.edgesMeeting A, J e -
      ((A.card * D : ℕ) : ℝ) * t| ≤ _
  calc
    |∑ e ∈ H.edgesMeeting A, J e -
        ((A.card * D : ℕ) : ℝ) * t| ≤
      |∑ e ∈ H.edgesMeeting A, J e -
          ((H.edgesMeeting A).card : ℝ) * t| +
        |((H.edgesMeeting A).card : ℝ) * t -
          ((A.card * D : ℕ) : ℝ) * t| := by
      exact abs_sub_le _ _ _
    _ ≤ (((A.card * D : ℕ) : ℝ) * epsilon +
          ((A.card ^ 2 * C : ℕ) : ℝ)) +
        ((A.card * s + 2 * A.card ^ 2 * C : ℕ) : ℝ) :=
      add_le_add hsumAroundCard hcardAroundIdeal
    _ = ((A.card * D : ℕ) : ℝ) * epsilon +
        ((A.card * s + 3 * A.card ^ 2 * C : ℕ) : ℝ) := by
      push_cast
      ring

lemma rankTwoMomentError_nonneg
    (K D s C r : ℕ) {beta : ℝ} (hbeta₀ : 0 ≤ beta) :
    0 ≤ rankTwoMomentError K D s C beta r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [rankTwoMomentError_succ]
      have hcoef₀ : 0 ≤ 1 + beta * (K : ℝ) := by positivity
      have hstruct₀ : 0 ≤
          (((K * s + 3 * K ^ 2 * C : ℕ) : ℝ) / (D : ℝ)) := by
        positivity
      have hquad₀ : 0 ≤
          ((3 : ℝ) / 2) * (K : ℝ) ^ 2 + 2 * (K : ℝ) := by
        positivity
      positivity

/-- Scaled form of the rank-two meeting-sum estimate.  This is the exact
first-order term used in the Euler comparison. -/
lemma rankTwo_scaled_sum_jointMoment_meeting_sub_le
    {H : Erdos76.FiniteHypergraph V E} {D s C K r : ℕ}
    (hD : 0 < D) (hunif : H.IsUniform 2) (hsD : s ≤ D)
    (hdegUpper : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hdegLower : ∀ v ∈ H.vertexSet, D - s ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {beta y epsilon : ℝ} (hbeta₀ : 0 ≤ beta)
    (hp₁ : beta / (D : ℝ) ≤ 1)
    (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1) (hepsilon₀ : 0 ≤ epsilon)
    (A : Finset V) (hAsub : A ⊆ H.vertexSet) (hAK : A.card ≤ K)
    (hclose : ∀ B : Finset V, B ⊆ H.vertexSet → B.card ≤ A.card + 2 →
      |rankTwoJointMoment H beta D r B - y ^ B.card| ≤ epsilon) :
    |(beta / (D : ℝ)) *
          (∑ e ∈ H.edgesMeeting A,
            rankTwoJointMoment H beta D r (A ∪ H.support e)) -
        (A.card : ℝ) * beta * y ^ (A.card + 1)| ≤
      beta * ((K : ℝ) * epsilon +
        ((K * s + 3 * K ^ 2 * C : ℕ) : ℝ) / (D : ℝ)) := by
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hp₀ : 0 ≤ beta / (D : ℝ) := div_nonneg hbeta₀ hDR.le
  have hsum := rankTwo_sum_jointMoment_meeting_sub_le
    hunif hsD hdegUpper hdegLower hpair hp₀ hp₁ hy₀ hy₁ hepsilon₀
    A hAsub hclose
  let S : ℝ := ∑ e ∈ H.edgesMeeting A,
    rankTwoJointMoment H beta D r (A ∪ H.support e)
  let t : ℝ := y ^ (A.card + 1)
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDR
  have hrewrite :
      (beta / (D : ℝ)) * S - (A.card : ℝ) * beta * t =
        (beta / (D : ℝ)) *
          (S - ((A.card * D : ℕ) : ℝ) * t) := by
    field_simp [hDne]
    push_cast
    ring
  have hstructNat : A.card * s + 3 * A.card ^ 2 * C ≤
      K * s + 3 * K ^ 2 * C := by
    have hsq : A.card ^ 2 ≤ K ^ 2 := Nat.pow_le_pow_left hAK 2
    exact Nat.add_le_add
      (Nat.mul_le_mul_right s hAK)
      (by simpa [Nat.mul_assoc] using
        (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right C hsq)))
  have hstructR :
      ((A.card * s + 3 * A.card ^ 2 * C : ℕ) : ℝ) / (D : ℝ) ≤
        ((K * s + 3 * K ^ 2 * C : ℕ) : ℝ) / (D : ℝ) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hstructNat) hDR.le
  have hcardR : (A.card : ℝ) * epsilon ≤ (K : ℝ) * epsilon :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hAK) hepsilon₀
  change |(beta / (D : ℝ)) * S - (A.card : ℝ) * beta * t| ≤ _
  rw [hrewrite, abs_mul, abs_of_nonneg hp₀]
  calc
    beta / (D : ℝ) *
        |S - ((A.card * D : ℕ) : ℝ) * t| ≤
      beta / (D : ℝ) *
        (((A.card * D : ℕ) : ℝ) * epsilon +
          ((A.card * s + 3 * A.card ^ 2 * C : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum hp₀
    _ = beta * ((A.card : ℝ) * epsilon +
        ((A.card * s + 3 * A.card ^ 2 * C : ℕ) : ℝ) / (D : ℝ)) := by
      field_simp [hDne]
      push_cast
      ring
    _ ≤ beta * ((K : ℝ) * epsilon +
        ((K * s + 3 * K ^ 2 * C : ℕ) : ℝ) / (D : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hcardR hstructR) hbeta₀

/-- Unconditional fixed-length mean-field comparison in rank two.  The
cardinality allowance `A.card + 2*r ≤ K` is precisely what is needed for
the forward joint-moment recurrence, since adjoining a two-element support
adds at most two vertices. -/
theorem rankTwoJointMoment_close_meanField
    {H : Erdos76.FiniteHypergraph V E} {D s C K : ℕ}
    (hD : 0 < D) (hunif : H.IsUniform 2) (hsD : s ≤ D)
    (hdegUpper : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hdegLower : ∀ v ∈ H.vertexSet, D - s ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {beta : ℝ} (hbeta₀ : 0 ≤ beta) (hbeta₁ : beta ≤ 1) :
    ∀ r (A : Finset V), A ⊆ H.vertexSet → A.card + 2 * r ≤ K →
      |rankTwoJointMoment H beta D r A -
          rankTwoMeanFieldSurvival beta r ^ A.card| ≤
        rankTwoMomentError K D s C beta r := by
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDR
  have hp₀ : 0 ≤ beta / (D : ℝ) := div_nonneg hbeta₀ hDR.le
  have hDone : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hp₁ : beta / (D : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hDR).2
    nlinarith
  intro r
  induction r with
  | zero =>
      intro A hAsub hAK
      simp [rankTwoJointMoment, Erdos76.FiniteHypergraph.UncoveredBy]
  | succ r ih =>
      intro A hAsub hAK
      let y : ℝ := rankTwoMeanFieldSurvival beta r
      let x : ℝ := rankTwoMeanFieldSurvival beta (r + 1)
      let epsilon : ℝ := rankTwoMomentError K D s C beta r
      let J : ℝ := rankTwoJointMoment H beta D r A
      let S : ℝ := ∑ e ∈ H.edgesMeeting A,
        rankTwoJointMoment H beta D r (A ∪ H.support e)
      let linear : ℝ := y ^ A.card -
        (A.card : ℝ) * beta * y ^ (A.card + 1)
      let central : ℝ :=
        (1 + beta * (K : ℝ)) * epsilon +
          beta * (((K * s + 3 * K ^ 2 * C : ℕ) : ℝ) / (D : ℝ))
      have hAK' : A.card ≤ K := by omega
      have hround : A.card + 2 * r ≤ K := by omega
      have hyMem : y ∈ Set.Icc (0 : ℝ) 1 := by
        exact rankTwoMeanFieldSurvival_mem_Icc hbeta₀ hbeta₁ r
      have hxMem : x ∈ Set.Icc (0 : ℝ) 1 := by
        exact rankTwoMeanFieldSurvival_mem_Icc hbeta₀ hbeta₁ (r + 1)
      have hepsilon₀ : 0 ≤ epsilon :=
        rankTwoMomentError_nonneg K D s C r hbeta₀
      have hclose (B : Finset V) (hBsub : B ⊆ H.vertexSet)
          (hBcard : B.card ≤ A.card + 2) :
          |rankTwoJointMoment H beta D r B - y ^ B.card| ≤ epsilon := by
        apply ih B hBsub
        omega
      have hJclose : |J - y ^ A.card| ≤ epsilon := by
        simpa [J] using ih A hAsub hround
      have hSclose :
          |(beta / (D : ℝ)) * S -
              (A.card : ℝ) * beta * y ^ (A.card + 1)| ≤
            beta * ((K : ℝ) * epsilon +
              ((K * s + 3 * K ^ 2 * C : ℕ) : ℝ) / (D : ℝ)) := by
        simpa [S] using rankTwo_scaled_sum_jointMoment_meeting_sub_le
          hD hunif hsD hdegUpper hdegLower hpair hbeta₀ hp₁
          hyMem.1 hyMem.2 hepsilon₀ A hAsub hAK' hclose
      have hcentral₀ : 0 ≤ central := by
        dsimp [central]
        have hcoef₀ : 0 ≤ 1 + beta * (K : ℝ) := by positivity
        have hstruct₀ : 0 ≤
            ((K * s + 3 * K ^ 2 * C : ℕ) : ℝ) / (D : ℝ) := by
          positivity
        positivity
      have hfirstOrder :
          |(J - (beta / (D : ℝ)) * S) - linear| ≤ central := by
        have hJbounds := abs_le.mp hJclose
        have hSbounds := abs_le.mp hSclose
        rw [abs_le]
        dsimp [linear, central]
        constructor <;> linarith
      have hrec : rankTwoJointMoment H beta D (r + 1) A ∈
          Set.Icc
            (J - (beta / (D : ℝ)) * S)
            (J - (beta / (D : ℝ) -
                (((2 * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2)) * S +
              ((((A.card * D : ℕ) : ℝ) *
                  (beta / (D : ℝ))) ^ 2 / 2) * J) := by
        simpa [rankTwoJointMoment, J, S] using
          (innerJointUncoveredMass_succ_mem_Icc
            (H := H) (k := 2) (D := D) (by omega) hunif hdegUpper
            ∅ A r (beta / (D : ℝ)) hp₀ hp₁)
      have hJmem : J ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [J, rankTwoJointMoment] using
          (H.innerJointUncoveredMass_bernoulli_mem_Icc
            (p := fun _ ↦ beta / (D : ℝ)) (fun _ ↦ hp₀) (fun _ ↦ hp₁)
            r ∅ A)
      have hSmem : S ∈ Set.Icc (0 : ℝ) ((A.card * D : ℕ) : ℝ) := by
        have heach (e : E) : rankTwoJointMoment H beta D r
            (A ∪ H.support e) ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [rankTwoJointMoment] using
            (H.innerJointUncoveredMass_bernoulli_mem_Icc
              (p := fun _ ↦ beta / (D : ℝ))
              (fun _ ↦ hp₀) (fun _ ↦ hp₁) r ∅ (A ∪ H.support e))
        have hmeeting := H.edgesMeeting_card_le_mul_degree A D hdegUpper
        constructor
        · dsimp [S]
          exact sum_nonneg fun e _ ↦ (heach e).1
        · calc
            S ≤ ∑ _e ∈ H.edgesMeeting A, (1 : ℝ) := by
              dsimp [S]
              exact sum_le_sum fun e _ ↦ (heach e).2
            _ = ((H.edgesMeeting A).card : ℝ) := by simp
            _ ≤ ((A.card * D : ℕ) : ℝ) := by exact_mod_cast hmeeting
      let d : ℝ := beta * y ^ 2
      have hd₀ : 0 ≤ d := mul_nonneg hbeta₀ (pow_nonneg hyMem.1 _)
      have hdBeta : d ≤ beta := by
        dsimp [d]
        have hySq : y ^ 2 ≤ 1 := pow_le_one₀ hyMem.1 hyMem.2
        nlinarith
      have hxy : x = y - d := by
        simp [x, y, d, rankTwoMeanFieldSurvival_succ]
      have hpower := rankTwoPowerLinearizationError_mem_Icc A.card
        hxMem.1 hxMem.2 hyMem.2 hd₀ hxy
      have hpowFactor :
          (A.card : ℝ) * d * y ^ (A.card - 1) =
            (A.card : ℝ) * beta * y ^ (A.card + 1) := by
        by_cases ha : A.card = 0
        · simp [ha]
        · have haOne : 1 ≤ A.card := Nat.one_le_iff_ne_zero.mpr ha
          dsimp [d]
          rw [show A.card + 1 = 2 + (A.card - 1) by omega, pow_add]
          ring
      have hideal : x ^ A.card = linear +
          rankTwoPowerLinearizationError A.card x y d := by
        unfold rankTwoPowerLinearizationError
        rw [hpowFactor]
        dsimp [linear]
        ring
      have hdSq : d ^ 2 ≤ beta ^ 2 := by nlinarith
      have hcardSq : (A.card : ℝ) ^ 2 ≤ (K : ℝ) ^ 2 := by
        have hcardR : (A.card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hAK'
        nlinarith
      have hpowerBound :
          rankTwoPowerLinearizationError A.card x y d ≤
            (K : ℝ) ^ 2 * beta ^ 2 := by
        exact hpower.2.trans
          (mul_le_mul hcardSq hdSq (sq_nonneg _) (sq_nonneg _))
      have haltBound :
          (((2 * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2) * S ≤
            2 * (K : ℝ) * beta ^ 2 := by
        have hcoef₀ : 0 ≤
            ((2 * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2 := by
          positivity
        calc
          (((2 * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2) * S ≤
              (((2 * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2) *
                ((A.card * D : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hSmem.2 hcoef₀
          _ = 2 * (A.card : ℝ) * beta ^ 2 := by
            field_simp [hDne]
            push_cast
            ring
          _ ≤ 2 * (K : ℝ) * beta ^ 2 := by
            have hcardR : (A.card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hAK'
            nlinarith [sq_nonneg beta]
      have hbonfBound :
          (((((A.card * D : ℕ) : ℝ) *
              (beta / (D : ℝ))) ^ 2) / 2) * J ≤
            ((K : ℝ) ^ 2 * beta ^ 2) / 2 := by
        have hcoef₀ : 0 ≤
            ((((A.card * D : ℕ) : ℝ) *
              (beta / (D : ℝ))) ^ 2) / 2 := by positivity
        calc
          (((((A.card * D : ℕ) : ℝ) *
              (beta / (D : ℝ))) ^ 2) / 2) * J ≤
              ((((A.card * D : ℕ) : ℝ) *
                (beta / (D : ℝ))) ^ 2) / 2 := by
            simpa using mul_le_mul_of_nonneg_left hJmem.2 hcoef₀
          _ = ((A.card : ℝ) ^ 2 * beta ^ 2) / 2 := by
            field_simp [hDne]
            push_cast
            ring
          _ ≤ ((K : ℝ) ^ 2 * beta ^ 2) / 2 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcardSq (sq_nonneg beta)) (by norm_num)
      have hfirstBounds := abs_le.mp hfirstOrder
      rw [abs_le]
      constructor
      · have hnextLower := hrec.1
        have hlinLower : linear - central ≤
            J - (beta / (D : ℝ)) * S := by linarith
        have herrorDom : central + (K : ℝ) ^ 2 * beta ^ 2 ≤
            rankTwoMomentError K D s C beta (r + 1) := by
          rw [rankTwoMomentError_succ]
          dsimp [central, epsilon]
          have hK₀ : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
          have hbSq : 0 ≤ beta ^ 2 := sq_nonneg beta
          nlinarith
        rw [hideal]
        linarith
      · have hnextUpper := hrec.2
        have hlinUpper :
            J - (beta / (D : ℝ)) * S ≤ linear + central := by linarith
        have hupperRewrite :
            J - (beta / (D : ℝ) -
                (((2 * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2)) * S +
              ((((A.card * D : ℕ) : ℝ) *
                  (beta / (D : ℝ))) ^ 2 / 2) * J =
              (J - (beta / (D : ℝ)) * S) +
                (((2 * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2) * S +
                ((((A.card * D : ℕ) : ℝ) *
                    (beta / (D : ℝ))) ^ 2 / 2) * J := by ring
        rw [hupperRewrite] at hnextUpper
        have herrorDom : central + 2 * (K : ℝ) * beta ^ 2 +
              ((K : ℝ) ^ 2 * beta ^ 2) / 2 ≤
            rankTwoMomentError K D s C beta (r + 1) := by
          rw [rankTwoMomentError_succ]
          change central + 2 * (K : ℝ) * beta ^ 2 +
              ((K : ℝ) ^ 2 * beta ^ 2) / 2 ≤
            central + (((3 : ℝ) / 2) * (K : ℝ) ^ 2 +
              2 * (K : ℝ)) * beta ^ 2
          have hsq₀ : 0 ≤ (K : ℝ) ^ 2 * beta ^ 2 :=
            mul_nonneg (sq_nonneg _) (sq_nonneg _)
          calc
            central + 2 * (K : ℝ) * beta ^ 2 +
                ((K : ℝ) ^ 2 * beta ^ 2) / 2 ≤
              (central + 2 * (K : ℝ) * beta ^ 2 +
                ((K : ℝ) ^ 2 * beta ^ 2) / 2) +
                  (K : ℝ) ^ 2 * beta ^ 2 := le_add_of_nonneg_right hsq₀
            _ = central + (((3 : ℝ) / 2) * (K : ℝ) ^ 2 +
                2 * (K : ℝ)) * beta ^ 2 := by ring
        have hpowerNonneg := hpower.1
        linarith [hideal]

lemma rankTwoMomentError_le_succ
    (K D s C r : ℕ) {beta : ℝ} (hbeta₀ : 0 ≤ beta) :
    rankTwoMomentError K D s C beta r ≤
      rankTwoMomentError K D s C beta (r + 1) := by
  rw [rankTwoMomentError_succ]
  have hE₀ := rankTwoMomentError_nonneg K D s C r hbeta₀
  have hstruct₀ : 0 ≤
      ((K * s + 3 * K ^ 2 * C : ℕ) : ℝ) / (D : ℝ) := by positivity
  have hquad₀ : 0 ≤
      ((3 : ℝ) / 2) * (K : ℝ) ^ 2 + 2 * (K : ℝ) := by positivity
  have hKE₀ : 0 ≤ beta * (K : ℝ) *
      rankTwoMomentError K D s C beta r := by positivity
  have hstructTerm₀ : 0 ≤ beta *
      (((K * s + 3 * K ^ 2 * C : ℕ) : ℝ) / (D : ℝ)) :=
    mul_nonneg hbeta₀ hstruct₀
  have hquadTerm₀ : 0 ≤
      (((3 : ℝ) / 2) * (K : ℝ) ^ 2 + 2 * (K : ℝ)) * beta ^ 2 :=
    mul_nonneg hquad₀ (sq_nonneg beta)
  calc
    rankTwoMomentError K D s C beta r ≤
        rankTwoMomentError K D s C beta r +
          beta * (K : ℝ) * rankTwoMomentError K D s C beta r +
          beta * (((K * s + 3 * K ^ 2 * C : ℕ) : ℝ) / (D : ℝ)) +
          (((3 : ℝ) / 2) * (K : ℝ) ^ 2 + 2 * (K : ℝ)) * beta ^ 2 := by
      linarith
    _ = (1 + beta * (K : ℝ)) * rankTwoMomentError K D s C beta r +
          beta * (((K * s + 3 * K ^ 2 * C : ℕ) : ℝ) / (D : ℝ)) +
          (((3 : ℝ) / 2) * (K : ℝ) ^ 2 + 2 * (K : ℝ)) * beta ^ 2 := by
      ring

lemma rankTwoMomentError_monotone
    (K D s C : ℕ) {beta : ℝ} (hbeta₀ : 0 ≤ beta) :
    Monotone (rankTwoMomentError K D s C beta) := by
  exact monotone_nat_of_le_succ fun r ↦
    rankTwoMomentError_le_succ K D s C r hbeta₀

/-- For rank two, the live-edge mass is the joint moment on the two
vertices in the support of that edge. -/
lemma rankTwo_innerLiveMass_eq_jointMoment
    {H : Erdos76.FiniteHypergraph V E} (hunif : H.IsUniform 2)
    (beta : ℝ) (D r : ℕ) (e : E) :
    H.innerLiveMass
        (Erdos76.FiniteNibble.bernoulliMass univ
          (fun _ ↦ beta / (D : ℝ))) r ∅ e =
      rankTwoJointMoment H beta D r (H.support e) := by
  rw [H.innerLiveMass_eq_sum_all_uncovered_of_uniform (by omega) hunif]
  rfl

/-- Uniform fixed-length consequence of the joint-moment comparison. -/
theorem rankTwo_innerLiveMass_close_meanField
    {H : Erdos76.FiniteHypergraph V E} {D s C L : ℕ}
    (hD : 0 < D) (hunif : H.IsUniform 2) (hsD : s ≤ D)
    (hdegUpper : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hdegLower : ∀ v ∈ H.vertexSet, D - s ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {beta : ℝ} (hbeta₀ : 0 ≤ beta) (hbeta₁ : beta ≤ 1)
    (e : E) (r : ℕ) (hr : r ≤ L) :
    |H.innerLiveMass
          (Erdos76.FiniteNibble.bernoulliMass univ
            (fun _ ↦ beta / (D : ℝ))) r ∅ e -
        rankTwoMeanFieldSurvival beta r ^ 2| ≤
      rankTwoMomentError (2 + 2 * L) D s C beta L := by
  rw [rankTwo_innerLiveMass_eq_jointMoment hunif]
  have hpoint := rankTwoJointMoment_close_meanField (K := 2 + 2 * L)
    hD hunif hsD hdegUpper hdegLower hpair hbeta₀ hbeta₁ r (H.support e)
    (H.support_subset_vertexSet e) (by
      rw [hunif e]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hr) 2)
  rw [hunif e] at hpoint
  exact hpoint.trans
    ((rankTwoMomentError_monotone (2 + 2 * L) D s C hbeta₀) hr)

/-- The rank-two joint-moment comparison feeds directly into the two-sided
matching-trial marginal.  All remaining assumptions are scalar inequalities
on the explicit error budget. -/
theorem rankTwo_innerAcceptanceMass_twoSided
    {H : Erdos76.FiniteHypergraph V E} {D s C L : ℕ}
    (hD : 0 < D) (hunif : H.IsUniform 2) (hsD : s ≤ D)
    (hdegUpper : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hdegLower : ∀ v ∈ H.vertexSet, D - s ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {beta zeta : ℝ} (hbeta₀ : 0 ≤ beta) (hbeta₁ : beta ≤ 1)
    (hq₀ : 0 ≤ beta / (D : ℝ) -
      (((2 * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2))
    (hlower : (1 - zeta) / (D : ℝ) ≤
      (beta / (D : ℝ) -
        (((2 * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2)) *
        (∑ r ∈ range L,
          (rankTwoMeanFieldSurvival beta r ^ 2 -
            rankTwoMomentError (2 + 2 * L) D s C beta L)))
    (hupper : beta / (D : ℝ) *
        (∑ r ∈ range L,
          (rankTwoMeanFieldSurvival beta r ^ 2 +
            rankTwoMomentError (2 + 2 * L) D s C beta L)) ≤
      (1 + zeta) / (D : ℝ)) (e : E) :
    (1 - zeta) / (D : ℝ) ≤
        H.innerAcceptanceMass L (fun _ ↦ beta / (D : ℝ)) e ∧
      H.innerAcceptanceMass L (fun _ ↦ beta / (D : ℝ)) e ≤
        (1 + zeta) / (D : ℝ) := by
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hp₀ : 0 ≤ beta / (D : ℝ) := div_nonneg hbeta₀ hDR.le
  have hp₁ : beta / (D : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hDR).2
    have hDone : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    linarith
  have hclose : ∀ r < L,
      |H.innerLiveMass
          (Erdos76.FiniteNibble.bernoulliMass univ
            (fun _ ↦ beta / (D : ℝ))) r ∅ e -
        rankTwoMeanFieldSurvival beta r ^ 2| ≤
          rankTwoMomentError (2 + 2 * L) D s C beta L := by
    intro r hr
    exact rankTwo_innerLiveMass_close_meanField hD hunif hsD hdegUpper hdegLower
      hpair hbeta₀ hbeta₁ e r (Nat.le_of_lt hr)
  have hliveLower : ∀ r < L,
      rankTwoMeanFieldSurvival beta r ^ 2 -
          rankTwoMomentError (2 + 2 * L) D s C beta L ≤
        H.innerLiveMass
          (Erdos76.FiniteNibble.bernoulliMass univ
            (fun _ ↦ beta / (D : ℝ))) r ∅ e := by
    intro r hr
    have hb := abs_sub_le_iff.mp (hclose r hr)
    linarith
  have hliveUpper : ∀ r < L,
      H.innerLiveMass
          (Erdos76.FiniteNibble.bernoulliMass univ
            (fun _ ↦ beta / (D : ℝ))) r ∅ e ≤
        rankTwoMeanFieldSurvival beta r ^ 2 +
          rankTwoMomentError (2 + 2 * L) D s C beta L := by
    intro r hr
    have hb := abs_sub_le_iff.mp (hclose r hr)
    linarith
  constructor
  · exact hlower.trans
      (H.sub_mul_sum_le_innerAcceptanceMass_const_of_innerLiveMass_ge
        hunif hdegUpper hp₀ hp₁ hq₀ L
        (fun r ↦ rankTwoMeanFieldSurvival beta r ^ 2 -
          rankTwoMomentError (2 + 2 * L) D s C beta L) hliveLower)
  · exact (H.innerAcceptanceMass_le_mul_sum_of_innerLiveMass_le
      (fun _ ↦ hp₀) (fun _ ↦ hp₁) L e
      (fun r ↦ rankTwoMeanFieldSurvival beta r ^ 2 +
        rankTwoMomentError (2 + 2 * L) D s C beta L) hliveUpper).trans hupper

end FiniteHypergraph

end PippengerInner

end

end Erdos622
