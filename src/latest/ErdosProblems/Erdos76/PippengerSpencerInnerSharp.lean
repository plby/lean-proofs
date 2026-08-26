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
import ErdosProblems.Erdos76.PippengerSpencerInnerSharpAnalysis
import ErdosProblems.Erdos76.PippengerSpencerInnerSharpInterface
import ErdosProblems.Erdos76.PippengerSpencerInnerSurvival

/-!
# The sharp fixed-length inner marginal

This file supplies the quantitative probabilistic heart of the
Pippenger--Spencer iteration.  The deterministic comparison sequence is the
Euler trajectory for `y' = -y^k`: one nibble round decreases the uncovered
vertex density by approximately `beta * y^k`, while a fixed edge is live
with probability approximately `y^k`.  The exact telescoping identity below
turns control of that trajectory into the sharp marginal `1 / D`.
-/

open Finset Real
open scoped BigOperators Topology

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteHypergraph

universe uV uE

variable {V : Type uV} {E : Type uE}
  [DecidableEq V] [Fintype E] [DecidableEq E]

/-- For a positive uniform hypergraph, the live mass of an edge is the
joint uncovered mass of its support. -/
lemma innerLiveMass_eq_innerJointUncoveredMass_support
    {H : FiniteHypergraph V E} {k r : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (w : Finset E → ℝ)
    (M : Finset E) (e : E) :
    H.innerLiveMass w r M e =
      H.innerJointUncoveredMass w r M (H.support e) := by
  rw [H.innerLiveMass_eq_sum_all_uncovered_of_uniform hk hunif]
  rfl

/-- For constant Bernoulli sampling, conditional new acceptance is between
the elementary alteration lower bound and raw sampling. -/
lemma innerNewAcceptanceMass_const_mem_Icc
    {H : FiniteHypergraph V E} {k D : ℕ} (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (M : Finset E) (e : E) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    H.innerNewAcceptanceMass M (fun _ ↦ p) e ∈
      Set.Icc
        ((p - ((k * D : ℕ) : ℝ) * p ^ 2) *
          (if H.InnerLive M e then 1 else 0))
        (p * (if H.InnerLive M e then 1 else 0)) := by
  have hcard : (H.innerLiveConflictNeighbors M e).card ≤ k * D := by
    calc
      (H.innerLiveConflictNeighbors M e).card ≤ H.conflictDegree e := by
        apply card_le_card
        intro f hf
        rw [mem_filter]
        have hf' := (H.mem_innerLiveConflictNeighbors M e f).1 hf
        exact ⟨mem_univ f, hf'.1.symm, hf'.2.2⟩
      _ ≤ k * D := H.conflictDegree_le_uniform_mul hunif hdeg e
  have hprodIcc := prod_one_sub_mem_Icc
    (H.innerLiveConflictNeighbors M e) (fun _ : E ↦ p)
    (fun _ _ ↦ hp₀) (fun _ _ ↦ hp₁)
  have hprodLower :
      1 - (((k * D : ℕ) : ℝ) * p) ≤
        ∏ f ∈ H.innerLiveConflictNeighbors M e, (1 - p) := by
    calc
      1 - (((k * D : ℕ) : ℝ) * p) ≤
          1 - ((H.innerLiveConflictNeighbors M e).card : ℝ) * p := by
        have hcardR :
            ((H.innerLiveConflictNeighbors M e).card : ℝ) ≤
              ((k * D : ℕ) : ℝ) := by exact_mod_cast hcard
        exact sub_le_sub_left (mul_le_mul_of_nonneg_right hcardR hp₀) 1
      _ = 1 - ∑ f ∈ H.innerLiveConflictNeighbors M e, p := by simp
      _ ≤ ∏ f ∈ H.innerLiveConflictNeighbors M e, (1 - p) :=
        one_sub_sum_le_prod_one_sub _ _
          (fun _ _ ↦ hp₀) (fun _ _ ↦ hp₁)
  rw [H.innerNewAcceptanceMass_eq]
  by_cases hlive : H.InnerLive M e
  · rw [if_pos hlive, if_pos hlive]
    simp only [mul_one]
    constructor
    · calc
        p - (((k * D : ℕ) : ℝ) * p ^ 2) =
            p * (1 - (((k * D : ℕ) : ℝ) * p)) := by ring
        _ ≤ p * ∏ f ∈ H.innerLiveConflictNeighbors M e, (1 - p) :=
          mul_le_mul_of_nonneg_left hprodLower hp₀
    · simpa using mul_le_mul_of_nonneg_left hprodIcc.2 hp₀
  · simp [hlive]

/-- Conditional one-round Bonferroni bounds for joint uncoveredness.  The
linear term is the exact expected number of newly accepted matching edges
meeting `A`; the upper error is the quadratic Bernoulli pair bound. -/
theorem oneRoundJointUncoveredMass_mem_Icc
    (H : FiniteHypergraph V E) (M : Finset E) (A : Finset V)
    (D : ℕ) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hunc : ∀ v ∈ A, H.UncoveredBy M v) :
    (∑ S : Finset E,
        FiniteNibble.bernoulliMass univ (fun _ ↦ p) S *
          if ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v then 1 else 0) ∈
      Set.Icc
        (1 - ∑ e ∈ H.edgesMeeting A, H.innerNewAcceptanceMass M (fun _ ↦ p) e)
        (1 - ∑ e ∈ H.edgesMeeting A, H.innerNewAcceptanceMass M (fun _ ↦ p) e +
          ((((A.card * D : ℕ) : ℝ) * p) ^ 2) / 2) := by
  let w : Finset E → ℝ := FiniteNibble.bernoulliMass univ (fun _ ↦ p)
  let N : Finset E → ℕ := fun S ↦ (H.innerNewAcceptedMeeting M S A).card
  have hw₀ (S : Finset E) : 0 ≤ w S :=
    FiniteNibble.bernoulliMass_nonneg (subset_univ S)
      (fun _ _ ↦ hp₀) (fun _ _ ↦ hp₁)
  have hmass : ∑ S : Finset E, w S = 1 := by
    simpa [w] using FiniteNibble.sum_bernoulliMass (univ : Finset E) (fun _ ↦ p)
  have hfirst :
      (∑ S : Finset E, w S * (N S : ℝ)) =
        ∑ e ∈ H.edgesMeeting A,
          H.innerNewAcceptanceMass M (fun _ ↦ p) e := by
    rw [show (∑ e ∈ H.edgesMeeting A,
          H.innerNewAcceptanceMass M (fun _ ↦ p) e) =
        ∑ e with ¬Disjoint (H.support e) A,
          H.innerNewAcceptanceMass M (fun _ ↦ p) e by
      rfl]
    simpa [w, N] using
      H.sum_bernoulliMass_mul_innerNewAcceptedMeeting_card M (fun _ ↦ p) A
  have hzero (S : Finset E) :
      (if ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v then (1 : ℝ) else 0) =
        if N S = 0 then 1 else 0 := by
    have hiff :=
      H.jointUncovered_innerStep_iff_innerNewAcceptedMeeting_eq_empty
        (S := S) hunc
    by_cases hjoint : ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v
    · have hempty := hiff.mp hjoint
      have hn : N S = 0 := by simp [N, hempty]
      rw [if_pos hjoint, if_pos hn]
    · have hne : N S ≠ 0 := by
        intro hz
        apply hjoint
        apply hiff.mpr
        exact card_eq_zero.mp hz
      rw [if_neg hjoint, if_neg hne]
  constructor
  · calc
      1 - ∑ e ∈ H.edgesMeeting A,
          H.innerNewAcceptanceMass M (fun _ ↦ p) e =
          ∑ S : Finset E, w S * (1 - (N S : ℝ)) := by
        simp_rw [mul_sub]
        rw [sum_sub_distrib]
        simp only [mul_one]
        rw [hmass, hfirst]
      _ ≤ ∑ S : Finset E, w S *
          (if N S = 0 then 1 else 0) := by
        apply sum_le_sum
        intro S _
        exact mul_le_mul_of_nonneg_left
          (one_sub_natCast_le_indicator_eq_zero (N S)) (hw₀ S)
      _ = ∑ S : Finset E, w S *
          (if ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v then 1 else 0) := by
        apply sum_congr rfl
        intro S _
        rw [hzero]
  · calc
      (∑ S : Finset E, w S *
          (if ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v then 1 else 0)) =
          ∑ S : Finset E, w S * (if N S = 0 then 1 else 0) := by
        apply sum_congr rfl
        intro S _
        rw [hzero]
      _ ≤ ∑ S : Finset E, w S *
          (1 - (N S : ℝ) + (N S : ℝ) * ((N S : ℝ) - 1) / 2) := by
        apply sum_le_sum
        intro S _
        exact mul_le_mul_of_nonneg_left
          (indicator_eq_zero_le_one_sub_add_pairCount (N S)) (hw₀ S)
      _ = (1 - ∑ e ∈ H.edgesMeeting A,
          H.innerNewAcceptanceMass M (fun _ ↦ p) e) +
          ∑ S : Finset E, w S * (N S : ℝ) * ((N S : ℝ) - 1) / 2 := by
        rw [show (∑ S : Finset E, w S *
            (1 - (N S : ℝ) + (N S : ℝ) * ((N S : ℝ) - 1) / 2)) =
            (∑ S : Finset E, w S * (1 - (N S : ℝ))) +
              ∑ S : Finset E, w S * (N S : ℝ) * ((N S : ℝ) - 1) / 2 by
          rw [← sum_add_distrib]
          apply sum_congr rfl
          intro S _
          ring]
        simp_rw [mul_sub]
        rw [sum_sub_distrib]
        simp only [mul_one]
        rw [hmass, hfirst]
      _ ≤ (1 - ∑ e ∈ H.edgesMeeting A,
          H.innerNewAcceptanceMass M (fun _ ↦ p) e) +
          ((((A.card * D : ℕ) : ℝ) * p) ^ 2) / 2 := by
        gcongr
        simpa [w, N] using
          H.sum_bernoulliMass_mul_innerNewAcceptedMeeting_pairCount_le
            M A D p hp₀ hp₁ hdeg

/-- State-independent one-round form of the Bonferroni bounds.  The
previous joint-uncovered indicator makes both bounds vanish on states from
which joint uncoveredness can no longer be recovered. -/
theorem oneRoundJointUncoveredMass_indicator_mem_Icc
    (H : FiniteHypergraph V E) {k D : ℕ} (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (M : Finset E) (A : Finset V) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (∑ S : Finset E,
        FiniteNibble.bernoulliMass univ (fun _ ↦ p) S *
          if ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v then 1 else 0) ∈
      Set.Icc
        ((if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) -
          p * (if ∀ v ∈ A, H.UncoveredBy M v then 1 else 0) *
            ∑ e ∈ H.edgesMeeting A,
              if H.InnerLive M e then 1 else 0)
        ((if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) -
          (p - (((k * D : ℕ) : ℝ) * p ^ 2)) *
            (if ∀ v ∈ A, H.UncoveredBy M v then 1 else 0) *
            (∑ e ∈ H.edgesMeeting A,
              if H.InnerLive M e then 1 else 0) +
          ((((A.card * D : ℕ) : ℝ) * p) ^ 2) / 2 *
            (if ∀ v ∈ A, H.UncoveredBy M v then 1 else 0)) := by
  let Q : ℝ := ∑ S : Finset E,
    FiniteNibble.bernoulliMass univ (fun _ ↦ p) S *
      if ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v then 1 else 0
  let liveCount : ℝ := ∑ e ∈ H.edgesMeeting A,
    if H.InnerLive M e then 1 else 0
  let first : ℝ := ∑ e ∈ H.edgesMeeting A,
    H.innerNewAcceptanceMass M (fun _ ↦ p) e
  let pairError : ℝ := ((((A.card * D : ℕ) : ℝ) * p) ^ 2) / 2
  by_cases hA : ∀ v ∈ A, H.UncoveredBy M v
  · have hone := H.oneRoundJointUncoveredMass_mem_Icc M A D p hp₀ hp₁ hdeg hA
    have hfirstUpper : first ≤ p * liveCount := by
      dsimp only [first, liveCount]
      rw [Finset.mul_sum]
      apply sum_le_sum
      intro e _
      exact H.innerNewAcceptanceMass_const_mem_Icc hunif hdeg M e hp₀ hp₁ |>.2
    have hfirstLower :
        (p - (((k * D : ℕ) : ℝ) * p ^ 2)) * liveCount ≤ first := by
      dsimp only [first, liveCount]
      rw [Finset.mul_sum]
      apply sum_le_sum
      intro e _
      exact H.innerNewAcceptanceMass_const_mem_Icc hunif hdeg M e hp₀ hp₁ |>.1
    change Q ∈ Set.Icc _ _
    rw [if_pos hA]
    simp only [mul_one, one_mul]
    change Q ∈ Set.Icc (1 - p * liveCount)
      (1 - (p - (((k * D : ℕ) : ℝ) * p ^ 2)) * liveCount + pairError)
    change Q ∈ Set.Icc (1 - first) (1 - first + pairError) at hone
    exact ⟨(sub_le_sub_left hfirstUpper 1).trans hone.1,
      hone.2.trans (by
        simpa [add_comm] using (add_le_add_right
          (sub_le_sub_left hfirstLower 1) pairError))⟩
  · have hnot (S : Finset E) :
        ¬∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v :=
      H.not_jointUncovered_innerStep hA
    have hQ : Q = 0 := by
      dsimp only [Q]
      apply sum_eq_zero
      intro S _
      simp [hnot S]
    change Q ∈ Set.Icc _ _
    rw [if_neg hA, hQ]
    simp

/-- Exact averaged joint-moment recurrence.  Its only error term is the
quadratic one-round Bonferroni correction; all live-state terms are rewritten
as joint uncovered masses on `A ∪ support e`. -/
theorem innerJointUncoveredMass_succ_mem_Icc
    (H : FiniteHypergraph V E) {k D : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (r : ℕ) (M : Finset E) (A : Finset V) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    H.innerJointUncoveredMass
        (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) (r + 1) M A ∈
      Set.Icc
        (H.innerJointUncoveredMass
            (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A -
          p * ∑ e ∈ H.edgesMeeting A,
            H.innerJointUncoveredMass
              (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M
              (A ∪ H.support e))
        (H.innerJointUncoveredMass
            (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A -
          (p - (((k * D : ℕ) : ℝ) * p ^ 2)) *
            ∑ e ∈ H.edgesMeeting A,
              H.innerJointUncoveredMass
                (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M
                (A ∪ H.support e) +
          ((((A.card * D : ℕ) : ℝ) * p) ^ 2) / 2 *
            H.innerJointUncoveredMass
              (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A) := by
  let w : Finset E → ℝ := FiniteNibble.bernoulliMass univ (fun _ ↦ p)
  let state : (Fin r → Finset E) → Finset E := fun X ↦
    (List.ofFn X).foldl H.innerStep M
  let oldIndicator : (Fin r → Finset E) → ℝ := fun X ↦
    if ∀ v ∈ A, H.UncoveredBy (state X) v then 1 else 0
  let liveCount : (Fin r → Finset E) → ℝ := fun X ↦
    ∑ e ∈ H.edgesMeeting A, if H.InnerLive (state X) e then 1 else 0
  let nextMass : (Fin r → Finset E) → ℝ := fun X ↦
    ∑ S : Finset E, w S *
      if ∀ v ∈ A, H.UncoveredBy (H.innerStep (state X) S) v then 1 else 0
  let oldMass : ℝ := H.innerJointUncoveredMass w r M A
  let enlargedMass : ℝ := ∑ e ∈ H.edgesMeeting A,
    H.innerJointUncoveredMass w r M (A ∪ H.support e)
  let q : ℝ := p - (((k * D : ℕ) : ℝ) * p ^ 2)
  let pairError : ℝ := ((((A.card * D : ℕ) : ℝ) * p) ^ 2) / 2
  have hw₀ (X : Fin r → Finset E) :
      0 ≤ FiniteProduct.productMass w X := by
    unfold FiniteProduct.productMass
    exact prod_nonneg fun i _ ↦
      FiniteNibble.bernoulliMass_nonneg (subset_univ (X i))
        (fun _ _ ↦ hp₀) (fun _ _ ↦ hp₁)
  have hpoint (X : Fin r → Finset E) :
      nextMass X ∈ Set.Icc
        (oldIndicator X - p * oldIndicator X * liveCount X)
        (oldIndicator X - q * oldIndicator X * liveCount X +
          pairError * oldIndicator X) := by
    simpa [nextMass, oldIndicator, liveCount, state, w, q, pairError] using
      H.oneRoundJointUncoveredMass_indicator_mem_Icc hunif hdeg
        (state X) A p hp₀ hp₁
  have havg :
      (∑ X : Fin r → Finset E,
          FiniteProduct.productMass w X * nextMass X) ∈
        Set.Icc
          (∑ X : Fin r → Finset E, FiniteProduct.productMass w X *
            (oldIndicator X - p * oldIndicator X * liveCount X))
          (∑ X : Fin r → Finset E, FiniteProduct.productMass w X *
            (oldIndicator X - q * oldIndicator X * liveCount X +
              pairError * oldIndicator X)) := by
    constructor
    · apply sum_le_sum
      intro X _
      exact mul_le_mul_of_nonneg_left (hpoint X).1 (hw₀ X)
    · apply sum_le_sum
      intro X _
      exact mul_le_mul_of_nonneg_left (hpoint X).2 (hw₀ X)
  have hOld :
      (∑ X : Fin r → Finset E,
        FiniteProduct.productMass w X * oldIndicator X) = oldMass := by
    rfl
  have hLive :
      (∑ X : Fin r → Finset E,
        FiniteProduct.productMass w X * oldIndicator X * liveCount X) =
        enlargedMass := by
    simpa [oldIndicator, liveCount, state, enlargedMass] using
      H.sum_productMass_mul_jointUncovered_mul_sum_innerLive
        hk hunif w r M A (H.edgesMeeting A)
  have hNext :
      (∑ X : Fin r → Finset E,
        FiniteProduct.productMass w X * nextMass X) =
        H.innerJointUncoveredMass w (r + 1) M A := by
    rw [H.innerJointUncoveredMass_succ_last]
  have hLower :
      (∑ X : Fin r → Finset E, FiniteProduct.productMass w X *
        (oldIndicator X - p * oldIndicator X * liveCount X)) =
        oldMass - p * enlargedMass := by
    calc
      (∑ X : Fin r → Finset E, FiniteProduct.productMass w X *
        (oldIndicator X - p * oldIndicator X * liveCount X)) =
          (∑ X : Fin r → Finset E,
            FiniteProduct.productMass w X * oldIndicator X) -
          p * (∑ X : Fin r → Finset E,
            FiniteProduct.productMass w X * oldIndicator X * liveCount X) := by
        simp_rw [mul_sub]
        rw [sum_sub_distrib, mul_sum]
        apply congrArg₂ (.-.) rfl
        apply sum_congr rfl
        intro X _
        ring
      _ = oldMass - p * enlargedMass := by rw [hOld, hLive]
  have hUpper :
      (∑ X : Fin r → Finset E, FiniteProduct.productMass w X *
        (oldIndicator X - q * oldIndicator X * liveCount X +
          pairError * oldIndicator X)) =
        oldMass - q * enlargedMass + pairError * oldMass := by
    calc
      (∑ X : Fin r → Finset E, FiniteProduct.productMass w X *
        (oldIndicator X - q * oldIndicator X * liveCount X +
          pairError * oldIndicator X)) =
          (∑ X : Fin r → Finset E,
            FiniteProduct.productMass w X * oldIndicator X) -
          q * (∑ X : Fin r → Finset E,
            FiniteProduct.productMass w X * oldIndicator X * liveCount X) +
          pairError * (∑ X : Fin r → Finset E,
            FiniteProduct.productMass w X * oldIndicator X) := by
        simp_rw [mul_add, mul_sub]
        rw [sum_add_distrib, sum_sub_distrib, mul_sum, mul_sum]
        apply congrArg₂ (.+.)
        · apply congrArg₂ (.-.) rfl
          apply sum_congr rfl
          intro X _
          ring
        · apply sum_congr rfl
          intro X _
          ring
      _ = oldMass - q * enlargedMass + pairError * oldMass := by
        rw [hOld, hLive]
  rw [hNext] at havg
  rw [hLower, hUpper] at havg
  simpa [w, oldMass, enlargedMass, q, pairError] using havg

/-- The number of nonexceptional edges meeting `A` is squeezed between the
near-regular incidence count (up to the low-codegree multiple-meeting
error) and the elementary maximum-degree count.  The lower bound is written
over the reals so that no truncated natural subtraction enters the later
moment comparison. -/
lemma singleMeetingEdges_card_mem_Icc
    (H : FiniteHypergraph V E) (A : Finset V) {k degreeLower D C : ℕ}
    (hunif : H.IsUniform k)
    (hlow : ∀ v ∈ A, degreeLower ≤ H.edgeDegree v)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C) :
    ((A.card * degreeLower : ℕ) : ℝ) -
        ((A.card ^ 2 * C * (k + 1) : ℕ) : ℝ) ≤
        ((H.singleMeetingEdges A).card : ℝ) ∧
      ((H.singleMeetingEdges A).card : ℝ) ≤
        ((A.card * D : ℕ) : ℝ) := by
  have hmulti := H.multiMeetingEdges_card_le_sq_mul_pairDegree A C hpair
  have hinc := H.card_mul_degreeLower_le_edgesMeeting_add_pairError
    A hunif hlow hpair
  have hdisj : Disjoint (H.singleMeetingEdges A) (H.multiMeetingEdges A) := by
    unfold singleMeetingEdges
    exact sdiff_disjoint
  have hcardMeeting :
      (H.edgesMeeting A).card =
        (H.singleMeetingEdges A).card + (H.multiMeetingEdges A).card := by
    rw [← H.edgesMeeting_eq_single_union_multi A,
      card_union_of_disjoint hdisj]
  have hsingleNat :
      A.card * degreeLower ≤
        (H.singleMeetingEdges A).card +
          A.card ^ 2 * C * (k + 1) := by
    rw [hcardMeeting] at hinc
    calc
      A.card * degreeLower ≤
          (H.singleMeetingEdges A).card +
            (H.multiMeetingEdges A).card + A.card ^ 2 * C * k := hinc
      _ ≤ (H.singleMeetingEdges A).card +
          A.card ^ 2 * C + A.card ^ 2 * C * k := by omega
      _ = (H.singleMeetingEdges A).card +
          A.card ^ 2 * C * (k + 1) := by
        simp only [Nat.mul_add, Nat.mul_one]
        omega
  have hsingleUpper :
      (H.singleMeetingEdges A).card ≤ A.card * D :=
    (card_le_card sdiff_subset).trans
      (H.edgesMeeting_card_le_mul_degree A D hdeg)
  have hsingleNatR :
      ((A.card * degreeLower : ℕ) : ℝ) ≤
        ((H.singleMeetingEdges A).card : ℝ) +
          ((A.card ^ 2 * C * (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast hsingleNat
  constructor
  · linarith
  · exact_mod_cast hsingleUpper

/-- Profile comparison for the enlarged joint moments in the exact
recurrence.  On edges meeting `A` in one vertex, every enlarged support has
the same cardinality and is assumed close to `target`.  Multiple-meeting
edges are bounded only by the unit interval; low codegree makes their total
contribution explicit. -/
theorem sum_edgesMeeting_profile_mem_Icc
    (H : FiniteHypergraph V E) (A : Finset V)
    {k degreeLower D C : ℕ} {U : Finset V → ℝ} {target epsilon : ℝ}
    (hunif : H.IsUniform k)
    (hlow : ∀ v ∈ A, degreeLower ≤ H.edgeDegree v)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (hU : ∀ B, U B ∈ Set.Icc (0 : ℝ) 1)
    (hepsilon₀ : 0 ≤ epsilon) (htarget : epsilon ≤ target)
    (hsingle : ∀ e ∈ H.singleMeetingEdges A,
      |U (A ∪ H.support e) - target| ≤ epsilon) :
    (
      (((A.card * degreeLower : ℕ) : ℝ) -
          ((A.card ^ 2 * C * (k + 1) : ℕ) : ℝ)) *
        (target - epsilon)) ≤
        ∑ e ∈ H.edgesMeeting A, U (A ∪ H.support e) ∧
      ∑ e ∈ H.edgesMeeting A, U (A ∪ H.support e) ≤
        ((A.card * D : ℕ) : ℝ) * (target + epsilon) +
          ((A.card ^ 2 * C : ℕ) : ℝ) := by
  have hsingleCard := H.singleMeetingEdges_card_mem_Icc A hunif hlow hdeg hpair
  have hmultiCard := H.multiMeetingEdges_card_le_sq_mul_pairDegree A C hpair
  have htargetMinus₀ : 0 ≤ target - epsilon := sub_nonneg.mpr htarget
  have hsingleBounds : ∀ e ∈ H.singleMeetingEdges A,
      target - epsilon ≤ U (A ∪ H.support e) ∧
        U (A ∪ H.support e) ≤ target + epsilon := by
    intro e he
    have habs := abs_sub_le_iff.mp (hsingle e he)
    constructor <;> linarith
  rw [H.sum_edgesMeeting_eq_sum_single_add_sum_multi]
  constructor
  · calc
      ((((A.card * degreeLower : ℕ) : ℝ) -
            ((A.card ^ 2 * C * (k + 1) : ℕ) : ℝ)) *
          (target - epsilon)) ≤
          ((H.singleMeetingEdges A).card : ℝ) *
            (target - epsilon) :=
        mul_le_mul_of_nonneg_right hsingleCard.1 htargetMinus₀
      _ = ∑ _e ∈ H.singleMeetingEdges A, (target - epsilon) := by simp
        <;> ring
      _ ≤ ∑ e ∈ H.singleMeetingEdges A, U (A ∪ H.support e) := by
        apply sum_le_sum
        intro e he
        exact (hsingleBounds e he).1
      _ ≤ (∑ e ∈ H.singleMeetingEdges A, U (A ∪ H.support e)) +
          ∑ e ∈ H.multiMeetingEdges A, U (A ∪ H.support e) := by
        exact le_add_of_nonneg_right (sum_nonneg fun e _ ↦ (hU _).1)
  · calc
      (∑ e ∈ H.singleMeetingEdges A, U (A ∪ H.support e)) +
          ∑ e ∈ H.multiMeetingEdges A, U (A ∪ H.support e) ≤
          ((H.singleMeetingEdges A).card : ℝ) * (target + epsilon) +
            ((H.multiMeetingEdges A).card : ℝ) := by
        apply add_le_add
        · calc
            ∑ e ∈ H.singleMeetingEdges A, U (A ∪ H.support e) ≤
                ∑ _e ∈ H.singleMeetingEdges A, (target + epsilon) := by
              apply sum_le_sum
              intro e he
              exact (hsingleBounds e he).2
            _ = ((H.singleMeetingEdges A).card : ℝ) *
                (target + epsilon) := by simp <;> ring
        · calc
            ∑ e ∈ H.multiMeetingEdges A, U (A ∪ H.support e) ≤
                ∑ _e ∈ H.multiMeetingEdges A, (1 : ℝ) := by
              apply sum_le_sum
              intro e _
              exact (hU _).2
            _ = ((H.multiMeetingEdges A).card : ℝ) := by simp
      _ ≤ ((A.card * D : ℕ) : ℝ) * (target + epsilon) +
          ((A.card ^ 2 * C : ℕ) : ℝ) := by
        have htargetPlus₀ : 0 ≤ target + epsilon := by linarith
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hsingleCard.2 htargetPlus₀
        · exact_mod_cast hmultiCard

/-- A truncation-stable version of `sum_edgesMeeting_profile_mem_Icc`.
Both lower factors are replaced by their nonnegative parts, so this remains
usable after many rounds even when a deliberately coarse uniform error
budget exceeds a very small high-order mean-field moment. -/
theorem sum_edgesMeeting_profile_max_mem_Icc
    (H : FiniteHypergraph V E) (A : Finset V)
    {k degreeLower D C : ℕ} {U : Finset V → ℝ} {target epsilon : ℝ}
    (hunif : H.IsUniform k)
    (hlow : ∀ v ∈ A, degreeLower ≤ H.edgeDegree v)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (hU : ∀ B, U B ∈ Set.Icc (0 : ℝ) 1)
    (htarget₀ : 0 ≤ target) (hepsilon₀ : 0 ≤ epsilon)
    (hsingle : ∀ e ∈ H.singleMeetingEdges A,
      |U (A ∪ H.support e) - target| ≤ epsilon) :
    (
      max 0
          (((A.card * degreeLower : ℕ) : ℝ) -
            ((A.card ^ 2 * C * (k + 1) : ℕ) : ℝ)) *
        max 0 (target - epsilon)) ≤
        ∑ e ∈ H.edgesMeeting A, U (A ∪ H.support e) ∧
      ∑ e ∈ H.edgesMeeting A, U (A ∪ H.support e) ≤
        ((A.card * D : ℕ) : ℝ) * (target + epsilon) +
          ((A.card ^ 2 * C : ℕ) : ℝ) := by
  have hsingleCard := H.singleMeetingEdges_card_mem_Icc A hunif hlow hdeg hpair
  have hmultiCard := H.multiMeetingEdges_card_le_sq_mul_pairDegree A C hpair
  let countLower : ℝ :=
    ((A.card * degreeLower : ℕ) : ℝ) -
      ((A.card ^ 2 * C * (k + 1) : ℕ) : ℝ)
  let valueLower : ℝ := max 0 (target - epsilon)
  have hcountLower : max 0 countLower ≤
      ((H.singleMeetingEdges A).card : ℝ) := by
    exact max_le (Nat.cast_nonneg _) hsingleCard.1
  have hvalueLower₀ : 0 ≤ valueLower := le_max_left _ _
  have hsingleBounds : ∀ e ∈ H.singleMeetingEdges A,
      valueLower ≤ U (A ∪ H.support e) ∧
        U (A ∪ H.support e) ≤ target + epsilon := by
    intro e he
    have habs := abs_sub_le_iff.mp (hsingle e he)
    constructor
    · apply max_le
      · exact (hU _).1
      · linarith
    · linarith
  rw [H.sum_edgesMeeting_eq_sum_single_add_sum_multi]
  constructor
  · calc
      max 0 countLower * valueLower ≤
          ((H.singleMeetingEdges A).card : ℝ) * valueLower :=
        mul_le_mul_of_nonneg_right hcountLower hvalueLower₀
      _ = ∑ _e ∈ H.singleMeetingEdges A, valueLower := by simp
      _ ≤ ∑ e ∈ H.singleMeetingEdges A, U (A ∪ H.support e) := by
        apply sum_le_sum
        intro e he
        exact (hsingleBounds e he).1
      _ ≤ (∑ e ∈ H.singleMeetingEdges A, U (A ∪ H.support e)) +
          ∑ e ∈ H.multiMeetingEdges A, U (A ∪ H.support e) := by
        exact le_add_of_nonneg_right (sum_nonneg fun e _ ↦ (hU _).1)
  · calc
      (∑ e ∈ H.singleMeetingEdges A, U (A ∪ H.support e)) +
          ∑ e ∈ H.multiMeetingEdges A, U (A ∪ H.support e) ≤
          ((H.singleMeetingEdges A).card : ℝ) * (target + epsilon) +
            ((H.multiMeetingEdges A).card : ℝ) := by
        apply add_le_add
        · calc
            ∑ e ∈ H.singleMeetingEdges A, U (A ∪ H.support e) ≤
                ∑ _e ∈ H.singleMeetingEdges A, (target + epsilon) := by
              apply sum_le_sum
              intro e he
              exact (hsingleBounds e he).2
            _ = ((H.singleMeetingEdges A).card : ℝ) *
                (target + epsilon) := by simp <;> ring
        · calc
            ∑ e ∈ H.multiMeetingEdges A, U (A ∪ H.support e) ≤
                ∑ _e ∈ H.multiMeetingEdges A, (1 : ℝ) := by
              apply sum_le_sum
              intro e _
              exact (hU _).2
            _ = ((H.multiMeetingEdges A).card : ℝ) := by simp
      _ ≤ ((A.card * D : ℕ) : ℝ) * (target + epsilon) +
          ((A.card ^ 2 * C : ℕ) : ℝ) := by
        have htargetPlus₀ : 0 ≤ target + epsilon := by linarith
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hsingleCard.2 htargetPlus₀
        · exact_mod_cast hmultiCard

/-- Real-parameter form of the truncation-stable profile comparison.  This
matches the near-regular and low-codegree hypotheses in
`TwoSidedFixedLengthInnerMarginalAt` exactly and avoids any rounding loss. -/
theorem sum_edgesMeeting_profile_real_max_mem_Icc
    (H : FiniteHypergraph V E) (A : Finset V)
    {k D : ℕ} {degreeLower codegreeUpper : ℝ}
    {U : Finset V → ℝ} {target epsilon : ℝ}
    (hunif : H.IsUniform k)
    (hlow : ∀ v ∈ A, degreeLower ≤ (H.edgeDegree v : ℝ))
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hcodegreeUpper₀ : 0 ≤ codegreeUpper)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      (H.edgePairDegree u v : ℝ) ≤ codegreeUpper)
    (hU : ∀ B, U B ∈ Set.Icc (0 : ℝ) 1)
    (htarget₀ : 0 ≤ target) (hepsilon₀ : 0 ≤ epsilon)
    (hsingle : ∀ e ∈ H.singleMeetingEdges A,
      |U (A ∪ H.support e) - target| ≤ epsilon) :
    (max 0
          ((A.card : ℝ) * degreeLower -
            (A.card : ℝ) ^ 2 * codegreeUpper * ((k : ℝ) + 1)) *
        max 0 (target - epsilon)) ≤
        ∑ e ∈ H.edgesMeeting A, U (A ∪ H.support e) ∧
      ∑ e ∈ H.edgesMeeting A, U (A ∪ H.support e) ≤
        ((A.card * D : ℕ) : ℝ) * (target + epsilon) +
          (A.card : ℝ) ^ 2 * codegreeUpper := by
  have hsingleLower := H.natCast_singleMeetingEdges_card_ge_real
    A degreeLower codegreeUpper hunif hlow hcodegreeUpper₀ hpair
  have hmultiUpper := H.natCast_multiMeetingEdges_card_le_sq_mul_pairDegree_real
    A codegreeUpper hcodegreeUpper₀ hpair
  have hsingleUpper :
      ((H.singleMeetingEdges A).card : ℝ) ≤
        ((A.card * D : ℕ) : ℝ) := by
    exact_mod_cast (card_le_card sdiff_subset |>.trans
      (H.edgesMeeting_card_le_mul_degree A D hdeg))
  let countLower : ℝ :=
    (A.card : ℝ) * degreeLower -
      (A.card : ℝ) ^ 2 * codegreeUpper * ((k : ℝ) + 1)
  let valueLower : ℝ := max 0 (target - epsilon)
  have hcountLower : max 0 countLower ≤
      ((H.singleMeetingEdges A).card : ℝ) := by
    exact max_le (Nat.cast_nonneg _) hsingleLower
  have hvalueLower₀ : 0 ≤ valueLower := le_max_left _ _
  have hsingleBounds : ∀ e ∈ H.singleMeetingEdges A,
      valueLower ≤ U (A ∪ H.support e) ∧
        U (A ∪ H.support e) ≤ target + epsilon := by
    intro e he
    have habs := abs_sub_le_iff.mp (hsingle e he)
    constructor
    · apply max_le
      · exact (hU _).1
      · linarith
    · linarith
  rw [H.sum_edgesMeeting_eq_sum_single_add_sum_multi]
  constructor
  · calc
      max 0 countLower * valueLower ≤
          ((H.singleMeetingEdges A).card : ℝ) * valueLower :=
        mul_le_mul_of_nonneg_right hcountLower hvalueLower₀
      _ = ∑ _e ∈ H.singleMeetingEdges A, valueLower := by simp
      _ ≤ ∑ e ∈ H.singleMeetingEdges A, U (A ∪ H.support e) := by
        apply sum_le_sum
        intro e he
        exact (hsingleBounds e he).1
      _ ≤ (∑ e ∈ H.singleMeetingEdges A, U (A ∪ H.support e)) +
          ∑ e ∈ H.multiMeetingEdges A, U (A ∪ H.support e) := by
        exact le_add_of_nonneg_right (sum_nonneg fun e _ ↦ (hU _).1)
  · calc
      (∑ e ∈ H.singleMeetingEdges A, U (A ∪ H.support e)) +
          ∑ e ∈ H.multiMeetingEdges A, U (A ∪ H.support e) ≤
          ((H.singleMeetingEdges A).card : ℝ) * (target + epsilon) +
            ((H.multiMeetingEdges A).card : ℝ) := by
        apply add_le_add
        · calc
            ∑ e ∈ H.singleMeetingEdges A, U (A ∪ H.support e) ≤
                ∑ _e ∈ H.singleMeetingEdges A, (target + epsilon) := by
              apply sum_le_sum
              intro e he
              exact (hsingleBounds e he).2
            _ = ((H.singleMeetingEdges A).card : ℝ) *
                (target + epsilon) := by simp <;> ring
        · calc
            ∑ e ∈ H.multiMeetingEdges A, U (A ∪ H.support e) ≤
                ∑ _e ∈ H.multiMeetingEdges A, (1 : ℝ) := by
              apply sum_le_sum
              intro e _
              exact (hU _).2
            _ = ((H.multiMeetingEdges A).card : ℝ) := by simp
      _ ≤ ((A.card * D : ℕ) : ℝ) * (target + epsilon) +
          (A.card : ℝ) ^ 2 * codegreeUpper := by
        have htargetPlus₀ : 0 ≤ target + epsilon := by linarith
        exact add_le_add
          (mul_le_mul_of_nonneg_right hsingleUpper htargetPlus₀)
          hmultiUpper

/-- One forward step of the finite-horizon joint-moment comparison.  Once
the moments on `A` and on all nonexceptional one-edge enlargements of `A`
are close to prescribed scalar profiles, the next moment lies in this
fully explicit interval.  This is the exact inductive interface between
the hypergraph estimates and the remaining scalar error recursion. -/
theorem innerJointUncoveredMass_succ_profile_mem_Icc
    (H : FiniteHypergraph V E) (A : Finset V)
    {k degreeLower D C r : ℕ} {p center target epsilonA epsilonNext : ℝ}
    (hk : 0 < k) (hunif : H.IsUniform k)
    (hlow : ∀ v ∈ A, degreeLower ≤ H.edgeDegree v)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hq₀ : 0 ≤ p - (((k * D : ℕ) : ℝ) * p ^ 2))
    (hepsilonNext₀ : 0 ≤ epsilonNext)
    (htarget : epsilonNext ≤ target)
    (hcenter :
      |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r ∅ A - center| ≤
        epsilonA)
    (henlarged : ∀ e ∈ H.singleMeetingEdges A,
      |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r ∅
            (A ∪ H.support e) - target| ≤ epsilonNext) :
    H.innerJointUncoveredMass
        (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) (r + 1) ∅ A ∈
      Set.Icc
        (center - epsilonA - p *
          (((A.card * D : ℕ) : ℝ) * (target + epsilonNext) +
            ((A.card ^ 2 * C : ℕ) : ℝ)))
        (center + epsilonA -
            (p - (((k * D : ℕ) : ℝ) * p ^ 2)) *
              (((((A.card * degreeLower : ℕ) : ℝ) -
                  ((A.card ^ 2 * C * (k + 1) : ℕ) : ℝ))) *
                (target - epsilonNext)) +
          ((((A.card * D : ℕ) : ℝ) * p) ^ 2) / 2 *
            (center + epsilonA)) := by
  let w : Finset E → ℝ :=
    FiniteNibble.bernoulliMass univ (fun _ ↦ p)
  let U : Finset V → ℝ := fun B ↦ H.innerJointUncoveredMass w r ∅ B
  let enlarged : ℝ := ∑ e ∈ H.edgesMeeting A, U (A ∪ H.support e)
  let q : ℝ := p - (((k * D : ℕ) : ℝ) * p ^ 2)
  let pairError : ℝ := ((((A.card * D : ℕ) : ℝ) * p) ^ 2) / 2
  have hU (B : Finset V) : U B ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [U, w]
    exact H.innerJointUncoveredMass_bernoulli_mem_Icc
      (fun _ ↦ p) (fun _ ↦ hp₀) (fun _ ↦ hp₁) r ∅ B
  have hprofile : enlarged ∈
      Set.Icc
        (((((A.card * degreeLower : ℕ) : ℝ) -
            ((A.card ^ 2 * C * (k + 1) : ℕ) : ℝ))) *
          (target - epsilonNext))
        (((A.card * D : ℕ) : ℝ) * (target + epsilonNext) +
          ((A.card ^ 2 * C : ℕ) : ℝ)) := by
    apply H.sum_edgesMeeting_profile_mem_Icc A hunif hlow hdeg hpair hU
      hepsilonNext₀ htarget
    intro e he
    simpa [U, w] using henlarged e he
  have hrec := H.innerJointUncoveredMass_succ_mem_Icc
    hk hunif hdeg r ∅ A p hp₀ hp₁
  have hcenterBounds :
      center - epsilonA ≤ U A ∧ U A ≤ center + epsilonA := by
    have habs := abs_sub_le_iff.mp hcenter
    dsimp only [U, w]
    constructor <;> linarith
  change H.innerJointUncoveredMass w (r + 1) ∅ A ∈ Set.Icc _ _
  change H.innerJointUncoveredMass w (r + 1) ∅ A ∈
    Set.Icc (U A - p * enlarged)
      (U A - q * enlarged + pairError * U A) at hrec
  constructor
  · calc
      center - epsilonA - p *
          (((A.card * D : ℕ) : ℝ) * (target + epsilonNext) +
            ((A.card ^ 2 * C : ℕ) : ℝ)) ≤
          U A - p * enlarged := by
        exact sub_le_sub hcenterBounds.1
          (mul_le_mul_of_nonneg_left hprofile.2 hp₀)
      _ ≤ H.innerJointUncoveredMass w (r + 1) ∅ A := hrec.1
  · calc
      H.innerJointUncoveredMass w (r + 1) ∅ A ≤
          U A - q * enlarged + pairError * U A := hrec.2
      _ ≤ center + epsilonA -
            q *
              (((((A.card * degreeLower : ℕ) : ℝ) -
                  ((A.card ^ 2 * C * (k + 1) : ℕ) : ℝ))) *
                (target - epsilonNext)) +
            pairError * (center + epsilonA) := by
        have hpairError₀ : 0 ≤ pairError := by
          dsimp only [pairError]
          positivity
        exact add_le_add
          (sub_le_sub hcenterBounds.2
            (mul_le_mul_of_nonneg_left hprofile.1 hq₀))
          (mul_le_mul_of_nonneg_left hcenterBounds.2 hpairError₀)

/-- Exact one-step recurrence in the real near-regular parameters, with
truncated lower factors.  Unlike the integer-threshold variant above, this
can be instantiated directly with `degreeLower = (1-eta)D` and
`codegreeUpper = eta D`. -/
theorem innerJointUncoveredMass_succ_profile_real_max_mem_Icc
    (H : FiniteHypergraph V E) (A : Finset V)
    {k D r : ℕ} {degreeLower codegreeUpper p center target
      epsilonA epsilonNext : ℝ}
    (hk : 0 < k) (hunif : H.IsUniform k)
    (hlow : ∀ v ∈ A, degreeLower ≤ (H.edgeDegree v : ℝ))
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hcodegreeUpper₀ : 0 ≤ codegreeUpper)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      (H.edgePairDegree u v : ℝ) ≤ codegreeUpper)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hq₀ : 0 ≤ p - (((k * D : ℕ) : ℝ) * p ^ 2))
    (htarget₀ : 0 ≤ target) (hepsilonNext₀ : 0 ≤ epsilonNext)
    (hcenter :
      |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r ∅ A - center| ≤
        epsilonA)
    (henlarged : ∀ e ∈ H.singleMeetingEdges A,
      |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r ∅
            (A ∪ H.support e) - target| ≤ epsilonNext) :
    H.innerJointUncoveredMass
        (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) (r + 1) ∅ A ∈
      Set.Icc
        (center - epsilonA - p *
          (((A.card * D : ℕ) : ℝ) * (target + epsilonNext) +
            (A.card : ℝ) ^ 2 * codegreeUpper))
        (center + epsilonA -
            (p - (((k * D : ℕ) : ℝ) * p ^ 2)) *
              (max 0
                  ((A.card : ℝ) * degreeLower -
                    (A.card : ℝ) ^ 2 * codegreeUpper * ((k : ℝ) + 1)) *
                max 0 (target - epsilonNext)) +
          ((((A.card * D : ℕ) : ℝ) * p) ^ 2) / 2 *
            (center + epsilonA)) := by
  let w : Finset E → ℝ :=
    FiniteNibble.bernoulliMass univ (fun _ ↦ p)
  let U : Finset V → ℝ := fun B ↦ H.innerJointUncoveredMass w r ∅ B
  let enlarged : ℝ := ∑ e ∈ H.edgesMeeting A, U (A ∪ H.support e)
  let q : ℝ := p - (((k * D : ℕ) : ℝ) * p ^ 2)
  let pairError : ℝ := ((((A.card * D : ℕ) : ℝ) * p) ^ 2) / 2
  have hU (B : Finset V) : U B ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [U, w]
    exact H.innerJointUncoveredMass_bernoulli_mem_Icc
      (fun _ ↦ p) (fun _ ↦ hp₀) (fun _ ↦ hp₁) r ∅ B
  have hprofile : enlarged ∈
      Set.Icc
        (max 0
            ((A.card : ℝ) * degreeLower -
              (A.card : ℝ) ^ 2 * codegreeUpper * ((k : ℝ) + 1)) *
          max 0 (target - epsilonNext))
        (((A.card * D : ℕ) : ℝ) * (target + epsilonNext) +
          (A.card : ℝ) ^ 2 * codegreeUpper) := by
    apply H.sum_edgesMeeting_profile_real_max_mem_Icc A hunif hlow hdeg
      hcodegreeUpper₀ hpair hU htarget₀ hepsilonNext₀
    intro e he
    simpa [U, w] using henlarged e he
  have hrec := H.innerJointUncoveredMass_succ_mem_Icc
    hk hunif hdeg r ∅ A p hp₀ hp₁
  have hcenterBounds :
      center - epsilonA ≤ U A ∧ U A ≤ center + epsilonA := by
    have habs := abs_sub_le_iff.mp hcenter
    dsimp only [U, w]
    constructor <;> linarith
  change H.innerJointUncoveredMass w (r + 1) ∅ A ∈ Set.Icc _ _
  change H.innerJointUncoveredMass w (r + 1) ∅ A ∈
    Set.Icc (U A - p * enlarged)
      (U A - q * enlarged + pairError * U A) at hrec
  constructor
  · calc
      center - epsilonA - p *
          (((A.card * D : ℕ) : ℝ) * (target + epsilonNext) +
            (A.card : ℝ) ^ 2 * codegreeUpper) ≤
          U A - p * enlarged := by
        exact sub_le_sub hcenterBounds.1
          (mul_le_mul_of_nonneg_left hprofile.2 hp₀)
      _ ≤ H.innerJointUncoveredMass w (r + 1) ∅ A := hrec.1
  · calc
      H.innerJointUncoveredMass w (r + 1) ∅ A ≤
          U A - q * enlarged + pairError * U A := hrec.2
      _ ≤ center + epsilonA -
            q *
              (max 0
                  ((A.card : ℝ) * degreeLower -
                    (A.card : ℝ) ^ 2 * codegreeUpper * ((k : ℝ) + 1)) *
                max 0 (target - epsilonNext)) +
            pairError * (center + epsilonA) := by
        have hpairError₀ : 0 ≤ pairError := by
          dsimp only [pairError]
          positivity
        exact add_le_add
          (sub_le_sub hcenterBounds.2
            (mul_le_mul_of_nonneg_left hprofile.1 hq₀))
          (mul_le_mul_of_nonneg_left hcenterBounds.2 hpairError₀)
  

/-- A uniform round-by-round comparison with the mean-field live-edge
profile gives the desired two-sided marginal.  The two scalar hypotheses are
exactly the final error budget; the remaining combinatorial work is the
pointwise estimate `hclose`. -/
theorem innerAcceptanceMass_twoSided_of_liveMass_close
    {H : FiniteHypergraph V E} {k D L : ℕ} (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {beta rho zeta : ℝ}
    (hp₀ : 0 ≤ beta / (D : ℝ)) (hp₁ : beta / (D : ℝ) ≤ 1)
    (hq₀ : 0 ≤ beta / (D : ℝ) -
      (((k * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2))
    (hlower : (1 - zeta) / (D : ℝ) ≤
      (beta / (D : ℝ) -
        (((k * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2)) *
        (∑ r ∈ range L, (meanFieldSurvival k beta r ^ k - rho)))
    (hupper : beta / (D : ℝ) *
        (∑ r ∈ range L, (meanFieldSurvival k beta r ^ k + rho)) ≤
      (1 + zeta) / (D : ℝ))
    (hclose : ∀ e r, r < L →
      |H.innerLiveMass
          (FiniteNibble.bernoulliMass univ
            (fun _ ↦ beta / (D : ℝ))) r ∅ e -
        meanFieldSurvival k beta r ^ k| ≤ rho) (e : E) :
    (1 - zeta) / (D : ℝ) ≤
        H.innerAcceptanceMass L (fun _ ↦ beta / (D : ℝ)) e ∧
      H.innerAcceptanceMass L (fun _ ↦ beta / (D : ℝ)) e ≤
        (1 + zeta) / (D : ℝ) := by
  have hliveLower : ∀ r < L, meanFieldSurvival k beta r ^ k - rho ≤
      H.innerLiveMass
        (FiniteNibble.bernoulliMass univ
          (fun _ ↦ beta / (D : ℝ))) r ∅ e := by
    intro r hr
    have habs := abs_sub_le_iff.mp (hclose e r hr)
    linarith
  have hliveUpper : ∀ r < L,
      H.innerLiveMass
          (FiniteNibble.bernoulliMass univ
            (fun _ ↦ beta / (D : ℝ))) r ∅ e ≤
        meanFieldSurvival k beta r ^ k + rho := by
    intro r hr
    have habs := abs_sub_le_iff.mp (hclose e r hr)
    linarith
  constructor
  · exact hlower.trans
      (H.sub_mul_sum_le_innerAcceptanceMass_const_of_innerLiveMass_ge
        hunif hdeg hp₀ hp₁ hq₀ L
        (fun r ↦ meanFieldSurvival k beta r ^ k - rho) hliveLower)
  · exact (H.innerAcceptanceMass_le_mul_sum_of_innerLiveMass_le
      (fun _ ↦ hp₀) (fun _ ↦ hp₁) L e
      (fun r ↦ meanFieldSurvival k beta r ^ k + rho) hliveUpper).trans hupper

end FiniteHypergraph

end

end Erdos76
