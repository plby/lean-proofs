/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationHorizon
import ErdosProblems.Erdos207.RegularizationJointInclusion
import ErdosProblems.Erdos207.JointInclusionImage

/-! # Decoding auxiliary hyperedges into ambient configuration bits -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def regularizationImageEdges
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J] {k : ℕ}
    (e : I ↪ J) (S : HypergraphRegularizationState I k) : Finset (Finset J) :=
  (regularizationAcceptedEdges S).image (Finset.map e)

theorem regularizationImageEdges_eq
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J] {k : ℕ}
    (e : I ↪ J) (S : HypergraphRegularizationState I k) :
    regularizationImageEdges e S = S.1.image (fun E ↦ E.1.map e) := by
  simp only [regularizationImageEdges, regularizationAcceptedEdges, image_image, Function.comp_def]

theorem regularizationImageEdges_uniform
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J] {k : ℕ}
    (e : I ↪ J) (S : HypergraphRegularizationState I k) :
    ∀ E ∈ regularizationImageEdges e S, E.card = k := by
  intro E hE
  obtain ⟨A, hA, rfl⟩ := mem_image.mp hE
  simpa only [card_map] using regularizationAcceptedEdges_uniform S A hA

theorem regularizationImageEdges_subset_of_avoid
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J] {k : ℕ}
    (e : I ↪ J) (C : Finset (Finset J)) (H0 : Finset (Finset I))
    (S : HypergraphRegularizationState I k)
    (havoid : Disjoint (regularizationAcceptedEdges S) H0)
    (hbad : ∀ E : Finset I, E.card = k → E.map e ∉ C → E ∈ H0) :
    regularizationImageEdges e S ⊆ C := by
  intro E hE
  obtain ⟨A, hA, rfl⟩ := mem_image.mp hE
  by_contra hnot
  exact disjoint_left.mp havoid hA
    (hbad A (regularizationAcceptedEdges_uniform S A hA) hnot)

theorem regularizationProcessLaw_image_joint_inclusion
    {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq J] {k : ℕ}
    (G0 H0 : Finset (Finset I)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card I)
    (b : ℕ) (e : I ↪ J) (U : Finset (Finset J)) :
    (regularizationProcessLaw G0 H0 hGH hk hsize b).probability
      (fun S ↦ U ⊆ regularizationImageEdges e S) ≤
      (2 * regularizationBaseHazard G0 k) ^ U.card := by
  simp only [regularizationImageEdges_eq]
  exact joint_inclusion_image_le (regularizationProcessLaw G0 H0 hGH hk hsize b)
    Prod.fst (fun E : UniformHyperedge I k ↦ E.1.map e)
    ((Finset.map_injective e).comp Subtype.val_injective)
    (2 * regularizationBaseHazard G0 k)
    (regularizationEvolve_joint_inclusion G0 H0 hGH hk hsize b (finiteHypergraphDegreeGap G0)) U

def regularizationImageBits
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J] {k : ℕ}
    (e : I ↪ J) (S : HypergraphRegularizationState I k) : Finset J → Bool :=
  fun C ↦ decide (C ∈ regularizationImageEdges e S)

@[simp] theorem regularizationImageBits_eq_true
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J] {k : ℕ}
    (e : I ↪ J) (S : HypergraphRegularizationState I k) (C : Finset J) :
    regularizationImageBits e S C = true ↔ C ∈ regularizationImageEdges e S := by
  simp [regularizationImageBits]

def regularizationImageLaw
    {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] {k : ℕ}
    (G0 H0 : Finset (Finset I)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card I)
    (b : ℕ) (e : I ↪ J) : FiniteLaw (Finset J → Bool) := by
  classical
  exact FiniteLaw.map (regularizationImageBits e)
    (regularizationProcessLaw G0 H0 hGH hk hsize b)

theorem regularizationImageLaw_joint_inclusion
    {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] {k : ℕ}
    (G0 H0 : Finset (Finset I)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card I)
    (b : ℕ) (e : I ↪ J) (U : Finset (Finset J)) :
    (regularizationImageLaw G0 H0 hGH hk hsize b e).probability
      (fun ω ↦ ∀ E ∈ U, ω E = true) ≤ (2 * regularizationBaseHazard G0 k) ^ U.card := by
  classical
  rw [regularizationImageLaw, FiniteLaw.probability_map]
  simp only [regularizationImageBits_eq_true]
  exact regularizationProcessLaw_image_joint_inclusion G0 H0 hGH hk hsize b e U

end

end Erdos207
