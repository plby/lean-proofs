/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.HypergraphRegularizationParameters

/-! # Finite accepted-edge states for adaptive hypergraph regularization -/

namespace Erdos207

open Finset

noncomputable section

abbrev HypergraphRegularizationState (V : Type*) [Fintype V] [DecidableEq V] (k : ℕ) :=
  Finset (UniformHyperedge V k) × Bool

def regularizationAcceptedEdges
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (S : HypergraphRegularizationState V k) : Finset (Finset V) := S.1.image Subtype.val

def regularizationCurrentFamily
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (G0 : Finset (Finset V)) (S : HypergraphRegularizationState V k) : Finset (Finset V) :=
  G0 ∪ regularizationAcceptedEdges S

def regularizationInitialState
    (V : Type*) [Fintype V] [DecidableEq V] (k : ℕ) : HypergraphRegularizationState V k :=
  (∅, false)

def regularizationReject
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (S : HypergraphRegularizationState V k) : HypergraphRegularizationState V k := (S.1, true)

def regularizationAccept
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (S : HypergraphRegularizationState V k) (H : Finset (Finset V))
    (ω : UniformHyperedge V k → Bool) : HypergraphRegularizationState V k :=
  (S.1 ∪ univ.filter (fun E ↦ ω E = true ∧ E.1 ∉ H), false)

@[simp] theorem regularizationCurrentFamily_initial
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (G0 : Finset (Finset V)) :
    regularizationCurrentFamily G0 (regularizationInitialState V k) = G0 := by
  simp [regularizationCurrentFamily, regularizationInitialState, regularizationAcceptedEdges]

@[simp] theorem regularizationCurrentFamily_reject
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (G0 : Finset (Finset V)) (S : HypergraphRegularizationState V k) :
    regularizationCurrentFamily G0 (regularizationReject S) = regularizationCurrentFamily G0 S := rfl

theorem regularizationCurrentFamily_mono_base
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    {G0 H0 : Finset (Finset V)} (h : G0 ⊆ H0) (S : HypergraphRegularizationState V k) :
    regularizationCurrentFamily G0 S ⊆ regularizationCurrentFamily H0 S :=
  union_subset_union h Subset.rfl

theorem regularizationAcceptedEdges_accept
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (S : HypergraphRegularizationState V k) (H : Finset (Finset V))
    (ω : UniformHyperedge V k → Bool) :
    regularizationAcceptedEdges (regularizationAccept S H ω) =
      regularizationAcceptedEdges S ∪ sampledFreshUniformHypergraph H ω := by
  exact image_union _ _

theorem regularizationCurrentFamily_accept
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (G0 : Finset (Finset V)) (S : HypergraphRegularizationState V k) (H : Finset (Finset V))
    (ω : UniformHyperedge V k → Bool) :
    regularizationCurrentFamily G0 (regularizationAccept S H ω) =
      regularizationCurrentFamily G0 S ∪ sampledFreshUniformHypergraph H ω := by
  unfold regularizationCurrentFamily
  rw [regularizationAcceptedEdges_accept, union_assoc]

theorem regularizationAcceptedEdges_uniform
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (S : HypergraphRegularizationState V k) :
    ∀ E ∈ regularizationAcceptedEdges S, E.card = k := by
  intro E hE
  obtain ⟨A, _hA, rfl⟩ := mem_image.mp hE
  exact (mem_powersetCard.mp A.2).2

theorem regularizationAccept_preserves_disjoint
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (H0 : Finset (Finset V)) (S : HypergraphRegularizationState V k)
    (hdis : Disjoint (regularizationAcceptedEdges S) H0) (ω : UniformHyperedge V k → Bool) :
    Disjoint (regularizationAcceptedEdges (regularizationAccept S (regularizationCurrentFamily H0 S) ω)) H0 := by
  rw [regularizationAcceptedEdges_accept, disjoint_union_left]
  refine ⟨hdis, ?_⟩
  exact (sampledFreshUniformHypergraph_disjoint (regularizationCurrentFamily H0 S) ω).mono_right
    subset_union_left

end

end Erdos207
