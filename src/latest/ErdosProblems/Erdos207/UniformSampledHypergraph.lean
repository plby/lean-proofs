/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.WeightedUniformSampler

/-! # The simple hypergraph represented by the weighted sampling bits -/

namespace Erdos207

open Finset

noncomputable section

def sampledFreshUniformHypergraph
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (H : Finset (Finset V)) (ω : UniformHyperedge V k → Bool) : Finset (Finset V) :=
  ((univ : Finset (UniformHyperedge V k)).filter fun E ↦ ω E = true ∧ E.1 ∉ H).image Subtype.val

theorem mem_sampledFreshUniformHypergraph_iff
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (H : Finset (Finset V)) (ω : UniformHyperedge V k → Bool) (E : Finset V) :
    E ∈ sampledFreshUniformHypergraph H ω ↔
      ∃ A : UniformHyperedge V k, A.1 = E ∧ ω A = true ∧ A.1 ∉ H := by
  simp only [sampledFreshUniformHypergraph, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨A, hA, heq⟩
    exact ⟨A, heq, hA⟩
  · rintro ⟨A, heq, hA⟩
    exact ⟨A, hA, heq⟩

theorem sampledFreshUniformHypergraph_uniform
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (H : Finset (Finset V)) (ω : UniformHyperedge V k → Bool) :
    ∀ E ∈ sampledFreshUniformHypergraph H ω, E.card = k := by
  intro E hE
  obtain ⟨A, rfl, _hA⟩ := (mem_sampledFreshUniformHypergraph_iff H ω E).mp hE
  exact (mem_powersetCard.mp A.2).2

theorem sampledFreshUniformHypergraph_disjoint
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (H : Finset (Finset V)) (ω : UniformHyperedge V k → Bool) :
    Disjoint (sampledFreshUniformHypergraph H ω) H := by
  apply disjoint_left.mpr
  intro E hE hH
  obtain ⟨A, rfl, _hbit, hnH⟩ := (mem_sampledFreshUniformHypergraph_iff H ω E).mp hE
  exact hnH hH

theorem sampledFreshUniformHypergraph_degree
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (H : Finset (Finset V)) (ω : UniformHyperedge V k → Bool) (v : V) :
    ((sampledFreshUniformHypergraph H ω).filter fun E ↦ v ∈ E).card =
      sampledFreshUniformDegree H v ω := by
  have heq : (sampledFreshUniformHypergraph H ω).filter (fun E ↦ v ∈ E) =
      ((uniformFreshIncidentIndex k H v).filter fun E ↦ ω E = true).image Subtype.val := by
    ext E
    simp only [mem_filter, mem_sampledFreshUniformHypergraph_iff, mem_image,
      uniformFreshIncidentIndex, mem_univ, true_and]
    constructor
    · rintro ⟨⟨A, hAE, hbit, hnH⟩, hv⟩
      exact ⟨A, ⟨⟨hAE ▸ hv, hnH⟩, hbit⟩, hAE⟩
    · rintro ⟨A, ⟨⟨hv, hnH⟩, hbit⟩, hAE⟩
      exact ⟨⟨A, hAE, hbit, hnH⟩, hAE ▸ hv⟩
  rw [heq, card_image_of_injective _ Subtype.val_injective]
  rfl

end

end Erdos207
