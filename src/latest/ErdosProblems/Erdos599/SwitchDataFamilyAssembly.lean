/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating

/-!
# Assembly of families of raw switching data

`SwitchData.RealizedBy` is deliberately a statement about one exact edge
relation.  Pointwise realizations therefore do not by themselves assemble:
paths chosen for different indices may meet.  This file records the precise
extra hypothesis under which they do assemble, namely disjointness of the
supports belonging to distinct indices.

The resulting construction realizes the union of the pointwise raw edge and
isolated-vertex data.  It should not be confused with simultaneously applying
several alternating routes to one reference warp: that operation uses one
symmetric difference with the union of the route edges, whereas the
construction here takes the union of the already switched edge relations.
-/

noncomputable section

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

namespace SwitchData

/-- The componentwise union of a family of raw switching data. -/
def familyUnion (S : I → SwitchData Gamma) : SwitchData Gamma where
  edges := ⋃ i, (S i).edges
  edges_in_graph := by
    rintro e he
    simp only [Set.mem_iUnion] at he
    obtain ⟨i, hei⟩ := he
    exact (S i).edges_in_graph hei
  isolated := ⋃ i, (S i).isolated

@[simp]
theorem familyUnion_edges (S : I → SwitchData Gamma) :
    (familyUnion S).edges = ⋃ i, (S i).edges :=
  rfl

@[simp]
theorem familyUnion_isolated (S : I → SwitchData Gamma) :
    (familyUnion S).isolated = ⋃ i, (S i).isolated :=
  rfl

/-- Cross-index support disjointness is exactly the compatibility datum
missing from a family of pointwise `RealizedBy` certificates. -/
def CrossSupportDisjoint (W : I → Set Gamma.DPath) : Prop :=
  ∀ ⟨i j : I⟩, i ≠ j →
    ∀ ⟨p : Gamma.DPath⟩, p ∈ W i →
      ∀ ⟨q : Gamma.DPath⟩, q ∈ W j →
        Disjoint p.support q.support

/-- Pairwise warp structure plus cross-index support disjointness makes the
union of the component families an honest warp. -/
theorem isWarp_iUnion
    {W : I → Set Gamma.DPath}
    (hW : ∀ i, Gamma.IsWarp (W i))
    (hcross : CrossSupportDisjoint W) :
    Gamma.IsWarp (⋃ i, W i) := by
  intro p hp q hq hpq
  simp only [Set.mem_iUnion] at hp hq
  obtain ⟨i, hpi⟩ := hp
  obtain ⟨j, hqj⟩ := hq
  by_cases hij : i = j
  · subst j
    exact hW i hpi hqj hpq
  · exact hcross hij hpi hqj

@[simp]
theorem familyEdges_iUnion (W : I → Set Gamma.DPath) :
    familyEdges (⋃ i, W i) = ⋃ i, familyEdges (W i) := by
  ext e
  simp only [familyEdges, Set.mem_iUnion]
  constructor
  · rintro ⟨p, ⟨i, hpi⟩, hep⟩
    exact ⟨i, p, hpi, hep⟩
  · rintro ⟨i, p, hpi, hep⟩
    exact ⟨p, ⟨i, hpi⟩, hep⟩

@[simp]
theorem isolatedVertices_iUnion (W : I → Set Gamma.DPath) :
    isolatedVertices (⋃ i, W i) = ⋃ i, isolatedVertices (W i) := by
  ext x
  simp only [isolatedVertices, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, hi⟩

/-- A compatible family of exact pointwise realizations realizes the union
of the raw switching data.  This is the strongest purely pointwise assembly
rule: without `hcross`, the union of the realizing families need not be a
warp. -/
theorem realizedBy_familyUnion
    {S : I → SwitchData Gamma} {W : I → Set Gamma.DPath}
    (hreal : ∀ i, (S i).RealizedBy (W i))
    (hcross : CrossSupportDisjoint W) :
    (familyUnion S).RealizedBy (⋃ i, W i) := by
  refine ⟨isWarp_iUnion (fun i ↦ (hreal i).1) hcross, ?_, ?_⟩
  · rw [familyEdges_iUnion]
    simp only [familyUnion_edges]
    congr 1
    funext i
    exact (hreal i).2.1
  · rw [isolatedVertices_iUnion]
    simp only [familyUnion_isolated]
    congr 1
    funext i
    exact (hreal i).2.2

/-- Consequently, compatible pointwise realizations combine into one honest
cyclowarp (with no cycle components). -/
theorem isCyclowarp_familyUnion
    {S : I → SwitchData Gamma} {W : I → Set Gamma.DPath}
    (hreal : ∀ i, (S i).RealizedBy (W i))
    (hcross : CrossSupportDisjoint W) :
    (familyUnion S).IsCyclowarp :=
  isCyclowarp_of_realizedBy (realizedBy_familyUnion hreal hcross)

end SwitchData
end Alternating
end Erdos599
