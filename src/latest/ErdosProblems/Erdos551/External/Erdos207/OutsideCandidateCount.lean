/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.GreedyObstructionCount

/-!
# Initial outside-candidate counts

For a fixed pair not belonging to the absorber graph, the only reasons that
a third vertex fails to give a canonical outside triangle are: the resulting
triangle belongs to the absorber bank, or one of the two new pairs belongs
to the absorber graph.  This file proves the resulting exact finite lower
bound without asymptotic notation.
-/

namespace Erdos207

open Finset

/-- There are exactly `|V|-2` possible third vertices for a genuine pair. -/
lemma card_thirdVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v) :
    Fintype.card (ThirdVertex u v) = Fintype.card V - 2 := by
  let e : ThirdVertex u v ≃ {w : V // ¬(w = u ∨ w = v)} :=
    Equiv.subtypeEquivProp (by
      funext w
      apply propext
      tauto)
  rw [Fintype.card_congr e, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq_or_eq_of_ne huv]

/-- Third vertices whose displayed triangle belongs to the absorber bank. -/
noncomputable def bankBlockedThirdVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : TripleSystemOn V) {u v : V} (huv : u ≠ v) :
    Finset (ThirdVertex u v) := by
  classical
  exact univ.filter fun w ↦ thirdVertexTriple huv w ∈ B

/-- Third vertices whose displayed triangle uses an absorber edge. -/
noncomputable def absorberEdgeBlockedThirdVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) {u v : V} (huv : u ≠ v) :
    Finset (ThirdVertex u v) := by
  classical
  exact univ.filter fun w ↦
    ¬TriangleAvoidsGraph H (thirdVertexTriple huv w)

@[simp]
lemma mem_bankBlockedThirdVertices_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {B : TripleSystemOn V} {u v : V} {huv : u ≠ v}
    {w : ThirdVertex u v} :
    w ∈ bankBlockedThirdVertices B huv ↔
      thirdVertexTriple huv w ∈ B := by
  classical
  simp [bankBlockedThirdVertices]

@[simp]
lemma mem_absorberEdgeBlockedThirdVertices_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {u v : V} {huv : u ≠ v}
    {w : ThirdVertex u v} :
    w ∈ absorberEdgeBlockedThirdVertices H huv ↔
      ¬TriangleAvoidsGraph H (thirdVertexTriple huv w) := by
  classical
  simp [absorberEdgeBlockedThirdVertices]

/-- Injectivity of the third-vertex parametrization makes the bank loss at
most the total size of the bank. -/
theorem card_bankBlockedThirdVertices_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {B : TripleSystemOn V} {u v : V} (huv : u ≠ v) :
    (bankBlockedThirdVertices B huv).card ≤ B.card := by
  let e : ThirdVertex u v ↪ TripleOn V :=
    ⟨thirdVertexTriple huv, thirdVertexTriple_injective huv⟩
  have hsub : (bankBlockedThirdVertices B huv).map e ⊆ B := by
    intro T hT
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hT
    exact mem_bankBlockedThirdVertices_iff.mp hw
  simpa using card_le_card hsub

/-- When `uv` itself is not an absorber edge, every absorber-edge loss is
an absorber neighbor of one endpoint. -/
lemma absorberEdgeBlockedThirdVertex_mem_neighbor_union
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {u v : V} (huv : u ≠ v)
    (huvH : ¬H.Adj u v) {w : ThirdVertex u v}
    (hw : w ∈ absorberEdgeBlockedThirdVertices H huv) :
    w.1 ∈ H.neighborFinset u ∪ H.neighborFinset v := by
  rw [mem_union, SimpleGraph.mem_neighborFinset,
    SimpleGraph.mem_neighborFinset]
  have hnotAvoid := mem_absorberEdgeBlockedThirdVertices_iff.mp hw
  rw [triangleAvoidsGraph_thirdVertexTriple_iff] at hnotAvoid
  tauto

theorem card_absorberEdgeBlockedThirdVertices_le_degree_add
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {u v : V} (huv : u ≠ v)
    (huvH : ¬H.Adj u v) :
    (absorberEdgeBlockedThirdVertices H huv).card ≤
      H.degree u + H.degree v := by
  let e : ThirdVertex u v ↪ V := Function.Embedding.subtype _
  have hsub : (absorberEdgeBlockedThirdVertices H huv).map e ⊆
      H.neighborFinset u ∪ H.neighborFinset v := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_map.mp hw
    exact absorberEdgeBlockedThirdVertex_mem_neighbor_union huv huvH hz
  calc
    (absorberEdgeBlockedThirdVertices H huv).card ≤
        (H.neighborFinset u ∪ H.neighborFinset v).card := by
      simpa using card_le_card hsub
    _ ≤ (H.neighborFinset u).card + (H.neighborFinset v).card :=
      card_union_le _ _
    _ = H.degree u + H.degree v := by
      rw [SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.card_neighborFinset_eq_degree]

/-- Every missing canonical outside candidate belongs to one of the two
explicit loss classes. -/
lemma outside_candidate_compl_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {B : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) :
    (univ \ candidateThirdVertices (outsideAvailableTriangles H B) huv) ⊆
      bankBlockedThirdVertices B huv ∪
        absorberEdgeBlockedThirdVertices H huv := by
  intro w hw
  have hnotCandidate :
      w ∉ candidateThirdVertices (outsideAvailableTriangles H B) huv :=
    (mem_sdiff.mp hw).2
  rw [mem_union, mem_bankBlockedThirdVertices_iff,
    mem_absorberEdgeBlockedThirdVertices_iff]
  rw [mem_candidateThirdVertices_iff,
    mem_outsideAvailableTriangles_iff] at hnotCandidate
  tauto

/-- Exact initial candidate lower bound.  Its left side is the total number
of possible third vertices, namely `|V|-2`; retaining the subtype cardinal
avoids any truncated-subtraction side conditions. -/
theorem card_thirdVertex_le_candidate_add_absorber_losses
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {B : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) (huvH : ¬H.Adj u v) :
    Fintype.card (ThirdVertex u v) ≤
      (candidateThirdVertices (outsideAvailableTriangles H B) huv).card +
        (H.degree u + H.degree v + B.card) := by
  let C := candidateThirdVertices (outsideAvailableTriangles H B) huv
  let E := absorberEdgeBlockedThirdVertices H huv
  let K := bankBlockedThirdVertices B huv
  have hcover : (univ : Finset (ThirdVertex u v)) ⊆ C ∪ (K ∪ E) := by
    intro w _hw
    by_cases hwC : w ∈ C
    · exact mem_union.mpr (Or.inl hwC)
    · apply mem_union.mpr
      right
      apply outside_candidate_compl_subset huv
      exact mem_sdiff.mpr ⟨mem_univ w, hwC⟩
  have htotal := card_le_card hcover
  have hKE : (K ∪ E).card ≤ B.card + (H.degree u + H.degree v) := by
    have hK := card_bankBlockedThirdVertices_le (B := B) huv
    have hE := card_absorberEdgeBlockedThirdVertices_le_degree_add
      (H := H) huv huvH
    calc
      (K ∪ E).card ≤ K.card + E.card := card_union_le K E
      _ ≤ B.card + (H.degree u + H.degree v) := Nat.add_le_add hK hE
  have hCU := card_union_le C (K ∪ E)
  have hall : Fintype.card (ThirdVertex u v) ≤ C.card + (K ∪ E).card := by
    simpa only [card_univ] using htotal.trans hCU
  calc
    Fintype.card (ThirdVertex u v) ≤ C.card + (K ∪ E).card := hall
    _ ≤ C.card + (B.card + (H.degree u + H.degree v)) :=
      Nat.add_le_add_left hKE C.card
    _ = (candidateThirdVertices (outsideAvailableTriangles H B) huv).card +
        (H.degree u + H.degree v + B.card) := by
      dsimp [C]
      omega

theorem card_sub_two_le_outside_candidate_add_absorber_losses
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {B : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) (huvH : ¬H.Adj u v) :
    Fintype.card V - 2 ≤
      (candidateThirdVertices (outsideAvailableTriangles H B) huv).card +
        (H.degree u + H.degree v + B.card) := by
  rw [← card_thirdVertex huv]
  exact card_thirdVertex_le_candidate_add_absorber_losses huv huvH

end Erdos207
