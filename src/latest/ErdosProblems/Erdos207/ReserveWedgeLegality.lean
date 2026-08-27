/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationReserveCandidates

/-!
# Turning reserve-wedge surplus into a legal triangle

The reserve event supplies ordinary vertices, whereas the constrained-greedy
obstruction lemmas use the subtype of vertices different from the displayed
edge endpoints.  This file gives the exact finite injection between those
sets and proves that a strict reserve surplus over all edge and forbidden
blockers contains a legal triangle.
-/

namespace Erdos207

open Finset

noncomputable section

/-- A strict surplus inside a prescribed reserve-supported candidate set is
already enough to find a legal extension through an uncovered edge. -/
theorem exists_legal_activeReserveWedge_of_blocked_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {G : SimpleGraph V} {U S : Finset V} {u v : V}
    (hpacking : IsPackingOn P) (havoid : AvoidsForbidden P F)
    (huvLeave : (leaveGraph P).Adj u v)
    (hu : u ∉ U) (hv : v ∉ U) (hSU : S ⊆ U)
    (ω : Sym2 V → Bool)
    (hA : ∀ w, ∀ hwS : w ∈ S,
      let w' : ThirdVertex u v :=
        ⟨w, fun h ↦ hu (h ▸ hSU hwS),
          fun h ↦ hv (h ▸ hSU hwS)⟩
      thirdVertexTriple huvLeave.ne w' ∈ A)
    (hcount :
      (edgeBlockedThirdVertices A P huvLeave.ne ∪
        forbiddenBlockedThirdVertices F A P huvLeave.ne).card <
      (activeReserveWedgeVertices G U S u v ω).card) :
    ∃ w : ThirdVertex u v,
      w.1 ∈ activeReserveWedgeVertices G U S u v ω ∧
      thirdVertexTriple huvLeave.ne w ∈ A ∧
      IsLegalExtension F P (thirdVertexTriple huvLeave.ne w) := by
  let C := activeReserveWedgeVertices G U S u v ω
  let e : {w // w ∈ C} ↪ ThirdVertex u v :=
    { toFun := fun w ↦ ⟨w.1,
        fun h ↦ hu (h ▸ hSU (mem_activeReserveWedgeVertices_iff.mp w.2).1),
        fun h ↦ hv (h ▸ hSU (mem_activeReserveWedgeVertices_iff.mp w.2).1)⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : ThirdVertex u v ↦ z.1) hxy }
  let C' : Finset (ThirdVertex u v) := C.attach.map e
  have hcardC' : C'.card = C.card := by
    simp [C']
  have hCsub : C' ⊆ candidateThirdVertices A huvLeave.ne := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hw
    rw [mem_candidateThirdVertices_iff]
    have hxS := (mem_activeReserveWedgeVertices_iff.mp x.2).1
    let z : ThirdVertex u v :=
      ⟨x.1, fun h ↦ hu (h ▸ hSU hxS), fun h ↦ hv (h ▸ hSU hxS)⟩
    have heq : e x = z := by
      apply Subtype.ext
      rfl
    rw [heq]
    exact hA x.1 hxS
  have hex : ∃ w ∈ C',
      w ∉ edgeBlockedThirdVertices A P huvLeave.ne ∪
        forbiddenBlockedThirdVertices F A P huvLeave.ne := by
    by_contra hnone
    push Not at hnone
    have hsub : C' ⊆
        edgeBlockedThirdVertices A P huvLeave.ne ∪
          forbiddenBlockedThirdVertices F A P huvLeave.ne := by
      intro w hw
      exact hnone w hw
    have hle := card_le_card hsub
    rw [hcardC'] at hle
    exact (not_lt_of_ge hle) hcount
  obtain ⟨w, hwC, hwfree⟩ := hex
  have hwCandidate : w ∈ candidateThirdVertices A huvLeave.ne := hCsub hwC
  have hTA : thirdVertexTriple huvLeave.ne w ∈ A :=
    mem_candidateThirdVertices_iff.mp hwCandidate
  have hwEdge : w ∉ edgeBlockedThirdVertices A P huvLeave.ne := by
    intro hw
    exact hwfree (mem_union.mpr (Or.inl hw))
  have hwForbidden :
      w ∉ forbiddenBlockedThirdVertices F A P huvLeave.ne := by
    intro hw
    exact hwfree (mem_union.mpr (Or.inr hw))
  have hTnotP : thirdVertexTriple huvLeave.ne w ∉ P := by
    intro hTP
    exact huvLeave.2 ⟨thirdVertexTriple huvLeave.ne w, hTP,
      left_mem_thirdVertexTriple _ _, right_mem_thirdVertexTriple _ _,
      huvLeave.ne⟩
  have havoids : TriangleAvoidsGraph (coveredGraph P)
      (thirdVertexTriple huvLeave.ne w) := by
    by_contra hnot
    exact hwEdge (mem_edgeBlockedThirdVertices_iff.mpr ⟨hTA, hnot⟩)
  have hnotCompletes :
      ¬CompletesForbidden F P (thirdVertexTriple huvLeave.ne w) := by
    intro hcomplete
    exact hwForbidden
      (mem_forbiddenBlockedThirdVertices_iff.mpr ⟨hTA, hcomplete⟩)
  have hlegal : IsLegalExtension F P (thirdVertexTriple huvLeave.ne w) :=
    (isLegalExtension_iff hpacking havoid _).mpr
      ⟨hTnotP, havoids, hnotCompletes⟩
  have hwActive : w.1 ∈ C := by
    obtain ⟨x, _hx, heqx⟩ := mem_map.mp hwC
    have hval : x.1 = w.1 := congrArg Subtype.val heqx
    exact hval ▸ x.2
  exact ⟨w, hwActive, hTA, hlegal⟩

/-- The active reserve supply coming from a one-edge iteration extension set
consists of ambient available triangles. -/
lemma activeReserveWedge_iterationExtension_thirdVertexTriple_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A : TripleSystemOn V} {U : Finset V}
    {u v w : V} (huv : u ≠ v) (hu : u ∉ U) (hv : v ∉ U)
    (ω : Sym2 V → Bool)
    (hw : w ∈ activeReserveWedgeVertices G U
      (iterationExtensionVertices A (SimpleGraph.edge u v) U) u v ω) :
    let w' : ThirdVertex u v :=
      ⟨w, fun h ↦ hu (h ▸ iterationExtensionVertices_subset A
        (SimpleGraph.edge u v) U
          (mem_activeReserveWedgeVertices_iff.mp hw).1),
        fun h ↦ hv (h ▸ iterationExtensionVertices_subset A
          (SimpleGraph.edge u v) U
            (mem_activeReserveWedgeVertices_iff.mp hw).1)⟩
    thirdVertexTriple huv w' ∈ A := by
  exact iterationExtensionVertices_edge_thirdVertexTriple_mem huv hu hv
    (mem_activeReserveWedgeVertices_iff.mp hw).1

end

end Erdos207
