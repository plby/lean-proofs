/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.GreedyLegality
import ErdosProblems.Erdos551.External.Erdos207.CoverDownMaximality

/-!
# Third-vertex obstruction counts

For an uncovered pair `uv`, every prospective triangle is determined by its
third vertex.  The only two possible obstructions (after ambient filtering)
are an already covered second pair or completion of a forbidden family.
-/

namespace Erdos207

open Finset

/-- Vertices distinct from both endpoints of a fixed ordered pair. -/
abbrev ThirdVertex {V : Type*} (u v : V) := {w : V // w ≠ u ∧ w ≠ v}

/-- The triangle determined by an ordered pair and a third vertex. -/
def thirdVertexTriple {V : Type*} [DecidableEq V]
    {u v : V} (huv : u ≠ v) (w : ThirdVertex u v) : TripleOn V :=
  tripleOfThree u v w.1 huv w.2.1.symm w.2.2.symm

@[simp]
lemma left_mem_thirdVertexTriple
    {V : Type*} [DecidableEq V] {u v : V} (huv : u ≠ v)
    (w : ThirdVertex u v) : u ∈ (thirdVertexTriple huv w).1 := by
  simp [thirdVertexTriple, tripleOfThree]

@[simp]
lemma right_mem_thirdVertexTriple
    {V : Type*} [DecidableEq V] {u v : V} (huv : u ≠ v)
    (w : ThirdVertex u v) : v ∈ (thirdVertexTriple huv w).1 := by
  simp [thirdVertexTriple, tripleOfThree]

/-- Ambient third vertices for the pair `uv`. -/
noncomputable def candidateThirdVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) {u v : V} (huv : u ≠ v) :
    Finset (ThirdVertex u v) := by
  classical
  exact univ.filter fun w ↦ thirdVertexTriple huv w ∈ A

/-- Candidate third vertices blocked by an already covered second pair. -/
noncomputable def edgeBlockedThirdVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (A P : TripleSystemOn V) {u v : V} (huv : u ≠ v) :
    Finset (ThirdVertex u v) := by
  classical
  exact (candidateThirdVertices A huv).filter fun w ↦
    ¬TriangleAvoidsGraph (coveredGraph P) (thirdVertexTriple huv w)

/-- Candidate third vertices blocked by a forbidden configuration. -/
noncomputable def forbiddenBlockedThirdVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A P : TripleSystemOn V)
    {u v : V} (huv : u ≠ v) : Finset (ThirdVertex u v) := by
  classical
  exact (candidateThirdVertices A huv).filter fun w ↦
    CompletesForbidden F P (thirdVertexTriple huv w)

/-- Third vertices giving genuinely legal extensions. -/
noncomputable def legalThirdVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A P : TripleSystemOn V)
    {u v : V} (huv : u ≠ v) : Finset (ThirdVertex u v) := by
  classical
  exact (candidateThirdVertices A huv).filter fun w ↦
    IsLegalExtension F P (thirdVertexTriple huv w)

lemma mem_candidateThirdVertices_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : TripleSystemOn V} {u v : V} {huv : u ≠ v}
    {w : ThirdVertex u v} :
    w ∈ candidateThirdVertices A huv ↔ thirdVertexTriple huv w ∈ A := by
  classical
  simp [candidateThirdVertices]

lemma mem_edgeBlockedThirdVertices_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P : TripleSystemOn V} {u v : V} {huv : u ≠ v}
    {w : ThirdVertex u v} :
    w ∈ edgeBlockedThirdVertices A P huv ↔
      thirdVertexTriple huv w ∈ A ∧
        ¬TriangleAvoidsGraph (coveredGraph P) (thirdVertexTriple huv w) := by
  classical
  simp [edgeBlockedThirdVertices, mem_candidateThirdVertices_iff]

lemma mem_forbiddenBlockedThirdVertices_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {u v : V} {huv : u ≠ v} {w : ThirdVertex u v} :
    w ∈ forbiddenBlockedThirdVertices F A P huv ↔
      thirdVertexTriple huv w ∈ A ∧
        CompletesForbidden F P (thirdVertexTriple huv w) := by
  classical
  simp [forbiddenBlockedThirdVertices, mem_candidateThirdVertices_iff]

lemma mem_legalThirdVertices_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {u v : V} {huv : u ≠ v} {w : ThirdVertex u v} :
    w ∈ legalThirdVertices F A P huv ↔
      thirdVertexTriple huv w ∈ A ∧
        IsLegalExtension F P (thirdVertexTriple huv w) := by
  classical
  simp [legalThirdVertices, mem_candidateThirdVertices_iff]

/-- A strict surplus of candidates over the union of the two obstruction
sets yields a legal extension through the uncovered pair. -/
theorem legalThirdVertices_nonempty_of_blocked_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    (hpacking : IsPackingOn P) (havoid : AvoidsForbidden P F)
    {u v : V} (huvLeave : (leaveGraph P).Adj u v)
    (hcount :
      (edgeBlockedThirdVertices A P huvLeave.ne ∪
        forbiddenBlockedThirdVertices F A P huvLeave.ne).card <
          (candidateThirdVertices A huvLeave.ne).card) :
    (legalThirdVertices F A P huvLeave.ne).Nonempty := by
  have hex : ∃ w ∈ candidateThirdVertices A huvLeave.ne,
      w ∉ edgeBlockedThirdVertices A P huvLeave.ne ∪
        forbiddenBlockedThirdVertices F A P huvLeave.ne := by
    by_contra hnone
    push Not at hnone
    have hsub : candidateThirdVertices A huvLeave.ne ⊆
        edgeBlockedThirdVertices A P huvLeave.ne ∪
          forbiddenBlockedThirdVertices F A P huvLeave.ne := by
      intro w hw
      exact hnone w hw
    have := card_le_card hsub
    omega
  obtain ⟨w, hwA, hwfree⟩ := hex
  have hwEdge : w ∉ edgeBlockedThirdVertices A P huvLeave.ne := by
    intro hw
    exact hwfree (mem_union.mpr (Or.inl hw))
  have hwForbidden :
      w ∉ forbiddenBlockedThirdVertices F A P huvLeave.ne := by
    intro hw
    exact hwfree (mem_union.mpr (Or.inr hw))
  have hTA : thirdVertexTriple huvLeave.ne w ∈ A :=
    mem_candidateThirdVertices_iff.mp hwA
  have hTnotP : thirdVertexTriple huvLeave.ne w ∉ P := by
    intro hTP
    have hcovered : (coveredGraph P).Adj u v :=
      coveredGraph_adj.mpr ⟨thirdVertexTriple huvLeave.ne w, hTP,
        left_mem_thirdVertexTriple _ _, right_mem_thirdVertexTriple _ _,
        huvLeave.ne⟩
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
  refine ⟨w, mem_legalThirdVertices_iff.mpr ⟨hTA, ?_⟩⟩
  exact (isLegalExtension_iff hpacking havoid _).mpr
    ⟨hTnotP, havoids, hnotCompletes⟩

/-- Surplus obstruction estimates for every outside leave-edge supply the
maximality extension condition. -/
theorem outsideLeaveEdgesLegallyExtendable_of_blocked_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {H : SimpleGraph V} {X : Finset V}
    (hpacking : IsPackingOn P) (havoid : AvoidsForbidden P F)
    (hcount : ∀ ⦃u v : V⦄
      (huv : (graphDifference (leaveGraph P) H).Adj u v),
      (u ∉ X ∨ v ∉ X) →
      (edgeBlockedThirdVertices A P huv.1.ne ∪
        forbiddenBlockedThirdVertices F A P huv.1.ne).card <
          (candidateThirdVertices A huv.1.ne).card) :
    OutsideLeaveEdgesLegallyExtendable F A P H X := by
  intro u v huv houtside
  have hne : u ≠ v := huv.1.ne
  have hsurplus := hcount huv houtside
  have hlegal := legalThirdVertices_nonempty_of_blocked_lt
    hpacking havoid huv.1 hsurplus
  obtain ⟨w, hw⟩ := hlegal
  have hw' := mem_legalThirdVertices_iff.mp hw
  exact ⟨thirdVertexTriple hne w, hw'.1,
    left_mem_thirdVertexTriple hne w,
    right_mem_thirdVertexTriple hne w, hw'.2⟩

end Erdos207
