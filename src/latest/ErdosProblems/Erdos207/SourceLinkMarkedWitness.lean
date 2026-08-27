/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkRealizedCoordinates

/-! # Canonical marked witnesses for sampled forbidden triangles -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourceLinkWitnessMarking
    {V : Type*} [DecidableEq V] (I D E : TripleSystemOn V) (T : TripleOn V) : SourceLinkMarking V :=
  (T, E ∩ I, (E \ I) ∩ D, E \ (I ∪ D))

theorem sourceLinkWitnessMarking_system
    {V : Type*} [DecidableEq V] (I D E : TripleSystemOn V) (T : TripleOn V) :
    (sourceLinkWitnessMarking I D E T).system = E := by
  ext S
  simp only [SourceLinkMarking.system, sourceLinkWitnessMarking, SourceLinkMarking.initial,
    SourceLinkMarking.later, SourceLinkMarking.candidate, mem_union, mem_inter, mem_sdiff]
  tauto

theorem sourceLinkWitnessMarking_candidate_subset
    {V : Type*} [DecidableEq V] {I D E Q : TripleSystemOn V} (T : TripleOn V)
    (hcover : E ⊆ I ∪ D ∪ Q) : (sourceLinkWitnessMarking I D E T).candidate ⊆ Q := by
  intro S hS
  have hm : S ∈ E ∧ S ∉ I ∪ D := mem_sdiff.mp hS
  exact (mem_union.mp (hcover hm.1)).resolve_left hm.2

theorem isSourceLinkMarking_witness
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V}
    {A I D E Q : TripleSystemOn V} {T : TripleOn V}
    (hE : E ∈ F) (hT : T ∈ E) (hTQ : T ∈ Q) (hTold : T ∉ I ∪ D)
    (hcover : E ⊆ I ∪ D ∪ Q) (hQA : Q ⊆ A)
    (hlevel : ∀ S ∈ Q, W.level S = Fin.last ell) (he : e ∈ tripleEdgeFinset T)
    (hother : ∃ S ∈ E.erase T, W.level S = Fin.last ell)
    (hnotInitial : ¬ E.erase T ⊆ I) :
    IsSourceLinkMarking W F e A (sourceLinkWitnessMarking I D E T) := by
  refine ⟨?_, ?_, ?_, ?_, he, hlevel T hTQ, (sourceLinkWitnessMarking_candidate_subset T hcover).trans hQA, ?_⟩
  · rw [sourceLinkWitnessMarking_system]
    exact mem_filter.mpr ⟨hE,
      ⟨T, mem_filter.mpr ⟨mem_univ _, he, hlevel T hTQ⟩, hT, hother⟩, empty_subset _⟩
  · apply disjoint_left.mpr
    intro S hSI hSD
    exact (mem_sdiff.mp (mem_inter.mp hSD).1).2 (mem_inter.mp hSI).2
  · apply disjoint_left.mpr
    intro S hOld hNew
    have hnot := (mem_sdiff.mp hNew).2
    rcases mem_union.mp hOld with hSI | hSD
    · exact hnot (mem_union_left _ (mem_inter.mp hSI).2)
    · exact hnot (mem_union_right _ (mem_inter.mp hSD).2)
  · exact mem_sdiff.mpr ⟨hT, hTold⟩
  · obtain ⟨S, hS, hSI⟩ := not_subset.mp hnotInitial
    have hm := mem_erase.mp hS
    by_cases hSD : S ∈ D
    · exact ⟨S, mem_union_left _ (mem_inter.mpr ⟨mem_sdiff.mpr ⟨hm.2, hSI⟩, hSD⟩)⟩
    · exact ⟨S, mem_union_right _ (mem_erase.mpr ⟨hm.1, mem_sdiff.mpr
        ⟨hm.2, fun hOld ↦ (mem_union.mp hOld).elim hSI hSD⟩⟩)⟩

theorem sourceLinkWitnessMarking_coordinates_realized
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (I D E Q : TripleSystemOn V)
    (T : TripleOn V) (e : Sym2 V) (reserve : Finset (Sym2 V))
    (hcover : E ⊆ I ∪ D ∪ Q)
    (hedges : Q.biUnion tripleEdgeFinset ⊆ sourceLinkRetainedEdges G U I D reserve) :
    (sourceLinkWitnessMarking I D E T).coordinates e ⊆
      sourceLinkRealizedCoordinates G U I D Q reserve := by
  apply disjSum_mono
  · apply disjSum_mono
    · exact inter_subset_right
    · exact disjSum_mono inter_subset_right (sourceLinkWitnessMarking_candidate_subset T hcover)
  · intro f hf
    obtain ⟨S, hS, hfS⟩ := mem_biUnion.mp (mem_erase.mp hf).2
    exact hedges (mem_biUnion.mpr ⟨S, sourceLinkWitnessMarking_candidate_subset T hcover hS, hfS⟩)

theorem exists_sourceLink_marked_witness
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V}
    {A I D E Q : TripleSystemOn V} {T : TripleOn V}
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (hE : E ∈ F) (hT : T ∈ E) (hTQ : T ∈ Q) (hTold : T ∉ I ∪ D)
    (hcover : E ⊆ I ∪ D ∪ Q) (hQA : Q ⊆ A)
    (hlevel : ∀ S ∈ Q, W.level S = Fin.last ell) (he : e ∈ tripleEdgeFinset T)
    (hother : ∃ S ∈ E.erase T, W.level S = Fin.last ell)
    (hnotInitial : ¬ E.erase T ⊆ I)
    (hedges : Q.biUnion tripleEdgeFinset ⊆ sourceLinkRetainedEdges G U I D reserve) :
    ∃ x ∈ sourceLinkMarkings W F e A, x.root = T ∧ x.system = E ∧
      x.coordinates e ⊆ sourceLinkRealizedCoordinates G U I D Q reserve := by
  refine ⟨sourceLinkWitnessMarking I D E T, ?_, rfl, sourceLinkWitnessMarking_system I D E T,
    sourceLinkWitnessMarking_coordinates_realized G U I D E Q T e reserve hcover hedges⟩
  exact mem_filter.mpr ⟨mem_univ _, isSourceLinkMarking_witness hE hT hTQ hTold hcover hQA hlevel he hother hnotInitial⟩

theorem sourceLinkWitness_historical_safety
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V}
    {I D historical E Q : TripleSystemOn V} {T : TripleOn V}
    (hE : E ∈ F) (hT : T ∈ E) (hcover : E ⊆ I ∪ D ∪ Q)
    (hsafe : ¬ CompletesForbidden F (I ∪ historical) T)
    (hnew : ∀ S ∈ D \ historical, W.level S = Fin.last ell)
    (hQ : ∀ S ∈ Q, W.level S = Fin.last ell) :
    (∃ S ∈ E.erase T, W.level S = Fin.last ell) ∧ ¬ E.erase T ⊆ I := by
  have hnot : ¬ E.erase T ⊆ I ∪ historical := fun hs ↦ hsafe ⟨E, hE, hT, hs⟩
  constructor
  · obtain ⟨S, hS, hSnot⟩ := not_subset.mp hnot
    refine ⟨S, hS, ?_⟩
    rcases mem_union.mp (hcover (mem_erase.mp hS).2) with hOld | hNew
    · rcases mem_union.mp hOld with hSI | hSD
      · exact (hSnot (mem_union_left _ hSI)).elim
      · exact hnew S (mem_sdiff.mpr ⟨hSD, fun hSH ↦ hSnot (mem_union_right _ hSH)⟩)
    · exact hQ S hNew
  · exact fun hs ↦ hnot (hs.trans subset_union_left)

theorem sourceLinkRetainedEdges_root_not_old
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {I D Q : TripleSystemOn V}
    {reserve : Finset (Sym2 V)} {T : TripleOn V} {e : Sym2 V}
    (hT : T ∈ Q) (he : e ∈ tripleEdgeFinset T)
    (hedges : Q.biUnion tripleEdgeFinset ⊆ sourceLinkRetainedEdges G U I D reserve) : T ∉ I ∪ D := by
  intro hOld
  have hretained := mem_filter.mp (hedges (mem_biUnion.mpr ⟨T, hT, he⟩))
  apply hretained.2.1
  rw [coveredGraph_edgeSet_eq_biUnion]
  exact mem_biUnion.mpr ⟨T, hOld, he⟩

theorem exists_sourceLink_marked_witness_of_historical_safe
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V}
    {A I D historical E Q : TripleSystemOn V} {T : TripleOn V}
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (hE : E ∈ F) (hT : T ∈ E) (hTQ : T ∈ Q)
    (hcover : E ⊆ I ∪ D ∪ Q) (hQA : Q ⊆ A)
    (hlevel : ∀ S ∈ Q, W.level S = Fin.last ell) (he : e ∈ tripleEdgeFinset T)
    (hsafe : ¬ CompletesForbidden F (I ∪ historical) T)
    (hnew : ∀ S ∈ D \ historical, W.level S = Fin.last ell)
    (hedges : Q.biUnion tripleEdgeFinset ⊆ sourceLinkRetainedEdges G U I D reserve) :
    ∃ x ∈ sourceLinkMarkings W F e A, x.root = T ∧ x.system = E ∧
      x.coordinates e ⊆ sourceLinkRealizedCoordinates G U I D Q reserve := by
  have hgood := sourceLinkWitness_historical_safety hE hT hcover hsafe hnew hlevel
  exact exists_sourceLink_marked_witness G U reserve hE hT hTQ
    (sourceLinkRetainedEdges_root_not_old hTQ he hedges) hcover hQA hlevel he hgood.1 hgood.2 hedges

end

end Erdos207
