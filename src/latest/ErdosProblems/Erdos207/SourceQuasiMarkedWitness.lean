/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiJointInclusion

/-! # Actual forbidden completions yield realized proper quasi-moment codes -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourceQuasiWitnessMarking
    {V : Type*} [DecidableEq V] (u : V) (T : TripleOn V) (I E : TripleSystemOn V) :
    SourceQuasiMarking V := (u, T, (E.erase T) ∩ I, (E.erase T) \ I)

theorem sourceQuasiWitnessMarking_system
    {V : Type*} [DecidableEq V] (u : V) (T : TripleOn V) (I E : TripleSystemOn V)
    (hT : T ∈ E) : (sourceQuasiWitnessMarking u T I E).system = E := by
  change insert T ((E.erase T) ∩ I ∪ (E.erase T) \ I) = E
  rw [union_comm, sdiff_union_inter, insert_erase hT]

theorem isSourceQuasiMarking_witness
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    {u : V} {T : TripleOn V} {I E : TripleSystemOn V}
    (hu : u ∈ S) (huB : u ∉ B) (hvertices : T.1 = insert u e.toFinset)
    (he : e ∈ tripleEdgeFinset T) (hlevel : W.level T = Fin.last ell)
    (hE : E ∈ F) (hT : T ∈ E) (hnot : ¬ E.erase T ⊆ I) :
    IsSourceQuasiMarking W F e S B (sourceQuasiWitnessMarking u T I E) := by
  refine ⟨hu, huB, hvertices, he, hlevel, ?_, ?_, ?_, ?_⟩
  · change T ∉ (E.erase T ∩ I) ∪ (E.erase T \ I)
    rw [union_comm, sdiff_union_inter]
    exact notMem_erase _ _
  · apply disjoint_left.mpr
    intro U hI hD
    exact (mem_sdiff.mp hD).2 (mem_inter.mp hI).2
  · obtain ⟨D, hD, hDI⟩ := not_subset.mp hnot
    exact ⟨D, mem_sdiff.mpr ⟨hD, hDI⟩⟩
  · rwa [sourceQuasiWitnessMarking_system u T I E hT]

theorem sourceQuasiWitnessMarking_coordinates_realized
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (T : TripleOn V) (I D E : TripleSystemOn V) (B : Finset V)
    (hcover : E.erase T ⊆ I ∪ D)
    (hG : sourceQuasiSpokes B u ⊆ graphEdges G)
    (hres : ∀ e ∈ sourceQuasiSpokes B u, e ∉ (coveredGraph (I ∪ D)).edgeSet) :
    (sourceQuasiWitnessMarking u T I E).coordinates B ⊆ sourceQuasiRealizedCoordinates G I D := by
  apply disjSum_mono
  · apply disjSum_mono inter_subset_right
    intro U hU
    exact (mem_union.mp (hcover (mem_sdiff.mp hU).1)).resolve_left (mem_sdiff.mp hU).2
  · intro e he
    exact mem_filter.mpr ⟨hG he, hres e he⟩

theorem exists_sourceQuasi_marked_witness
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    {u : V} {T : TripleOn V} {I D : TripleSystemOn V}
    (G : SimpleGraph V) (hu : u ∈ S) (huB : u ∉ B)
    (hvertices : T.1 = insert u e.toFinset) (he : e ∈ tripleEdgeFinset T)
    (hlevel : W.level T = Fin.last ell)
    (hcomplete : CompletesForbidden F (I ∪ D) T) (hinitial : ¬ CompletesForbidden F I T)
    (hG : sourceQuasiSpokes B u ⊆ graphEdges G)
    (hres : ∀ a ∈ sourceQuasiSpokes B u, a ∉ (coveredGraph (I ∪ D)).edgeSet) :
    ∃ x ∈ sourceQuasiMarkings W F e S B, x.vertex = u ∧
      x.coordinates B ⊆ sourceQuasiRealizedCoordinates G I D := by
  obtain ⟨E, hE, hTE, hcover⟩ := hcomplete
  have hnot : ¬ E.erase T ⊆ I := fun h ↦ hinitial ⟨E, hE, hTE, h⟩
  refine ⟨sourceQuasiWitnessMarking u T I E,
    mem_sourceQuasiMarkings_iff.mpr (isSourceQuasiMarking_witness hu huB hvertices he hlevel hE hTE hnot),
    rfl, sourceQuasiWitnessMarking_coordinates_realized G u T I D E B hcover hG hres⟩

end

end Erdos207
