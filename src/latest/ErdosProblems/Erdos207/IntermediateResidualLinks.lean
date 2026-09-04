/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousMasterLawUpdate
import ErdosProblems.Erdos207.ReserveSupportedResidualLink
import ErdosProblems.Erdos207.DynamicResidualStructure

/-!
# Canonical residual links after the internal-edge stage

Parity of the current graph and packing of the preliminary/internal family
give a canonical balanced residual bipartition at every outer center.  The
internal cover puts both sides inside the next vortex set, while coverage of
all nonreserve crossing edges makes every spoke a reserve edge.  This file
packages exactly the structural input expected by the reserve-aware
simultaneous-link update.
-/

namespace Erdos207

open Finset

noncomputable section

/-- The inclusion of vertices outside a finite set into the ambient type. -/
def outsideVertexEmbedding
    {V : Type*} [DecidableEq V] (U : Finset V) : {x : V // x ∉ U} ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- Canonical balanced residual links at all outer centers. -/
def canonicalResidualLinks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (R : TripleSystemOn V)
    (heven : ∀ v, Even (G.degree v))
    (htri : ConsistsOfTriangles G R)
    (hpacking : IsPackingOn R) :
    {x : V // x ∉ U} -> BipartiteLink V := fun o =>
  residualBipartiteLink G R o.1
    (residualNeighbors_even heven htri hpacking o.1)

theorem canonicalResidualLinks_isResidualBipartition
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {R : TripleSystemOn V}
    (heven : ∀ v, Even (G.degree v))
    (htri : ConsistsOfTriangles G R)
    (hpacking : IsPackingOn R)
    (o : {x : V // x ∉ U}) :
    IsResidualBipartition G R o.1
      (canonicalResidualLinks G U R heven htri hpacking o) := by
  let hres : Even (residualNeighbors G R o.1).card :=
    residualNeighbors_even heven htri hpacking o.1
  exact ⟨residualBipartiteLink_center G R o.1 hres,
    residualBipartiteLink_union G R o.1 hres,
    residualBipartiteLink_balanced G R o.1 hres⟩

/-- All structural and reserve-support facts needed for the simultaneous
link kernel, obtained from the two coverage certificates of the preceding
stage. -/
theorem exists_residualLinks_masterData
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {U : Finset V} {reserve : Finset (Sym2 V)}
    {F : ForbiddenFamilyOn V} {A I D R : TripleSystemOn V}
    (heven : ∀ v, Even ((neighborsIn G univ v).card))
    (htri : ConsistsOfTriangles G R)
    (hpacking : IsPackingOn R)
    (hselected : R ⊆ A)
    (hdisjoint : Disjoint I (D ∪ R))
    (hinternal : ∀ u v : V, G.Adj u v -> u ∉ U -> v ∉ U ->
      (coveredGraph R).Adj u v)
    (hcrossing : CoversCrossingOutsideReserve G U reserve R) :
    let center := outsideVertexEmbedding U
    ∃ K : {x : V // x ∉ U} -> BipartiteLink V,
      IsIntermediateLinkState G U A I D R K ∧
      (∀ o, (K o).center = center o) ∧
      (∀ o, center o ∉ U) ∧
      (∀ o, (K o).left ⊆ U) ∧
      (∀ o, (K o).right ⊆ U) ∧
      (∀ o, (K o).SpokesIn reserve) := by
  dsimp only
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  have hevenDegree : ∀ v, Even (G.degree v) := by
    intro v
    have hneighbors : neighborsIn G univ v = G.neighborFinset v := by
      ext x
      simp only [mem_neighborsIn_iff, mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hneighbors]
    exact heven v
  let K := canonicalResidualLinks G U R hevenDegree htri hpacking
  have hK : ∀ o, IsResidualBipartition G R o.1 (K o) :=
    fun o => canonicalResidualLinks_isResidualBipartition
      hevenDegree htri hpacking o
  have hinner : ∀ o : {x : V // x ∉ U},
      residualNeighbors G R o.1 ⊆ U := by
    intro o
    exact residualNeighbors_subset_of_internal_cover
      (D := R) (P := R) Subset.rfl hinternal o.2
  refine ⟨K, ⟨hK, hselected, hdisjoint⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro o
    exact (hK o).1
  · intro o
    exact o.2
  · intro o x hx
    apply hinner o
    rw [← (hK o).2.1]
    exact mem_union_left (K o).right hx
  · intro o x hx
    apply hinner o
    rw [← (hK o).2.1]
    exact mem_union_right (K o).left hx
  · intro o
    exact (hK o).spokesIn_of_coversOutsideReserve o.2 (hinner o)
      hcrossing

end

end Erdos207
