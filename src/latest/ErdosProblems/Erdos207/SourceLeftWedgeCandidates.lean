/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLeftObstructionCount
import ErdosProblems.Erdos207.InternalEdgeTerminalRootSuccess

/-! # An exact left-moment count for pair-safe active reserve candidates -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem sourceQuasiSpokes_pair_eq_reserveWedgeBlock
    {V : Type*} [DecidableEq V] (u v w : V) :
    sourceQuasiSpokes (s(u,v)).toFinset w = reserveWedgeBlock u v w := by
  simp only [sourceQuasiSpokes, Sym2.toFinset_mk_eq, image_insert, image_singleton, reserveWedgeBlock]
  rw [show s(w,u) = s(u,w) from Sym2.eq_swap, show s(w,v) = s(v,w) from Sym2.eq_swap]

theorem mem_sourceLeftObstructedVertices_of_pair_safe_wedge
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (Γ : SimpleGraph V)
    (I D : TripleSystemOn V) (reserve : Finset (Sym2 V)) (S : Finset V)
    {u v : V} (huv : u ≠ v) (w : ThirdVertex u v) (hw : w.1 ∈ S)
    (hlevel : W.level (thirdVertexTriple huv w) = Fin.last ell)
    (hpair : TriangleAvoidsGraph (coveredGraph (I ∪ D)) (thirdVertexTriple huv w))
    (hcomplete : CompletesForbidden F (I ∪ D) (thirdVertexTriple huv w))
    (hinitial : ¬ CompletesForbidden F I (thirdVertexTriple huv w))
    (hreserve : reserveWedgeBlock u v w.1 ⊆ reserve) (hRG : reserve ⊆ graphEdges Γ) :
    w.1 ∈ sourceLeftObstructedVertices W F s(u,v) S Γ I D reserve := by
  have hspokes : sourceQuasiSpokes (s(u,v)).toFinset w.1 ⊆ reserve := by
    rwa [sourceQuasiSpokes_pair_eq_reserveWedgeBlock]
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨hw, ?_, hspokes.trans hRG, ?_, thirdVertexTriple huv w, ?_, ?_, hlevel,
    hcomplete, hinitial⟩, hspokes⟩
  · simpa only [Sym2.toFinset_mk_eq, mem_insert, mem_singleton, not_or] using w.2
  · intro a ha
    rw [sourceQuasiSpokes_pair_eq_reserveWedgeBlock] at ha
    rcases mem_insert.mp ha with rfl | ha
    · exact hpair u (left_mem_thirdVertexTriple _ _) w.1 (third_mem_thirdVertexTriple _ _) w.2.1.symm
    · have heq := mem_singleton.mp ha
      rw [heq]
      exact hpair v (right_mem_thirdVertexTriple _ _) w.1 (third_mem_thirdVertexTriple _ _) w.2.2.symm
  · ext x
    simp only [thirdVertexTriple, tripleOfThree, Sym2.toFinset_mk_eq, mem_insert, mem_singleton]
    tauto
  · exact mk_mem_tripleEdgeFinset_iff.mpr
      ⟨left_mem_thirdVertexTriple _ _, right_mem_thirdVertexTriple _ _, huv⟩

theorem card_activeReserveWedge_le_legal_add_pair_add_left
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (G Γ : SimpleGraph V) (U S : Finset V)
    (I D A : TripleSystemOn V) {u v : V} (huv : u ≠ v) (bits : Sym2 V → Bool)
    (hpacking : IsPackingOn (I ∪ D)) (havoid : AvoidsForbidden (I ∪ D) F)
    (huncovered : ¬ (coveredGraph (I ∪ D)).Adj u v)
    (hu : u ∉ U) (hv : v ∉ U) (hS : S ⊆ U) (hbase : G ≤ Γ)
    (hA : ∀ w : ThirdVertex u v, w.1 ∈ S → thirdVertexTriple huv w ∈ A)
    (hlevel : ∀ T ∈ A, W.level T = Fin.last ell)
    (hinitial : ∀ T ∈ A, ¬ CompletesForbidden F I T) :
    (activeReserveWedgeVertices G U S u v bits).card ≤
      (activeReserveLegalThirdVertices F G U S bits (I ∪ D) u v huv).card +
      (edgeBlockedThirdVertices A (I ∪ D) huv).card +
      (sourceLeftObstructedVertices W F s(u,v) U Γ I D (reserveEdges G U bits)).card := by
  let Legal := activeReserveLegalThirdVertices F G U S bits (I ∪ D) u v huv
  let Pair := edgeBlockedThirdVertices A (I ∪ D) huv
  let Left := sourceLeftObstructedVertices W F s(u,v) U Γ I D (reserveEdges G U bits)
  have hRG : reserveEdges G U bits ⊆ graphEdges Γ := by
    intro a ha
    apply mem_graphEdges_iff.mpr
    exact (SimpleGraph.edgeSet_subset_edgeSet.mpr hbase)
      (mem_crossingEdges_iff.mp (reserveEdges_subset_crossingEdges G U bits ha)).1
  have hcover : activeReserveWedgeVertices G U S u v bits ⊆
      Legal.image Subtype.val ∪ (Pair.image Subtype.val ∪ Left) := by
    intro x hx
    have hd := mem_activeReserveWedgeVertices_iff.mp hx
    let w : ThirdVertex u v := ⟨x, fun h ↦ hu (h ▸ hS hd.1), fun h ↦ hv (h ▸ hS hd.1)⟩
    have hTA := hA w hd.1
    by_cases hlegal : IsLegalExtension F (I ∪ D) (thirdVertexTriple huv w)
    · exact mem_union_left _ (mem_image.mpr ⟨w,
        mem_activeReserveLegalThirdVertices_iff.mpr ⟨hx, hlegal⟩, rfl⟩)
    by_cases hpair : TriangleAvoidsGraph (coveredGraph (I ∪ D)) (thirdVertexTriple huv w)
    · have hnot : thirdVertexTriple huv w ∉ I ∪ D := by
        intro hT
        exact huncovered (coveredGraph_adj.mpr ⟨thirdVertexTriple huv w, hT,
          left_mem_thirdVertexTriple _ _, right_mem_thirdVertexTriple _ _, huv⟩)
      have hcomplete : CompletesForbidden F (I ∪ D) (thirdVertexTriple huv w) := by
        by_contra hc
        exact hlegal ((isLegalExtension_iff hpacking havoid _).mpr ⟨hnot, hpair, hc⟩)
      exact mem_union_right _ (mem_union_right _
        (mem_sourceLeftObstructedVertices_of_pair_safe_wedge W F Γ I D (reserveEdges G U bits) U
          huv w (hS hd.1) (hlevel _ hTA) hpair hcomplete (hinitial _ hTA) hd.2 hRG))
    · exact mem_union_right _ (mem_union_left _ (mem_image.mpr ⟨w,
        mem_edgeBlockedThirdVertices_iff.mpr ⟨hTA, hpair⟩, rfl⟩))
  have hc := card_le_card hcover
  have hu' := card_union_le (Legal.image Subtype.val) (Pair.image Subtype.val ∪ Left)
  have hv' := card_union_le (Pair.image Subtype.val) Left
  have hL : (Legal.image Subtype.val).card ≤ Legal.card := card_image_le
  have hP : (Pair.image Subtype.val).card ≤ Pair.card := card_image_le
  change _ ≤ Legal.card + Pair.card + Left.card
  omega

end

end Erdos207
