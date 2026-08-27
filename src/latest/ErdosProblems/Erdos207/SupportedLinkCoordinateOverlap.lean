/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LinkCoordinateOverlap
import ErdosProblems.Erdos207.SupportedTypicalResidualLinks

/-! # Coordinate overlap charged to current centers, not every ambient outside vertex -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

theorem card_otherLinkCoordinates_le_relevant_reserveCommonCenters
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V) (center : O ↪ V)
    (hcenter : ∀ o, (K o).center = center o)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    (S : Finset V) (reserve : Finset (Sym2 V))
    (hS : ∀ y : SimultaneousLinkPair O V K, r y.1 y.2.1 y.2.2 → center y.1 ∈ S)
    (hspokes : ∀ y : SimultaneousLinkPair O V K, r y.1 y.2.1 y.2.2 →
      reserveWedgeBlock ((K y.1).leftEmbedding y.2.1) ((K y.1).rightEmbedding y.2.2)
        ((K y.1).center) ⊆ reserve)
    (x : SimultaneousLinkPair O V K) :
    (otherLinkCoordinates K r x).card ≤
      (reserveCommonCenters S reserve ((K x.1).leftEmbedding x.2.1)
        ((K x.1).rightEmbedding x.2.2)).card := by
  apply card_le_card_of_injOn (f := fun y : SimultaneousLinkPair O V K ↦ center y.1)
  · intro y hy
    have hyd := (mem_filter.mp hy).2
    apply mem_filter.mpr
    refine ⟨hS y hyd.2.1, ?_⟩
    have hblocks := reserveWedgeBlock_eq_of_fixedPair_eq hyd.2.2 (center y.1)
    rw [← hblocks, ← hcenter y.1]
    exact hspokes y hyd.2.1
  · intro y hy z hz heq
    exact simultaneousLinkPair_eq_of_center_innerEdge K (center.injective heq)
      ((mem_filter.mp hy).2.2.2.trans (mem_filter.mp hz).2.2.2.symm)

theorem residualLink_otherCoordinates_le_current_reserve_overlap
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {current U : Finset V} {R : TripleSystemOn V} {reserve : Finset (Sym2 V)}
    (K : {x : V // x ∉ U} → BipartiteLink V)
    (hK : ∀ o, IsResidualBipartition G R o.1 (K o))
    (hsupp : GraphSupportedOn G (current : Set V))
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (hspokes : ∀ o, (K o).SpokesIn reserve)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    (M : ℕ) (hM : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → (reserveCommonCenters (current \ U) reserve u v).card ≤ M) :
    ∀ x : SimultaneousLinkPair {v : V // v ∉ U} V K, (otherLinkCoordinates K r x).card ≤ M := by
  intro x
  apply le_trans (card_otherLinkCoordinates_le_relevant_reserveCommonCenters K (outsideVertexEmbedding U)
    (fun o ↦ (hK o).1) r (current \ U) reserve ?_ ?_ x)
    (hM _ (hleft x.1 x.2.1.2) _ (hright x.1 x.2.2.2) ((K x.1).left_ne_right x.2.1 x.2.2))
  · intro y _
    have hres : y.2.1.1 ∈ residualNeighbors G R y.1.1 := by
      rw [← (hK y.1).2.1]
      exact mem_union_left _ y.2.1.2
    exact mem_sdiff.mpr ⟨(hsupp (mem_residualNeighbors_iff.mp hres).1).1, y.1.2⟩
  · intro y _
    simp only [reserveWedgeBlock, insert_subset_iff, singleton_subset_iff]
    constructor
    · have hs := (hspokes y.1).1 y.2.1.1 y.2.1.2
      change s(y.2.1.1, (K y.1).center) ∈ reserve
      rw [Sym2.eq_swap]
      exact hs
    · have hs := (hspokes y.1).2 y.2.2.1 y.2.2.2
      change s(y.2.2.1, (K y.1).center) ∈ reserve
      rw [Sym2.eq_swap]
      exact hs

end

end Erdos207
