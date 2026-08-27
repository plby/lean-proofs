/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousLinkCollision
import ErdosProblems.Erdos207.ReserveCommonCenterTail

/-! # Actual link-coordinate multiplicity injects into two-spoke centres -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem simultaneousLinkPair_eq_of_center_innerEdge
    {O V : Type*} [DecidableEq V] (K : O → BipartiteLink V)
    {x y : SimultaneousLinkPair O V K} (hcenter : x.1 = y.1)
    (hedge : simultaneousLinkInnerEdge K x = simultaneousLinkInnerEdge K y) : x = y := by
  obtain ⟨o, a, b⟩ := x
  obtain ⟨p, c, d⟩ := y
  dsimp only at hcenter
  subst p
  change s((K o).leftEmbedding a, (K o).rightEmbedding b) =
    s((K o).leftEmbedding c, (K o).rightEmbedding d) at hedge
  rcases Sym2.eq_iff.mp hedge with h | h
  · have hac := (K o).leftEmbedding.injective h.1
    have hbd := (K o).rightEmbedding.injective h.2
    subst c
    subst d
    rfl
  · exact ((K o).left_ne_right a d h.1).elim

theorem reserveWedgeBlock_eq_of_fixedPair_eq
    {V : Type*} [DecidableEq V] {u v a b : V}
    (h : s(u,v) = s(a,b)) (w : V) : reserveWedgeBlock u v w = reserveWedgeBlock a b w := by
  rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · simp only [reserveWedgeBlock, pair_comm]

theorem card_otherLinkCoordinates_le_reserveCommonCenters
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V) (center : O ↪ V)
    (hcenter : ∀ o, (K o).center = center o)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    (S : Finset V) (reserve : Finset (Sym2 V))
    (hS : ∀ o, center o ∈ S)
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
    refine ⟨hS y.1, ?_⟩
    have hblocks := reserveWedgeBlock_eq_of_fixedPair_eq hyd.2.2 (center y.1)
    rw [← hblocks, ← hcenter y.1]
    exact hspokes y hyd.2.1
  · intro y hy z hz heq
    have hcenters : y.1 = z.1 := center.injective heq
    have hyd := (mem_filter.mp hy).2.2.2
    have hzd := (mem_filter.mp hz).2.2.2
    exact simultaneousLinkPair_eq_of_center_innerEdge K hcenters (hyd.trans hzd.symm)

theorem card_linkCoordinateFiber_le_other_add_one
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) (e : Sym2 V) (M : ℕ)
    (hM : ∀ x : SimultaneousLinkPair O V K, (otherLinkCoordinates K r x).card ≤ M) :
    (univ.filter (fun x : SimultaneousLinkPair O V K ↦
      r x.1 x.2.1 x.2.2 ∧ simultaneousLinkInnerEdge K x = e)).card ≤ M + 1 := by
  let fiber := univ.filter (fun x : SimultaneousLinkPair O V K ↦
    r x.1 x.2.1 x.2.2 ∧ simultaneousLinkInnerEdge K x = e)
  by_cases hnonempty : fiber.Nonempty
  · obtain ⟨x, hx⟩ := hnonempty
    have hxd := (mem_filter.mp hx).2
    have hsub : fiber ⊆ insert x (otherLinkCoordinates K r x) := by
      intro y hy
      have hyd := (mem_filter.mp hy).2
      have hedge := hyd.2.trans hxd.2.symm
      by_cases hcenter : y.1 = x.1
      · exact mem_insert.mpr (Or.inl (simultaneousLinkPair_eq_of_center_innerEdge K hcenter hedge))
      · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_univ y, hcenter, hyd.1, hedge⟩)
    exact (card_le_card hsub).trans ((card_insert_le _ _).trans (Nat.add_le_add_right (hM x) 1))
  · have hempty : fiber = ∅ := not_nonempty_iff_eq_empty.mp hnonempty
    change fiber.card ≤ M + 1
    rw [hempty, card_empty]
    omega

end

end Erdos207
