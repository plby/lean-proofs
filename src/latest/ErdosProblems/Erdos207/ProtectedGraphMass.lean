/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SupportedGraphDegreeSum
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryGeometry

/-! # A deterministic edge-mass bound for every crossing-reserve outcome -/

namespace Erdos207

open Finset

noncomputable section

theorem reserveProtected_deletedEdges_subset_image
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D U : Finset V) (R : Finset (Sym2 V))
    (hG : GraphSupportedOn G (D : Set V)) (hR : R ⊆ crossingEdges G U) :
    graphEdges G \ graphEdges (reserveProtectedOuterGraph G U R) ⊆
      (U ×ˢ D).image (fun p ↦ s(p.1, p.2)) := by
  intro e
  refine Sym2.inductionOn e (fun x y he ↦ ?_)
  have hxy : G.Adj x y := mem_graphEdges_iff.mp (mem_sdiff.mp he).1
  have hD := hG hxy
  have htouch : x ∈ U ∨ y ∈ U := by
    by_cases hx : x ∈ U
    · exact Or.inl hx
    by_cases hy : y ∈ U
    · exact Or.inr hy
    exfalso
    apply (mem_sdiff.mp he).2
    rw [graphEdges_reserveProtectedOuterGraph]
    apply mem_sdiff.mpr
    refine ⟨mem_outerGraphEdges_iff.mpr ⟨(mem_sdiff.mp he).1, ?_⟩, ?_⟩
    · intro hsub
      exact hx (hsub (by simp))
    · intro hr
      obtain ⟨v, hv⟩ := (mem_crossingEdges_iff.mp (hR hr)).2.1
      have hvU := (mem_inter.mp hv).2
      have hvxy : v = x ∨ v = y := by
        simpa only [Sym2.toFinset_mk_eq, mem_insert, mem_singleton] using (mem_inter.mp hv).1
      rcases hvxy with rfl | rfl
      · exact hx hvU
      · exact hy hvU
  rcases htouch with hx | hy
  · exact mem_image.mpr ⟨(x, y), mem_product.mpr ⟨hx, hD.2⟩, rfl⟩
  · exact mem_image.mpr ⟨(y, x), mem_product.mpr ⟨hy, hD.1⟩, by simp [Sym2.eq_swap]⟩

theorem reserveProtected_graph_edge_loss
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D U : Finset V) (R : Finset (Sym2 V))
    (hG : GraphSupportedOn G (D : Set V)) (hR : R ⊆ crossingEdges G U) :
    (graphEdges G).card ≤ (graphEdges (reserveProtectedOuterGraph G U R)).card + U.card * D.card := by
  let E := graphEdges (reserveProtectedOuterGraph G U R)
  have hsub : graphEdges G ⊆ E ∪ (graphEdges G \ E) := by
    intro e he
    by_cases h : e ∈ E
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_sdiff.mpr ⟨he, h⟩)
  have hbad : (graphEdges G \ E).card ≤ U.card * D.card := by
    calc
      _ ≤ ((U ×ˢ D).image (fun p ↦ s(p.1, p.2))).card :=
        card_le_card (reserveProtected_deletedEdges_subset_image G D U R hG hR)
      _ ≤ (U ×ˢ D).card := card_image_le
      _ = _ := card_product U D
  exact ((card_le_card hsub).trans (card_union_le _ _)).trans (Nat.add_le_add_left hbad _)

theorem reserveProtected_graph_mass_of_neighbor_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D U : Finset V) (R : Finset (Sym2 V))
    (hG : GraphSupportedOn G (D : Set V)) (hR : R ⊆ crossingEdges G U) (p : ℝ)
    (hdegree : ∀ v ∈ D, p * D.card / 2 ≤ (neighborsIn G D v).card)
    (hinner : (U.card : ℝ) ≤ p * D.card / 8) :
    p * (D.card : ℝ) ^ 2 / 8 ≤ (graphEdges (reserveProtectedOuterGraph G U R)).card := by
  have hlower := graphEdges_mass_of_neighbor_lower G D hG p hdegree
  have hloss : ((graphEdges G).card : ℝ) ≤
      (graphEdges (reserveProtectedOuterGraph G U R)).card + (U.card : ℝ) * D.card := by
    exact_mod_cast reserveProtected_graph_edge_loss G D U R hG hR
  have hmul := mul_le_mul_of_nonneg_right hinner (Nat.cast_nonneg D.card : (0 : ℝ) ≤ D.card)
  nlinarith

end

end Erdos207
