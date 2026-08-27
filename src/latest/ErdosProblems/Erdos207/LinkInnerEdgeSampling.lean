/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DisjointWitnessSampling
import ErdosProblems.Erdos207.SampledLinkCollisionControl
import ErdosProblems.Erdos207.LinkCoordinateOverlap

/-! # Inner-edge damage has the smaller fibre-times-triangle inclusion scale -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem simultaneousLinkInnerEdge_eq_of_internal_edge
    {O V : Type*} [DecidableEq V] (K : O → BipartiteLink V) (U : Finset V)
    (hout : ∀ o, (K o).center ∉ U) (x : SimultaneousLinkPair O V K)
    {e : Sym2 V} (hinner : e.toFinset ⊆ U)
    (he : e ∈ tripleEdgeFinset (simultaneousLinkPairTriple K x)) :
    e = simultaneousLinkInnerEdge K x := by
  induction e using Sym2.ind with
  | h u v =>
    have hm := mk_mem_tripleEdgeFinset_iff.mp he
    have huU : u ∈ U := hinner (by simp)
    have hvU : v ∈ U := hinner (by simp)
    exact simultaneousLinkInnerEdge_eq_of_mem_ne_center K x hm.1 hm.2.1
      (fun h ↦ hout x.1 (h ▸ huU)) (fun h ↦ hout x.1 (h ▸ hvU)) hm.2.2

def linkInnerEdgeFan
    {V : Type*} [DecidableEq V] (A : TripleSystemOn V) (e : Sym2 V) : TripleSystemOn V :=
  A.filter fun T ↦ e ∈ tripleEdgeFinset T

theorem linkInnerEdgeFan_pairwiseDisjoint
    {O V : Type*} [DecidableEq V] (K : O → BipartiteLink V) (U : Finset V)
    (hout : ∀ o, (K o).center ∉ U) (A : TripleSystemOn V) (hA : IsSimultaneousLinkFamily K A)
    (E : Finset (Sym2 V)) (hinner : ∀ e ∈ E, e.toFinset ⊆ U) :
    (E : Set (Sym2 V)).PairwiseDisjoint (linkInnerEdgeFan A) := by
  intro e he f hf hef
  apply disjoint_left.mpr
  intro T hTe hTf
  have hTed := mem_filter.mp hTe
  have hTfd := mem_filter.mp hTf
  obtain ⟨x, rfl⟩ := hA T hTed.1
  exact hef ((simultaneousLinkInnerEdge_eq_of_internal_edge K U hout x (hinner e he) hTed.2).trans
    (simultaneousLinkInnerEdge_eq_of_internal_edge K U hout x (hinner f hf) hTfd.2).symm)

theorem card_linkInnerEdgeFan_le_coordinates
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V) (U : Finset V) (hout : ∀ o, (K o).center ∉ U)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) (A : TripleSystemOn V)
    (hA : ∀ T ∈ A, ∃ x : SimultaneousLinkPair O V K,
      r x.1 x.2.1 x.2.2 ∧ T = simultaneousLinkPairTriple K x)
    (e : Sym2 V) (hinner : e.toFinset ⊆ U) :
    (linkInnerEdgeFan A e).card ≤
      (univ.filter (fun x : SimultaneousLinkPair O V K ↦
        r x.1 x.2.1 x.2.2 ∧ simultaneousLinkInnerEdge K x = e)).card := by
  let coords := univ.filter (fun x : SimultaneousLinkPair O V K ↦
    r x.1 x.2.1 x.2.2 ∧ simultaneousLinkInnerEdge K x = e)
  have hchoose : ∀ T : linkInnerEdgeFan A e, ∃ x : coords,
      T.1 = simultaneousLinkPairTriple K x.1 := by
    intro T
    have hTd := mem_filter.mp T.2
    obtain ⟨x, hr, hx⟩ := hA T.1 hTd.1
    have heT : e ∈ tripleEdgeFinset (simultaneousLinkPairTriple K x) := hx ▸ hTd.2
    exact ⟨⟨x, mem_filter.mpr ⟨mem_univ x, hr,
      (simultaneousLinkInnerEdge_eq_of_internal_edge K U hout x hinner heT).symm⟩⟩, hx⟩
  choose f hf using hchoose
  have hinj : Function.Injective f := by
    intro T D heq
    apply Subtype.ext
    exact (hf T).trans ((congrArg (fun x : coords ↦ simultaneousLinkPairTriple K x.1) heq).trans (hf D).symm)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

theorem card_linkInnerEdgeFan_le_other_overlap
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V) (U : Finset V) (hout : ∀ o, (K o).center ∉ U)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) (A : TripleSystemOn V)
    (hA : ∀ T ∈ A, ∃ x : SimultaneousLinkPair O V K,
      r x.1 x.2.1 x.2.2 ∧ T = simultaneousLinkPairTriple K x)
    (e : Sym2 V) (hinner : e.toFinset ⊆ U) (M : ℕ)
    (hM : ∀ x : SimultaneousLinkPair O V K, (otherLinkCoordinates K r x).card ≤ M) :
    (linkInnerEdgeFan A e).card ≤ M + 1 :=
  (card_linkInnerEdgeFan_le_coordinates K U hout r A hA e hinner).trans
    (card_linkCoordinateFiber_le_other_add_one K r e M hM)

theorem FiniteLaw.probability_internal_link_edges_subset_le
    {Ω O V : Type*} [Fintype Ω] [DecidableEq V]
    (L : FiniteLaw Ω) (selected : Ω → TripleSystemOn V)
    (K : O → BipartiteLink V) (U : Finset V) (hout : ∀ o, (K o).center ∉ U)
    (A : TripleSystemOn V) (hA : IsSimultaneousLinkFamily K A)
    (hselected : L.SupportedOn fun omega ↦ selected omega ⊆ A)
    (sigma : ℝ≥0) (hjoint : ∀ Q : TripleSystemOn V,
      L.probability (fun omega ↦ Q ⊆ selected omega) ≤ sigma ^ Q.card)
    (E : Finset (Sym2 V)) (hinner : ∀ e ∈ E, e.toFinset ⊆ U)
    (M : ℕ) (hM : ∀ e ∈ E, (linkInnerEdgeFan A e).card ≤ M) :
    L.probability (fun omega ↦ E ⊆ (selected omega).biUnion tripleEdgeFinset) ≤
      ((M : ℝ≥0) * sigma) ^ E.card := by
  apply le_trans _ (L.probability_disjointWitnesses_le_uniform selected sigma hjoint
    (linkInnerEdgeFan A) E (linkInnerEdgeFan_pairwiseDisjoint K U hout A hA E hinner) M hM)
  apply L.probability_mono_of_supported hselected
  intro omega hsub hE e he
  obtain ⟨T, hT, heT⟩ := mem_biUnion.mp (hE he)
  exact ⟨T, mem_filter.mpr ⟨hsub hT, heT⟩, hT⟩

theorem FiniteLaw.probability_internal_link_edges_card_ge_le
    {Ω O V : Type*} [Fintype Ω] [DecidableEq V]
    (L : FiniteLaw Ω) (selected : Ω → TripleSystemOn V)
    (K : O → BipartiteLink V) (U : Finset V) (hout : ∀ o, (K o).center ∉ U)
    (A : TripleSystemOn V) (hA : IsSimultaneousLinkFamily K A)
    (hselected : L.SupportedOn fun omega ↦ selected omega ⊆ A)
    (sigma : ℝ≥0) (hjoint : ∀ Q : TripleSystemOn V,
      L.probability (fun omega ↦ Q ⊆ selected omega) ≤ sigma ^ Q.card)
    (E : Finset (Sym2 V)) (hinner : ∀ e ∈ E, e.toFinset ⊆ U)
    (M : ℕ) (hM : ∀ e ∈ E, (linkInnerEdgeFan A e).card ≤ M)
    (s R : ℕ) (hR : 0 < R) (hs : 2*s ≤ R) :
    L.probability (fun omega ↦ R ≤ (E ∩ (selected omega).biUnion tripleEdgeFinset).card) ≤
      (2 * (E.card : ℝ≥0) * M * sigma / R) ^ s := by
  apply le_trans _ (L.probability_activeWitnessIndices_card_ge_le selected sigma hjoint
    (linkInnerEdgeFan A) E (linkInnerEdgeFan_pairwiseDisjoint K U hout A hA E hinner) M hM s R hR hs)
  apply L.probability_mono_of_supported hselected
  intro omega hsub hlarge
  apply hlarge.trans
  apply card_le_card
  intro e he
  have hed := mem_inter.mp he
  obtain ⟨T, hT, heT⟩ := mem_biUnion.mp hed.2
  exact mem_filter.mpr ⟨hed.1, T, mem_filter.mpr ⟨hsub hT, heT⟩, hT⟩

end

end Erdos207
