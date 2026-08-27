/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkCanonicalEdgeWeight

/-! # The inner-set cardinality bound for the distinguished link fan -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem card_tripleCrossingEdges_of_two_inner_vertices
    {V : Type*} [DecidableEq V] (U : Finset V) (T : TripleOn V)
    (hinner : (T.1 ∩ U).card = 2) : (tripleCrossingEdges U T).card = 2 := by
  obtain ⟨a, b, hab, hinter⟩ := card_eq_two.mp hinner
  have ha : a ∈ U := (mem_inter.mp (hinter.symm ▸ (show a ∈ ({a, b} : Finset V) by simp))).2
  have hb : b ∈ U := (mem_inter.mp (hinter.symm ▸ (show b ∈ ({a, b} : Finset V) by simp))).2
  have houtside : (T.1 \ U).card = 1 := by
    have hc := card_sdiff_add_card_inter T.1 U
    rw [hinner, T.2] at hc
    omega
  obtain ⟨c, hrest⟩ := card_eq_one.mp houtside
  have hc : c ∉ U := (mem_sdiff.mp (hrest.symm ▸ mem_singleton_self c)).2
  have hT : T.1 = {c, a, b} := by
    calc
      T.1 = (T.1 \ U) ∪ (T.1 ∩ U) := (sdiff_union_inter _ _).symm
      _ = _ := by
        rw [hrest, hinter]
        ext v
        simp [or_comm, or_left_comm]
  have heq : tripleCrossingEdges U T = {s(c, a), s(c, b)} := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
        simp only [tripleCrossingEdges, mem_filter, mk_mem_tripleEdgeFinset_iff,
          hT, mem_insert, mem_singleton, isCrossingEdge_mk_iff, Sym2.eq_iff]
        aesop
  rw [heq, card_pair_eq_two_iff]
  intro hpair
  apply hab
  have hh : (c = c ∧ a = b) ∨ (c = b ∧ a = c) := by
    simpa only [Sym2.eq_iff] using hpair
  rcases hh with hh | hh
  · exact hh.2
  · exact hh.2.trans hh.1

theorem link_third_vertex_subset_inner
    {V : Type*} [DecidableEq V] {U : Finset V} {e : Sym2 V} {T : TripleOn V}
    (hoff : ¬ e.IsDiag) (he : e ∈ tripleEdgeFinset T) (hcross : IsCrossingEdge U e)
    (hinner : (T.1 ∩ U).card = 2) : T.1 \ e.toFinset ⊆ U := by
  have hpair := (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e T hoff).mp he
  have houtside : (T.1 \ U).card = 1 := by
    have hc := card_sdiff_add_card_inter T.1 U
    rw [hinner, T.2] at hc
    omega
  obtain ⟨v, hv⟩ := hcross.2
  have hvT : v ∈ T.1 \ U := mem_sdiff.mpr ⟨hpair (mem_sdiff.mp hv).1, (mem_sdiff.mp hv).2⟩
  intro w hw
  by_contra hwU
  have hwT : w ∈ T.1 \ U := mem_sdiff.mpr ⟨(mem_sdiff.mp hw).1, hwU⟩
  have hwv := (card_le_one.mp houtside.le) w hwT v hvT
  exact (mem_sdiff.mp hw).2 (hwv.symm ▸ (mem_sdiff.mp hv).1)

theorem card_fixed_pair_inner_third_vertex_le
    {V : Type*} [Fintype V] [DecidableEq V] (P U : Finset V) (hP : P.card = 2)
    (B : TripleSystemOn V) (hpair : ∀ T ∈ B, P ⊆ T.1)
    (hthird : ∀ T ∈ B, T.1 \ P ⊆ U) : B.card ≤ U.card := by
  calc
    _ ≤ (U.powersetCard 1).card := by
      apply card_le_card_of_injOn (f := fun T : TripleOn V ↦ T.1 \ P)
      · intro T hT
        apply mem_powersetCard.mpr
        refine ⟨hthird T hT, ?_⟩
        rw [card_sdiff_of_subset (hpair T hT), T.2, hP]
      · intro T hT D hD heq
        have heq' : T.1 \ P = D.1 \ P := heq
        apply Subtype.ext
        calc
          T.1 = P ∪ (T.1 \ P) := (union_sdiff_of_subset (hpair T hT)).symm
          _ = P ∪ (D.1 \ P) := by rw [heq']
          _ = D.1 := union_sdiff_of_subset (hpair D hD)
    _ = _ := by rw [card_powersetCard, Nat.choose_one_right]

theorem card_sourceLink_inner_fan_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (U : Finset V) (e : Sym2 V) (A : TripleSystemOn V)
    (hoff : ¬ e.IsDiag) (hcross : IsCrossingEdge U e)
    (hinner : ∀ T ∈ A, (T.1 ∩ U).card = 2) :
    (sourceTerminalEdgeFan W e ∩ A).card ≤ U.card := by
  apply card_fixed_pair_inner_third_vertex_le e.toFinset U (Sym2.card_toFinset_of_not_isDiag e hoff)
  · intro T hT
    exact (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e T hoff).mp
      (mem_filter.mp (mem_inter.mp hT).1).2.1
  · intro T hT
    exact link_third_vertex_subset_inner hoff (mem_filter.mp (mem_inter.mp hT).1).2.1 hcross
      (hinner T (mem_inter.mp hT).2)

end

end Erdos207
