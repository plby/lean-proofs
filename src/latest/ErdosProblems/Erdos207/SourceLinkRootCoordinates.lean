/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkNonrootWeights

/-! # Compatible roots in the marked link coordinate space -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceLinkUnderlyingRoot_eq_empty_iff
    {V : Type*} [DecidableEq V] (H : Finset (SourceLinkCoordinate V)) :
    sourceLinkUnderlyingRoot H = ∅ ↔ H.toLeft = ∅ := by
  constructor
  · intro h
    have houter := union_eq_empty.mp h
    have hinner := union_eq_empty.mp houter.1
    have hright : H.toLeft.toRight = ∅ := by
      rw [← toLeft_disjSum_toRight (u := H.toLeft.toRight), hinner.2, houter.2]
      rfl
    rw [← toLeft_disjSum_toRight (u := H.toLeft), hinner.1, hright]
    rfl
  · intro h
    unfold sourceLinkUnderlyingRoot
    rw [h]
    rfl

theorem SourceLinkMarking.rooted_coordinate_constraints
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    {x : SourceLinkMarking V} (hx : IsSourceLinkMarking W F e A x)
    {H : Finset (SourceLinkCoordinate V)} (hH : H ⊆ x.coordinates e) :
    e ∉ H.toRight ∧ (∀ f ∈ H.toRight, ¬ f.IsDiag) ∧
      sourceLinkUnderlyingRoot H ⊆ x.system ∧
      (H.Nonempty → (sourceLinkUnderlyingRoot H).Nonempty ∨ H.toRight.Nonempty) := by
  have hparts := subset_disjSum.mp hH
  refine ⟨fun he ↦ (mem_erase.mp (hparts.2 he)).1 rfl, ?_,
    (mem_familyExtensions_iff.mp (sourceLinkMarking_rooted_system_mem hx hH)).2, ?_⟩
  · intro f hf
    obtain ⟨T, _hT, hfT⟩ := mem_biUnion.mp (mem_erase.mp (hparts.2 hf)).2
    induction f using Sym2.ind with
    | h u v =>
        rw [Sym2.mk_isDiag_iff]
        exact (mk_mem_tripleEdgeFinset_iff.mp hfT).2.2
  · intro hnon
    by_cases hroot : (sourceLinkUnderlyingRoot H).Nonempty
    · exact Or.inl hroot
    · right
      have hleft := (sourceLinkUnderlyingRoot_eq_empty_iff H).mp (not_nonempty_iff_eq_empty.mp hroot)
      obtain ⟨c, hc⟩ := hnon
      rcases c with c | f
      · have hm : c ∈ H.toLeft := mem_toLeft.mpr hc
        rw [hleft] at hm
        exact (notMem_empty _ hm).elim
      · exact ⟨f, mem_toRight.mpr hc⟩

theorem SourceLinkMarking.exceptional_root_coordinates
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    {x : SourceLinkMarking V} (hx : IsSourceLinkMarking W F e A x)
    (hpack : IsPackingOn x.system) {H : Finset (SourceLinkCoordinate V)}
    (hH : H ⊆ x.coordinates e)
    (hex : IsSourceLinkExceptionalRoot e (sourceLinkUnderlyingRoot H) H.toRight) :
    H.toLeft = {Sum.inr (Sum.inr x.root)} ∧ H.toRight ⊆ tripleEdgeFinset x.root ∧
      sourceLinkUnderlyingRoot H = {x.root} := by
  obtain ⟨T, hT, heT, hedge⟩ := hex
  have hR := (SourceLinkMarking.rooted_coordinate_constraints hx hH).2.2.1
  have hTE : T ∈ x.system := hR (hT.symm ▸ mem_singleton_self T)
  have heq : T = x.root := hpack.eq_of_common_graph_edge hTE
    (SourceLinkMarking.root_mem_system hx) heT hx.2.2.2.2.1
  subst T
  refine ⟨?_, hedge, hT⟩
  have hsubset : H.toLeft ⊆ {Sum.inr (Sum.inr x.root)} := by
    intro c hc
    have htri := (subset_disjSum.mp hH).1 hc
    have hnot := SourceLinkMarking.root_not_mem_initial_later hx
    rcases c with D | D | D
    · have hDI : D ∈ x.initial := by simpa only [triangleCoordinates, inl_mem_disjSum] using htri
      have hDR : D ∈ sourceLinkUnderlyingRoot H :=
        mem_union_left _ (mem_union_left _ (mem_toLeft.mpr hc))
      have hD : D = x.root := mem_singleton.mp (hT ▸ hDR)
      exact (hnot (mem_union_left _ (hD ▸ hDI))).elim
    · have hDL : D ∈ x.later := by
        simpa only [triangleCoordinates, inr_mem_disjSum, inl_mem_disjSum] using htri
      have hDR : D ∈ sourceLinkUnderlyingRoot H :=
        mem_union_left _ (mem_union_right _ (mem_toLeft.mpr (mem_toRight.mpr hc)))
      have hD : D = x.root := mem_singleton.mp (hT ▸ hDR)
      exact (hnot (mem_union_right _ (hD ▸ hDL))).elim
    · have hDR : D ∈ sourceLinkUnderlyingRoot H :=
        mem_union_right _ (mem_toRight.mpr (mem_toRight.mpr hc))
      have hD : D = x.root := mem_singleton.mp (hT ▸ hDR)
      simp only [hD, mem_singleton]
  have hnon : H.toLeft.Nonempty := by
    by_contra hempty
    have hh := (sourceLinkUnderlyingRoot_eq_empty_iff H).mpr (not_nonempty_iff_eq_empty.mp hempty)
    rw [hT] at hh
    exact singleton_ne_empty _ hh
  exact eq_of_subset_of_card_le hsubset (by have := card_pos.mpr hnon; simp only [card_singleton]; omega)

end

end Erdos207
