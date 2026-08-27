/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceFullTwoEdgeWeight

/-! # Unmarked families underlying the source link moment -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceLinkUnderlyingFamily
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (e : Sym2 V)
    (edges : Finset (Sym2 V)) : ForbiddenFamilyOn V :=
  F.filter fun E ↦
    (∃ T ∈ sourceTerminalEdgeFan W e, T ∈ E ∧
      ∃ D ∈ E.erase T, W.level D = Fin.last ell) ∧
    edges ⊆ E.biUnion tripleEdgeFinset

def IsSourceLinkExceptionalRoot
    {V : Type*} [DecidableEq V] (e : Sym2 V)
    (Q : TripleSystemOn V) (edges : Finset (Sym2 V)) : Prop :=
  ∃ T, Q = {T} ∧ e ∈ tripleEdgeFinset T ∧ edges ⊆ tripleEdgeFinset T

theorem IsPackingOn.eq_of_common_graph_edge
    {V : Type*} [Fintype V] [DecidableEq V] {E : TripleSystemOn V}
    (h : IsPackingOn E) {T D : TripleOn V} (hT : T ∈ E) (hD : D ∈ E)
    {e : Sym2 V} (heT : e ∈ tripleEdgeFinset T) (heD : e ∈ tripleEdgeFinset D) : T = D := by
  by_contra hne
  exact disjoint_left.mp
    (h.isTriangleDecomposition.pairwiseDisjoint_tripleEdgeFinset hT hD hne) heT heD

theorem sourceLinkUnderlyingFamily_data
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V}
    {edges : Finset (Sym2 V)} {E : TripleSystemOn V}
    (hE : E ∈ sourceLinkUnderlyingFamily W F e edges) :
    E ∈ F ∧
    (∃ T ∈ sourceTerminalEdgeFan W e, T ∈ E ∧
      ∃ D ∈ E.erase T, W.level D = Fin.last ell) ∧
    edges ⊆ E.biUnion tripleEdgeFinset := by
  exact mem_filter.mp hE

theorem SourceVortexWellSpread.link_underlying_order_four_other_terminal
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W 4 F y z)
    {e : Sym2 V} {edges : Finset (Sym2 V)} {E : TripleSystemOn V}
    (hE : E ∈ sourceLinkUnderlyingFamily W F e edges)
    {T D : TripleOn V} (hT : T ∈ E) (heT : e ∈ tripleEdgeFinset T)
    (hD : D ∈ E.erase T) : W.level D = Fin.last ell := by
  have hm := sourceLinkUnderlyingFamily_data hE
  obtain ⟨T', hT', hT'E, D', hD', hlevel⟩ := hm.2.1
  have heq := (h.uniform E hm.1).2.eq_of_common_graph_edge hT hT'E heT (mem_filter.mp hT').2.1
  subst T'
  have hcard : (E.erase T).card = 1 := by
    rw [card_erase_of_mem hT, (h.uniform E hm.1).1]
  have hDD' : D = D' := (card_le_one.mp hcard.le) D hD D' hD'
  exact hDD'.symm ▸ hlevel

theorem SourceVortexWellSpread.link_underlying_nonexceptional_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z)
    (e : Sym2 V) (hoff : ¬ e.IsDiag) (Q : TripleSystemOn V)
    (edges : Finset (Sym2 V)) (hpin : e ∉ edges)
    (hedges : ∀ f ∈ edges, ¬ f.IsDiag)
    (hroot : Q.Nonempty ∨ edges.Nonempty) (hQcard : Q.card ≤ j - 3)
    (hexception : ¬ IsSourceLinkExceptionalRoot e Q edges) :
    (∑ E ∈ familyExtensions (sourceLinkUnderlyingFamily W F e edges) Q,
      setWeight (vortexTripleWeight W 1) (E \ Q)) ≤
      (1 + (ell + 1) ^ 2 : ℕ) * (j ^ ell : ℕ) * z / W.terminalSize := by
  let G := familyExtensions (sourceLinkUnderlyingFamily W F e edges) Q
  have hGF : G ⊆ familyExtensions F Q := by
    intro E hE
    have hm := mem_familyExtensions_iff.mp hE
    exact mem_familyExtensions_iff.mpr ⟨(sourceLinkUnderlyingFamily_data hm.1).1, hm.2⟩
  have hcover : ∀ E ∈ G, ∃ D ∈ sourceTerminalEdgeFan W e, D ∈ E := by
    intro E hE
    obtain ⟨D, hD, hDE, _⟩ := (sourceLinkUnderlyingFamily_data (mem_familyExtensions_iff.mp hE).1).2.1
    exact ⟨D, hD, hDE⟩
  have ha : (ell + 1 : ℕ) ≤ 1 + (ell + 1) ^ 2 := by nlinarith
  have ha' : (1 : ℕ) ≤ 1 + (ell + 1) ^ 2 := by omega
  by_cases htwo : 2 ≤ Q.card
  · apply ((sum_le_sum_of_subset_of_nonneg hGF (fun _ _ _ ↦ zero_le)).trans
      (h.full_middle_root_weight_le_uniform Q htwo hQcard)).trans
    calc
      _ = 1 * (j ^ ell : ℕ) * z / (W.terminalSize : ℝ≥0) := by rw [one_mul]
      _ ≤ _ := by gcongr; exact_mod_cast ha'
  · by_cases hQ : Q.Nonempty
    · have hone : Q.card = 1 := by have := card_pos.mpr hQ; omega
      obtain ⟨T, hQT⟩ := card_eq_one.mp hone
      by_cases heT : e ∈ tripleEdgeFinset T
      · have hout : ¬ edges ⊆ tripleEdgeFinset T := by
          intro hs
          exact hexception ⟨T, hQT, heT, hs⟩
        obtain ⟨f, hf, hfT⟩ := not_subset.mp hout
        have hb := h.full_singleton_pinned_edge_weight_le T f (hedges f hf) hfT G
          (hQT ▸ hGF) (fun E hE ↦ by
            have hm := mem_familyExtensions_iff.mp hE
            have hd := sourceLinkUnderlyingFamily_data hm.1
            obtain ⟨D, hDE, hfD⟩ := mem_biUnion.mp (hd.2.2 hf)
            have hDT : D ≠ T := fun heq ↦ hfT (heq ▸ hfD)
            refine ⟨D, mem_erase.mpr ⟨hDT, hDE⟩, hfD, ?_⟩
            intro hj
            subst j
            exact h.link_underlying_order_four_other_terminal hm.1
              (hm.2 (hQT ▸ mem_singleton_self T)) heT (mem_erase.mpr ⟨hDT, hDE⟩))
        change (∑ E ∈ G, setWeight (vortexTripleWeight W 1) (E \ Q)) ≤ _
        rw [hQT]
        apply hb.trans
        gcongr
      · have hb := h.full_nonempty_pinned_terminal_edge_weight_le Q hQ hQcard e hoff
          (fun D hD ↦ by have heq : D = T := mem_singleton.mp (hQT ▸ hD); simpa only [heq] using heT)
          G hGF hcover
        apply hb.trans
        gcongr
    · have hQempty := not_nonempty_iff_eq_empty.mp hQ
      obtain ⟨f, hf⟩ := hroot.resolve_left hQ
      have hne : e ≠ f := fun heq ↦ hpin (heq.symm ▸ hf)
      have hb := h.full_two_pinned_edges_weight_le e f hoff (hedges f hf) hne G
        (fun E hE ↦ (mem_familyExtensions_iff.mp (hGF hE)).1) hcover
        (fun E hE ↦ (sourceLinkUnderlyingFamily_data (mem_familyExtensions_iff.mp hE).1).2.2 hf)
      simpa only [G, hQempty, sdiff_empty] using hb

end

end Erdos207
