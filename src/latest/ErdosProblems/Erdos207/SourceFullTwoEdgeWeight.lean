/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceFullEdgeWeight
import ErdosProblems.Erdos207.PairSharingIntersection

/-! # The full-weight saving from two distinct pinned edges -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceVortexWellSpread.full_existing_terminal_edge_root_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (e : Sym2 V)
    (G : ForbiddenFamilyOn V) (hG : G ⊆ F)
    (hcover : ∀ E ∈ G, ∃ D ∈ sourceTerminalEdgeFan W e, D ∈ E)
    (T : TripleOn V) (heT : e ∈ tripleEdgeFinset T) :
    vortexTripleWeight W 1 T *
      (∑ E ∈ familyExtensions G {T}, setWeight (vortexTripleWeight W 1) (E \ {T})) ≤
      (j ^ ell : ℕ) * z / W.terminalSize := by
  classical
  by_cases hnonempty : (familyExtensions G {T}).Nonempty
  · obtain ⟨E, hE⟩ := hnonempty
    have hm := mem_familyExtensions_iff.mp hE
    have hTE : T ∈ E := hm.2 (mem_singleton_self T)
    obtain ⟨D, hD, hDE⟩ := hcover E hm.1
    have hd := (mem_filter.mp hD).2
    have heq : T = D := by
      by_contra hne
      have hdis := (h.uniform E (hG hm.1)).2.isTriangleDecomposition.pairwiseDisjoint_tripleEdgeFinset
        hTE hDE hne
      exact disjoint_left.mp hdis heT hd.1
    have hlevel : W.level T = Fin.last ell := heq.symm ▸ hd.2
    have hsub : familyExtensions G {T} ⊆ familyExtensions F {T} := by
      intro C hC
      have hh := mem_familyExtensions_iff.mp hC
      exact mem_familyExtensions_iff.mpr ⟨hG hh.1, hh.2⟩
    have hb := (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ zero_le)).trans
      (h.full_singleton_weight_le_uniform T)
    calc
      _ ≤ vortexTripleWeight W 1 T * ((j ^ ell : ℕ) * z) := by gcongr
      _ = _ := by simp only [vortexTripleWeight, hlevel, Vortex.terminalSize]; ring
  · rw [not_nonempty_iff_eq_empty.mp hnonempty, sum_empty, mul_zero]
    exact zero_le

theorem SourceVortexWellSpread.full_two_pinned_edges_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z)
    (e e' : Sym2 V) (hoff : ¬ e.IsDiag) (hoff' : ¬ e'.IsDiag) (hne : e ≠ e')
    (G : ForbiddenFamilyOn V) (hG : G ⊆ F)
    (hcover : ∀ E ∈ G, ∃ D ∈ sourceTerminalEdgeFan W e, D ∈ E)
    (hcover' : ∀ E ∈ G, e' ∈ E.biUnion tripleEdgeFinset) :
    (∑ E ∈ G, setWeight (vortexTripleWeight W 1) E) ≤
      (1 + (ell + 1) ^ 2 : ℕ) * (j ^ ell : ℕ) * z / W.terminalSize := by
  classical
  let B := universeTriplesContainingPair e'.toFinset
  let K : ℝ≥0 := (j ^ ell : ℕ) * z / W.terminalSize
  let a : ℝ≥0 := (ell + 1 : ℕ)
  let f : TripleOn V → ℝ≥0 := fun T ↦ vortexTripleWeight W 1 T *
    ∑ E ∈ familyExtensions G {T}, setWeight (vortexTripleWeight W 1) (E \ {T})
  have hsum : (∑ E ∈ G, setWeight (vortexTripleWeight W 1) E) ≤ ∑ T ∈ B, f T := by
    have hb := fullRootWeight_expose_cover_le G (vortexTripleWeight W 1) ∅ B G
      (by simp [familyExtensions]) (fun E hE ↦ by
        obtain ⟨D, hDE, heD⟩ := mem_biUnion.mp (hcover' E hE)
        exact ⟨D, mem_universeTriplesContainingPair_iff.mpr
          ((mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e' D hoff').mp heD), hDE⟩)
      (disjoint_empty_right B)
    simpa only [sdiff_empty, insert_empty, f] using hb
  have hcommon : ∑ T ∈ B with e ∈ tripleEdgeFinset T, f T ≤ K := by
    have hcard : (B.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card ≤ 1 := by
      have hsub : B.filter (fun T ↦ e ∈ tripleEdgeFinset T) ⊆
          universeTriplesContainingPair e.toFinset ∩ universeTriplesContainingPair e'.toFinset := by
        intro T hT
        have hm := mem_filter.mp hT
        exact mem_inter.mpr ⟨mem_universeTriplesContainingPair_iff.mpr
          ((mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e T hoff).mp hm.2), hm.1⟩
      apply (card_le_card hsub).trans
      apply card_triplesContaining_distinct_pairs_le_one
        (Sym2.card_toFinset_of_not_isDiag e hoff) (Sym2.card_toFinset_of_not_isDiag e' hoff')
      intro heq
      apply hne
      apply Sym2.ext
      intro v
      rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, heq]
    calc
      _ ≤ ∑ _T ∈ B with e ∈ tripleEdgeFinset _T, K := by
        apply sum_le_sum
        intro T hT
        exact h.full_existing_terminal_edge_root_weight_le e G hG hcover T (mem_filter.mp hT).2
      _ = ((B.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ≥0) * K := by simp
      _ ≤ 1 * K := by gcongr; exact_mod_cast hcard
      _ = K := one_mul K
  have hother : ∑ T ∈ B with e ∉ tripleEdgeFinset T, f T ≤ a * (a * K) := by
    have hBsum : (∑ T ∈ B with e ∉ tripleEdgeFinset T, vortexTripleWeight W 1 T) ≤ a := by
      apply (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ zero_le)).trans
      simpa only [mul_one] using sum_vortexTripleWeight_containingPair_le W 1 e'.toFinset
        (Sym2.card_toFinset_of_not_isDiag e' hoff')
    calc
      _ ≤ ∑ T ∈ B with e ∉ tripleEdgeFinset T, vortexTripleWeight W 1 T * (a * K) := by
        apply sum_le_sum
        intro T hT
        apply mul_le_mul_of_nonneg_left _ zero_le
        have hb := h.full_nonempty_pinned_terminal_edge_weight_le {T} (singleton_nonempty T)
          (by simp; have := h.order; omega) e hoff
          (fun D hD ↦ by simpa only [mem_singleton.mp hD] using (mem_filter.mp hT).2)
          (familyExtensions G {T}) (fun E hE ↦ by
            have hm := mem_familyExtensions_iff.mp hE
            exact mem_familyExtensions_iff.mpr ⟨hG hm.1, hm.2⟩)
          (fun E hE ↦ hcover E (mem_familyExtensions_iff.mp hE).1)
        simpa only [a, K, mul_div_assoc, mul_assoc] using hb
      _ = (∑ T ∈ B with e ∉ tripleEdgeFinset T, vortexTripleWeight W 1 T) * (a * K) :=
        (sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hBsum zero_le
  apply hsum.trans
  calc
    _ = (∑ T ∈ B with e ∈ tripleEdgeFinset T, f T) +
        ∑ T ∈ B with e ∉ tripleEdgeFinset T, f T :=
      (sum_filter_add_sum_filter_not B (fun T ↦ e ∈ tripleEdgeFinset T) f).symm
    _ ≤ K + a * (a * K) := add_le_add hcommon hother
    _ = _ := by simp only [K, a, Nat.cast_add, Nat.cast_one, Nat.cast_pow]; ring

end

end Erdos207
