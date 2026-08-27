/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceFullRootTransfer
import ErdosProblems.Erdos207.SourceFullRootUniform
import ErdosProblems.Erdos207.SourceTerminalPairFullWeight
import ErdosProblems.Erdos207.SourceNibbleEdgeFan

/-! # Full configuration weights with an additional pinned graph edge -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem fullRootWeight_expose_cover_bound
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (w : TripleOn V → ℝ≥0) (Q B : TripleSystemOn V)
    (G : ForbiddenFamilyOn V) (hG : G ⊆ familyExtensions F Q)
    (hcover : ∀ E ∈ G, ∃ T ∈ B, T ∈ E) (hBQ : Disjoint B Q)
    (a κ : ℝ≥0) (hB : (∑ T ∈ B, w T) ≤ a)
    (hroot : ∀ T ∈ B,
      (∑ E ∈ familyExtensions F (insert T Q), setWeight w (E \ insert T Q)) ≤ κ) :
    (∑ E ∈ G, setWeight w (E \ Q)) ≤ a * κ := by
  apply (fullRootWeight_expose_cover_le F w Q B G hG hcover hBQ).trans
  calc
    _ ≤ ∑ T ∈ B, w T * κ := by
      apply sum_le_sum
      intro T hT
      exact mul_le_mul_of_nonneg_left (hroot T hT) zero_le
    _ = (∑ T ∈ B, w T) * κ := (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hB zero_le

theorem sum_sourceTerminalEdgeFan_weight_le_one
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (e : Sym2 V) (hoff : ¬ e.IsDiag) :
    (∑ T ∈ sourceTerminalEdgeFan W e, vortexTripleWeight W 1 T) ≤ 1 := by
  have hsub : sourceTerminalEdgeFan W e ⊆
      (universeTriplesContainingPair e.toFinset).filter
        (fun T ↦ W.level T = Fin.last ell) := by
    intro T hT
    have hm := (mem_filter.mp hT).2
    exact mem_filter.mpr ⟨mem_universeTriplesContainingPair_iff.mpr
      ((mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e T hoff).mp hm.1), hm.2⟩
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ zero_le)).trans
    (sum_vortexTripleWeight_containingPair_level_le W 1 e.toFinset
      (Sym2.card_toFinset_of_not_isDiag e hoff) (Fin.last ell))

theorem SourceVortexWellSpread.full_singleton_pinned_edge_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (T : TripleOn V)
    (e : Sym2 V) (hoff : ¬ e.IsDiag) (hout : e ∉ tripleEdgeFinset T)
    (G : ForbiddenFamilyOn V) (hG : G ⊆ familyExtensions F {T})
    (hcover : ∀ E ∈ G, ∃ D ∈ E.erase T,
      e ∈ tripleEdgeFinset D ∧ (j = 4 → W.level D = Fin.last ell)) :
    (∑ E ∈ G, setWeight (vortexTripleWeight W 1) (E \ {T})) ≤
      (ell + 1 : ℕ) * (j ^ ell : ℕ) * z / W.terminalSize := by
  have hpair : ¬ e.toFinset ⊆ T.1 := by
    intro hs
    exact hout ((mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e T hoff).mpr hs)
  by_cases hj : j = 4
  · subst j
    have hsub : G ⊆ W.terminalPairExtensions F T
        ⟨e.toFinset, Sym2.card_toFinset_of_not_isDiag e hoff⟩ := by
      intro E hE
      obtain ⟨D, hDE, heD, hlevel⟩ := hcover E hE
      have hm := mem_familyExtensions_iff.mp (hG hE)
      exact (W.mem_terminalPairExtensions_iff F T _ E).mpr
        ⟨hm.1, hm.2 (mem_singleton_self T), D, hDE, hlevel rfl,
          (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e D hoff).mp heD⟩
    apply ((sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ zero_le)).trans
      (h.terminal_pair_full_weight_le T _ hpair)).trans
    have hc : (1 : ℝ≥0) ≤ (ell + 1 : ℕ) * (4 ^ ell : ℕ) := by
      exact_mod_cast (show 1 ≤ (ell + 1) * 4 ^ ell by
        have hp : 0 < (ell + 1) * 4 ^ ell := by positivity
        omega)
    calc
      z / W.terminalSize = 1 * z / W.terminalSize := by rw [one_mul]
      _ ≤ _ := by gcongr
  · have hj5 : 5 ≤ j := by have := h.order; omega
    let B := universeTriplesContainingPair e.toFinset
    have hB : Disjoint B {T} := by
      rw [disjoint_singleton_right]
      exact fun hT ↦ hpair (mem_universeTriplesContainingPair_iff.mp hT)
    have hsum : (∑ D ∈ B, vortexTripleWeight W 1 D) ≤ (ell + 1 : ℕ) := by
      simpa only [mul_one] using sum_vortexTripleWeight_containingPair_le W 1 e.toFinset
        (Sym2.card_toFinset_of_not_isDiag e hoff)
    have hb := fullRootWeight_expose_cover_bound F (vortexTripleWeight W 1) {T} B G hG
      (fun E hE ↦ by
        obtain ⟨D, hDE, heD, _⟩ := hcover E hE
        exact ⟨D, mem_universeTriplesContainingPair_iff.mpr
          ((mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e D hoff).mp heD),
          (mem_erase.mp hDE).2⟩) hB (ell + 1 : ℕ)
      ((j ^ ell : ℕ) * z / W.terminalSize) hsum (fun D hDB ↦ by
        have hDT : D ≠ T := by
          intro heq
          exact disjoint_left.mp hB hDB (by simp [heq])
        have hc : (insert D ({T} : TripleSystemOn V)).card = 2 := by simp [hDT]
        exact h.full_middle_root_weight_le_uniform (insert D {T}) (by omega) (by omega))
    simpa only [mul_div_assoc, mul_assoc] using hb

theorem SourceVortexWellSpread.full_nonempty_pinned_terminal_edge_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (Q : TripleSystemOn V)
    (hQ : Q.Nonempty) (hQcard : Q.card ≤ j - 3)
    (e : Sym2 V) (hoff : ¬ e.IsDiag)
    (hout : ∀ T ∈ Q, e ∉ tripleEdgeFinset T)
    (G : ForbiddenFamilyOn V) (hG : G ⊆ familyExtensions F Q)
    (hcover : ∀ E ∈ G, ∃ D ∈ sourceTerminalEdgeFan W e, D ∈ E) :
    (∑ E ∈ G, setWeight (vortexTripleWeight W 1) (E \ Q)) ≤
      (ell + 1 : ℕ) * (j ^ ell : ℕ) * z / W.terminalSize := by
  by_cases htwo : 2 ≤ Q.card
  · apply ((sum_le_sum_of_subset_of_nonneg hG (fun _ _ _ ↦ zero_le)).trans
      (h.full_middle_root_weight_le_uniform Q htwo hQcard)).trans
    have hc : (1 : ℝ≥0) ≤ (ell + 1 : ℕ) := by exact_mod_cast (Nat.le_add_left 1 ell)
    calc
      (j ^ ell : ℕ) * z / (W.terminalSize : ℝ≥0) =
        1 * (j ^ ell : ℕ) * z / W.terminalSize := by rw [one_mul]
      _ ≤ _ := by gcongr
  · have hone : Q.card = 1 := by have := card_pos.mpr hQ; omega
    obtain ⟨T, rfl⟩ := card_eq_one.mp hone
    apply h.full_singleton_pinned_edge_weight_le T e hoff (hout T (mem_singleton_self T)) G hG
    intro E hE
    obtain ⟨D, hD, hDE⟩ := hcover E hE
    have hm := (mem_filter.mp hD).2
    have hDT : D ≠ T := by
      intro heq
      exact hout T (mem_singleton_self T) (heq ▸ hm.1)
    exact ⟨D, mem_erase.mpr ⟨hDT, hDE⟩, hm.1, fun _ ↦ hm.2⟩

end

end Erdos207
