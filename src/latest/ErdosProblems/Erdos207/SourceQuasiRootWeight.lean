/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiWeightTransfer

/-! # Nonempty-root weights for proper quasi-moment witnesses -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem SourceQuasiMarking.remove_root_weight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    {x : SourceQuasiMarking V} (hx : IsSourceQuasiMarking W F e S B x)
    (hn : 0 < W.terminalSize) (R : TripleSystemOn V) (hR : R ⊆ x.system \ {x.root}) :
    setWeight (vortexTripleWeight W 1) ((x.system \ {x.root}) \ R) =
      W.terminalSize * setWeight (vortexTripleWeight W 1) (x.system \ R) := by
  have hroot : x.root ∉ R := by
    intro hr
    exact (mem_sdiff.mp (hR hr)).2 (mem_singleton_self _)
  have hnot : x.root ∉ (x.system \ {x.root}) \ R := by simp
  have hset : x.system \ R = insert x.root ((x.system \ {x.root}) \ R) := by
    ext T
    simp only [mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hT, hTR⟩
      by_cases heq : T = x.root
      · exact Or.inl heq
      · exact Or.inr ⟨⟨hT, heq⟩, hTR⟩
    · rintro (rfl | hT)
      · exact ⟨mem_insert_self _ _, hroot⟩
      · exact ⟨hT.1.1, hT.2⟩
  have hwroot : vortexTripleWeight W 1 x.root = 1 / (W.terminalSize : ℝ≥0) := by
    rw [vortexTripleWeight, hx.terminal]
    rfl
  rw [hset]
  simp only [setWeight, prod_insert hnot, hwroot]
  have hn' : (W.terminalSize : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp

theorem SourceVortexWellSpread.sourceQuasi_triangle_root_extension_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) {e : Sym2 V} {S B : Finset V}
    (hoff : ¬ e.IsDiag) (heB : e.toFinset ⊆ B)
    (f₀ f₁ : TripleOn V → ℝ≥0) (p : ℝ≥0) (hp : p ≤ 1)
    (h₀ : ∀ T, f₀ T ≤ vortexTripleWeight W 1 T)
    (h₁ : ∀ T, f₁ T ≤ vortexTripleWeight W 1 T)
    (H : Finset (SourceQuasiCoordinate V)) (hRne : (sourceQuasiUnderlyingRoot H).Nonempty) :
    extensionWeight (fun x : sourceQuasiMarkings W F e S B ↦ x.1.coordinates B)
      (sourceQuasiWeight f₀ f₁ p) H ≤
      (2 : ℝ≥0) ^ (j - 2) * (ell + 1 : ℕ) * (j ^ ell : ℕ) * z := by
  let A := (sourceQuasiMarkings W F e S B).filter (fun x ↦ H ⊆ x.coordinates B)
  let G := A.image SourceQuasiMarking.system
  let R := sourceQuasiUnderlyingRoot H
  have hA : A ⊆ sourceQuasiMarkings W F e S B := filter_subset _ _
  have hGF : G ⊆ F := by
    intro E hE
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hE
    exact (mem_sourceQuasiMarkings_iff.mp (hA hx)).mem_family
  have hGR : G ⊆ familyExtensions F R := by
    intro E hE
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hE
    have hd := mem_sourceQuasiMarkings_iff.mp (hA hx)
    exact mem_familyExtensions_iff.mpr ⟨hd.mem_family,
      (SourceQuasiMarking.rooted_constraints hd (mem_filter.mp hx).2).1.trans sdiff_subset⟩
  by_cases hAn : A.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hAn
    have hd₀ := mem_sourceQuasiMarkings_iff.mp (hA hx₀)
    have hR₀ := (SourceQuasiMarking.rooted_constraints hd₀ (mem_filter.mp hx₀).2).1
    have hRcard : R.card ≤ j - 3 := by
      have hb := card_le_card hR₀
      rw [card_sdiff_of_subset (show ({x₀.root} : TripleSystemOn V) ⊆ x₀.system from
          singleton_subset_iff.mpr (mem_insert_self _ _)),
        (h.uniform x₀.system hd₀.mem_family).1, card_singleton] at hb
      dsimp only [R]
      omega
    have hout : ∀ T ∈ R, e ∉ tripleEdgeFinset T := by
      intro T hT heT
      have hT' := mem_sdiff.mp (hR₀ hT)
      have heq := (h.uniform x₀.system hd₀.mem_family).2.eq_of_common_graph_edge
        hT'.1 (mem_insert_self _ _) heT hd₀.pin_mem
      exact hT'.2 (mem_singleton.mpr heq)
    have hcover : ∀ E ∈ G, ∃ T ∈ sourceTerminalEdgeFan W e, T ∈ E := by
      intro E hE
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hE
      have hd := mem_sourceQuasiMarkings_iff.mp (hA hx)
      exact ⟨x.root, mem_filter.mpr ⟨mem_univ _, hd.pin_mem, hd.terminal⟩, mem_insert_self _ _⟩
    have hsum := h.full_nonempty_pinned_terminal_edge_weight_le R hRne hRcard e hoff hout G hGR hcover
    have hb := sourceQuasi_weight_transfer_le
      (fun E hE ↦ (h.uniform E hE).2) (fun E hE ↦ (h.uniform E hE).1) heB A hA G hGF
      (fun x hx ↦ mem_image.mpr ⟨x, hx, rfl⟩)
      (fun x ↦ setWeight (sourceQuasiWeight f₀ f₁ p) (x.coordinates B \ H))
      (fun E ↦ W.terminalSize * setWeight (vortexTripleWeight W 1) (E \ R)) (fun x hx ↦ by
        have hd := mem_sourceQuasiMarkings_iff.mp (hA hx)
        have hh := (mem_filter.mp hx).2
        exact (SourceQuasiMarking.remainder_weight_le hd f₀ f₁ (vortexTripleWeight W 1) p hp h₀ h₁ hh).trans_eq
          (SourceQuasiMarking.remove_root_weight hd h.terminal_nonempty R
            (SourceQuasiMarking.rooted_constraints hd hh).1))
    rw [sourceQuasi_extension_eq_sum_filter]
    apply hb.trans
    rw [← mul_sum]
    calc
      _ ≤ (2 : ℝ≥0) ^ (j - 2) * (W.terminalSize *
          ((ell + 1 : ℕ) * (j ^ ell : ℕ) * z / W.terminalSize)) := by gcongr
      _ = _ := by
        have hn : (W.terminalSize : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt h.terminal_nonempty
        field_simp
  · rw [sourceQuasi_extension_eq_sum_filter]
    change (∑ x ∈ A, _) ≤ _
    rw [not_nonempty_iff_eq_empty.mp hAn, sum_empty]
    exact zero_le

theorem SourceVortexWellSpread.sourceQuasi_edge_root_extension_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) {e : Sym2 V} {S B : Finset V}
    (hoff : ¬ e.IsDiag) (heB : e.toFinset ⊆ B)
    (f₀ f₁ : TripleOn V → ℝ≥0) (p : ℝ≥0) (hp : p ≤ 1)
    (h₀ : ∀ T, f₀ T ≤ vortexTripleWeight W 1 T)
    (h₁ : ∀ T, f₁ T ≤ vortexTripleWeight W 1 T)
    (H : Finset (SourceQuasiCoordinate V)) (hR : sourceQuasiUnderlyingRoot H = ∅)
    (hedge : H.toRight.Nonempty) :
    extensionWeight (fun x : sourceQuasiMarkings W F e S B ↦ x.1.coordinates B)
      (sourceQuasiWeight f₀ f₁ p) H ≤
      (2 : ℝ≥0) ^ (j - 2) * 2 * (j ^ ell : ℕ) * z := by
  obtain ⟨a, ha⟩ := hedge
  let A := (sourceQuasiMarkings W F e S B).filter (fun x ↦ H ⊆ x.coordinates B)
  let u := fun x : SourceQuasiMarking V ↦
    setWeight (sourceQuasiWeight f₀ f₁ p) (x.coordinates B \ H)
  have hA : A ⊆ sourceQuasiMarkings W F e S B := filter_subset _ _
  have hmap : ∀ x ∈ A, x.root ∈ sourceQuasiRootFan e a.toFinset := by
    intro x hx
    have hd := mem_sourceQuasiMarkings_iff.mp (hA hx)
    exact mem_filter.mpr ⟨mem_univ _, x.vertex,
      SourceQuasiMarking.vertex_mem_edge hd (mem_filter.mp hx).2 ha, hd.root_vertices⟩
  have hfixed : ∀ T ∈ sourceQuasiRootFan e a.toFinset,
      (∑ x ∈ A with x.root = T, u x) ≤ (2 : ℝ≥0) ^ (j - 2) * ((j ^ ell : ℕ) * z) := by
    intro T _
    have hb := sourceQuasi_fixed_root_weight_transfer_le
      (fun E hE ↦ (h.uniform E hE).2) (fun E hE ↦ (h.uniform E hE).1) heB A hA
      (vortexTripleWeight W 1) u 1 T (fun x hx hroot ↦ by
        have hd := mem_sourceQuasiMarkings_iff.mp (hA hx)
        simpa only [hR, sdiff_empty, hroot, one_mul] using
          SourceQuasiMarking.remainder_weight_le hd f₀ f₁ (vortexTripleWeight W 1) p hp h₀ h₁
            (mem_filter.mp hx).2)
    apply hb.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (h.full_singleton_weight_le_uniform T)
      (show 0 ≤ (2 : ℝ≥0) ^ (j - 2) from zero_le)
  rw [sourceQuasi_extension_eq_sum_filter]
  change (∑ x ∈ A, u x) ≤ _
  rw [← sum_fiberwise_of_maps_to hmap u]
  calc
    _ ≤ ∑ _T ∈ sourceQuasiRootFan e a.toFinset,
        (2 : ℝ≥0) ^ (j - 2) * ((j ^ ell : ℕ) * z) := sum_le_sum hfixed
    _ = (2 : ℝ≥0) ^ (j - 2) * (sourceQuasiRootFan e a.toFinset).card * (j ^ ell : ℕ) * z := by
      simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := by
      gcongr
      have ha2 : a.toFinset.card ≤ 2 := by
        by_cases hdiag : a.IsDiag
        · rw [Sym2.card_toFinset_of_isDiag a hdiag]
          decide
        · rw [Sym2.card_toFinset_of_not_isDiag a hdiag]
      exact_mod_cast (card_sourceQuasiRootFan_le e a.toFinset hoff).trans ha2

end

end Erdos207
