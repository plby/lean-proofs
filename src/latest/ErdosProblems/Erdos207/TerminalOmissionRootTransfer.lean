/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGeneralMomentWeights

/-! # Moving prescribed selected triangles into the exposed root -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem terminalOmission_move_selected_to_root
    {V : Type*} [Fintype V] [DecidableEq V] {ell f : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {Q H : TripleSystemOn V}
    {x : TripleSystemOn V × TripleSystemOn V}
    (hx : x ∈ terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) f)
    (hH : H ⊆ x.2) :
    (x.1, x.2 \ H) ∈ terminalOmissionCodes W (familyExtensions F (Q ∪ H))
      (fun E ↦ E \ (Q ∪ H)) (f - H.card) := by
  have hm := mem_terminalOmissionCodes_iff.mp hx
  have hE := mem_familyExtensions_iff.mp hm.1
  have hA := mem_terminalRemainderChoices_iff.mp hm.2
  apply mem_terminalOmissionCodes_iff.mpr
  refine ⟨mem_familyExtensions_iff.mpr ⟨hE.1, union_subset hE.2 (hH.trans (hA.1.trans sdiff_subset))⟩,
    mem_terminalRemainderChoices_iff.mpr ⟨?_, ?_, ?_⟩⟩
  · intro T hT
    have ht := mem_sdiff.mp hT
    have he := mem_sdiff.mp (hA.1 ht.1)
    exact mem_sdiff.mpr ⟨he.1, fun hmem ↦ (mem_union.mp hmem).elim he.2 ht.2⟩
  · rw [card_sdiff_of_subset hH, hA.2.1]
  · intro T hT
    have ht := mem_sdiff.mp hT
    have he := mem_sdiff.mp ht.1
    have hn : T ∉ Q ∧ T ∉ H :=
      ⟨fun hT ↦ he.2 (mem_union_left _ hT), fun hT ↦ he.2 (mem_union_right _ hT)⟩
    apply hA.2.2 T
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨he.1, hn.1⟩, fun hTA ↦ ht.2 (mem_sdiff.mpr ⟨hTA, hn.2⟩)⟩

theorem selected_remainder_code_injOn
    {V : Type*} [DecidableEq V] (H : TripleSystemOn V)
    (S : Finset (TripleSystemOn V × TripleSystemOn V))
    (hH : ∀ x ∈ S, H ⊆ x.2) :
    Set.InjOn (fun x : TripleSystemOn V × TripleSystemOn V ↦ (x.1, x.2 \ H)) (S : Set _) := by
  intro x hx y hy heq
  have hfirst := congrArg Prod.fst heq
  have hsecond := congrArg Prod.snd heq
  change x.1 = y.1 at hfirst
  apply Prod.ext hfirst
  change x.2 \ H = y.2 \ H at hsecond
  calc
    x.2 = (x.2 \ H) ∪ H := (sdiff_union_of_subset (hH x hx)).symm
    _ = (y.2 \ H) ∪ H := by rw [hsecond]
    _ = y.2 := sdiff_union_of_subset (hH y hy)

theorem sourceRootOmission_remainder_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (Q H : TripleSystemOn V) (f : ℕ) (w : ℝ≥0) :
    (∑ x ∈ (terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) f).filter (fun x ↦ H ⊆ x.2),
      setWeight (vortexTripleWeight W w) (x.2 \ H)) ≤
      sourceRootOmissionWeight W F (Q ∪ H) (f - H.card) w := by
  classical
  let S := (terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) f).filter (fun x ↦ H ⊆ x.2)
  let code := fun x : TripleSystemOn V × TripleSystemOn V ↦ (x.1, x.2 \ H)
  have hinj : Set.InjOn code (S : Set _) :=
    selected_remainder_code_injOn H S (fun x hx ↦ (mem_filter.mp hx).2)
  have hsub : S.image code ⊆ terminalOmissionCodes W (familyExtensions F (Q ∪ H))
      (fun E ↦ E \ (Q ∪ H)) (f - H.card) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    exact terminalOmission_move_selected_to_root (mem_filter.mp hx).1 (mem_filter.mp hx).2
  change (∑ x ∈ S, setWeight (vortexTripleWeight W w) (code x).2) ≤ _
  rw [← sum_image (f := fun y : TripleSystemOn V × TripleSystemOn V ↦ setWeight (vortexTripleWeight W w) y.2) hinj]
  exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ zero_le)

end

end Erdos207
