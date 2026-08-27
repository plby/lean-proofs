/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkRootCoordinates
import ErdosProblems.Erdos207.SourceLinkFiberWeight

/-! # The sharp exceptional-root bound in the source link moment -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceVortexWellSpread.sourceLink_exceptional_extension_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) {e : Sym2 V} {A : TripleSystemOn V}
    (f₀ f₁ f₂ : TripleOn V → ℝ≥0) (fe : Sym2 V → ℝ≥0) (p : ℝ≥0) (hp : p ≤ 1)
    (h₀ : ∀ T, f₀ T ≤ vortexTripleWeight W 1 T)
    (h₁ : ∀ T, f₁ T ≤ p * vortexTripleWeight W 1 T)
    (h₂ : ∀ T ∈ A, f₂ T * setWeight fe (tripleEdgeFinset T) ≤ p * vortexTripleWeight W 1 T)
    (he : ∀ f, fe f ≤ 1) (H : Finset (SourceLinkCoordinate V))
    (hex : IsSourceLinkExceptionalRoot e (sourceLinkUnderlyingRoot H) H.toRight) :
    extensionWeight (fun x : sourceLinkMarkings W F e A ↦ x.1.coordinates e)
      (sourceLinkMixedWeight f₀ f₁ f₂ fe) H ≤
      (4 : ℝ≥0) ^ (j - 2) * (j ^ ell : ℕ) * y := by
  classical
  have hweight : ∀ x ∈ sourceLinkMarkings W F e A, H ⊆ x.coordinates e →
      setWeight (sourceLinkMixedWeight f₀ f₁ f₂ fe) (x.coordinates e \ H) ≤
        1 * setWeight (vortexTripleWeight W 1) (x.system \ sourceLinkUnderlyingRoot H) := by
    intro x hx hH
    have hd : IsSourceLinkMarking W F e A x := (mem_filter.mp hx).2
    have hpack := (h.uniform x.system (sourceLinkUnderlyingFamily_data hd.1).1).2
    have hr := SourceLinkMarking.exceptional_root_coordinates hd hpack hH hex
    have hblock := SourceLinkMarking.deleted_root_coordinate_weight_le hd hpack f₀ f₁ f₂ fe he H hr.1 hr.2.1
    have hb := SourceLinkMarking.nonroot_block_weight_le_density hd f₀ f₁ f₂ (vortexTripleWeight W 1) fe p hp
      (fun T _ ↦ h₀ T) (fun T _ ↦ h₁ T)
      (fun T hT ↦ h₂ T (hd.2.2.2.2.2.2.1 (mem_erase.mp hT).2))
    rw [one_mul, hr.2.2]
    exact (hblock.trans hb).trans (mul_le_of_le_one_left zero_le hp)
  have hb := sourceLink_rooted_weight_transfer_le (W := W) (e := e) (A := A)
    (fun E hE ↦ (h.uniform E hE).2) (fun E hE ↦ (h.uniform E hE).1)
    (vortexTripleWeight W 1) _ 1 H hweight
  have hexpr : extensionWeight (fun x : sourceLinkMarkings W F e A ↦ x.1.coordinates e)
      (sourceLinkMixedWeight f₀ f₁ f₂ fe) H =
      ∑ x ∈ sourceLinkMarkings W F e A, if H ⊆ x.coordinates e then
        setWeight (sourceLinkMixedWeight f₀ f₁ f₂ fe) (x.coordinates e \ H) else 0 := by
    unfold extensionWeight
    exact (Finset.sum_subtype (sourceLinkMarkings W F e A)
      (p := fun x ↦ x ∈ sourceLinkMarkings W F e A) (fun _ ↦ Iff.rfl)
      (fun x ↦ if H ⊆ x.coordinates e then
        setWeight (sourceLinkMixedWeight f₀ f₁ f₂ fe) (x.coordinates e \ H) else 0)).symm
  rw [hexpr]
  apply hb.trans
  obtain ⟨T, hT, _⟩ := hex
  rw [mul_one, hT]
  have hsub : familyExtensions (sourceLinkUnderlyingFamily W F e H.toRight) {T} ⊆ familyExtensions F {T} := by
    intro E hE
    have hm := mem_familyExtensions_iff.mp hE
    exact mem_familyExtensions_iff.mpr ⟨(sourceLinkUnderlyingFamily_data hm.1).1, hm.2⟩
  have hu := (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ zero_le)).trans
    (h.full_singleton_weight_le T)
  have hj : j - 3 + 1 ≤ j := by have := h.order; omega
  calc
    _ ≤ (4 : ℝ≥0) ^ (j - 2) * (((j - 3 + 1) ^ ell : ℕ) * y) := by gcongr
    _ ≤ (4 : ℝ≥0) ^ (j - 2) * ((j ^ ell : ℕ) * y) := by gcongr
    _ = _ := (mul_assoc _ _ _).symm

end

end Erdos207
