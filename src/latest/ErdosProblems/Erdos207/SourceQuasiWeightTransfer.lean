/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiWeight
import ErdosProblems.Erdos207.SourceQuasiGeometry
import ErdosProblems.Erdos207.SourceLinkFiberWeight

/-! # Bounded-colouring transfer for quasi-moment weights -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem sourceQuasi_weight_transfer_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    (hpack : ∀ E ∈ F, IsPackingOn E) (hcard : ∀ E ∈ F, E.card = j - 2)
    (heB : e.toFinset ⊆ B) (A : Finset (SourceQuasiMarking V))
    (hA : A ⊆ sourceQuasiMarkings W F e S B)
    (G : ForbiddenFamilyOn V) (hGF : G ⊆ F)
    (hmap : ∀ x ∈ A, x.system ∈ G)
    (u : SourceQuasiMarking V → ℝ≥0) (v : TripleSystemOn V → ℝ≥0)
    (hw : ∀ x ∈ A, u x ≤ v x.system) :
    (∑ x ∈ A, u x) ≤ (2 : ℝ≥0) ^ (j - 2) * ∑ E ∈ G, v E := by
  have hb := sum_le_mul_sum_of_bounded_fibers A G SourceQuasiMarking.system u v
    (2 ^ (j - 2)) hmap (fun E hE ↦ by
      have hs : A.filter (fun x ↦ x.system = E) ⊆
          (sourceQuasiMarkings W F e S B).filter (fun x ↦ x.system = E) :=
        filter_subset_filter _ hA
      apply (card_le_card hs).trans
      simpa only [hcard E (hGF hE)] using
        card_sourceQuasiMarkings_system_fiber_le (W := W) (S := S) hpack heB E) hw
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hb

theorem sourceQuasi_fixed_root_weight_transfer_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    (hpack : ∀ E ∈ F, IsPackingOn E) (hcard : ∀ E ∈ F, E.card = j - 2)
    (heB : e.toFinset ⊆ B) (A : Finset (SourceQuasiMarking V))
    (hA : A ⊆ sourceQuasiMarkings W F e S B)
    (π : TripleOn V → ℝ≥0) (u : SourceQuasiMarking V → ℝ≥0) (c : ℝ≥0) (T : TripleOn V)
    (hw : ∀ x ∈ A, x.root = T → u x ≤ c * setWeight π (x.system \ {T})) :
    (∑ x ∈ A with x.root = T, u x) ≤
      (2 : ℝ≥0) ^ (j - 2) * c * ∑ E ∈ familyExtensions F {T}, setWeight π (E \ {T}) := by
  have hb := sourceQuasi_weight_transfer_le hpack hcard heB (A.filter (fun x ↦ x.root = T))
    ((filter_subset _ _).trans hA) (familyExtensions F {T})
    (fun E hE ↦ (mem_familyExtensions_iff.mp hE).1) (fun x hx ↦ by
      have hm := mem_filter.mp hx
      have hd := mem_sourceQuasiMarkings_iff.mp (hA hm.1)
      exact mem_familyExtensions_iff.mpr ⟨hd.mem_family,
        singleton_subset_iff.mpr (hm.2 ▸ (mem_insert_self x.root (x.initial ∪ x.later)))⟩)
    u (fun E ↦ c * setWeight π (E \ {T}))
    (fun x hx ↦ hw x (mem_filter.mp hx).1 (mem_filter.mp hx).2)
  simpa only [← mul_sum, ← mul_assoc] using hb

theorem sourceQuasi_extension_eq_sum_filter
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (e : Sym2 V) (S B : Finset V)
    (π : SourceQuasiCoordinate V → ℝ≥0) (H : Finset (SourceQuasiCoordinate V)) :
    extensionWeight (fun x : sourceQuasiMarkings W F e S B ↦ x.1.coordinates B) π H =
      ∑ x ∈ (sourceQuasiMarkings W F e S B).filter (fun x ↦ H ⊆ x.coordinates B),
        setWeight π (x.coordinates B \ H) := by
  unfold extensionWeight
  rw [sum_filter]
  exact (sum_subtype (sourceQuasiMarkings W F e S B)
    (p := fun x ↦ x ∈ sourceQuasiMarkings W F e S B) (fun _ ↦ Iff.rfl)
    (fun x ↦ if H ⊆ x.coordinates B then setWeight π (x.coordinates B \ H) else 0)).symm

theorem SourceVortexWellSpread.sourceQuasi_empty_extension_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) {e : Sym2 V} {S B : Finset V}
    (hoff : ¬ e.IsDiag) (heB : e.toFinset ⊆ B)
    (f₀ f₁ : TripleOn V → ℝ≥0) (p : ℝ≥0) (hp : p ≤ 1)
    (h₀ : ∀ T, f₀ T ≤ vortexTripleWeight W 1 T)
    (h₁ : ∀ T, f₁ T ≤ p * vortexTripleWeight W 1 T) :
    extensionWeight (fun x : sourceQuasiMarkings W F e S B ↦ x.1.coordinates B)
      (sourceQuasiWeight f₀ f₁ p) ∅ ≤
      (2 : ℝ≥0) ^ (j - 2) * (j ^ ell : ℕ) * y * p ^ (B.card + 1) * S.card := by
  let A := sourceQuasiMarkings W F e S B
  let u := fun x : SourceQuasiMarking V ↦ setWeight (sourceQuasiWeight f₀ f₁ p) (x.coordinates B)
  have hmap : ∀ x ∈ A, x.root ∈ sourceQuasiRootFan e S := fun x hx ↦
    SourceQuasiMarking.root_mem_fan (mem_sourceQuasiMarkings_iff.mp hx)
  have hfixed : ∀ T ∈ sourceQuasiRootFan e S,
      (∑ x ∈ A with x.root = T, u x) ≤
        (2 : ℝ≥0) ^ (j - 2) * p ^ (B.card + 1) * ((j ^ ell : ℕ) * y) := by
    intro T _
    have ht := sourceQuasi_fixed_root_weight_transfer_le
      (fun E hE ↦ (h.uniform E hE).2) (fun E hE ↦ (h.uniform E hE).1) heB A (Subset.refl _)
      (vortexTripleWeight W 1) u (p ^ (B.card + 1)) T (fun x hx hroot ↦ by
        have hd := mem_sourceQuasiMarkings_iff.mp hx
        simpa only [hroot] using SourceQuasiMarking.full_weight_le_density hd
          f₀ f₁ (vortexTripleWeight W 1) p hp h₀ h₁)
    apply ht.trans
    have hs := h.full_singleton_weight_le T
    have hj : j - 3 + 1 ≤ j := by have := h.order; omega
    have hsingle : (∑ E ∈ familyExtensions F {T}, setWeight (vortexTripleWeight W 1) (E \ {T})) ≤
        (j ^ ell : ℕ) * y := hs.trans (by gcongr)
    exact mul_le_mul_of_nonneg_left hsingle zero_le
  rw [sourceQuasi_extension_eq_sum_filter]
  simp only [empty_subset, filter_true, sdiff_empty]
  change (∑ x ∈ A, u x) ≤ _
  rw [← sum_fiberwise_of_maps_to hmap u]
  calc
    _ ≤ ∑ _T ∈ sourceQuasiRootFan e S,
        (2 : ℝ≥0) ^ (j - 2) * p ^ (B.card + 1) * ((j ^ ell : ℕ) * y) := sum_le_sum hfixed
    _ = (2 : ℝ≥0) ^ (j - 2) * (j ^ ell : ℕ) * y * p ^ (B.card + 1) *
        (sourceQuasiRootFan e S).card := by simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := by gcongr; exact_mod_cast card_sourceQuasiRootFan_le e S hoff

end

end Erdos207
