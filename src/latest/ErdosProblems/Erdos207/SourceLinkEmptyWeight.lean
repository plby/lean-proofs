/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkNonrootWeights
import ErdosProblems.Erdos207.SourceLinkFiberWeight

/-! # The sharp empty-root weight after summing the distinguished link fan -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceLink_fixed_root_weight_transfer_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    (hpack : ∀ E ∈ F, IsPackingOn E) (hcard : ∀ E ∈ F, E.card = j - 2)
    (π : TripleOn V → ℝ≥0) (u : SourceLinkMarking V → ℝ≥0) (c : ℝ≥0) (T : TripleOn V)
    (hweight : ∀ x ∈ sourceLinkMarkings W F e A, x.root = T →
      u x ≤ c * setWeight π (x.system \ {T})) :
    (∑ x ∈ sourceLinkMarkings W F e A with x.root = T, u x) ≤
      (4 : ℝ≥0) ^ (j - 2) * c * ∑ E ∈ familyExtensions F {T}, setWeight π (E \ {T}) := by
  classical
  let S := (sourceLinkMarkings W F e A).filter (fun x ↦ x.root = T)
  have hb := sum_le_mul_sum_of_bounded_fibers S (familyExtensions F {T}) SourceLinkMarking.system u
    (fun E ↦ c * setWeight π (E \ {T})) (4 ^ (j - 2)) (fun x hx ↦ by
      have hm := mem_filter.mp hx
      have hd : IsSourceLinkMarking W F e A x := (mem_filter.mp hm.1).2
      exact mem_familyExtensions_iff.mpr ⟨(sourceLinkUnderlyingFamily_data hd.1).1,
        singleton_subset_iff.mpr (hm.2 ▸ SourceLinkMarking.root_mem_system hd)⟩)
    (fun E hE ↦ by
      have hsub : S.filter (fun x ↦ x.system = E) ⊆
          (sourceLinkMarkings W F e A).filter (fun x ↦ x.system = E) := by
        intro x hx
        have hm := mem_filter.mp hx
        exact mem_filter.mpr ⟨(mem_filter.mp hm.1).1, hm.2⟩
      have hh := card_sourceLinkMarkings_system_fiber_le (W := W) (e := e) (A := A) hpack E
      rw [hcard E (mem_familyExtensions_iff.mp hE).1] at hh
      exact (card_le_card hsub).trans hh)
    (fun x hx ↦ hweight x (mem_filter.mp hx).1 (mem_filter.mp hx).2)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, ← mul_sum, ← mul_assoc] using hb

theorem SourceVortexWellSpread.sourceLink_empty_extension_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) {e : Sym2 V} {A : TripleSystemOn V}
    (f₀ f₁ f₂ : TripleOn V → ℝ≥0) (fe : Sym2 V → ℝ≥0) (p r₀ : ℝ≥0) (hp : p ≤ 1)
    (h₀ : ∀ T, f₀ T ≤ vortexTripleWeight W 1 T)
    (h₁ : ∀ T, f₁ T ≤ p * vortexTripleWeight W 1 T)
    (h₂ : ∀ T ∈ A, f₂ T * setWeight fe (tripleEdgeFinset T) ≤ p * vortexTripleWeight W 1 T)
    (hr₀ : ∀ T ∈ sourceTerminalEdgeFan W e ∩ A,
      f₂ T * setWeight fe ((tripleEdgeFinset T).erase e) ≤ r₀)
    (hbudget : ((sourceTerminalEdgeFan W e ∩ A).card : ℝ≥0) * r₀ * p ≤ 1) :
    extensionWeight (fun x : sourceLinkMarkings W F e A ↦ x.1.coordinates e)
      (sourceLinkMixedWeight f₀ f₁ f₂ fe) ∅ ≤
      (4 : ℝ≥0) ^ (j - 2) * (j ^ ell : ℕ) * y := by
  classical
  let B := sourceTerminalEdgeFan W e ∩ A
  let u : SourceLinkMarking V → ℝ≥0 := fun x ↦
    setWeight (sourceLinkMixedWeight f₀ f₁ f₂ fe) (x.coordinates e)
  have hroot : ∀ x ∈ sourceLinkMarkings W F e A, x.root ∈ B := by
    intro x hx
    have hd : IsSourceLinkMarking W F e A x := (mem_filter.mp hx).2
    exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hd.2.2.2.2.1, hd.2.2.2.2.2.1⟩,
      hd.2.2.2.2.2.2.1 hd.2.2.2.1⟩
  have hfixed : ∀ T ∈ B, (∑ x ∈ sourceLinkMarkings W F e A with x.root = T, u x) ≤
      (4 : ℝ≥0) ^ (j - 2) * (r₀ * p) * ((j ^ ell : ℕ) * y) := by
    intro T _hT
    have hb := sourceLink_fixed_root_weight_transfer_le (W := W) (e := e) (A := A)
      (fun E hE ↦ (h.uniform E hE).2) (fun E hE ↦ (h.uniform E hE).1)
      (vortexTripleWeight W 1) u (r₀ * p) T (fun x hx hT ↦ by
        have hd : IsSourceLinkMarking W F e A x := (mem_filter.mp hx).2
        have hpck := (h.uniform x.system (sourceLinkUnderlyingFamily_data hd.1).1).2
        have hnon := SourceLinkMarking.nonroot_block_weight_le_density hd f₀ f₁ f₂
          (vortexTripleWeight W 1) fe p hp (fun D _ ↦ h₀ D) (fun D _ ↦ h₁ D)
          (fun D hD ↦ h₂ D (hd.2.2.2.2.2.2.1 (mem_erase.mp hD).2))
        have hrootwt := hr₀ x.root (hroot x hx)
        calc
          u x = (f₂ x.root * setWeight fe ((tripleEdgeFinset x.root).erase e)) *
              (setWeight f₀ x.initial * setWeight f₁ x.later *
                ∏ D ∈ x.candidate.erase x.root, f₂ D * setWeight fe (tripleEdgeFinset D)) := by
            dsimp only [u]
            rw [SourceLinkMarking.full_coordinate_weight_factor hd hpck]
            ring
          _ ≤ r₀ * (p * setWeight (vortexTripleWeight W 1) (x.system \ {x.root})) := by gcongr
          _ = _ := by rw [hT, mul_assoc])
    have hu := h.full_singleton_weight_le T
    have hj : j - 3 + 1 ≤ j := by have := h.order; omega
    apply hb.trans
    calc
      _ ≤ (4 : ℝ≥0) ^ (j - 2) * (r₀ * p) * (((j - 3 + 1) ^ ell : ℕ) * y) := by gcongr
      _ ≤ _ := by gcongr
  have hexpr : extensionWeight (fun x : sourceLinkMarkings W F e A ↦ x.1.coordinates e)
      (sourceLinkMixedWeight f₀ f₁ f₂ fe) ∅ = ∑ x ∈ sourceLinkMarkings W F e A, u x := by
    unfold extensionWeight
    simp only [empty_subset, if_true, sdiff_empty]
    exact (Finset.sum_subtype (sourceLinkMarkings W F e A)
      (p := fun x ↦ x ∈ sourceLinkMarkings W F e A) (fun _ ↦ Iff.rfl) u).symm
  rw [hexpr, ← sum_fiberwise_of_maps_to hroot u]
  calc
    _ ≤ ∑ _T ∈ B, (4 : ℝ≥0) ^ (j - 2) * (r₀ * p) * ((j ^ ell : ℕ) * y) := sum_le_sum hfixed
    _ = ((B.card : ℝ≥0) * r₀ * p) * ((4 : ℝ≥0) ^ (j - 2) * (j ^ ell : ℕ) * y) := by
      simp only [sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_of_le_one_left zero_le hbudget

end

end Erdos207
