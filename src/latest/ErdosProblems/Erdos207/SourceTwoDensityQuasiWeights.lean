/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiMomentWeights

/-! # Separate triangle and spoke densities for the source left moment -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem SourceQuasiMarking.full_weight_le_two_densities
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    {x : SourceQuasiMarking V} (hx : IsSourceQuasiMarking W F e S B x)
    (f₀ f₁ π : TripleOn V → ℝ≥0) (p pe : ℝ≥0) (hp : p ≤ 1)
    (h₀ : ∀ T, f₀ T ≤ π T) (h₁ : ∀ T, f₁ T ≤ p * π T) :
    setWeight (sourceQuasiWeight f₀ f₁ pe) (x.coordinates B) ≤
      (p * pe ^ B.card) * setWeight π (x.system \ {x.root}) := by
  have hpD : p ^ x.later.card ≤ p :=
    pow_le_of_le_one zero_le hp (Nat.ne_of_gt (card_pos.mpr hx.later_nonempty))
  rw [sourceQuasiWeight_factor]
  simp only [SourceQuasiMarking.coordinates, toLeft_disjSum, toRight_disjSum, sourceQuasiSpokes_card]
  calc
    _ ≤ setWeight π x.initial * setWeight (fun T ↦ p * π T) x.later * pe ^ B.card := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      exact mul_le_mul (prod_le_prod' (fun T _ ↦ h₀ T)) (prod_le_prod' (fun T _ ↦ h₁ T)) zero_le zero_le
    _ = p ^ x.later.card * pe ^ B.card * setWeight π (x.system \ {x.root}) := by
      rw [SourceQuasiMarking.remainder_eq hx]
      simp only [setWeight, prod_mul_distrib, prod_const, prod_union hx.disjoint]
      ring
    _ ≤ _ := by gcongr

theorem SourceVortexWellSpread.sourceQuasi_empty_two_density_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) {e : Sym2 V} {S B : Finset V}
    (hoff : ¬ e.IsDiag) (heB : e.toFinset ⊆ B)
    (f₀ f₁ : TripleOn V → ℝ≥0) (p pe : ℝ≥0) (hp : p ≤ 1)
    (h₀ : ∀ T, f₀ T ≤ vortexTripleWeight W 1 T)
    (h₁ : ∀ T, f₁ T ≤ p * vortexTripleWeight W 1 T) :
    extensionWeight (fun x : sourceQuasiMarkings W F e S B ↦ x.1.coordinates B)
      (sourceQuasiWeight f₀ f₁ pe) ∅ ≤
      (2 : ℝ≥0) ^ (j-2) * (j^ell : ℕ) * y * p * pe^B.card * S.card := by
  let A := sourceQuasiMarkings W F e S B
  let u := fun x : SourceQuasiMarking V ↦ setWeight (sourceQuasiWeight f₀ f₁ pe) (x.coordinates B)
  have hmap : ∀ x ∈ A, x.root ∈ sourceQuasiRootFan e S := fun x hx ↦
    SourceQuasiMarking.root_mem_fan (mem_sourceQuasiMarkings_iff.mp hx)
  have hfixed : ∀ T ∈ sourceQuasiRootFan e S,
      (∑ x ∈ A with x.root = T, u x) ≤
        (2 : ℝ≥0) ^ (j-2) * (p * pe^B.card) * ((j^ell : ℕ)*y) := by
    intro T _
    have ht := sourceQuasi_fixed_root_weight_transfer_le
      (fun E hE ↦ (h.uniform E hE).2) (fun E hE ↦ (h.uniform E hE).1) heB A (Subset.refl _)
      (vortexTripleWeight W 1) u (p * pe^B.card) T (fun x hx hroot ↦ by
        have hd := mem_sourceQuasiMarkings_iff.mp hx
        simpa only [hroot] using SourceQuasiMarking.full_weight_le_two_densities hd
          f₀ f₁ (vortexTripleWeight W 1) p pe hp h₀ h₁)
    apply ht.trans
    have hs := h.full_singleton_weight_le T
    have hj : j-3+1 ≤ j := by have := h.order; omega
    have hsingle : (∑ E ∈ familyExtensions F {T}, setWeight (vortexTripleWeight W 1) (E \ {T})) ≤
        (j^ell : ℕ)*y := hs.trans (by gcongr)
    exact mul_le_mul_of_nonneg_left hsingle zero_le
  rw [sourceQuasi_extension_eq_sum_filter]
  simp only [empty_subset, filter_true, sdiff_empty]
  change (∑ x ∈ A, u x) ≤ _
  rw [← sum_fiberwise_of_maps_to hmap u]
  calc
    _ ≤ ∑ _T ∈ sourceQuasiRootFan e S,
        (2 : ℝ≥0) ^ (j-2) * (p*pe^B.card) * ((j^ell : ℕ)*y) := sum_le_sum hfixed
    _ = (2 : ℝ≥0) ^ (j-2) * (j^ell : ℕ) * y * p * pe^B.card *
        (sourceQuasiRootFan e S).card := by simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := by gcongr; exact_mod_cast card_sourceQuasiRootFan_le e S hoff

theorem SourceVortexWellSpread.sourceQuasi_two_density_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) {e : Sym2 V} {S B : Finset V}
    (hoff : ¬ e.IsDiag) (heB : e.toFinset ⊆ B)
    (f₀ f₁ : TripleOn V → ℝ≥0) (p pe : ℝ≥0) (hp : p ≤ 1) (hpe : pe ≤ 1)
    (h₀ : ∀ T, f₀ T ≤ vortexTripleWeight W 1 T)
    (h₁ : ∀ T, f₁ T ≤ p * vortexTripleWeight W 1 T)
    (hscale : z ≤ y*p*pe^B.card*S.card) :
    HasExtensionBound (fun x : sourceQuasiMarkings W F e S B ↦ x.1.coordinates B)
      (sourceQuasiWeight f₀ f₁ pe)
      ((2 : ℝ≥0) ^ (j-2) * (ell+3 : ℕ) * (j^ell : ℕ) * y * p * pe^B.card * S.card) := by
  have h₁' : ∀ T, f₁ T ≤ vortexTripleWeight W 1 T := fun T ↦
    (h₁ T).trans (mul_le_of_le_one_left zero_le hp)
  have hconst : (1 : ℝ≥0) ≤ (ell+3 : ℕ) := by exact_mod_cast (show 1 ≤ ell+3 by omega)
  have hconst' : (2 : ℝ≥0) ≤ (ell+3 : ℕ) := by exact_mod_cast (show 2 ≤ ell+3 by omega)
  have hconst'' : ((ell+1 : ℕ) : ℝ≥0) ≤ (ell+3 : ℕ) := by exact_mod_cast (show ell+1 ≤ ell+3 by omega)
  intro H
  by_cases hH : H = ∅
  · subst H
    apply (h.sourceQuasi_empty_two_density_le hoff heB f₀ f₁ p pe hp h₀ h₁).trans
    calc
      _ = (2 : ℝ≥0) ^ (j-2) * 1 * (j^ell : ℕ) * y * p * pe^B.card * S.card := by rw [mul_one]
      _ ≤ _ := by gcongr
  by_cases hR : (sourceQuasiUnderlyingRoot H).Nonempty
  · apply (h.sourceQuasi_triangle_root_extension_le hoff heB f₀ f₁ pe hpe h₀ h₁' H hR).trans
    calc
      _ ≤ (2 : ℝ≥0) ^ (j-2) * (ell+1 : ℕ) * (j^ell : ℕ) * (y*p*pe^B.card*S.card) := by gcongr
      _ = (2 : ℝ≥0) ^ (j-2) * (ell+1 : ℕ) * (j^ell : ℕ) * y * p * pe^B.card * S.card := by ring
      _ ≤ _ := by gcongr
  · have hRempty := not_nonempty_iff_eq_empty.mp hR
    have hparts : H.toLeft.toLeft = ∅ ∧ H.toLeft.toRight = ∅ := union_eq_empty.mp hRempty
    have hleft : H.toLeft.card = 0 := by
      have hc := card_toLeft_add_card_toRight (u := H.toLeft)
      rw [hparts.1, hparts.2, card_empty] at hc
      omega
    have hedge : H.toRight.Nonempty := by
      apply card_pos.mp
      have hc := card_toLeft_add_card_toRight (u := H)
      have hh := card_pos.mpr (nonempty_iff_ne_empty.mpr hH)
      omega
    apply (h.sourceQuasi_edge_root_extension_le hoff heB f₀ f₁ pe hpe h₀ h₁' H hRempty hedge).trans
    calc
      _ ≤ (2 : ℝ≥0) ^ (j-2) * 2 * (j^ell : ℕ) * (y*p*pe^B.card*S.card) := by gcongr
      _ = (2 : ℝ≥0) ^ (j-2) * 2 * (j^ell : ℕ) * y * p * pe^B.card * S.card := by ring
      _ ≤ _ := by gcongr

theorem SourceVortexWellSpread.sourceLeft_canonical_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (e : Sym2 V) (S : Finset V) (hoff : ¬ e.IsDiag)
    (p r : ℝ≥0) (hp : p ≤ 1) (hr : r ≤ 1) (hscale : z ≤ y*r^2*p^3*S.card) :
    HasExtensionBound (fun x : sourceQuasiMarkings W F e S e.toFinset ↦ x.1.coordinates e.toFinset)
      (sourceQuasiWeight (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹) (vortexTripleWeight W p) (p*r))
      ((2 : ℝ≥0) ^ (j-2) * (ell+3 : ℕ) * (j^ell : ℕ) * y * r^2 * p^3 * S.card) := by
  have hpe : p*r ≤ 1 := (mul_le_of_le_one_right zero_le hr).trans hp
  have hscale' : z ≤ y*p*(p*r)^e.toFinset.card*S.card := by
    rw [Sym2.card_toFinset_of_not_isDiag e hoff]
    convert hscale using 1 <;> ring
  have hb := h.sourceQuasi_two_density_hasExtensionBound hoff (Subset.refl _)
    (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹) (vortexTripleWeight W p) p (p*r) hp hpe
    (W.ambient_inverse_le_triple_weight h.terminal_nonempty)
    (fun T ↦ by simp only [vortexTripleWeight]; exact le_of_eq (by ring)) hscale'
  intro H
  apply (hb H).trans_eq
  rw [Sym2.card_toFinset_of_not_isDiag e hoff]
  ring

end

end Erdos207
