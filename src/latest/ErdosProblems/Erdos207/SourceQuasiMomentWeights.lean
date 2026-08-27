/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiRootWeight
import ErdosProblems.Erdos207.SourceLinkCanonicalMoment

/-! # Complete maximum-extension bound for the proper quasi-moment -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem SourceVortexWellSpread.sourceQuasi_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V] {ell j hmax : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) {e : Sym2 V} {S B : Finset V}
    (hoff : ¬ e.IsDiag) (heB : e.toFinset ⊆ B) (hB : B.card ≤ hmax)
    (f₀ f₁ : TripleOn V → ℝ≥0) (p : ℝ≥0) (hp : p ≤ 1)
    (h₀ : ∀ T, f₀ T ≤ vortexTripleWeight W 1 T)
    (h₁ : ∀ T, f₁ T ≤ p * vortexTripleWeight W 1 T)
    (hscale : z ≤ y * p ^ (hmax + 1) * S.card) :
    HasExtensionBound (fun x : sourceQuasiMarkings W F e S B ↦ x.1.coordinates B)
      (sourceQuasiWeight f₀ f₁ p)
      ((2 : ℝ≥0) ^ (j - 2) * (ell + 3 : ℕ) * (j ^ ell : ℕ) * y * p ^ (B.card + 1) * S.card) := by
  have h₁' : ∀ T, f₁ T ≤ vortexTripleWeight W 1 T := fun T ↦
    (h₁ T).trans (mul_le_of_le_one_left zero_le hp)
  have hz : z ≤ y * p ^ (B.card + 1) * S.card := by
    apply hscale.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (NNReal.pow_antitone_exp _ _ (Nat.add_le_add_right hB 1) hp) zero_le) zero_le
  have hconst : (1 : ℝ≥0) ≤ (ell + 3 : ℕ) := by exact_mod_cast (show 1 ≤ ell + 3 by omega)
  have hconst' : (2 : ℝ≥0) ≤ (ell + 3 : ℕ) := by exact_mod_cast (show 2 ≤ ell + 3 by omega)
  have hconst'' : ((ell + 1 : ℕ) : ℝ≥0) ≤ (ell + 3 : ℕ) := by
    exact_mod_cast (show ell + 1 ≤ ell + 3 by omega)
  intro H
  by_cases hH : H = ∅
  · subst H
    apply (h.sourceQuasi_empty_extension_le hoff heB f₀ f₁ p hp h₀ h₁).trans
    calc
      _ = (2 : ℝ≥0) ^ (j - 2) * 1 * (j ^ ell : ℕ) * y * p ^ (B.card + 1) * S.card := by rw [mul_one]
      _ ≤ _ := by gcongr
  by_cases hR : (sourceQuasiUnderlyingRoot H).Nonempty
  · apply (h.sourceQuasi_triangle_root_extension_le hoff heB f₀ f₁ p hp h₀ h₁' H hR).trans
    calc
      _ ≤ (2 : ℝ≥0) ^ (j - 2) * (ell + 1 : ℕ) * (j ^ ell : ℕ) *
          (y * p ^ (B.card + 1) * S.card) := by gcongr
      _ = (2 : ℝ≥0) ^ (j - 2) * (ell + 1 : ℕ) * (j ^ ell : ℕ) * y * p ^ (B.card + 1) * S.card := by ring
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
    apply (h.sourceQuasi_edge_root_extension_le hoff heB f₀ f₁ p hp h₀ h₁' H hRempty hedge).trans
    calc
      _ ≤ (2 : ℝ≥0) ^ (j - 2) * 2 * (j ^ ell : ℕ) * (y * p ^ (B.card + 1) * S.card) := by gcongr
      _ = (2 : ℝ≥0) ^ (j - 2) * 2 * (j ^ ell : ℕ) * y * p ^ (B.card + 1) * S.card := by ring
      _ ≤ _ := by gcongr

theorem SourceVortexWellSpread.sourceQuasi_canonical_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V] {ell j hmax : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) {e : Sym2 V} {S B : Finset V}
    (hoff : ¬ e.IsDiag) (heB : e.toFinset ⊆ B) (hB : B.card ≤ hmax)
    (p : ℝ≥0) (hp : p ≤ 1) (hscale : z ≤ y * p ^ (hmax + 1) * S.card) :
    HasExtensionBound (fun x : sourceQuasiMarkings W F e S B ↦ x.1.coordinates B)
      (sourceQuasiWeight (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹) (vortexTripleWeight W p) p)
      ((2 : ℝ≥0) ^ (j - 2) * (ell + 3 : ℕ) * (j ^ ell : ℕ) * y * p ^ (B.card + 1) * S.card) := by
  apply h.sourceQuasi_hasExtensionBound hoff heB hB _ _ p hp
    (W.ambient_inverse_le_triple_weight h.terminal_nonempty) _ hscale
  intro T
  simp only [vortexTripleWeight]
  exact le_of_eq (by ring)

end

end Erdos207
