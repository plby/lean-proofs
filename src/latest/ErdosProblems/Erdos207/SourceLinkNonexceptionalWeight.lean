/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkFiberWeight

/-! # Marked link weights: nonexceptional and fully fixed triangle roots -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceVortexWellSpread.sourceLink_nonexceptional_extension_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j q : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) {e : Sym2 V} {A : TripleSystemOn V}
    (f₀ f₁ f₂ : TripleOn V → ℝ≥0) (fe : Sym2 V → ℝ≥0) (w : ℝ≥0)
    (h₀ : ∀ T, f₀ T ≤ w * vortexTripleWeight W 1 T)
    (h₁ : ∀ T, f₁ T ≤ w * vortexTripleWeight W 1 T)
    (h₂ : ∀ T ∈ A, f₂ T ≤ w * vortexTripleWeight W 1 T)
    (he : ∀ f, fe f ≤ 1) (hw : 1 ≤ w) (hjq : j ≤ q)
    (hscale : z * w ^ (q + 1) / W.terminalSize ≤ y)
    (H : Finset (SourceLinkCoordinate V)) (hoff : ¬ e.IsDiag) (hpin : e ∉ H.toRight)
    (hedges : ∀ f ∈ H.toRight, ¬ f.IsDiag)
    (hroot : (sourceLinkUnderlyingRoot H).Nonempty ∨ H.toRight.Nonempty)
    (hcard : (sourceLinkUnderlyingRoot H).card ≤ j - 3)
    (hexception : ¬ IsSourceLinkExceptionalRoot e (sourceLinkUnderlyingRoot H) H.toRight) :
    extensionWeight (fun x : sourceLinkMarkings W F e A ↦ x.1.coordinates e)
      (sourceLinkMixedWeight f₀ f₁ f₂ fe) H ≤
      (4 : ℝ≥0) ^ (j - 2) * ((1 + (ell + 1) ^ 2 : ℕ) * (j ^ ell : ℕ)) * y := by
  have hb := sourceLink_crude_extension_weight_le (W := W) (e := e) (A := A)
    (fun E hE ↦ (h.uniform E hE).2)
    (fun E hE ↦ (h.uniform E hE).1) f₀ f₁ f₂ (vortexTripleWeight W 1) fe w h₀ h₁ h₂ he H
  have hu := h.link_underlying_nonexceptional_weight_le e hoff (sourceLinkUnderlyingRoot H)
    H.toRight hpin hedges hroot hcard hexception
  have hw' : w ^ (j - 2 - (sourceLinkUnderlyingRoot H).card) ≤ w ^ (q + 1) :=
    pow_le_pow_right₀ hw (by omega)
  apply hb.trans
  calc
    _ ≤ (4 : ℝ≥0) ^ (j - 2) * w ^ (j - 2 - (sourceLinkUnderlyingRoot H).card) *
        ((1 + (ell + 1) ^ 2 : ℕ) * (j ^ ell : ℕ) * z / W.terminalSize) := by gcongr
    _ = (4 : ℝ≥0) ^ (j - 2) * ((1 + (ell + 1) ^ 2 : ℕ) * (j ^ ell : ℕ)) *
        (z * w ^ (j - 2 - (sourceLinkUnderlyingRoot H).card) / W.terminalSize) := by ring
    _ ≤ (4 : ℝ≥0) ^ (j - 2) * ((1 + (ell + 1) ^ 2 : ℕ) * (j ^ ell : ℕ)) *
        (z * w ^ (q + 1) / W.terminalSize) := by gcongr
    _ ≤ _ := by gcongr

theorem SourceVortexWellSpread.sourceLink_full_root_extension_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) {e : Sym2 V} {A : TripleSystemOn V}
    (f₀ f₁ f₂ : TripleOn V → ℝ≥0) (fe : Sym2 V → ℝ≥0) (w : ℝ≥0)
    (h₀ : ∀ T, f₀ T ≤ w * vortexTripleWeight W 1 T)
    (h₁ : ∀ T, f₁ T ≤ w * vortexTripleWeight W 1 T)
    (h₂ : ∀ T ∈ A, f₂ T ≤ w * vortexTripleWeight W 1 T)
    (he : ∀ f, fe f ≤ 1) (H : Finset (SourceLinkCoordinate V))
    (hcard : (sourceLinkUnderlyingRoot H).card = j - 2) :
    extensionWeight (fun x : sourceLinkMarkings W F e A ↦ x.1.coordinates e)
      (sourceLinkMixedWeight f₀ f₁ f₂ fe) H ≤ (4 : ℝ≥0) ^ (j - 2) := by
  have hb := sourceLink_crude_extension_weight_le (W := W) (e := e) (A := A)
    (fun E hE ↦ (h.uniform E hE).2)
    (fun E hE ↦ (h.uniform E hE).1) f₀ f₁ f₂ (vortexTripleWeight W 1) fe w h₀ h₁ h₂ he H
  rw [hcard, Nat.sub_self, pow_zero, mul_one] at hb
  have hsub : familyExtensions (sourceLinkUnderlyingFamily W F e H.toRight) (sourceLinkUnderlyingRoot H) ⊆
      familyExtensions F (sourceLinkUnderlyingRoot H) := by
    intro E hE
    have hm := mem_familyExtensions_iff.mp hE
    exact mem_familyExtensions_iff.mpr ⟨(sourceLinkUnderlyingFamily_data hm.1).1, hm.2⟩
  have hu := (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ zero_le)).trans
    (h.full_all_root_weight_le_one (sourceLinkUnderlyingRoot H) hcard)
  exact hb.trans (mul_le_of_le_one_right zero_le hu)

end

end Erdos207
