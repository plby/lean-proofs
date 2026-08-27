/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkEmptyWeight
import ErdosProblems.Erdos207.SourceLinkExceptionalWeight
import ErdosProblems.Erdos207.SourceLinkNonexceptionalWeight

/-! # A complete finite maximum-extension bound for the source link moment

The hypotheses expose the pointwise and edge-block inequalities which the
canonical source weights must satisfy. No extension bound is assumed.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceVortexWellSpread.sourceLink_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V] {ell j q : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) {e : Sym2 V} {A : TripleSystemOn V}
    (hoff : ¬ e.IsDiag) (hjq : j ≤ q) (hy : 1 ≤ y)
    (f₀ f₁ f₂ : TripleOn V → ℝ≥0) (fe : Sym2 V → ℝ≥0) (p w r₀ : ℝ≥0)
    (hp : p ≤ 1) (hw : 1 ≤ w)
    (h₀ : ∀ T, f₀ T ≤ vortexTripleWeight W 1 T)
    (h₁ : ∀ T, f₁ T ≤ p * vortexTripleWeight W 1 T)
    (h₂ : ∀ T ∈ A, f₂ T ≤ w * vortexTripleWeight W 1 T)
    (hblock : ∀ T ∈ A, f₂ T * setWeight fe (tripleEdgeFinset T) ≤ p * vortexTripleWeight W 1 T)
    (he : ∀ f, fe f ≤ 1)
    (hr₀ : ∀ T ∈ sourceTerminalEdgeFan W e ∩ A,
      f₂ T * setWeight fe ((tripleEdgeFinset T).erase e) ≤ r₀)
    (hbudget : ((sourceTerminalEdgeFan W e ∩ A).card : ℝ≥0) * r₀ * p ≤ 1)
    (hscale : z * w ^ (q + 1) / W.terminalSize ≤ y) :
    HasExtensionBound (fun x : sourceLinkMarkings W F e A ↦ x.1.coordinates e)
      (sourceLinkMixedWeight f₀ f₁ f₂ fe)
      ((4 : ℝ≥0) ^ (j - 2) * ((1 + (ell + 1) ^ 2 : ℕ) * (j ^ ell : ℕ)) * y) := by
  classical
  have h₀' : ∀ T, f₀ T ≤ w * vortexTripleWeight W 1 T := by
    intro T
    exact (h₀ T).trans (le_mul_of_one_le_left zero_le hw)
  have h₁' : ∀ T, f₁ T ≤ w * vortexTripleWeight W 1 T := by
    intro T
    exact (h₁ T).trans (mul_le_mul_of_nonneg_right (hp.trans hw) zero_le)
  have hK : (1 : ℝ≥0) ≤ (1 + (ell + 1) ^ 2 : ℕ) := by exact_mod_cast (Nat.le_add_right 1 _)
  have hJ : (1 : ℝ≥0) ≤ (j ^ ell : ℕ) := by
    exact_mod_cast (one_le_pow₀ (show 1 ≤ j by have := h.order; omega) : 1 ≤ j ^ ell)
  have hsmall : (4 : ℝ≥0) ^ (j - 2) * (j ^ ell : ℕ) * y ≤
      (4 : ℝ≥0) ^ (j - 2) * ((1 + (ell + 1) ^ 2 : ℕ) * (j ^ ell : ℕ)) * y := by
    calc
      _ = (4 : ℝ≥0) ^ (j - 2) * (1 * (j ^ ell : ℕ)) * y := by rw [one_mul]
      _ ≤ _ := by gcongr
  intro H
  by_cases hHempty : H = ∅
  · subst H
    exact (h.sourceLink_empty_extension_le f₀ f₁ f₂ fe p r₀ hp h₀ h₁ hblock hr₀ hbudget).trans hsmall
  by_cases hwitness : ∃ x ∈ sourceLinkMarkings W F e A, H ⊆ x.coordinates e
  · obtain ⟨x, hx, hHx⟩ := hwitness
    have hd : IsSourceLinkMarking W F e A x := (mem_filter.mp hx).2
    have hc := SourceLinkMarking.rooted_coordinate_constraints hd hHx
    have hcard : (sourceLinkUnderlyingRoot H).card ≤ j - 2 :=
      (card_le_card hc.2.2.1).trans_eq (h.uniform x.system (sourceLinkUnderlyingFamily_data hd.1).1).1
    by_cases hfull : (sourceLinkUnderlyingRoot H).card = j - 2
    · apply (h.sourceLink_full_root_extension_le f₀ f₁ f₂ fe w h₀' h₁' h₂ he H hfull).trans
      have hfac := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hJ) hy
      calc
        _ = (4 : ℝ≥0) ^ (j - 2) * 1 := (mul_one _).symm
        _ ≤ (4 : ℝ≥0) ^ (j - 2) * (((1 + (ell + 1) ^ 2 : ℕ) * (j ^ ell : ℕ)) * y) := by gcongr
        _ = _ := (mul_assoc _ _ _).symm
    · by_cases hex : IsSourceLinkExceptionalRoot e (sourceLinkUnderlyingRoot H) H.toRight
      · exact (h.sourceLink_exceptional_extension_le f₀ f₁ f₂ fe p hp h₀ h₁ hblock he H hex).trans hsmall
      · exact h.sourceLink_nonexceptional_extension_le f₀ f₁ f₂ fe w h₀' h₁' h₂ he hw hjq hscale H
          hoff hc.1 hc.2.1 (hc.2.2.2 (nonempty_iff_ne_empty.mpr hHempty)) (by omega) hex
  · have hz : extensionWeight (fun x : sourceLinkMarkings W F e A ↦ x.1.coordinates e)
        (sourceLinkMixedWeight f₀ f₁ f₂ fe) H = 0 := by
      unfold extensionWeight
      apply sum_eq_zero
      intro x _
      exact if_neg (fun hHx ↦ hwitness ⟨x.1, x.2, hHx⟩)
    rw [hz]
    exact zero_le

end

end Erdos207
