/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TerminalOmissionRootTransfer

/-! # Full source extension bounds for the first generalized crude statistic -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceOmission_extension_power_ratio
    (n : ℝ≥0) (hn : 0 < n) (j r f h : ℕ) (hfit : r + f + 3 ≤ j) (hh : h ≤ f) :
    n ^ (j - (r + h + 3)) / n ^ (f - h) = n ^ (j - r - 3 - f) := by
  have he : j - (r + h + 3) = (f - h) + (j - r - 3 - f) := by omega
  rw [he, pow_add, mul_div_cancel_left₀ _ (pow_ne_zero _ hn.ne')]

theorem SourceVortexWellSpread.root_omission_extension_sum_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j f : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (Q : TripleSystemOn V)
    (hQ : 2 ≤ Q.card) (hfit : Q.card + f + 3 ≤ j) (w : ℝ≥0) (hw : 1 ≤ w)
    (H : TripleSystemOn V) :
    (∑ x ∈ (terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) f).filter (fun x ↦ H ⊆ x.2),
      setWeight (vortexTripleWeight W w) (x.2 \ H)) ≤
      ((f + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j - 2) * z) * w ^ f *
        (W.terminalSize : ℝ≥0) ^ (j - Q.card - 3 - f) := by
  classical
  let S := (terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) f).filter (fun x ↦ H ⊆ x.2)
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx⟩ := hS
    have hx0 := mem_filter.mp hx
    have hc := mem_terminalRemainderChoices_iff.mp (mem_terminalOmissionCodes_iff.mp hx0.1).2
    have hHcard : H.card ≤ f := (card_le_card hx0.2).trans_eq hc.2.1
    have hdis : Disjoint Q H := by
      apply disjoint_left.mpr
      intro T hTQ hTH
      exact (mem_sdiff.mp (hc.1 (hx0.2 hTH))).2 hTQ
    have hcard : (Q ∪ H).card = Q.card + H.card := card_union_of_disjoint hdis
    have hroot : (Q ∪ H).Nonempty := card_pos.mp (by rw [hcard]; omega)
    have hrootcard : (Q ∪ H).card ≤ j - 2 := by rw [hcard]; omega
    have hexponent : vortexRootExponent j (Q ∪ H).card = Q.card + H.card + 3 := by
      rw [hcard]
      exact vortexRootExponent_middle (by omega) (by omega)
    have hbound := h.root_omission_weight_le (f := f - H.card) (Q ∪ H) hroot hrootcard w
    rw [hexponent, mul_div_assoc, sourceOmission_extension_power_ratio _
      (by exact_mod_cast h.terminal_nonempty) j Q.card f H.card hfit hHcard] at hbound
    apply (sourceRootOmission_remainder_weight_le W F Q H f w).trans hbound |>.trans
    have hprofile : (((f - H.card + 1) ^ ell : ℕ) : ℝ≥0) ≤ ((f + 1) ^ ell : ℕ) := by
      exact_mod_cast Nat.pow_le_pow_left (show f - H.card + 1 ≤ f + 1 by omega) ell
    have hwp : w ^ (f - H.card) ≤ w ^ f := pow_le_pow_right₀ hw (Nat.sub_le _ _)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul' (mul_le_mul_of_nonneg_right hprofile zero_le) hwp) zero_le
  · have hempty : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    change (∑ x ∈ S, setWeight (vortexTripleWeight W w) (x.2 \ H)) ≤ _
    rw [hempty, sum_empty]
    exact zero_le

theorem SourceVortexWellSpread.root_omission_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V] {ell j f : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (Q : TripleSystemOn V)
    (hQ : 2 ≤ Q.card) (hfit : Q.card + f + 3 ≤ j) (w : ℝ≥0) (hw : 1 ≤ w) :
    HasExtensionBound
      (fun x : terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) f ↦ x.1.2)
      (vortexTripleWeight W w)
      (((f + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j - 2) * z) * w ^ f *
        (W.terminalSize : ℝ≥0) ^ (j - Q.card - 3 - f)) := by
  classical
  intro H
  unfold extensionWeight
  let codes := terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) f
  calc
    _ = ∑ x ∈ codes, if H ⊆ x.2 then setWeight (vortexTripleWeight W w) (x.2 \ H) else 0 :=
      (Finset.sum_subtype codes (by simp [codes])
        (fun x ↦ if H ⊆ x.2 then setWeight (vortexTripleWeight W w) (x.2 \ H) else 0)).symm
    _ = ∑ x ∈ codes.filter (fun x ↦ H ⊆ x.2), setWeight (vortexTripleWeight W w) (x.2 \ H) := by
      rw [sum_filter]
    _ ≤ _ := h.root_omission_extension_sum_le Q hQ hfit w hw H

end

end Erdos207
