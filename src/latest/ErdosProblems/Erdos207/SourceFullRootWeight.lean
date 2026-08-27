/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGeneralMomentWeights

/-! # Full configuration weights with fixed triangle roots and no omissions -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceVortexWellSpread.full_root_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (Q : TripleSystemOn V)
    (hQ : Q.Nonempty) (hQcard : Q.card ≤ j - 2) :
    (∑ E ∈ familyExtensions F Q, setWeight (vortexTripleWeight W 1) (E \ Q)) ≤
      ((j - 2 - Q.card + 1) ^ ell : ℕ) * z *
        (W.terminalSize : ℝ≥0) ^ (j - vortexRootExponent j Q.card) /
          (W.terminalSize : ℝ≥0) ^ (j - 2 - Q.card) := by
  have hbound := W.weight_sum_le_of_profile_count (familyExtensions F Q) (fun E ↦ E \ Q)
    1 z h.terminal_nonempty (f := j - 2 - Q.card) (d := j - vortexRootExponent j Q.card)
    (fun E hE ↦ by
      have hm := mem_familyExtensions_iff.mp hE
      rw [card_sdiff_of_subset hm.2, (h.uniform E hm.1).1])
    (fun t ↦ by
      have heq : (familyExtensions F Q).filter (fun E ↦ W.outerProfile (E \ Q) = t) =
          W.profiledExtensions F Q t := by
        ext E
        simp only [mem_filter, mem_familyExtensions_iff, W.mem_profiledExtensions_iff, and_assoc]
      rw [heq]
      exact h.extensions Q t hQ hQcard)
  simpa only [one_pow, mul_one] using hbound

theorem SourceVortexWellSpread.full_singleton_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (T : TripleOn V) :
    (∑ E ∈ familyExtensions F {T}, setWeight (vortexTripleWeight W 1) (E \ {T})) ≤
      ((j - 3 + 1) ^ ell : ℕ) * y := by
  have hbound := W.weight_sum_le_of_profile_count (familyExtensions F {T}) (fun E ↦ E \ {T})
    1 y h.terminal_nonempty (f := j - 3) (d := j - 3)
    (fun E hE ↦ by
      have hm := mem_familyExtensions_iff.mp hE
      rw [card_sdiff_of_subset hm.2, (h.uniform E hm.1).1, card_singleton]
      omega)
    (fun t ↦ by
      have heq : (familyExtensions F {T}).filter (fun E ↦ W.outerProfile (E \ {T}) = t) =
          W.profiledExtensions F {T} t := by
        ext E
        simp only [mem_filter, mem_familyExtensions_iff, W.mem_profiledExtensions_iff, and_assoc]
      rw [heq]
      exact h.singleton_extensions T t)
  have hn : (W.terminalSize : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h.terminal_nonempty)
  simpa only [one_pow, mul_one, mul_div_cancel_right₀ _ (pow_ne_zero _ hn)] using hbound

theorem SourceVortexWellSpread.full_middle_root_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (Q : TripleSystemOn V)
    (hQ : 2 ≤ Q.card) (hQcard : Q.card ≤ j - 3) :
    (∑ E ∈ familyExtensions F Q, setWeight (vortexTripleWeight W 1) (E \ Q)) ≤
      ((j - 2 - Q.card + 1) ^ ell : ℕ) * z / W.terminalSize := by
  have hroot : vortexRootExponent j Q.card = Q.card + 3 :=
    vortexRootExponent_middle (by omega) (by omega)
  have hbound := h.full_root_weight_le Q (card_pos.mp (by omega)) (by have := h.order; omega)
  have hn : (W.terminalSize : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h.terminal_nonempty)
  have hexp : j - 2 - Q.card = (j - (Q.card + 3)) + 1 := by
    have := h.order
    omega
  apply hbound.trans_eq
  rw [hroot, hexp, pow_succ]
  field_simp

theorem SourceVortexWellSpread.full_all_root_weight_le_one
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (Q : TripleSystemOn V) (hQcard : Q.card = j - 2) :
    (∑ E ∈ familyExtensions F Q, setWeight (vortexTripleWeight W 1) (E \ Q)) ≤ 1 := by
  have hsub : familyExtensions F Q ⊆ {Q} := by
    intro E hE
    have hm := mem_familyExtensions_iff.mp hE
    exact mem_singleton.mpr (eq_of_subset_of_card_le hm.2 (by rw [hQcard, (h.uniform E hm.1).1])).symm
  calc
    _ ≤ ∑ E ∈ ({Q} : Finset (TripleSystemOn V)), setWeight (vortexTripleWeight W 1) (E \ Q) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ zero_le)
    _ = 1 := by simp [setWeight]

end

end Erdos207
