/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceFullRootWeight

/-! # Uniform finite coefficients for full configuration weights -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceVortexWellSpread.full_singleton_weight_le_z
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (T : TripleOn V) :
    (∑ E ∈ familyExtensions F {T}, setWeight (vortexTripleWeight W 1) (E \ {T})) ≤
      ((j - 3 + 1) ^ ell : ℕ) * z := by
  have hb := h.full_root_weight_le {T} (singleton_nonempty T) (by simp; have := h.order; omega)
  have hn : (W.terminalSize : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt h.terminal_nonempty)
  have hexp : j - 2 - 1 = j - 3 := by omega
  simpa only [card_singleton, hexp, vortexRootExponent_one,
    mul_div_cancel_right₀ _ (pow_ne_zero _ hn)] using hb

theorem SourceVortexWellSpread.full_singleton_weight_le_uniform
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (T : TripleOn V) :
    (∑ E ∈ familyExtensions F {T}, setWeight (vortexTripleWeight W 1) (E \ {T})) ≤
      (j ^ ell : ℕ) * z := by
  apply (h.full_singleton_weight_le_z T).trans
  have hj : j - 3 + 1 ≤ j := by have := h.order; omega
  gcongr

theorem SourceVortexWellSpread.full_middle_root_weight_le_uniform
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (Q : TripleSystemOn V)
    (hQ : 2 ≤ Q.card) (hQcard : Q.card ≤ j - 3) :
    (∑ E ∈ familyExtensions F Q, setWeight (vortexTripleWeight W 1) (E \ Q)) ≤
      (j ^ ell : ℕ) * z / W.terminalSize := by
  apply (h.full_middle_root_weight_le Q hQ hQcard).trans
  have hj : j - 2 - Q.card + 1 ≤ j := by have := h.order; omega
  gcongr

end

end Erdos207
