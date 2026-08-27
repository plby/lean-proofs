/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceTerminalOmissionWeight
import ErdosProblems.Erdos207.UniformExtensionWeight

/-! # Source general-moment weights for one family and distinct collisions -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceRootOmissionWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (Q : TripleSystemOn V)
    (f : ℕ) (w : ℝ≥0) : ℝ≥0 :=
  ∑ x ∈ terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) f,
    setWeight (vortexTripleWeight W w) x.2

theorem SourceVortexWellSpread.root_omission_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j f : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (Q : TripleSystemOn V)
    (hQ : Q.Nonempty) (hQcard : Q.card ≤ j - 2) (w : ℝ≥0) :
    sourceRootOmissionWeight W F Q f w ≤
      ((f + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j - 2) * z) * w ^ f *
        (W.terminalSize : ℝ≥0) ^ (j - vortexRootExponent j Q.card) /
          (W.terminalSize : ℝ≥0) ^ f := by
  apply terminalOmission_weight_le_of_profile_count W (familyExtensions F Q)
    (fun E ↦ E \ Q) w z h.terminal_nonempty
  · intro E hE
    exact (card_le_card sdiff_subset).trans_eq
      (h.uniform E (mem_familyExtensions_iff.mp hE).1).1
  · intro t
    have heq : (familyExtensions F Q).filter (fun E ↦ W.outerProfile (E \ Q) = t) =
        W.profiledExtensions F Q t := by
      ext E
      simp only [mem_filter, mem_familyExtensions_iff, W.mem_profiledExtensions_iff,
        and_assoc]
    rw [heq]
    exact h.extensions Q t hQ hQcard

theorem SourceVortexWellSpread.singleton_omission_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j f : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (T : TripleOn V) (w : ℝ≥0) :
    sourceRootOmissionWeight W F {T} f w ≤
      ((f + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j - 3) * y) * w ^ f *
        (W.terminalSize : ℝ≥0) ^ (j - 3) / (W.terminalSize : ℝ≥0) ^ f := by
  apply terminalOmission_weight_le_of_profile_count W (familyExtensions F {T})
    (fun E ↦ E \ {T}) w y h.terminal_nonempty
  · intro E hE
    have hm := mem_familyExtensions_iff.mp hE
    rw [card_sdiff_of_subset hm.2, (h.uniform E hm.1).1, card_singleton]
    omega
  · intro t
    have heq : (familyExtensions F {T}).filter
        (fun E ↦ W.outerProfile (E \ {T}) = t) = W.profiledExtensions F {T} t := by
      ext E
      simp only [mem_filter, mem_familyExtensions_iff, W.mem_profiledExtensions_iff,
        and_assoc]
    rw [heq]
    exact h.singleton_extensions T t

def sourceDistinctOmissionWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (f : ℕ) (w : ℝ≥0) : ℝ≥0 :=
  ∑ x ∈ terminalOmissionCodes W (distinctEqualRemainderPairs F T T')
      (fun E ↦ E.1.erase T) f,
    setWeight (vortexTripleWeight W w) x.2

theorem SourceVortexWellSpread.distinct_omission_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j f : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (T T' : TripleOn V) (w : ℝ≥0) :
    sourceDistinctOmissionWeight W F T T' f w ≤
      ((f + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j - 3) * z) * w ^ f *
        (W.terminalSize : ℝ≥0) ^ (j - 4) / (W.terminalSize : ℝ≥0) ^ f := by
  apply terminalOmission_weight_le_of_profile_count W (distinctEqualRemainderPairs F T T')
    (fun E ↦ E.1.erase T) w z h.terminal_nonempty
  · intro E hE
    have hm := mem_distinctEqualRemainderPairs_iff.mp hE
    rw [card_erase_of_mem hm.2.2.2.1, (h.uniform E.1 hm.1).1]
    omega
  · intro t
    exact h.equal_remainders T T' t

end

end Erdos207
