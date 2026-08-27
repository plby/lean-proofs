/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RandomConfigurationCountTails

/-! # Only zero profiles can change when terminal configurations are added -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def IsTerminalConfigurationFamily
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) : Prop :=
  ∀ C ∈ F, ∀ T ∈ C, W.level T = Fin.last ell

theorem terminalRandomConfigurations_isTerminal
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) : IsTerminalConfigurationFamily W (terminalRandomConfigurations W j) := by
  intro C hC T hT
  exact terminalRandomConfigurations_level W hC hT

theorem IsTerminalConfigurationFamily.mono
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V}
    (hF : IsTerminalConfigurationFamily W F) (hGF : G ⊆ F) : IsTerminalConfigurationFamily W G :=
  fun C hC T hT ↦ hF C (hGF hC) T hT

@[simp] theorem Vortex.sourceProfileScale_zero
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ} (W : Vortex V ell) (d : ℕ) :
    W.sourceProfileScale d 0 = (W.terminalSize : ℝ≥0) ^ d := by
  simp [Vortex.sourceProfileScale, Vortex.profileScale, VortexProfile.mass]

theorem IsTerminalConfigurationFamily.outerProfile_subfamily
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V}
    (hF : IsTerminalConfigurationFamily W F) {C D : TripleSystemOn V}
    (hC : C ∈ F) (hDC : D ⊆ C) : W.outerProfile D = 0 :=
  W.outerProfile_eq_zero_of_terminal D (fun T hT ↦ hF C hC T (hDC hT))

theorem IsTerminalConfigurationFamily.profiledExtensions_zero
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V}
    (hF : IsTerminalConfigurationFamily W F) (R : TripleSystemOn V) :
    W.profiledExtensions F R 0 = familyExtensions F R := by
  ext C
  simp only [W.mem_profiledExtensions_iff, mem_familyExtensions_iff]
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · intro h
    exact ⟨h.1, h.2, hF.outerProfile_subfamily h.1 sdiff_subset⟩

theorem IsTerminalConfigurationFamily.profiledExtensions_eq_empty
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V}
    (hF : IsTerminalConfigurationFamily W F) (R : TripleSystemOn V)
    (t : VortexProfile ell) (ht : t ≠ 0) : W.profiledExtensions F R t = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro C hC
  have h := (W.mem_profiledExtensions_iff _ _ _ _).mp hC
  exact ht (h.2.2.symm.trans (hF.outerProfile_subfamily h.1 sdiff_subset))

theorem Vortex.profiledExtensions_union
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (R : TripleSystemOn V) (t : VortexProfile ell) :
    W.profiledExtensions (F ∪ G) R t = W.profiledExtensions F R t ∪ W.profiledExtensions G R t := by
  ext C
  simp only [W.mem_profiledExtensions_iff, mem_union]
  tauto

theorem Vortex.terminalPairExtensions_union
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T : TripleOn V) (P : VortexPairOn V) :
    W.terminalPairExtensions (F ∪ G) T P = W.terminalPairExtensions F T P ∪ W.terminalPairExtensions G T P := by
  ext C
  simp only [W.mem_terminalPairExtensions_iff, mem_union]
  constructor
  · rintro ⟨hF | hG, hrest⟩
    · exact Or.inl ⟨hF, hrest⟩
    · exact Or.inr ⟨hG, hrest⟩
  · rintro (h | h)
    · exact ⟨Or.inl h.1, h.2⟩
    · exact ⟨Or.inr h.1, h.2⟩

theorem profiledDistinctPairs_union_eq_of_nonzero
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (t : VortexProfile ell) (ht : t ≠ 0) (hG : IsTerminalConfigurationFamily W G) :
    W.profiledDistinctEqualRemainderPairs (F ∪ G) T T' t = W.profiledDistinctEqualRemainderPairs F T T' t := by
  ext C
  constructor
  · intro hC
    obtain ⟨hC1, hC2, hne, hT, hT', hrem, hprof⟩ :=
      (W.mem_profiledDistinctEqualRemainderPairs_iff _ _ _ _ _).mp hC
    have hfirst : C.1 ∈ F := by
      rcases mem_union.mp hC1 with h | h
      · exact h
      · exact (ht (hprof.symm.trans (hG.outerProfile_subfamily h (erase_subset _ _)))).elim
    have hsecond : C.2 ∈ F := by
      rcases mem_union.mp hC2 with h | h
      · exact h
      · have hzero := hG.outerProfile_subfamily h (erase_subset T' C.2)
        exact (ht (hprof.symm.trans ((congrArg W.outerProfile hrem).trans hzero))).elim
    exact (W.mem_profiledDistinctEqualRemainderPairs_iff _ _ _ _ _).mpr
      ⟨hfirst, hsecond, hne, hT, hT', hrem, hprof⟩
  · intro hC
    obtain ⟨hC1, hC2, hrest⟩ := (W.mem_profiledDistinctEqualRemainderPairs_iff _ _ _ _ _).mp hC
    exact (W.mem_profiledDistinctEqualRemainderPairs_iff _ _ _ _ _).mpr
      ⟨mem_union_left _ hC1, mem_union_left _ hC2, hrest⟩

end

end Erdos207
