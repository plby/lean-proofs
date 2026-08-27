/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexPureProfile

/-! # Count inclusions for configurations added at one exact outer level -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem profiledExtensions_subset_old_of_not_pure
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (F Fsup : ForbiddenFamilyOn V) (i : Fin ell)
    (huniform : ∀ E ∈ Fsup, E.card = j - 2)
    (hnew : ∀ E ∈ Fsup \ F, ∀ T ∈ E, W.level T = i.castSucc)
    (R : TripleSystemOn V) (t : VortexProfile ell)
    (ht : t ≠ vortexPureProfile i (j - 2 - R.card)) :
    W.profiledExtensions Fsup R t ⊆ W.profiledExtensions F R t := by
  intro E hE
  obtain ⟨hEF, hRE, hprofile⟩ := (W.mem_profiledExtensions_iff Fsup R t E).mp hE
  have hOld : E ∈ F := by
    by_contra hn
    have hp := W.outerProfile_eq_pure_of_level (E \ R) i
      (fun T hT ↦ hnew E (mem_sdiff.mpr ⟨hEF, hn⟩) T (mem_sdiff.mp hT).1)
    rw [card_sdiff_of_subset hRE, huniform E hEF] at hp
    exact ht (hprofile.symm.trans hp)
  exact (W.mem_profiledExtensions_iff F R t E).mpr ⟨hOld, hRE, hprofile⟩

theorem profiledExtensions_pure_subset_zero
    {V : Type*} [Fintype V] [DecidableEq V] {ell0 ell1 j : ℕ}
    (W0 : Vortex V ell0) (W1 : Vortex V ell1) (F : ForbiddenFamilyOn V) (i : Fin ell1)
    (hlevel : ∀ T, W1.level T = i.castSucc → W0.level T = Fin.last ell0)
    (huniform : ∀ E ∈ F, E.card = j - 2) (R : TripleSystemOn V) :
    W1.profiledExtensions F R (vortexPureProfile i (j - 2 - R.card)) ⊆
      W0.profiledExtensions F R 0 := by
  intro E hE
  obtain ⟨hEF, hRE, hprofile⟩ := (W1.mem_profiledExtensions_iff F R _ E).mp hE
  have hc : (E \ R).card = j - 2 - R.card := by rw [card_sdiff_of_subset hRE, huniform E hEF]
  have hlevels := W1.level_eq_of_outerProfile_pure (E \ R) i (by simpa only [hc] using hprofile)
  exact (W0.mem_profiledExtensions_iff F R 0 E).mpr ⟨hEF, hRE,
    W0.outerProfile_eq_zero_of_terminal (E \ R) (fun T hT ↦ hlevel T (hlevels T hT))⟩

theorem profiledDistinctPairs_subset_old_of_not_pure
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (F Fsup : ForbiddenFamilyOn V) (i : Fin ell)
    (huniform : ∀ E ∈ Fsup, E.card = j - 2)
    (hnew : ∀ E ∈ Fsup \ F, ∀ T ∈ E, W.level T = i.castSucc)
    (T T' : TripleOn V) (t : VortexProfile ell)
    (ht : t ≠ vortexPureProfile i (j - 3)) :
    W.profiledDistinctEqualRemainderPairs Fsup T T' t ⊆
      W.profiledDistinctEqualRemainderPairs F T T' t := by
  intro p hp
  obtain ⟨hE, hE', hne, hT, hT', hrem, hprofile⟩ :=
    (W.mem_profiledDistinctEqualRemainderPairs_iff Fsup T T' t p).mp hp
  have hold : ∀ (E : TripleSystemOn V) (D : TripleOn V), E ∈ Fsup → D ∈ E →
      W.outerProfile (E.erase D) = t → E ∈ F := by
    intro E D hEF hDE hprof
    by_contra hn
    have hlev := W.outerProfile_eq_pure_of_level (E.erase D) i
      (fun Q hQ ↦ hnew E (mem_sdiff.mpr ⟨hEF, hn⟩) Q (mem_of_mem_erase hQ))
    have hc : (E.erase D).card = j - 3 := by
      rw [card_erase_of_mem hDE, huniform E hEF]
      omega
    rw [hc] at hlev
    exact ht (hprof.symm.trans hlev)
  exact (W.mem_profiledDistinctEqualRemainderPairs_iff F T T' t p).mpr
    ⟨hold p.1 T hE hT hprofile, hold p.2 T' hE' hT' (hrem ▸ hprofile),
      hne, hT, hT', hrem, hprofile⟩

theorem profiledDistinctPairs_pure_subset_zero
    {V : Type*} [Fintype V] [DecidableEq V] {ell0 ell1 j : ℕ}
    (W0 : Vortex V ell0) (W1 : Vortex V ell1) (F : ForbiddenFamilyOn V) (i : Fin ell1)
    (hlevel : ∀ T, W1.level T = i.castSucc → W0.level T = Fin.last ell0)
    (huniform : ∀ E ∈ F, E.card = j - 2) (T T' : TripleOn V) :
    W1.profiledDistinctEqualRemainderPairs F T T' (vortexPureProfile i (j - 3)) ⊆
      W0.profiledDistinctEqualRemainderPairs F T T' 0 := by
  intro p hp
  obtain ⟨hE, hE', hne, hT, hT', hrem, hprofile⟩ :=
    (W1.mem_profiledDistinctEqualRemainderPairs_iff F T T' _ p).mp hp
  have hc : (p.1.erase T).card = j - 3 := by
    rw [card_erase_of_mem hT, huniform p.1 hE]
    omega
  have hlevels := W1.level_eq_of_outerProfile_pure (p.1.erase T) i (by simpa only [hc] using hprofile)
  exact (W0.mem_profiledDistinctEqualRemainderPairs_iff F T T' 0 p).mpr
    ⟨hE, hE', hne, hT, hT', hrem,
      W0.outerProfile_eq_zero_of_terminal (p.1.erase T) (fun Q hQ ↦ hlevel Q (hlevels Q hQ))⟩

theorem terminalPairExtensions_subset_old_of_new_outer
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F Fsup : ForbiddenFamilyOn V) (i : Fin ell)
    (hnew : ∀ E ∈ Fsup \ F, ∀ Q ∈ E, W.level Q = i.castSucc)
    (T : TripleOn V) (P : VortexPairOn V) :
    W.terminalPairExtensions Fsup T P ⊆ W.terminalPairExtensions F T P := by
  intro E hE
  obtain ⟨hEF, hT, D, hD, hterminal, hP⟩ := (W.mem_terminalPairExtensions_iff Fsup T P E).mp hE
  have hOld : E ∈ F := by
    by_contra hn
    have hlev := hnew E (mem_sdiff.mpr ⟨hEF, hn⟩) D (mem_of_mem_erase hD)
    have hv := congrArg Fin.val (hlev.symm.trans hterminal)
    have hi := i.isLt
    simp only [Fin.val_castSucc, Fin.val_last] at hv
    omega
  exact (W.mem_terminalPairExtensions_iff F T P E).mpr ⟨hOld, hT, D, hD, hterminal, hP⟩

end

end Erdos207
