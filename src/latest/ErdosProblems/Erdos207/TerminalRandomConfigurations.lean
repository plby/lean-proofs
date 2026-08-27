/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGlobalAbsorberWellSpread
import ErdosProblems.Erdos207.MixedConfigurationPairBlocks

/-! # The actual terminal, vertex-disjoint random configuration universe -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def terminalRandomConfigurations
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ} (W : Vortex V ell) (j : ℕ) :
    ForbiddenFamilyOn V := by
  classical
  exact ((triplesSupportedOn (W.U (Fin.last ell))).powersetCard (j - 2)).filter fun C ↦
    (C : Set (TripleOn V)).PairwiseDisjoint (fun T ↦ T.1)

theorem mem_terminalRandomConfigurations_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) :
    C ∈ terminalRandomConfigurations W j ↔
      C ⊆ triplesSupportedOn (W.U (Fin.last ell)) ∧ C.card = j - 2 ∧
        (C : Set (TripleOn V)).PairwiseDisjoint (fun T ↦ T.1) := by
  classical
  simp only [terminalRandomConfigurations, mem_filter, mem_powersetCard, and_assoc]

theorem terminalRandomConfigurations_uniform
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) (hC : C ∈ terminalRandomConfigurations W j) :
    C.card = j - 2 ∧ IsPackingOn C := by
  have hm := (mem_terminalRandomConfigurations_iff W C).mp hC
  refine ⟨hm.2.1, ?_⟩
  intro u v _huv T hT huT _hvT T' hT' huT' _hvT'
  by_contra hne
  have hd : Disjoint T.1 T'.1 := hm.2.2 hT hT' hne
  exact Finset.disjoint_left.mp hd huT huT'

theorem Vortex.outerProfile_eq_zero_of_terminal
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V)
    (hterminal : ∀ T ∈ C, W.level T = Fin.last ell) : W.outerProfile C = 0 := by
  funext i
  change (C ∩ W.trianglesAtLevel i.castSucc).card = 0
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro T hT
  have hm := mem_inter.mp hT
  have hlevel := (W.mem_trianglesAtLevel_iff i.castSucc T).mp hm.2
  have hv := congrArg Fin.val hlevel
  simp only [hterminal T hm.1, Fin.val_last, Fin.val_castSucc] at hv
  omega

theorem terminalRandomConfigurations_level
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) {C : TripleSystemOn V} (hC : C ∈ terminalRandomConfigurations W j)
    {T : TripleOn V} (hT : T ∈ C) : W.level T = Fin.last ell := by
  have hsub := mem_triplesSupportedOn_iff.mp (((mem_terminalRandomConfigurations_iff W C).mp hC).1 hT)
  apply le_antisymm (Fin.le_last _)
  exact (W.subset_iff_le_level T (Fin.last ell)).mp hsub

theorem card_familyExtensions_terminalRandomConfigurations_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (R : TripleSystemOn V) :
    (familyExtensions (terminalRandomConfigurations W j) R).card ≤
      (W.terminalSize ^ 3) ^ (j - 2 - R.card) := by
  let U := triplesSupportedOn (W.U (Fin.last ell))
  have hinj : (familyExtensions (terminalRandomConfigurations W j) R).card ≤
      (U.powersetCard (j - 2 - R.card)).card := by
    apply card_le_card_of_injOn (fun C ↦ C \ R)
    · intro C hC
      have hm := mem_familyExtensions_iff.mp hC
      have hd := (mem_terminalRandomConfigurations_iff W C).mp hm.1
      apply mem_powersetCard.mpr
      refine ⟨sdiff_subset.trans hd.1, ?_⟩
      rw [card_sdiff_of_subset hm.2, hd.2.1]
    · intro C hC D hD heq
      change C \ R = D \ R at heq
      have hRC := (mem_familyExtensions_iff.mp hC).2
      have hRD := (mem_familyExtensions_iff.mp hD).2
      calc
        C = R ∪ (C \ R) := (union_sdiff_of_subset hRC).symm
        _ = R ∪ (D \ R) := by rw [heq]
        _ = D := union_sdiff_of_subset hRD
  calc
    _ ≤ (U.powersetCard (j - 2 - R.card)).card := hinj
    _ = U.card.choose (j - 2 - R.card) := card_powersetCard _ _
    _ ≤ U.card ^ (j - 2 - R.card) := Nat.choose_le_pow _ _
    _ ≤ _ := Nat.pow_le_pow_left (card_triplesSupportedOn_le_cube _) _

theorem card_distinctPairs_terminalRandomConfigurations_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (T T' : TripleOn V) :
    (distinctEqualRemainderPairs (terminalRandomConfigurations W j) T T').card ≤
      (W.terminalSize ^ 3) ^ (j - 3) := by
  let F := terminalRandomConfigurations W j
  let U := triplesSupportedOn (W.U (Fin.last ell))
  have hinj : (distinctEqualRemainderPairs F T T').card ≤ (U.powersetCard (j - 3)).card := by
    apply card_le_card_of_injOn (fun C ↦ C.1.erase T)
    · intro C hC
      have hm := mem_distinctEqualRemainderPairs_iff.mp hC
      have hd := (mem_terminalRandomConfigurations_iff W C.1).mp hm.1
      apply mem_powersetCard.mpr
      refine ⟨(erase_subset _ _).trans hd.1, ?_⟩
      rw [card_erase_of_mem hm.2.2.2.1, hd.2.1]
      omega
    · intro C hC D hD heq
      change C.1.erase T = D.1.erase T at heq
      have hCT := (mem_distinctEqualRemainderPairs_iff.mp hC).2.2.2.1
      have hDT := (mem_distinctEqualRemainderPairs_iff.mp hD).2.2.2.1
      apply distinctEqualRemainderPairs_fst_injOn F T T' hC hD
      calc
        C.1 = insert T (C.1.erase T) := (insert_erase hCT).symm
        _ = insert T (D.1.erase T) := by rw [heq]
        _ = D.1 := insert_erase hDT
  calc
    _ ≤ (U.powersetCard (j - 3)).card := hinj
    _ = U.card.choose (j - 3) := card_powersetCard _ _
    _ ≤ U.card ^ (j - 3) := Nat.choose_le_pow _ _
    _ ≤ _ := Nat.pow_le_pow_left (card_triplesSupportedOn_le_cube _) _

end

end Erdos207
