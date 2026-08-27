/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyRootedConfigurationWeight
import ErdosProblems.Erdos207.GreedyConfigurationThreats

/-! # Configuration jumps controlled by two-root classes -/

namespace Erdos207

open Finset

noncomputable section

theorem mem_greedyRootedConfigurationClass_pair_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root U : TripleOn V} {c : ℕ} {C : TripleSystemOn V}
    (hroot : root ∈ S.available) (hU : U ∈ S.available) :
    C ∈ greedyRootedConfigurationClass J S {root, U} c ↔
      C ∈ greedyConfigurationClass J S root c ∧ U ∈ C := by
  simp only [greedyRootedConfigurationClass, mem_filter, insert_subset_iff,
    singleton_subset_iff, mem_inter, hroot, hU, and_true,
    mem_greedyConfigurationClass]
  tauto

theorem greedyConfigurationGains_subset_twoRootClass
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root T : TripleOn V} {c : ℕ}
    (hroot : root ∈ S.available) (hT : T ∈ S.available) :
    greedyConfigurationGains F J S root c T ⊆
      greedyRootedConfigurationClass J S {root, T} c := by
  intro C hC
  exact (mem_greedyRootedConfigurationClass_pair_iff hroot hT).mpr
    ⟨(mem_filter.mp hC).1, (mem_filter.mp hC).2.1⟩

theorem greedyConfigurationLosses_subset_threat_twoRootClasses
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root T : TripleOn V} {c : ℕ}
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hT : T ∈ S.available \ greedyClosedThreats F S root) :
    greedyConfigurationLosses F J S root c T ⊆
      ((greedyClosedThreats F S T).erase root).biUnion fun U ↦
        greedyRootedConfigurationClass J S {root, U} c := by
  intro C hC
  obtain ⟨hclass, U, hU, hthreat⟩ :=
    (mem_greedyConfigurationLosses_iff hS (mem_sdiff.mp hT).1).mp hC
  have hUroot : U ≠ root := by
    intro h
    exact (mem_sdiff.mp hT).2 (h ▸ hthreat)
  have hUT : U ∈ greedyClosedThreats F S T :=
    (mem_greedyClosedThreats_comm F S (mem_sdiff.mp hT).1 (mem_inter.mp hU).2).mpr hthreat
  exact mem_biUnion.mpr ⟨U, mem_erase.mpr ⟨hUroot, hUT⟩,
    (mem_greedyRootedConfigurationClass_pair_iff hroot (mem_inter.mp hU).2).mpr
      ⟨hclass, (mem_inter.mp hU).1⟩⟩

theorem card_configurationGains_le_twoRootBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root T : TripleOn V} {c P : ℕ}
    (hroot : root ∈ S.available)
    (hT : T ∈ S.available \ greedyClosedThreats F S root)
    (hcount : ∀ U ∈ S.available, U ≠ root →
      (greedyRootedConfigurationClass J S {root, U} c).card ≤ P) :
    (greedyConfigurationGains F J S root c T).card ≤ P := by
  have hne : T ≠ root := by
    intro h
    subst T
    exact (mem_sdiff.mp hT).2 (mem_greedyClosedThreats_self F S hroot)
  exact (card_le_card (greedyConfigurationGains_subset_twoRootClass hroot
    (mem_sdiff.mp hT).1)).trans (hcount T (mem_sdiff.mp hT).1 hne)

theorem card_configurationLosses_le_threat_mul_twoRootBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root T : TripleOn V} {c P : ℕ}
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hT : T ∈ S.available \ greedyClosedThreats F S root)
    (hcount : ∀ U ∈ S.available, U ≠ root →
      (greedyRootedConfigurationClass J S {root, U} c).card ≤ P) :
    (greedyConfigurationLosses F J S root c T).card ≤
      (greedyClosedThreats F S T).card * P := by
  calc
    _ ≤ (((greedyClosedThreats F S T).erase root).biUnion fun U ↦
        greedyRootedConfigurationClass J S {root, U} c).card :=
      card_le_card (greedyConfigurationLosses_subset_threat_twoRootClasses hS hroot hT)
    _ ≤ ∑ U ∈ (greedyClosedThreats F S T).erase root,
        (greedyRootedConfigurationClass J S {root, U} c).card := card_biUnion_le
    _ ≤ ∑ _U ∈ (greedyClosedThreats F S T).erase root, P := by
      apply sum_le_sum
      intro U hU
      exact hcount U (mem_inter.mp (mem_erase.mp hU).2).1 (mem_erase.mp hU).1
    _ = ((greedyClosedThreats F S T).erase root).card * P := by simp
    _ ≤ _ := Nat.mul_le_mul_right P (card_le_card (erase_subset root _))

theorem greedyConfigurationClass_abs_increment_le_rootBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root T : TripleOn V} (c P Q : ℕ)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hT : T ∈ S.available \ greedyClosedThreats F S root)
    (hgain : ∀ U ∈ S.available, U ≠ root →
      (greedyRootedConfigurationClass J S {root, U} c).card ≤ P)
    (hloss : ∀ U ∈ S.available, U ≠ root →
      (greedyRootedConfigurationClass J S {root, U} (c + 1)).card ≤ Q) :
    |((greedyConfigurationClass J (greedyStep F S T) root (c + 1)).card : ℝ) -
      (greedyConfigurationClass J S root (c + 1)).card| ≤
        (max P ((greedyClosedThreats F S T).card * Q) : ℕ) := by
  rw [greedyConfigurationClass_increment_succ c hS (mem_sdiff.mp hT).1]
  have hg : ((greedyConfigurationGains F J S root c T).card : ℝ) ≤ P := by
    exact_mod_cast card_configurationGains_le_twoRootBound hroot hT hgain
  have hl : ((greedyConfigurationLosses F J S root (c + 1) T).card : ℝ) ≤
      ((greedyClosedThreats F S T).card * Q : ℕ) := by
    exact_mod_cast card_configurationLosses_le_threat_mul_twoRootBound hS hroot hT hloss
  have hp : (P : ℝ) ≤ (max P ((greedyClosedThreats F S T).card * Q) : ℕ) := by
    exact_mod_cast le_max_left P ((greedyClosedThreats F S T).card * Q)
  have hq : (((greedyClosedThreats F S T).card * Q : ℕ) : ℝ) ≤
      (max P ((greedyClosedThreats F S T).card * Q) : ℕ) := by
    exact_mod_cast le_max_right P ((greedyClosedThreats F S T).card * Q)
  have hg0 : (0 : ℝ) ≤ (greedyConfigurationGains F J S root c T).card := Nat.cast_nonneg _
  have hl0 : (0 : ℝ) ≤ (greedyConfigurationLosses F J S root (c + 1) T).card :=
    Nat.cast_nonneg _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end

end Erdos207
