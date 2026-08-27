/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyConfigurationThreats
import ErdosProblems.Erdos207.GreedyConfigurationCardinality

/-! # Root-preserving gain selectors and the exact internal-threat defect -/

namespace Erdos207

open Finset

noncomputable section

def greedyConfigurationGainSelectors
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (root : TripleOn V) (C : TripleSystemOn V) : TripleSystemOn V := by
  classical
  exact ((C ∩ S.available).erase root).filter fun T ↦
    ∀ U ∈ (C ∩ S.available).erase T, T ∉ greedyClosedThreats F S U

def greedyConfigurationBadGainSelectors
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (root : TripleOn V) (C : TripleSystemOn V) : TripleSystemOn V := by
  classical
  exact ((C ∩ S.available).erase root).filter fun T ↦
    ∃ U ∈ (C ∩ S.available).erase T, T ∈ greedyClosedThreats F S U

theorem root_preserving_configuration_gain_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {T root : TripleOn V} {c : ℕ} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available) :
    (T ∈ S.available \ greedyClosedThreats F S root ∧
      C ∈ greedyConfigurationGains F J S root c T) ↔
      (C ∈ greedyConfigurationClass J S root c ∧
        T ∈ greedyConfigurationGainSelectors F S root C) := by
  classical
  constructor
  · rintro ⟨hT, hC⟩
    obtain ⟨hclass, hTC, hsafe⟩ :=
      (mem_greedyConfigurationGains_iff hS (mem_sdiff.mp hT).1).mp hC
    refine ⟨hclass, mem_filter.mpr ⟨mem_erase.mpr ⟨?_, ?_⟩, ?_⟩⟩
    · intro h
      subst T
      exact (mem_sdiff.mp hT).2 (mem_greedyClosedThreats_self F S hroot)
    · exact mem_inter.mpr ⟨hTC, (mem_sdiff.mp hT).1⟩
    · intro U hU
      exact hsafe U (mem_erase.mp hU).2 (mem_erase.mp hU).1
  · rintro ⟨hclass, hT⟩
    obtain ⟨hTW, hsafe⟩ := mem_filter.mp hT
    have hTA := (mem_inter.mp (mem_erase.mp hTW).2).2
    have hTC := (mem_inter.mp (mem_erase.mp hTW).2).1
    have hTroot : T ≠ root := (mem_erase.mp hTW).1
    have hrootC := (mem_greedyConfigurationClass.mp hclass).2.1
    have hnotRoot : T ∉ greedyClosedThreats F S root :=
      hsafe root (mem_erase.mpr ⟨hTroot.symm, mem_inter.mpr ⟨hrootC, hroot⟩⟩)
    refine ⟨mem_sdiff.mpr ⟨hTA, hnotRoot⟩, ?_⟩
    exact (mem_greedyConfigurationGains_iff hS hTA).mpr
      ⟨hclass, hTC, fun U hU hUT ↦ hsafe U (mem_erase.mpr ⟨hUT, hU⟩)⟩

theorem greedyConfigurationGainSelectors_card_add_bad
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (root : TripleOn V) (C : TripleSystemOn V) :
    (greedyConfigurationGainSelectors F S root C).card +
      (greedyConfigurationBadGainSelectors F S root C).card =
        ((C ∩ S.available).erase root).card := by
  classical
  let W := (C ∩ S.available).erase root
  let safe := fun T ↦ ∀ U ∈ (C ∩ S.available).erase T,
    T ∉ greedyClosedThreats F S U
  have hbad : greedyConfigurationBadGainSelectors F S root C =
      W.filter (fun T ↦ ¬ safe T) := by
    ext T
    simp only [greedyConfigurationBadGainSelectors, mem_filter, W, safe]
    push Not
    rfl
  rw [hbad]
  exact card_filter_add_card_filter_not (s := W) safe

theorem greedyConfigurationGainSelectors_card_add_bad_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root : TripleOn V} {c d : ℕ} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hC : C ∈ greedyConfigurationClass J S root c) (hcard : C.card = d + 1) :
    (greedyConfigurationGainSelectors F S root C).card +
      (greedyConfigurationBadGainSelectors F S root C).card = d - c := by
  rw [greedyConfigurationGainSelectors_card_add_bad,
    greedyConfigurationClass_available_nonroot_card hS hroot hC hcard]

end

end Erdos207
