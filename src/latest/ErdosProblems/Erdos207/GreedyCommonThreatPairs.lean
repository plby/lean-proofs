/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CommonThreatFamilyUnion
import ErdosProblems.Erdos207.GreedyConfigurationClasses

/-! # The actual third crude statistic is bounded by indexed witnesses -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Ordered distinct configuration pairs with the two specified available
parts. The definition includes the equal-root case. -/
def greedyCommonThreatPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (F G : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T T' : TripleOn V) :
    Finset (TripleSystemOn V × TripleSystemOn V) := by
  classical
  exact (F ×ˢ G).filter fun p ↦ p.1 ≠ p.2 ∧
    ∃ U ∈ S.available, U ≠ T ∧ U ≠ T' ∧
      p.1 ∩ S.available = {T, U} ∧ p.2 ∩ S.available = {T', U} ∧
      (p.1 ∪ p.2) \ S.available ⊆ S.chosen

def greedyCommonThreatPairWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (F G : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T T' : TripleOn V)
    (p : greedyCommonThreatPairs F G S T T') : CommonThreatWitness F G T T' := by
  classical
  have hd := mem_filter.mp p.2
  let U := hd.2.2.choose
  have hu := hd.2.2.choose_spec
  change U ∈ S.available ∧ U ≠ T ∧ U ≠ T' ∧
    p.1.1 ∩ S.available = {T, U} ∧ p.1.2 ∩ S.available = {T', U} ∧
    (p.1.1 ∪ p.1.2) \ S.available ⊆ S.chosen at hu
  have hUT := hu.2.1
  have hUT' := hu.2.2.1
  have hfirst := hu.2.2.2.1
  have hsecond := hu.2.2.2.2.1
  have hT : T ∈ p.1.1 ∩ S.available := by rw [hfirst]; simp
  have hT' : T' ∈ p.1.2 ∩ S.available := by rw [hsecond]; simp
  refine ⟨U, p.1.1, p.1.2, (mem_product.mp hd.1).1, (mem_product.mp hd.1).2,
    (mem_inter.mp hT).1, (mem_inter.mp hT').1, ?_, ?_, hUT, hUT', ?_, ?_, hd.2.1⟩
  · exact (mem_inter.mp (show U ∈ p.1.1 ∩ S.available by rw [hfirst]; simp)).1
  · exact (mem_inter.mp (show U ∈ p.1.2 ∩ S.available by rw [hsecond]; simp)).1
  · intro hx
    have hh : T' ∈ ({T, U} : TripleSystemOn V) :=
      hfirst ▸ mem_inter.mpr ⟨hx, (mem_inter.mp hT').2⟩
    simpa only [mem_insert, mem_singleton, Ne.symm hUT', or_false] using hh
  · intro hx
    have hh : T ∈ ({T', U} : TripleSystemOn V) :=
      hsecond ▸ mem_inter.mpr ⟨hx, (mem_inter.mp hT).2⟩
    simpa only [mem_insert, mem_singleton, Ne.symm hUT, or_false] using hh

theorem greedyCommonThreatPairWitness_remainder_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (F G : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T T' : TripleOn V)
    (p : greedyCommonThreatPairs F G S T T') :
    (greedyCommonThreatPairWitness F G S T T' p).remainder ⊆ S.chosen := by
  classical
  let w := greedyCommonThreatPairWitness F G S T T' p
  have hd := mem_filter.mp p.2
  have hu := hd.2.2.choose_spec
  change w.bridge ∈ S.available ∧ w.bridge ≠ T ∧ w.bridge ≠ T' ∧
    w.first ∩ S.available = {T, w.bridge} ∧
    w.second ∩ S.available = {T', w.bridge} ∧
    (w.first ∪ w.second) \ S.available ⊆ S.chosen at hu
  obtain ⟨_, _, _, hf, hs, hrest⟩ := hu
  intro x hx
  have hxunion : x ∈ w.first ∪ w.second := (mem_sdiff.mp (w.remainder_eq_sdiff ▸ hx)).1
  apply hrest (mem_sdiff.mpr ⟨hxunion, ?_⟩)
  intro hxA
  rcases mem_union.mp hxunion with hxF | hxG
  · have h : x ∈ ({T, w.bridge} : TripleSystemOn V) := hf ▸ mem_inter.mpr ⟨hxF, hxA⟩
    rcases mem_insert.mp h with rfl | h
    · exact w.first_not_mem_remainder hx
    · exact w.bridge_not_mem_remainder (mem_singleton.mp h ▸ hx)
  · have h : x ∈ ({T', w.bridge} : TripleSystemOn V) := hs ▸ mem_inter.mpr ⟨hxG, hxA⟩
    rcases mem_insert.mp h with rfl | h
    · exact w.second_not_mem_remainder hx
    · exact w.bridge_not_mem_remainder (mem_singleton.mp h ▸ hx)

theorem greedyCommonThreatPairWitness_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (F G : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T T' : TripleOn V) :
    Function.Injective (greedyCommonThreatPairWitness F G S T T') := by
  intro p z h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun w ↦ w.first) h) (congrArg (fun w ↦ w.second) h)

theorem greedyCommonThreatPairs_card_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (F G : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T T' : TripleOn V) :
    ((greedyCommonThreatPairs F G S T T').card : ℝ≥0) ≤
      selectedCount (fun w : CommonThreatWitness F G T T' ↦ w.remainder) S.chosen := by
  classical
  have h := sum_le_sum_of_injective_code
    (greedyCommonThreatPairWitness F G S T T')
    (greedyCommonThreatPairWitness_injective F G S T T')
    (fun _ ↦ 1) (fun w ↦ if w.remainder ⊆ S.chosen then 1 else 0) (by
      intro p
      rw [if_pos (greedyCommonThreatPairWitness_remainder_subset F G S T T' p)])
  simpa only [selectedCount, sum_const, card_univ, Fintype.card_coe,
    nsmul_eq_mul, mul_one] using h

end

end Erdos207
