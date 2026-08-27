/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DistinctEqualRemainders
import ErdosProblems.Erdos207.UniformExtensionWeight

/-! # Separating derived members in the off-diagonal W2 count -/

namespace Erdos207

open Finset

theorem card_distinctEqualRemainderPairs_fst_filter_le
    {W : Type*} [DecidableEq W] (F D : Finset (Finset W)) (T T' : W) :
    ((distinctEqualRemainderPairs F T T').filter fun p ↦ p.1 ∈ D).card ≤
      (familyExtensions D {T}).card := by
  apply card_le_card_of_injOn (fun p ↦ p.1)
  · intro p hp
    obtain ⟨hp, hpD⟩ := mem_filter.mp hp
    exact mem_familyExtensions_iff.mpr ⟨hpD,
      singleton_subset_iff.mpr (mem_distinctEqualRemainderPairs_iff.mp hp).2.2.2.1⟩
  · intro p hp q hq hfirst
    exact distinctEqualRemainderPairs_fst_injOn F T T'
      (mem_filter.mp hp).1 (mem_filter.mp hq).1 hfirst

theorem card_distinctEqualRemainderPairs_snd_filter_le
    {W : Type*} [DecidableEq W] (F D : Finset (Finset W)) (T T' : W) :
    ((distinctEqualRemainderPairs F T T').filter fun p ↦ p.2 ∈ D).card ≤
      (familyExtensions D {T'}).card := by
  apply card_le_card_of_injOn (fun p ↦ p.2)
  · intro p hp
    obtain ⟨hp, hpD⟩ := mem_filter.mp hp
    exact mem_familyExtensions_iff.mpr ⟨hpD,
      singleton_subset_iff.mpr (mem_distinctEqualRemainderPairs_iff.mp hp).2.2.2.2.1⟩
  · intro p hp q hq hsecond
    change p.2 = q.2 at hsecond
    have hp' := mem_distinctEqualRemainderPairs_iff.mp (mem_filter.mp hp).1
    have hq' := mem_distinctEqualRemainderPairs_iff.mp (mem_filter.mp hq).1
    apply Prod.ext _ hsecond
    calc
      p.1 = insert T (p.1.erase T) := (insert_erase hp'.2.2.2.1).symm
      _ = insert T (q.1.erase T) := by rw [hp'.2.2.2.2.2, hsecond, ← hq'.2.2.2.2.2]
      _ = q.1 := insert_erase hq'.2.2.2.1

theorem card_distinctEqualRemainderPairs_le_split
    {W : Type*} [DecidableEq W] (F D : Finset (Finset W)) (T T' : W) :
    (distinctEqualRemainderPairs F T T').card ≤
      (familyExtensions D {T}).card + (familyExtensions D {T'}).card +
        (distinctEqualRemainderPairs (F \ D) T T').card := by
  let P := distinctEqualRemainderPairs F T T'
  have hsub : P ⊆ (P.filter fun p ↦ p.1 ∈ D) ∪
      (P.filter fun p ↦ p.2 ∈ D) ∪ distinctEqualRemainderPairs (F \ D) T T' := by
    intro p hp
    by_cases hfirst : p.1 ∈ D
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hp, hfirst⟩))
    by_cases hsecond : p.2 ∈ D
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hp, hsecond⟩))
    apply mem_union_right
    have h := mem_distinctEqualRemainderPairs_iff.mp hp
    exact mem_distinctEqualRemainderPairs_iff.mpr
      ⟨mem_sdiff.mpr ⟨h.1, hfirst⟩, mem_sdiff.mpr ⟨h.2.1, hsecond⟩, h.2.2⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  exact Nat.add_le_add_right ((card_union_le _ _).trans
    (Nat.add_le_add (card_distinctEqualRemainderPairs_fst_filter_le F D T T')
      (card_distinctEqualRemainderPairs_snd_filter_le F D T T'))) _

end Erdos207
