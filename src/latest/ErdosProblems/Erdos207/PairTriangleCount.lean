/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberWeightBudget

/-!
# Counting ambient triangles through a fixed pair

A rooted threat designates a triangle through a fixed distinct pair.  Such a
triangle has only one free vertex, so there are at most `|V|` choices.  This
linear count is the outer factor in the rooted well-spread estimate.
-/

namespace Erdos207

open Finset

/-- Ambient triples containing both prescribed vertices. -/
def universeTriplesThroughPair
    {V : Type*} [Fintype V] [DecidableEq V] (u v : V) :
    Finset (TripleOn V) :=
  (univ : Finset (TripleOn V)).filter fun T ↦ u ∈ T.1 ∧ v ∈ T.1

@[simp]
lemma mem_universeTriplesThroughPair_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} {T : TripleOn V} :
    T ∈ universeTriplesThroughPair u v ↔ u ∈ T.1 ∧ v ∈ T.1 := by
  simp [universeTriplesThroughPair]

/-- One-element subsets, used to retain the third vertex of a rooted
triangle without making a choice. -/
abbrev SingletonOn (V : Type*) := {s : Finset V // s.card = 1}

def eraseThroughPair
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v)
    (T : universeTriplesThroughPair u v) : SingletonOn V :=
  ⟨(T.1.1.erase u).erase v, by
    have hu : u ∈ T.1.1 :=
      (mem_universeTriplesThroughPair_iff.mp T.2).1
    have hv : v ∈ T.1.1 :=
      (mem_universeTriplesThroughPair_iff.mp T.2).2
    have hvErase : v ∈ T.1.1.erase u := mem_erase.mpr ⟨huv.symm, hv⟩
    rw [card_erase_of_mem hvErase, card_erase_of_mem hu, T.1.2]⟩

lemma eraseThroughPair_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v) :
    Function.Injective (eraseThroughPair huv) := by
  intro T U hTU
  apply Subtype.ext
  apply Subtype.ext
  have huT : u ∈ T.1.1 :=
    (mem_universeTriplesThroughPair_iff.mp T.2).1
  have hvT : v ∈ T.1.1 :=
    (mem_universeTriplesThroughPair_iff.mp T.2).2
  have huU : u ∈ U.1.1 :=
    (mem_universeTriplesThroughPair_iff.mp U.2).1
  have hvU : v ∈ U.1.1 :=
    (mem_universeTriplesThroughPair_iff.mp U.2).2
  have hvTErase : v ∈ T.1.1.erase u := mem_erase.mpr ⟨huv.symm, hvT⟩
  have hvUErase : v ∈ U.1.1.erase u := mem_erase.mpr ⟨huv.symm, hvU⟩
  have hErase : (T.1.1.erase u).erase v = (U.1.1.erase u).erase v :=
    congrArg Subtype.val hTU
  calc
    T.1.1 = insert u (T.1.1.erase u) := (insert_erase huT).symm
    _ = insert u (insert v ((T.1.1.erase u).erase v)) := by
      rw [insert_erase hvTErase]
    _ = insert u (insert v ((U.1.1.erase u).erase v)) := by rw [hErase]
    _ = insert u (U.1.1.erase u) := by rw [insert_erase hvUErase]
    _ = U.1.1 := insert_erase huU

/-- At most `|V|` ambient triangles pass through a fixed distinct pair. -/
theorem card_universeTriplesThroughPair_le
    (V : Type*) [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v) :
    (universeTriplesThroughPair u v).card ≤ Fintype.card V := by
  calc
    (universeTriplesThroughPair u v).card =
        Fintype.card (universeTriplesThroughPair u v) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card (SingletonOn V) :=
      Fintype.card_le_of_injective (eraseThroughPair huv)
        (eraseThroughPair_injective huv)
    _ = Nat.choose (Fintype.card V) 1 := by
      simpa only [SingletonOn] using
        (Fintype.card_finset_len (α := V) 1)
    _ = Fintype.card V := Nat.choose_one_right _

end Erdos207
