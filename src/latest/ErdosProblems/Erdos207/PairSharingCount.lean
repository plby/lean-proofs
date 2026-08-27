/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairTriangleCount

/-!
# Counting triples which share a pair

The order-four rooted threats consist of two triples spanning at most four
vertices.  Their two triples therefore share a pair.  This file records the
linear ambient bound for the possible second triple.
-/

namespace Erdos207

open Finset

/-- Ambient triples which contain a prescribed two-element set. -/
def universeTriplesContainingPair
    {V : Type*} [Fintype V] [DecidableEq V] (P : Finset V) :
    Finset (TripleOn V) :=
  (univ : Finset (TripleOn V)).filter fun T ↦ P ⊆ T.1

@[simp]
lemma mem_universeTriplesContainingPair_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : Finset V} {T : TripleOn V} :
    T ∈ universeTriplesContainingPair P ↔ P ⊆ T.1 := by
  simp [universeTriplesContainingPair]

def eraseContainingPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset V) (hP : P.card = 2)
    (T : universeTriplesContainingPair P) : SingletonOn V :=
  ⟨T.1.1 \ P, by
    rw [card_sdiff_of_subset
      (mem_universeTriplesContainingPair_iff.mp T.2), T.1.2, hP]⟩

lemma eraseContainingPair_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset V) (hP : P.card = 2) :
    Function.Injective (eraseContainingPair P hP) := by
  intro T U hTU
  apply Subtype.ext
  apply Subtype.ext
  have hdiff : T.1.1 \ P = U.1.1 \ P :=
    congrArg Subtype.val hTU
  have hPT : P ⊆ T.1.1 :=
    mem_universeTriplesContainingPair_iff.mp T.2
  have hPU : P ⊆ U.1.1 :=
    mem_universeTriplesContainingPair_iff.mp U.2
  calc
    T.1.1 = P ∪ (T.1.1 \ P) := (union_sdiff_of_subset hPT).symm
    _ = P ∪ (U.1.1 \ P) := by rw [hdiff]
    _ = U.1.1 := union_sdiff_of_subset hPU

/-- At most `|V|` triples contain a fixed pair. -/
theorem card_universeTriplesContainingPair_le
    (V : Type*) [Fintype V] [DecidableEq V]
    (P : Finset V) (hP : P.card = 2) :
    (universeTriplesContainingPair P).card ≤ Fintype.card V := by
  calc
    (universeTriplesContainingPair P).card =
        Fintype.card (universeTriplesContainingPair P) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card (SingletonOn V) :=
      Fintype.card_le_of_injective (eraseContainingPair P hP)
        (eraseContainingPair_injective P hP)
    _ = Nat.choose (Fintype.card V) 1 := by
      simpa only [SingletonOn] using
        (Fintype.card_finset_len (α := V) 1)
    _ = Fintype.card V := Nat.choose_one_right _

/-- All triples whose intersection with `T` contains a pair. -/
def triplesSharingPair
    {V : Type*} [Fintype V] [DecidableEq V] (T : TripleOn V) :
    Finset (TripleOn V) :=
  (univ : Finset (TripleOn V)).filter fun U ↦ 2 ≤ (T.1 ∩ U.1).card

@[simp]
lemma mem_triplesSharingPair_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {T U : TripleOn V} :
    U ∈ triplesSharingPair T ↔ 2 ≤ (T.1 ∩ U.1).card := by
  simp [triplesSharingPair]

lemma triplesSharingPair_subset_pair_union
    {V : Type*} [Fintype V] [DecidableEq V] (T : TripleOn V) :
    triplesSharingPair T ⊆
      (T.1.powersetCard 2).biUnion fun P ↦
        universeTriplesContainingPair P := by
  intro U hU
  have hinter : 2 ≤ (T.1 ∩ U.1).card :=
    mem_triplesSharingPair_iff.mp hU
  obtain ⟨P, hP⟩ := powersetCard_nonempty.mpr hinter
  have hPT : P ⊆ T.1 :=
    (mem_powersetCard.mp hP).1.trans inter_subset_left
  have hPU : P ⊆ U.1 :=
    (mem_powersetCard.mp hP).1.trans inter_subset_right
  apply mem_biUnion.mpr
  refine ⟨P, mem_powersetCard.mpr
    ⟨hPT, (mem_powersetCard.mp hP).2⟩, ?_⟩
  exact mem_universeTriplesContainingPair_iff.mpr hPU

/-- A triple has three pairs, and each pair has at most `|V|` extensions. -/
theorem card_triplesSharingPair_le
    (V : Type*) [Fintype V] [DecidableEq V] (T : TripleOn V) :
    (triplesSharingPair T).card ≤ 3 * Fintype.card V := by
  calc
    (triplesSharingPair T).card ≤
        ((T.1.powersetCard 2).biUnion fun P ↦
          universeTriplesContainingPair P).card :=
      card_le_card (triplesSharingPair_subset_pair_union T)
    _ ≤ ∑ P ∈ T.1.powersetCard 2,
        (universeTriplesContainingPair P).card :=
      card_biUnion_le
    _ ≤ ∑ _P ∈ T.1.powersetCard 2, Fintype.card V := by
      apply sum_le_sum
      intro P hP
      exact card_universeTriplesContainingPair_le V P
        (mem_powersetCard.mp hP).2
    _ = 3 * Fintype.card V := by
      rw [sum_const, nsmul_eq_mul, card_powersetCard, T.2]
      norm_num

end Erdos207
