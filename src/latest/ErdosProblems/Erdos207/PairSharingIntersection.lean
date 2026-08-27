/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairStarCardinality

/-! # Nine possible pair-sharing intersections for edge-disjoint roots -/

namespace Erdos207

open Finset

noncomputable section

theorem triple_eq_of_containing_distinct_pairs
    {V : Type*} [DecidableEq V] {P Q : Finset V} {T U : TripleOn V}
    (hP : P.card = 2) (hQ : Q.card = 2) (hne : P ≠ Q)
    (hPT : P ⊆ T.1) (hPU : P ⊆ U.1) (hQT : Q ⊆ T.1) (hQU : Q ⊆ U.1) : T = U := by
  by_contra h
  have hi := distinct_triples_inter_card_le_two h
  have heP : P = T.1 ∩ U.1 := eq_of_subset_of_card_le
    (fun x hx ↦ mem_inter.mpr ⟨hPT hx, hPU hx⟩) (by rw [hP]; exact hi)
  have heQ : Q = T.1 ∩ U.1 := eq_of_subset_of_card_le
    (fun x hx ↦ mem_inter.mpr ⟨hQT hx, hQU hx⟩) (by rw [hQ]; exact hi)
  exact hne (heP.trans heQ.symm)

theorem card_triplesContaining_distinct_pairs_le_one
    {V : Type*} [Fintype V] [DecidableEq V] {P Q : Finset V}
    (hP : P.card = 2) (hQ : Q.card = 2) (hne : P ≠ Q) :
    (universeTriplesContainingPair P ∩ universeTriplesContainingPair Q).card ≤ 1 := by
  apply card_le_one.mpr
  intro T hT U hU
  have ht := mem_inter.mp hT
  have hu := mem_inter.mp hU
  exact triple_eq_of_containing_distinct_pairs hP hQ hne
    (mem_universeTriplesContainingPair_iff.mp ht.1) (mem_universeTriplesContainingPair_iff.mp hu.1)
    (mem_universeTriplesContainingPair_iff.mp ht.2) (mem_universeTriplesContainingPair_iff.mp hu.2)

theorem card_pairSharing_inter_le_nine
    {V : Type*} [Fintype V] [DecidableEq V] {T T' : TripleOn V}
    (hdis : (T.1 ∩ T'.1).card ≤ 1) :
    (triplesSharingPair T ∩ triplesSharingPair T').card ≤ 9 := by
  let pairs := T.1.powersetCard 2 ×ˢ T'.1.powersetCard 2
  let C := fun p : Finset V × Finset V ↦
    universeTriplesContainingPair p.1 ∩ universeTriplesContainingPair p.2
  have hsub : triplesSharingPair T ∩ triplesSharingPair T' ⊆ pairs.biUnion C := by
    intro U hU
    obtain ⟨P, hP, hUP⟩ := mem_biUnion.mp
      (triplesSharingPair_subset_pair_union T (mem_inter.mp hU).1)
    obtain ⟨Q, hQ, hUQ⟩ := mem_biUnion.mp
      (triplesSharingPair_subset_pair_union T' (mem_inter.mp hU).2)
    exact mem_biUnion.mpr ⟨(P, Q), mem_product.mpr ⟨hP, hQ⟩, mem_inter.mpr ⟨hUP, hUQ⟩⟩
  have hcount : ∀ p ∈ pairs, (C p).card ≤ 1 := by
    intro p hp
    have hP := mem_powersetCard.mp (mem_product.mp hp).1
    have hQ := mem_powersetCard.mp (mem_product.mp hp).2
    apply card_triplesContaining_distinct_pairs_le_one hP.2 hQ.2
    intro heq
    have hsubset : p.1 ⊆ T.1 ∩ T'.1 := fun x hx ↦
      mem_inter.mpr ⟨hP.1 hx, hQ.1 (heq ▸ hx)⟩
    have hsize := card_le_card hsubset
    omega
  calc
    _ ≤ (pairs.biUnion C).card := card_le_card hsub
    _ ≤ ∑ p ∈ pairs, (C p).card := card_biUnion_le
    _ ≤ ∑ _p ∈ pairs, 1 := sum_le_sum hcount
    _ = 9 := by simp [pairs, card_product, card_powersetCard, T.2, T'.2]

end

end Erdos207
