/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CrossConfigurationPairs

/-! # The four-way distinct-pair union bound at an arbitrary profile -/

namespace Erdos207

open Finset

noncomputable section

theorem card_profiledDistinctPairs_union_le_four_profile
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V) (t : VortexProfile ell) :
    (W.profiledDistinctEqualRemainderPairs (F ∪ G) T T' t).card ≤
      (W.profiledDistinctEqualRemainderPairs F T T' t).card + (distinctEqualRemainderPairs G T T').card +
        (crossDistinctConfigurationPairs F G T T').card + (crossDistinctConfigurationPairs G F T T').card := by
  let A := W.profiledDistinctEqualRemainderPairs F T T' t
  let B := distinctEqualRemainderPairs G T T'
  let C := crossDistinctConfigurationPairs F G T T'
  let D := crossDistinctConfigurationPairs G F T T'
  have hsub : W.profiledDistinctEqualRemainderPairs (F ∪ G) T T' t ⊆ A ∪ B ∪ C ∪ D := by
    intro p hp
    obtain ⟨hp1, hp2, hne, hT, hT', hrem, hprof⟩ := (W.mem_profiledDistinctEqualRemainderPairs_iff _ _ _ _ _).mp hp
    rcases mem_union.mp hp1 with hF1 | hG1 <;> rcases mem_union.mp hp2 with hF2 | hG2
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _
        ((W.mem_profiledDistinctEqualRemainderPairs_iff _ _ _ _ _).mpr ⟨hF1, hF2, hne, hT, hT', hrem, hprof⟩)))
    · exact mem_union_left _ (mem_union_right _
        (mem_crossDistinctConfigurationPairs_iff.mpr ⟨hF1, hG2, hne, hT, hT', hrem⟩))
    · exact mem_union_right _
        (mem_crossDistinctConfigurationPairs_iff.mpr ⟨hG1, hF2, hne, hT, hT', hrem⟩)
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _
        (mem_distinctEqualRemainderPairs_iff.mpr ⟨hG1, hG2, hne, hT, hT', hrem⟩)))
  calc
    _ ≤ (A ∪ B ∪ C ∪ D).card := card_le_card hsub
    _ ≤ (A ∪ B ∪ C).card + D.card := card_union_le _ _
    _ ≤ ((A ∪ B).card + C.card) + D.card := Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (card_union_le _ _) _) _

end

end Erdos207
