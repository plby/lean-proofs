/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceCandidate

/-!
# Union of vertex-disjoint linkages

This cardinal-free lemma is kept independently of the singular retargeting
construction so regular halfway transactions can use it without importing
that larger construction.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularRetargetedRow

open DirectedPath

universe u

variable {V : Type u}

/-- Two vertex-disjoint linkages to one target can be united. -/
theorem linkageBetween_union_of_vertexSet_disjoint
    (G : DWeb V) {A B C : Set V} {P Q : Set G.DPath}
    (hP : IsLinkageBetween G A C P)
    (hQ : IsLinkageBetween G B C Q)
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet Q)) :
    IsLinkageBetween G (A ∪ B) C (P ∪ Q) := by
  have hAvertex : A ⊆ G.vertexSet P := by
    rw [← hP.initialSet_eq]
    rintro x ⟨p, hp, rfl⟩
    exact ⟨p, hp, p.initial_mem_support⟩
  have hBvertex : B ⊆ G.vertexSet Q := by
    rw [← hQ.initialSet_eq]
    rintro x ⟨q, hq, rfl⟩
    exact ⟨q, hq, q.initial_mem_support⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rcases hp with hpP | hpQ <;> rcases hq with hqP | hqQ
    · exact hP.isWarp hpP hqP hpq
    · apply Set.disjoint_left.2
      intro x hxp hxq
      exact Set.disjoint_left.1 hdisjoint
        ⟨p, hpP, hxp⟩ ⟨q, hqQ, hxq⟩
    · apply Set.disjoint_left.2
      intro x hxp hxq
      exact Set.disjoint_left.1 hdisjoint
        ⟨q, hqP, hxq⟩ ⟨p, hpQ, hxp⟩
    · exact hQ.isWarp hpQ hqQ hpq
  · intro p hp
    rcases hp with hpP | hpQ
    · exact hP.finiteCharacter hpP
    · exact hQ.finiteCharacter hpQ
  · rw [G.initialSet_union, hP.initialSet_eq, hQ.initialSet_eq]
  · intro x hx
    obtain ⟨p, hpP | hpQ, hpx⟩ := hx
    · exact hP.terminalFrontier_subset ⟨p, hpP, hpx⟩
    · exact hQ.terminalFrontier_subset ⟨p, hpQ, hpx⟩
  · intro p hp
    rcases hp with hpP | hpQ
    · have hpath := hP.endpointPure p hpP
      rcases hpath with ⟨q, rfl, hends, hsource⟩
      have havoidB : Disjoint q.support B := by
        rw [Set.disjoint_left]
        intro x hxq hxB
        exact Set.disjoint_left.1 hdisjoint
          ⟨.inl q, hpP, hxq⟩ (hBvertex hxB)
      refine ⟨q, rfl, ?_, ?_⟩
      · apply Set.Subset.antisymm
        · rintro x ⟨hxq, (hxA | hxB) | hxC⟩
          · exact hends ▸ ⟨hxq, Or.inl hxA⟩
          · exact False.elim (Set.disjoint_left.1 havoidB hxq hxB)
          · exact hends ▸ ⟨hxq, Or.inr hxC⟩
        · intro x hx
          have hxOld : x ∈ q.support ∩ (A ∪ C) := hends.symm ▸ hx
          exact ⟨hxOld.1, hxOld.2.elim
            (fun hxA ↦ Or.inl (Or.inl hxA)) Or.inr⟩
      · apply Set.Subset.antisymm
        · rintro x ⟨hxq, hxA | hxB⟩
          · exact hsource ▸ ⟨hxq, hxA⟩
          · exact False.elim (Set.disjoint_left.1 havoidB hxq hxB)
        · intro x hx
          have hxOld : x ∈ q.support ∩ A := hsource.symm ▸ hx
          exact ⟨hxOld.1, Or.inl hxOld.2⟩
    · have hpath := hQ.endpointPure p hpQ
      rcases hpath with ⟨q, rfl, hends, hsource⟩
      have havoidA : Disjoint q.support A := by
        rw [Set.disjoint_left]
        intro x hxq hxA
        exact Set.disjoint_left.1 hdisjoint
          (hAvertex hxA) ⟨.inl q, hpQ, hxq⟩
      refine ⟨q, rfl, ?_, ?_⟩
      · apply Set.Subset.antisymm
        · rintro x ⟨hxq, (hxA | hxB) | hxC⟩
          · exact False.elim (Set.disjoint_left.1 havoidA hxq hxA)
          · exact hends ▸ ⟨hxq, Or.inl hxB⟩
          · exact hends ▸ ⟨hxq, Or.inr hxC⟩
        · intro x hx
          have hxOld : x ∈ q.support ∩ (B ∪ C) := hends.symm ▸ hx
          exact ⟨hxOld.1, hxOld.2.elim
            (fun hxB ↦ Or.inl (Or.inr hxB)) Or.inr⟩
      · apply Set.Subset.antisymm
        · rintro x ⟨hxq, hxA | hxB⟩
          · exact False.elim (Set.disjoint_left.1 havoidA hxq hxA)
          · exact hsource ▸ ⟨hxq, hxB⟩
        · intro x hx
          have hxOld : x ∈ q.support ∩ B := hsource.symm ▸ hx
          exact ⟨hxOld.1, Or.inr hxOld.2⟩

end SingularRetargetedRow
end CardinalInduction
end Erdos599
