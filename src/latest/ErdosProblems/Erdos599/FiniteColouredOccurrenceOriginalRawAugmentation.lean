/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceSwitch

/-!
# Retyping a finite current-safe switch as an original finite augmentation

A finite interval-safe word may use the forward warp present at its birth
stage rather than the original forward warp.  If every birth-stage edge is
either original-forward or reference, switching the reference by that word
nevertheless produces an honest augmenting warp contained in the union of
the original two relations.  Its non-reference added edges are original
forward edges, and both edge differences from the reference are finite.

This is an exact constructed bridge, not a converse normalization theorem:
the removed original-reference relation need not yet be interval-convex when
it is expressed relative to the original forward warp.
-/

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {original current Y : Set Gamma.DPath}

/-- A finite safe word over a current warp gives a finite raw augmentation
inside the original-forward/reference union.  In particular, after deleting
the reference edges from the output, every remaining edge is genuinely an
edge of the original forward warp. -/
theorem IsIntervalSafe.exists_originalRawAugmentation_of_current_edges
    (hcurrent : Gamma.IsWarp current) (hY : Gamma.IsWarp Y)
    (hcurrentFinite : Gamma.HasFiniteCharacter current)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hcurrentEdges : familyEdges current ⊆
      familyEdges original ∪ familyEdges Y)
    {Q : FiniteColouredOccurrenceWord current Y}
    (hQ : Q.IsIntervalSafe)
    (hne : Q.vertex 0 ≠ Q.vertex (Fin.last Q.length))
    (hfirst : Q.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y) :
    ∃ A : Set Gamma.DPath,
      Gamma.IsWarp A ∧ Gamma.HasFiniteCharacter A ∧
      familyEdges A = (familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges ∧
      familyEdges A ⊆ familyEdges original ∪ familyEdges Y ∧
      familyEdges A \ familyEdges Y ⊆ familyEdges original ∧
      (familyEdges A \ familyEdges Y).Finite ∧
      (familyEdges Y \ familyEdges A).Finite ∧
      isolatedVertices A = isolatedVertices Y ∧
      Gamma.initialSet A = Gamma.initialSet Y ∪ {Q.vertex 0} ∧
      Gamma.terminalFrontier A = Gamma.terminalFrontier Y ∪
        {Q.vertex (Fin.last Q.length)} := by
  obtain ⟨A, hA, hAfinite, hAedges, hAisolated, hAinitial, hAterminal⟩ :=
    hQ.exists_augmenting_warp hcurrent hY hcurrentFinite hYfinite
      hne hfirst hlast
  have hAsub : familyEdges A ⊆ familyEdges original ∪ familyEdges Y := by
    intro e he
    rw [hAedges] at he
    rcases he with heY | heQ
    · exact Or.inr heY.1
    · exact hcurrentEdges (Q.forwardEdges_subset_familyEdges heQ)
  have hAddedSub : familyEdges A \ familyEdges Y ⊆ familyEdges original := by
    intro e he
    rcases hAsub he.1 with heOriginal | heY
    · exact heOriginal
    · exact (he.2 heY).elim
  have hAddedFinite : (familyEdges A \ familyEdges Y).Finite := by
    apply Q.forwardEdges_finite.subset
    intro e he
    rw [hAedges] at he
    rcases he.1 with heY | heQ
    · exact (he.2 heY.1).elim
    · exact heQ
  have hRemovedFinite : (familyEdges Y \ familyEdges A).Finite := by
    apply Q.backwardEdges_finite.subset
    intro e he
    by_contra heR
    apply he.2
    rw [hAedges]
    exact Or.inl ⟨he.1, heR⟩
  exact ⟨A, hA, hAfinite, hAedges, hAsub, hAddedSub,
    hAddedFinite, hRemovedFinite, hAisolated, hAinitial, hAterminal⟩

#print axioms IsIntervalSafe.exists_originalRawAugmentation_of_current_edges

end Erdos599.Alternating.FiniteColouredOccurrenceWord
