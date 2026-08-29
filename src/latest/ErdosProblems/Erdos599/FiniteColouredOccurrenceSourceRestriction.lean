/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceReductionTransfer
import ErdosProblems.Erdos599.ColouredSafeFiniteSaturation
import ErdosProblems.Erdos599.SliceCandidate

/-!
# Restricting the forward warp to a finite family of exposed sources

For a set `J` of exposed initials, retain exactly the forward-warp members
rooted in the reference initial set or in `J`.  The resulting subwarp has no
new path endpoints: its exposed initial vertices are literally the values of
`J`, and both endpoint-purity hypotheses used by the coloured-safe
construction are inherited from the original warp.

This is only a source restriction.  It does not assert the finite Hall
inequality or normalize a later current-warp occurrence back to the fixed
forward warp.
-/

noncomputable section

namespace Erdos599.ColouredSafeReverseReachability

open Set DirectedPath Alternating
open CardinalInduction.SliceCandidate

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- The initial vertices retained for a source family `J`: all reference
initials and the underlying vertices of `J`. -/
def restrictedInitials
    (J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)) : Set V :=
  Gamma.initialSet Y ∪ Subtype.val '' J

/-- The full `W`-members whose initial vertices are retained. -/
def sourceRestriction
    (J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)) :
    Set Gamma.DPath :=
  initialPart Gamma W (restrictedInitials J)

theorem sourceRestriction_subset
    (J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)) :
    sourceRestriction J ⊆ W := by
  intro p hp
  exact hp.1

theorem sourceRestriction_isWarp
    (hW : Gamma.IsWarp W)
    (J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)) :
    Gamma.IsWarp (sourceRestriction J) := by
  intro p hp q hq hpq
  exact hW hp.1 hq.1 hpq

theorem sourceRestriction_finiteCharacter
    (hWfin : Gamma.HasFiniteCharacter W)
    (J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)) :
    Gamma.HasFiniteCharacter (sourceRestriction J) := by
  intro p hp
  exact hWfin hp.1

theorem familyEdges_sourceRestriction_subset
    (J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)) :
    familyEdges (sourceRestriction J) ⊆ familyEdges W := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, hp, hep⟩ := he
  exact ⟨p, hp.1, hep⟩

theorem terminalFrontier_sourceRestriction_subset
    (J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)) :
    Gamma.terminalFrontier (sourceRestriction J) ⊆
      Gamma.terminalFrontier W := by
  rintro x ⟨p, hp, hpx⟩
  exact ⟨p, hp.1, hpx⟩

/-- Under the ordinary reference-source containment, the restricted warp
has exactly the requested initial set. -/
theorem initialSet_sourceRestriction
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)) :
    Gamma.initialSet (sourceRestriction J) = restrictedInitials J := by
  rw [sourceRestriction, initialSet_initialPart]
  apply Set.inter_eq_right.mpr
  rintro x (hxY | hxJ)
  · exact hsource hxY
  · obtain ⟨s, hsJ, rfl⟩ := hxJ
    exact s.property.1

/-- The restricted warp inherits initial endpoint purity. -/
theorem sourceRestriction_initial_pure
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)) :
    Gamma.initialSet (sourceRestriction J) ∩ Gamma.vertexSet Y ⊆
      Gamma.initialSet Y := by
  rw [initialSet_sourceRestriction hsource]
  rintro x ⟨hx, hxY⟩
  rcases hx with hxInitial | hxJ
  · exact hxInitial
  · obtain ⟨s, _hsJ, hsx⟩ := hxJ
    subst x
    exact False.elim (s.property.2 hxY)

/-- The restricted warp inherits terminal endpoint purity because whole
forward members, rather than finite carrier fragments, were retained. -/
theorem sourceRestriction_terminal_pure
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)) :
    Gamma.terminalFrontier (sourceRestriction J) ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y := by
  intro x hx
  exact hterminal
    ⟨terminalFrontier_sourceRestriction_subset J hx.1, hx.2⟩

/-- The uncovered initial vertices of the restricted warp are exactly the
underlying vertices represented by `J`. -/
theorem initialSet_sourceRestriction_sdiff_vertexSet
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)) :
    Gamma.initialSet (sourceRestriction J) \ Gamma.vertexSet Y =
      Subtype.val '' J := by
  rw [initialSet_sourceRestriction hsource]
  ext x
  constructor
  · rintro ⟨hxInitial | hxJ, hxOff⟩
    · exact False.elim (hxOff (initialSet_subset_vertexSet Y hxInitial))
    · exact hxJ
  · rintro ⟨s, hsJ, rfl⟩
    exact ⟨Or.inr ⟨s, hsJ, rfl⟩, s.property.2⟩

/-- A finite safe terminal for the source-restricted warp is still a safe
terminal for the original forward warp. -/
theorem safelyReachable_sourceRestriction_subset
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)) (s : V) :
    safelyReachable (sourceRestriction J) Y s ⊆ safelyReachable W Y s := by
  rintro t ⟨ht, Q, hQ, hfirst, hlast⟩
  exact FiniteColouredOccurrenceWord.mem_safelyReachable_of_forwardEdges_subset
    hQ
    (Q.forwardEdges_subset_familyEdges.trans
      (familyEdges_sourceRestriction_subset J))
    hfirst hlast
    ⟨terminalFrontier_sourceRestriction_subset J ht.1, ht.2⟩

#print axioms initialSet_sourceRestriction
#print axioms sourceRestriction_initial_pure
#print axioms sourceRestriction_terminal_pure
#print axioms initialSet_sourceRestriction_sdiff_vertexSet
#print axioms safelyReachable_sourceRestriction_subset

end Erdos599.ColouredSafeReverseReachability
