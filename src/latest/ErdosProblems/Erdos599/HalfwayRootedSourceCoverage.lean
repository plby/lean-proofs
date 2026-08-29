/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClause

/-!
# Source coverage after adjoining the actual reference prefixes

Only reference paths meeting the new closed carrier need new source roots.
Paths lost by a moving frontier are also registered in that carrier. This
set-level argument isolates the exact prefix-incidence fact the source
diamond must supply; it does not assume an exact old terminal frontier.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The reference paths whose original source prefix is needed for the
source-diamond construction at an enlarged closed carrier. -/
def sourcePrefixOwners (current : LinkageBlueprint Gamma Y kappa)
    (T X : Set V) : Set Gamma.DPath :=
  (referencePathsMeeting Y T ∩ referencePathsMeeting Y X) \
    referencePathsMeeting Y current.vertexSet

theorem covers_source_of_source_referencePrefix_initials
    (current U : LinkageBlueprint Gamma Y kappa)
    {Told Tnew X : Set V}
    (hcurrent : Gamma.source ⊆
      current.initialSet ∪ current.retainedReferenceInitials Told)
    (holdInitial : current.initialSet ⊆ U.initialSet)
    (hcarrier : U.vertexSet ⊆ current.vertexSet ∪ X)
    (hlost : referencePathsMeeting Y Told \ referencePathsMeeting Y Tnew ⊆
      referencePathsMeeting Y X)
    (hprefix : Gamma.initialSet (sourcePrefixOwners current Told X) ∩ Gamma.source ⊆
      U.initialSet) :
    Gamma.source ⊆ U.initialSet ∪ U.retainedReferenceInitials Tnew := by
  intro x hxSource
  rcases hcurrent hxSource with hxCurrent | hxReference
  · exact Or.inl (holdInitial hxCurrent)
  · obtain ⟨p, hp, hpx⟩ := hxReference
    have hpOld : p ∈ referencePathsMeeting Y Told := hp.1
    have hpAvoid : p ∉ referencePathsMeeting Y current.vertexSet := hp.2
    have initial_if_meets_X (hpX : p ∈ referencePathsMeeting Y X) :
        x ∈ U.initialSet :=
      hprefix ⟨⟨p, ⟨⟨hpOld, hpX⟩, hpAvoid⟩, hpx⟩, hxSource⟩
    by_cases hpU : p ∈ referencePathsMeeting Y U.vertexSet
    · left
      apply initial_if_meets_X
      obtain ⟨v, hvp, hvU⟩ := hpU.2
      rcases hcarrier hvU with hvCurrent | hvX
      · exact False.elim (hpAvoid ⟨hpOld.1, v, hvp, hvCurrent⟩)
      · exact ⟨hpOld.1, v, hvp, hvX⟩
    · by_cases hpNew : p ∈ referencePathsMeeting Y Tnew
      · exact Or.inr ⟨p, ⟨hpNew, hpU⟩, hpx⟩
      · exact Or.inl (initial_if_meets_X (hlost ⟨hpOld, hpNew⟩))

/-- Stronger all-prefix-roots interface, retained for callers that also
activate prefixes whose initial vertices are not ambient sources. -/
theorem covers_source_of_referencePrefix_initials
    (current U : LinkageBlueprint Gamma Y kappa)
    {Told Tnew X : Set V}
    (hcurrent : Gamma.source ⊆
      current.initialSet ∪ current.retainedReferenceInitials Told)
    (holdInitial : current.initialSet ⊆ U.initialSet)
    (hcarrier : U.vertexSet ⊆ current.vertexSet ∪ X)
    (hlost : referencePathsMeeting Y Told \ referencePathsMeeting Y Tnew ⊆
      referencePathsMeeting Y X)
    (hprefix : Gamma.initialSet (sourcePrefixOwners current Told X) ⊆
      U.initialSet) :
    Gamma.source ⊆ U.initialSet ∪ U.retainedReferenceInitials Tnew :=
  covers_source_of_source_referencePrefix_initials current U
    hcurrent holdInitial hcarrier hlost (fun _ hx => hprefix hx.1)

#print axioms covers_source_of_source_referencePrefix_initials
#print axioms covers_source_of_referencePrefix_initials

end Erdos599.Blueprint.LinkageBlueprint
