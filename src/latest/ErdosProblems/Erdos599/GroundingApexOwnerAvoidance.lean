/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingRequestAvoidingControls
import ErdosProblems.Erdos599.GroundingFragmentCarrier

/-!
# The countable exceptional carrier of the request's own reference owner

At most one ladder component contains a given request apex in its trace.
Its trace minus the apex is countable and misses the join of the request
fan. Meeting that carrier is therefore a nonstationary exception which
can be excluded before making the actual simultaneous selection.
-/

noncomputable section

namespace Erdos599.GroundingApexOwnerAvoidance

open Set DirectedPath PopularAuxiliary.Input PopularGroundingBridge

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable {J : PopularAuxiliary.Input Gamma I} {C : Set J.LV}

/-- The full trace of the reference owner of this apex, if there is one. -/
def ownerCarrier (r : Request J C) : Set J.LV :=
  {z | ∃ Y ∈ J.ladder.paths,
    requestAuxVertex r ∈ PopularSwitching.ladderTrace J Y ∧
      z ∈ PopularSwitching.ladderTrace J Y}

theorem ownerCarrier_countable (r : Request J C) : (ownerCarrier r).Countable := by
  classical
  by_cases howner : ∃ Y ∈ J.ladder.paths,
      requestAuxVertex r ∈ PopularSwitching.ladderTrace J Y
  · obtain ⟨Y, hY, hapex⟩ := howner
    apply (PopularSwitching.ladderTrace_countable J Y).mono
    rintro z ⟨Z, hZ, hapexZ, hzZ⟩
    have hZY : Z = Y := by
      by_contra hne
      exact Set.disjoint_left.1
        (GroundingFragmentCarrier.ladderTrace_disjoint_of_ne J hZ hY hne)
        hapexZ hapex
    exact hZY ▸ hzZ
  · apply Set.countable_empty.mono
    rintro z ⟨Y, hY, hapex, _hzY⟩
    exact (howner ⟨Y, hY, hapex⟩).elim

/-- The apex itself is retained, while all its other owner gadgets are forbidden. -/
def offApexOwnerCarrier (r : Request J C) : Set J.LV :=
  ownerCarrier r \ {requestAuxVertex r}

theorem offApexOwnerCarrier_countable (r : Request J C) :
    (offApexOwnerCarrier r).Countable :=
  (ownerCarrier_countable r).mono Set.sdiff_subset

theorem apex_not_mem_offApexOwnerCarrier (r : Request J C) :
    requestAuxVertex r ∉ offApexOwnerCarrier r :=
  fun h ↦ h.2 rfl

def collidingPaths (r : Request J C) : Set (FinitePath J.lambda.graph) :=
  GroundingAvoidingControls.meetsCarrier (offApexOwnerCarrier r)

/-- Removing all such paths from the fan costs only nonstationarily many indices. -/
theorem collidingPaths_indices_nonstationary
    {kappa : Cardinal.{u}} {U : Popular.KappaIndexed J.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request J S.cut) :
    ¬ Stationary.IsStationaryBelow kappa
      (GroundingSelection.restrictedIndices U (requestFan S r) (collidingPaths r)) :=
  GroundingRequestAvoidingControls.meetsCarrier_indices_nonstationary_of_apex_not_mem
    S (offApexOwnerCarrier r) (offApexOwnerCarrier_countable r) r
      (apex_not_mem_offApexOwnerCarrier r)

#print axioms ownerCarrier_countable
#print axioms collidingPaths_indices_nonstationary

end Erdos599.GroundingApexOwnerAvoidance
