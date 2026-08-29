/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedProjectionCutOccurrence

/-!
# Occurrence-level contact sides

The active lifted family meets the incoming-copy image of a set only at
finite terminals, and it meets the outgoing-copy image only at initials.
Consequently the concrete macro-owned simultaneous assignment separates
same-side cut contacts even when projection identifies an incoming and an
outgoing occurrence downstairs.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

open Set DirectedPath _root_.Erdos599.Alternating
open Alternating.FracturedDuplication

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

/-- Incoming copies on active lifted members occur only as finite terminals. -/
theorem cutEndpointPure_activeLiftedPaths_incomingImage
    (Z : FracturedWarp Gamma) (X : Set V) :
    CutEndpointPure (activeLiftedPaths Z) (incoming '' X) := by
  rintro P ⟨p, hp, rfl⟩ z hz ⟨x, hxX, rfl⟩
  right
  obtain ⟨y, hyp, hy⟩ :=
    (mem_support_liftPath Z p (incoming x)).1 hz
  have hyx : y = x := by
    simpa only [project_occurrence, project_incoming] using
      congrArg project hy
  subst y
  have hterm : Gamma.terminal? p = some x := by
    by_cases hi : x = p.initial
    · have hcontra : outgoing x = incoming x := by
        simpa [occurrence, hi] using hy
      exact False.elim (outgoing_ne_incoming x hcontra)
    · by_cases ht : Gamma.terminal? p = some x
      · exact ht
      · have hcontra : plain x = incoming x := by
          simpa [occurrence, hi, ht] using hy
        exact False.elim (Role.noConfusion (congrArg Prod.snd hcontra))
  change (liftPath Z p).terminal? = some (incoming x)
  have hterm' : p.terminal? = some x := by
    simpa [DWeb.terminal?] using hterm
  rw [terminal_liftPath, hterm']
  simpa only [Option.map_some, Option.some.injEq] using hy

/-- Outgoing copies on active lifted members occur only as initials. -/
theorem cutEndpointPure_activeLiftedPaths_outgoingImage
    (Z : FracturedWarp Gamma) (X : Set V) :
    CutEndpointPure (activeLiftedPaths Z) (outgoing '' X) := by
  rintro P ⟨p, hp, rfl⟩ z hz ⟨x, hxX, rfl⟩
  left
  obtain ⟨y, hyp, hy⟩ :=
    (mem_support_liftPath Z p (outgoing x)).1 hz
  have hyx : y = x := by
    simpa only [project_occurrence, project_outgoing] using
      congrArg project hy
  subst y
  have hi : x = p.initial := by
    by_cases hi : x = p.initial
    · exact hi
    · by_cases ht : Gamma.terminal? p = some x
      · have hcontra : incoming x = outgoing x := by
          simpa [occurrence, hi, ht] using hy
        exact False.elim (outgoing_ne_incoming x hcontra.symm)
      · have hcontra : plain x = outgoing x := by
          simpa [occurrence, hi, ht] using hy
        exact False.elim (Role.noConfusion (congrArg Prod.snd hcontra))
  rw [initial_liftPath, ← hi]
  exact hy

/-- Same incoming projected contact forces equality of the selected lifted
sources. This is a consequence of the actual macro-owned construction, not
an assumed group compatibility field. -/
theorem MacroOwnedBracketSimultaneousAssignment.source_eq_of_common_incoming
    (Z : FracturedWarp Gamma) (X : Set V)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (A : MacroOwnedBracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (s t : {z // z ∈ (web Gamma Z).initialSet (activeLiftedPaths Z) \
      (web Gamma Z).initialSet
        (liftedReference Z (activeReference Z Y))})
    {x : V}
    (hs : incoming x ∈ (A.assigned s).vertexSet)
    (ht : incoming x ∈ (A.assigned t).vertexSet)
    (hxX : x ∈ X) : s = t := by
  by_contra hst
  have hdis := A.contactSet_pairwiseDisjoint
    (activeLiftedPaths_isWarp Z)
    (liftedReference_isWarp Z
      (activeReference_isWarp Z hY))
    (boundaryAligned_activeLifted Z hboundary hY hYfinite)
    (cutEndpointPure_activeLiftedPaths_incomingImage Z X)
    s t hst
  exact Set.disjoint_left.1 hdis
    ⟨hs, ⟨x, hxX, rfl⟩⟩ ⟨ht, ⟨x, hxX, rfl⟩⟩

/-- Same outgoing projected contact forces equality of the selected lifted
sources. -/
theorem MacroOwnedBracketSimultaneousAssignment.source_eq_of_common_outgoing
    (Z : FracturedWarp Gamma) (X : Set V)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (A : MacroOwnedBracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (s t : {z // z ∈ (web Gamma Z).initialSet (activeLiftedPaths Z) \
      (web Gamma Z).initialSet
        (liftedReference Z (activeReference Z Y))})
    {x : V}
    (hs : outgoing x ∈ (A.assigned s).vertexSet)
    (ht : outgoing x ∈ (A.assigned t).vertexSet)
    (hxX : x ∈ X) : s = t := by
  by_contra hst
  have hdis := A.contactSet_pairwiseDisjoint
    (activeLiftedPaths_isWarp Z)
    (liftedReference_isWarp Z
      (activeReference_isWarp Z hY))
    (boundaryAligned_activeLifted Z hboundary hY hYfinite)
    (cutEndpointPure_activeLiftedPaths_outgoingImage Z X)
    s t hst
  exact Set.disjoint_left.1 hdis
    ⟨hs, ⟨x, hxX, rfl⟩⟩ ⟨ht, ⟨x, hxX, rfl⟩⟩

end Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

#print axioms Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel.cutEndpointPure_activeLiftedPaths_incomingImage
#print axioms Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel.MacroOwnedBracketSimultaneousAssignment.source_eq_of_common_incoming
