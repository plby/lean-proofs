/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredLimitHitClosure
import ErdosProblems.Erdos599.HalfwayLadderReference

/-!
# Transport from the limiting reference to a selected-stage reference

The imaginary reference in the global half-way recursion is the limiting
ladder warp and may contain rays.  The finite reference used by a local
Assertion 9.31 transaction is instead the essential part of the accumulated
warp at the selected stage.  These families must not be identified.

This file proves the source-faithful bridge: if a limiting reference member
hits the selected frontier, the essential member ending at that hit is a
prefix of the limiting member.  Thus the local member is finite and retains
the same initial segment without asserting that the global family itself has
finite character.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {kappa : Cardinal.{u}}

/-- Deferred ladder legality has the same stage-to-limit extension theorem
as split legality.  Its proof uses only regularity, the direct-limit growth
law, and pairwise disjointness of the final warp. -/
theorem KappaLadder.Deferred.HalfwayGeometry.extends_limitWarp_of_stage_intersects
    {L : Gamma.KappaLadder kappa}
    (hL : KappaLadder.Deferred.HalfwayGeometry L)
    {a : Ladder.Stage kappa} {q p : Gamma.DPath}
    (hq : q ∈ L.warpAt a) (hp : p ∈ L.limitWarp)
    (hqp : (q.support ∩ p.support).Nonempty) :
    Gamma.Extends q p := by
  have hKappaLimit : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨r, hr, hqr⟩ := hL.limitStages.grows_to_limit
    (Ladder.finalStage kappa) hKappaLimit ⟨a.1, a.2⟩ q hq
  have hrpMeet : (r.support ∩ p.support).Nonempty := by
    obtain ⟨x, hxq, hxp⟩ := hqp
    exact ⟨x, Gamma.support_mono_of_extends hqr hxq, hxp⟩
  have hrp : r = p := by
    by_contra hne
    obtain ⟨x, hxr, hxp⟩ := hrpMeet
    exact Set.disjoint_left.1
      (hL.warpStages (Ladder.finalStage kappa) hr hp hne) hxr hxp
  rwa [hrp] at hqr

end DWeb

namespace Blueprint.LinkageBlueprint

open DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {kappa : Cardinal.{u}}

/-- A concrete frontier hit by a global limiting-reference member determines
a finite member of the selected local reference which ends at that hit and
is a prefix of the global member. -/
theorem ladderReference.exists_prefix_of_limitWarp_frontier_hit
    {L : Gamma.KappaLadder kappa}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a : Ladder.Stage kappa} {p : Gamma.DPath}
    (hp : p ∈ L.limitWarp) {x : V}
    (hxFrontier : x ∈ L.frontier a) (hxp : x ∈ p.support) :
    ∃ q ∈ ladderReference L a,
      q.terminal? = some x ∧ Gamma.Extends q p := by
  have hxTerminal : x ∈
      Gamma.terminalFrontier (ladderReference L a) := by
    rw [ladderReference.terminalFrontier_eq hL]
    exact hxFrontier
  obtain ⟨q, hqReference, hqTerminal⟩ := hxTerminal
  have hmeet : (q.support ∩ p.support).Nonempty :=
    ⟨x, Gamma.terminal_mem_support hqTerminal, hxp⟩
  have hext : Gamma.Extends q p :=
    hL.extends_limitWarp_of_stage_intersects hqReference.1 hp hmeet
  exact ⟨q, hqReference, hqTerminal, hext⟩

/-- Set-level form used by the stage-selection transaction. -/
theorem ladderReference.limitWarp_meeting_frontier_has_prefix
    {L : Gamma.KappaLadder kappa}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a : Ladder.Stage kappa} {p : Gamma.DPath}
    (hp : p ∈ L.limitWarp)
    (hhit : (L.frontier a ∩ p.support).Nonempty) :
    ∃ q ∈ ladderReference L a, Gamma.Extends q p := by
  obtain ⟨x, hxFrontier, hxp⟩ := hhit
  obtain ⟨q, hq, _hqTerminal, hext⟩ :=
    ladderReference.exists_prefix_of_limitWarp_frontier_hit
      hL hp hxFrontier hxp
  exact ⟨q, hq, hext⟩

#print axioms
  DWeb.KappaLadder.Deferred.HalfwayGeometry.extends_limitWarp_of_stage_intersects
#print axioms ladderReference.exists_prefix_of_limitWarp_frontier_hit
#print axioms ladderReference.limitWarp_meeting_frontier_has_prefix

end Blueprint.LinkageBlueprint
end Erdos599
