/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderFrontierInvariants
import ErdosProblems.Erdos599.LadderSuccessorBridge

/-!
# Terminal provenance at a full ladder rung

This file isolates the terminal-level trichotomy needed to classify a
successor-created finite obstruction.  When the rung starts at every source
of its quotient stage, a finite terminal of the successor is either a rung
terminal, the newly adjoined marker, or the terminal of an old inessential
component.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- Terminal provenance for a successor whose rung covers its quotient
source.  The last alternative records an old fixed component: if it were
old-essential, fullness of the rung would force a continuation, contrary to
the fixed-arrow clause. -/
theorem successorTerminal_mem_rung_or_marker_or_strictOld
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {a : Stage kappa}
    (hfull : (L.stageWeb a).initialSet (L.rung a) =
      (L.stageWeb a).source)
    {x : V} (hx : x ∈ Gamma.terminalFrontier (L.successorWarp a)) :
    x ∈ (L.stageWeb a).terminalFrontier (L.rung a) ∨
      (∃ y, L.marker a = some y ∧ x = y) ∨
      x ∈ Gamma.strictRoof
        (Gamma.terminalFrontier (L.warpAt a)) := by
  obtain ⟨q, hqSuccessor, hqx⟩ := hx
  rcases hlegal.successorComponentProvenance a q hqSuccessor with
      ⟨p, hpOld, hpq⟩ | ⟨y, hyMarker, rfl⟩
  · rcases hpq with ⟨hpRay, rfl⟩ |
        ⟨z, hpTerminal, hcontinue | hfixed⟩
    · rw [hpRay] at hqx
      cases hqx
    · obtain ⟨r, hrInitial, hrRung, _hpTerminal, _hextends,
          _hsupport, _hedges, hqTerminal⟩ := hcontinue
      left
      refine ⟨r, hrRung, ?_⟩
      exact (L.terminal?_liftStagePath a r).symm.trans
        (hqTerminal.symm.trans hqx)
    · obtain ⟨hnoRung, hqp⟩ := hfixed
      rw [hqp] at hqx
      right
      right
      have hpx : Gamma.terminal? p = some x := hqx
      have hzx : z = x :=
        Option.some.inj (hpTerminal.symm.trans hpx)
      subst z
      have hpNotEssential :
          p ∉ Gamma.essentialWarpPart (L.warpAt a) := by
        intro hpEssential
        have hxEssential :
            x ∈ Gamma.essential
              (Gamma.terminalFrontier (L.warpAt a)) := by
          obtain ⟨_hpOld, t, hpt, ht⟩ := hpEssential
          have htx : t = x := Option.some.inj (hpt.symm.trans hpx)
          exact htx ▸ ht
        have hxSource : x ∈ (L.stageWeb a).source := by
          change x ∈ L.frontier a
          rw [L.frontier_eq_essential_terminalFrontier
            hlegal.roofsSourceAtStages a]
          exact hxEssential
        have hxInitial :
            x ∈ (L.stageWeb a).initialSet (L.rung a) := by
          rw [hfull]
          exact hxSource
        obtain ⟨r, hrRung, hrInitial⟩ := hxInitial
        exact hnoRung ⟨r, hrRung, hrInitial⟩
      exact Gamma.terminal_mem_strictRoof_of_mem_inessentialPaths
        ⟨hpOld, hpNotEssential⟩ hpx
  · right
    left
    refine ⟨y, hyMarker, ?_⟩
    simpa using hqx.symm

end KappaLadder
end DWeb
end Erdos599
