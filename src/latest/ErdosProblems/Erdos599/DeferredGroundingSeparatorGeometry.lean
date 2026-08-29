/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingCutAvoidingSelection
import ErdosProblems.Erdos599.GroundingSimultaneousDecode

/-!
# Input geometry for deferred separator grounding

Two pieces of the legacy split separator pipeline are genuinely uniform in
the auxiliary input.  Deferred proxies faithfully name distinct limiting
components, and the essential terminal cut still separates the ambient web.
Making these facts explicit isolates the later obstruction to the
split-specific reduced-fragment and selected-relation layers.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Deferred proxies are literal, distinct recorded rays in the limiting
ladder. -/
theorem popularAuxiliary_proxyPathsFaithful
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L) :
    ProxyPathsFaithful (popularAuxiliaryInput L hL.legal) := by
  constructor
  · intro i
    obtain ⟨a, _ha, hchosen⟩ := i.2
    have hi := L.recorded_mem_inessential
      hL.legal.recordedPathsPersist hchosen
      (b := Ladder.finalStage kappa) (by
        change a.1 + 1 ≤ kappa.ord
        exact (Order.add_one_le_iff).2 a.2)
    change i.1 ∈ L.limitWarp
    exact hi.1
  · intro i j hij
    apply Subtype.ext
    simpa only [popularAuxiliaryInput, infinitePath] using hij

/-- The essential terminal cut of the deferred auxiliary separates the
ambient source from the ambient target. -/
theorem popularAuxiliary_terminalCut_isSeparator
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L) :
    Popular.IsSeparator Gamma
      (popularAuxiliaryInput L hlegal).terminalCut := by
  have hroof : Gamma.source ⊆ Gamma.roof
      (Gamma.terminalFrontier
        (popularAuxiliaryInput L hlegal).ladder.paths) := by
    simpa only [popularAuxiliaryInput, limitWarp] using
      hlegal.roofsSourceAtStages (Ladder.finalStage kappa)
  have hroofEssential : Gamma.source ⊆ Gamma.roof
      (popularAuxiliaryInput L hlegal).terminalCut := by
    intro x hx
    rw [PopularAuxiliary.Input.terminalCut,
      PopularAuxiliary.Input.essentialLadder,
      Gamma.terminalFrontier_essentialWarpPart, Gamma.roof_essential]
    exact hroof hx
  intro p hpSource hpTarget
  exact hroofEssential hpSource p ⟨rfl, hpTarget⟩

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.popularAuxiliary_proxyPathsFaithful
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.popularAuxiliary_terminalCut_isSeparator
