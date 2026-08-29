/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedAuxiliary
import ErdosProblems.Erdos599.SplitGroundingSeparator818
import ErdosProblems.Erdos599.GroundingErasedCarrierRank

/-!
# Common separator geometry for the grounded split auxiliary

The grounded auxiliary changes only which recorded components are admitted
as sources.  Its ladder is still the limiting ladder.  Consequently its
terminal cut has the same ambient separation property, and every proxy still
faithfully names a distinct limiting-ladder component.  These are the two
input-level facts needed by the generic decoded-carrier machinery.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb.KappaLadder

open GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Grounded split proxies faithfully name distinct members of the limiting
ladder.  Groundedness is used to select the proxy source, while membership in
the limiting warp follows from recorded-path persistence. -/
theorem splitGroundedPopularAuxiliary_proxyPathsFaithful
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :
    ProxyPathsFaithful (L.splitGroundedPopularAuxiliaryInput hL.legal) := by
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
    simpa only [splitGroundedPopularAuxiliaryInput,
      splitGroundedInfinitePath] using hij

/-- The terminal cut of the grounded split auxiliary separates the ambient
source from the ambient target.  This is the same limiting-warp statement as
for the all-record split auxiliary; it does not depend on its source index
type. -/
theorem splitGroundedPopularAuxiliary_terminalCut_isSeparator
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal) :
    Popular.IsSeparator Gamma
      (L.splitGroundedPopularAuxiliaryInput hL).terminalCut := by
  have hroof : Gamma.source ⊆ Gamma.roof
      (Gamma.terminalFrontier
        (L.splitGroundedPopularAuxiliaryInput hL).ladder.paths) := by
    simpa only [splitGroundedPopularAuxiliaryInput, limitWarp] using
      hL.roofsSourceAtStages (Ladder.finalStage kappa)
  have hroofEssential : Gamma.source ⊆ Gamma.roof
      (L.splitGroundedPopularAuxiliaryInput hL).terminalCut := by
    intro x hx
    rw [PopularAuxiliary.Input.terminalCut,
      PopularAuxiliary.Input.essentialLadder,
      Gamma.terminalFrontier_essentialWarpPart, Gamma.roof_essential]
    exact hroof hx
  intro p hpSource hpTarget
  exact hroofEssential hpSource p ⟨rfl, hpTarget⟩

end DWeb.KappaLadder
end Erdos599

