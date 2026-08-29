/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRelevantPruning
import ErdosProblems.Erdos599.DeferredGroundingSeparatorGeometry
import ErdosProblems.Erdos599.GroundingInputRelevantDecoder

/-!
# Assertion 8.18 for the deferred auxiliary

The finite last-contact descent uses only the auxiliary input geometry.  This
file instantiates the input-level decoder with the actual deferred limiting
warp and with the relevant boundary attached to the reserved cut-avoiding
record.  It does not assert the still-missing simultaneous switch or coverage
of arbitrary same-stage inessential hanging collisions.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Every ambient source is the initial vertex of a member of the limiting
warp stored by the deferred auxiliary.  Only the shared initial stage and
direct-limit clauses of deferred legality are used. -/
theorem popularAuxiliary_sourceCovered
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L) :
    GroundingInputRelevantDecoder.SourceCovered
      (popularAuxiliaryInput L hlegal) := by
  have hlimitOrd : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hlegal.regular.aleph0_le
  obtain ⟨D, hstage, hlimit⟩ :=
    hlegal.limitStages (Ladder.finalStage kappa) hlimitOrd
  let i : Set.Iio kappa.ord := ⟨0, hlegal.regular.ord_pos⟩
  intro x hx
  have hxi : x ∈ Gamma.initialSet (D.stage i) := by
    rw [hstage i]
    change x ∈ Gamma.initialSet
      (L.accumulated (Ladder.zeroStage kappa))
    rw [hlegal.initialStage, Gamma.initialSet_trivialWave]
    exact hx
  change x ∈ Gamma.initialSet
    (L.accumulated (Ladder.finalStage kappa))
  rw [hlimit, D.initialSet_limitPaths Gamma]
  exact Set.mem_iUnion.2 ⟨i, hxi⟩

namespace DeferredCutAvoidingRecord

variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}
variable {K : GroundingSelection.Controls S}

/-- Assertion 8.18 descent for the smaller relevant deferred boundary. -/
theorem relevantFiniteDescentDecoder
    (R : DeferredCutAvoidingRecord L hL S K) :
    GroundingInputRelevantDecoder.RelevantFiniteDescentDecoder
      R.relevantPruningData :=
  GroundingInputRelevantDecoder.relevantFiniteDescentDecoder
    R.relevantPruningData
    (popularAuxiliary_sourceCovered L hL.legal)
    (popularAuxiliary_terminalCut_isSeparator L hL.legal)
    S.separates

/-- The same descent, weakened to the canonical coarse boundary required by
`GroundingCutSwitchPruneOutput`. -/
theorem finiteDescentDecoder
    (R : DeferredCutAvoidingRecord L hL S K) :
    GroundingCut.FiniteDescentDecoder
      (popularAuxiliaryInput L hL.legal) S.cut :=
  GroundingInputRelevantDecoder.finiteDescentDecoder
    R.relevantPruningData
    (popularAuxiliary_sourceCovered L hL.legal)
    (popularAuxiliary_terminalCut_isSeparator L hL.legal)
    S.separates

/-- The relevant boundary itself separates the ambient source and target. -/
theorem relevantBB_isSeparator
    (R : DeferredCutAvoidingRecord L hL S K) :
    Popular.IsSeparator Gamma R.relevantBB :=
  GroundingInputRelevantDecoder.relevantBB_isSeparator
    R.relevantPruningData
    (popularAuxiliary_sourceCovered L hL.legal)
    (popularAuxiliary_terminalCut_isSeparator L hL.legal)
    S.separates

end DeferredCutAvoidingRecord

/-- For every separator/control pair, choosing the actual cut-avoiding
deferred record supplies the finite decoder field required by the
separator-arm certificate. -/
theorem finiteDescentDecoder
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (K : GroundingSelection.Controls S) :
    GroundingCut.FiniteDescentDecoder
      (popularAuxiliaryInput L hL.legal) S.cut := by
  obtain ⟨R⟩ := exists_deferredCutAvoidingRecord L hL S K
  exact R.finiteDescentDecoder

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.popularAuxiliary_sourceCovered
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.DeferredCutAvoidingRecord.finiteDescentDecoder
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.finiteDescentDecoder
