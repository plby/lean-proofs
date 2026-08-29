/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointInitialBlueprint
import ErdosProblems.Erdos599.HalfwayCausalSafeCurrentPath
import ErdosProblems.Erdos599.EssentialPartUnhinderedTransfer
import ErdosProblems.Erdos599.SingularQuotientReentry

/-!
# Actual safe paths at the genuine zero stage

Unhinderedness at zero is proved through the source quotient, independently
of the avoiding club. The causal choice is retrieved at this exact stage,
with its literal ambient lift contained in the existing global carrier.
This supplies the path input, not the remaining initial interval transaction.
-/

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem initialStageWeb_isUnhindered
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (hGamma : Gamma.IsUnhindered) :
    (C.ladder.stageWeb (initialStage C)).IsUnhindered := by
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (C.normalized hxy).1 hy
  have hquot : (Gamma.quotient Gamma.source).IsUnhindered :=
    _root_.Erdos599.CardinalInduction.SingularQuotientReentry.quotient_source_isUnhindered
      Gamma hNoEnter hGamma
  have hzero : C.ladder.warpAt (initialStage C) = Gamma.trivialWave := C.legal.initialStage
  have hstage : C.ladder.stageWeb (initialStage C) =
      (Gamma.quotient Gamma.source).essentialPart := by
    simp only [DWeb.KappaLadder.stageWeb, DWeb.stageWebOf, hzero,
      Gamma.terminalFrontier_trivialWave]
  rw [hstage]
  exact DWeb.essentialPart_isUnhindered_of_isUnhindered _ hquot

#print axioms initialStageWeb_isUnhindered

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint

namespace Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows

open Set Cardinal Order DirectedPath Ladder ColouredSafeEndpointBlueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- The initial safe choice is from stage zero, not from a fabricated
positive club stage. Its carrier was already inserted by the causal rows. -/
theorem exists_safeInitialStageTargetPath_in_globalCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized) (hUnhindered : Gamma.IsUnhindered)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    {z : V} (hz : z ∈ Gamma.source ∩ globalCarrier Gamma kappa hkappa hGamma seed hseed) :
    ∃ P : SafeStageTargetPath C (initialStage C) z,
      Gamma.vertexSet P.ambientFamily ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed ∧
      #(Gamma.vertexSet P.ambientFamily) ≤ kappa := by
  apply exists_safeStageTargetPath_in_globalCarrier hkappa hGamma hseed C hC
    (initialStage C) (initialStageWeb_isUnhindered C hUnhindered)
  rw [frontier_initialStage C hUnhindered]
  exact hz

#print axioms exists_safeInitialStageTargetPath_in_globalCarrier

end Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows
