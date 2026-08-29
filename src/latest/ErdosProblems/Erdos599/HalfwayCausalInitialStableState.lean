/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeExplicitEndpointAttachmentBoundary
import ErdosProblems.Erdos599.ColouredSafeEndpointProtectedOutput

/-!
# The actual initial stable state and protected half-way output

Start with the trivial source family at zero. Its safe path is captured
before choosing the interval row, outside assignment and rooted attachment.
The later state belongs to the original avoiding club and stays in the
actual causal carrier. Fair completion now has a constructed initial input.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows

open Set Cardinal Order DirectedPath Ladder ColouredSafeEndpointBlueprint
open _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- Construct the first stable club state from the genuine zero blueprint.
No stable-state or zero-in-club premise occurs. -/
theorem exists_initialStableState
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (hUnhindered : Gamma.IsUnhindered) {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    (hext : _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
      Gamma kappa) (hsub : HasHereditarySubdivisionIncidence Gamma.graph)
    {A0 : Set V} (hA0source : A0 ⊆ Gamma.source) (hA0card : #A0 ≤ kappa)
    (hA0Z : A0 ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    (hA0 : A0.Nonempty) :
    ∃ S : StableState C (globalCarrier Gamma kappa hkappa hGamma seed hseed),
      A0 ⊆ S.carrier ∧ A0 ⊆ (web C).initialSet S.family := by
  obtain ⟨z, hz⟩ := hA0
  obtain ⟨P, R, T, hRZ, _hTP⟩ := exists_initialPostClosureIntervalTransaction
    hkappa hGamma hUnhindered hseed C hC hext hA0source hA0card hA0Z hz
  obtain ⟨F⟩ := exists_splitProjectedOutsideFracturedWarp T.interval.ambientInterval R.closedSet
    T.interval.ambientInterval_linkage.isWarp T.interval.ambientInterval_linkage.finiteCharacter
  obtain ⟨A⟩ := T.exists_endpointReferenceAssignment F hsub
  have hW := initialFamily_isBlueprint C hA0source hA0card hUnhindered
  have hWseed : (web C).vertexSet (initialFamily C A0) ⊆
      A0 ∪ Gamma.vertexSet P.ambientFamily := by
    rw [vertexSet_initialFamily]
    exact Set.subset_union_left
  have hzW : z ∈ (web C).terminalFrontier (initialFamily C A0) := by
    rwa [terminalFrontier_initialFamily]
  obtain ⟨U, hU, _hUE, _hUV, _hUI, hkeepV, _hkeepE, hkeepI, hUX,
      _hPop, hstable, _hfrontV, _hfrontE, _hfrontT, _hreach, _hfresh⟩ :=
    A.exists_sourceCoveredBlueprint hW hWseed R.endpoint_closed hzW
  let S : StableState C (globalCarrier Gamma kappa hkappa hGamma seed hseed) :=
    ⟨R.later.stage, R.later.mem_club, C.old_lt_new.trans R.later.current_lt,
      U, hU, hstable, hUX.trans hRZ⟩
  refine ⟨S, ?_, ?_⟩
  · change A0 ⊆ (web C).vertexSet U
    simpa only [vertexSet_initialFamily] using hkeepV
  · change A0 ⊆ (web C).initialSet U
    simpa only [initialSet_initialFamily] using hkeepI

/-- Complete the actual initial state fairly and project its final paths.
Only the genuine extension and subdivision hypotheses remain. -/
theorem exists_endpointProtectedHalfway_of_nonempty
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (hUnhindered : Gamma.IsUnhindered) {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    (hext : _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
      Gamma kappa) (hsub : HasHereditarySubdivisionIncidence Gamma.graph)
    {A0 : Set V} (hA0source : A0 ⊆ Gamma.source) (hA0card : #A0 ≤ kappa)
    (hA0Z : A0 ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    (hA0 : A0.Nonempty) :
    Nonempty (CardinalInduction.LocalizedProtectedHalfwayGeometry Gamma A0 kappa) := by
  obtain ⟨S, hA0S, _hA0I⟩ := exists_initialStableState
    hkappa hGamma hUnhindered hseed C hC hext hsub hA0source hA0card hA0Z hA0
  exact exists_endpointProtectedHalfway hkappa hGamma hseed C hC hext hsub S hA0source hA0S

#print axioms exists_initialStableState
#print axioms exists_endpointProtectedHalfway_of_nonempty

end Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows
