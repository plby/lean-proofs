/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointContainedFrontier
import ErdosProblems.Erdos599.HalfwayCausalEndpointHammockRows
import ErdosProblems.Erdos599.HalfwayCausalSafeCurrentPath

/-!
# Actual causal frontier completion with its captured safe target path

Instantiate carrier-preserving endpoint resolution using the actual enriched
causal Section 9 carrier. Its full frontier terminal remains in that carrier,
so the existing causal safe-path theorem applies to this very terminal.
No independently assumed captured-path selector is required.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows

open Set Cardinal Order DirectedPath Ladder
open _root_.Erdos599.Alternating
open ColouredSafeEndpointBlueprint
open _root_.Erdos599.ColouredSafeLocalTransactionRealLedger
open _root_.Erdos599.ColouredSafeAugmentedRealReach

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem endpoint_closedCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed) :
    ClosedCarrier C (globalCarrier Gamma kappa hkappa hGamma seed hseed) := by
  constructor
  · rw [hC]
    exact reference_closed hkappa hGamma hseed
  · rw [hC]
    exact endpointHammockClosed_limitWarp hkappa hGamma hseed

/-- The actual frontier output and its actual deletion-safe target path
share the same causal carrier and the same displayed endpoint. -/
theorem exists_endpointFrontier_with_capturedPath
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    {W : Set (web C).DPath} (hW : IsBlueprint C C.newStage W)
    (hWZ : (web C).vertexSet W ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    {s : V} (hs : s ∈ (web C).vertexSet W) :
    ∃ U : Set (web C).DPath, IsBlueprint C C.newStage U ∧
      (web C).vertexSet U ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed ∧
      RealAdvance Gamma (web C) W U C.newSlice ∧
      (∃ z ∈ C.newSlice, z ∈ (web C).terminalFrontier U ∧
        RealReach Gamma (web C) U s z ∧ FullAccount Gamma (web C) W U {z} ∧
        ∃ P : SafeCurrentStageTargetPath C z,
          Gamma.vertexSet P.ambientFamily ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed ∧
          Gamma.vertexSet P.ambientFamily ⊆ C.ladder.limitRoof ∧
          #(Gamma.vertexSet P.ambientFamily) ≤ kappa) ∧
      (∀ x, IsRealTerminal (Gamma := web C) Gamma.graph.Adj W x →
        IsRealTerminal (Gamma := web C) Gamma.graph.Adj U x ∨
          RealReaches Gamma (web C) U x C.newSlice) ∧
      SourcePredecessorRefines Gamma (web C) W U := by
  obtain ⟨U, hU, hUZ, hadv, ⟨z, hz, hzTerminal, hreach, haccount⟩, hterms, hpred⟩ :=
    hW.exists_realAdvance_to_frontier_within
      (endpoint_closedCarrier hkappa hGamma hseed C hC) hWZ C.new_mem_club hinc hs
  have hzZ := hUZ (terminalFrontier_subset_vertexSet U hzTerminal)
  obtain ⟨P, hPZ, hPcard⟩ := exists_safeCurrentStageTargetPath_in_globalCarrier
    hkappa hGamma hseed C hC ⟨hz, hzZ⟩
  have hZRoof : globalCarrier Gamma kappa hkappa hGamma seed hseed ⊆ C.ladder.limitRoof := by
    rw [hC]
    exact globalCarrier_subset_limitRoof hkappa hGamma hseed
  exact ⟨U, hU, hUZ, hadv,
    ⟨z, hz, hzTerminal, hreach, haccount, P, hPZ, hPZ.trans hZRoof, hPcard⟩, hterms, hpred⟩

#print axioms endpoint_closedCarrier
#print axioms exists_endpointFrontier_with_capturedPath

end Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows
