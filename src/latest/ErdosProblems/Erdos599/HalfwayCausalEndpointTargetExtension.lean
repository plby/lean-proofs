/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalEndpointMovingClosure
import ErdosProblems.Erdos599.ColouredSafeEndpointOrdinaryExtension

/-!
# Actual contained ordinary target extension

The safe target path, contained moving closure, protected interval row and
fixed-original endpoint assignment are constructed in source order. The
output stays inside the actual causal carrier and retains the exact old
terminal ledger. No captured-path or moving-closure oracle is an input.
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

theorem exists_endpointOrdinaryExtension
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    {W : Set (web C).DPath} (hW : IsBlueprint C C.newStage W)
    (hWZ : (web C).vertexSet W ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    {z : V} (hzFrontier : z ∈ C.newSlice) (hz : z ∈ (web C).terminalFrontier W)
    (hext : _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
      Gamma kappa) (hsub : HasHereditarySubdivisionIncidence Gamma.graph) :
    ∃ (b : Stage (succ kappa)) (Q : Set (web C).DPath),
      b ∈ C.club ∧ C.newStage < b ∧ IsBlueprint C b Q ∧
      (web C).vertexSet Q ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed ∧
      (web C).vertexSet W ⊆ (web C).vertexSet Q ∧
      familyEdges W ⊆ familyEdges Q ∧
      (web C).initialSet W ⊆ (web C).initialSet Q ∧
      (web C).terminalFrontier Q ⊆ popular C ∧
      (web C).terminalFrontier Q ∩ C.ladder.frontier b ⊆ C.persistent ∧
      RealReaches Gamma (web C) Q z Gamma.target ∧
      (∀ x, x ∈ (web C).terminalFrontier W → x ≠ z →
        (x ∉ C.newSlice ∨ x ∈ C.persistent) → x ∈ (web C).terminalFrontier Q) ∧
      (∀ {x y}, y ∈ (web C).vertexSet W → (x, y) ∈ familyEdges Q →
        (x, y) ∈ familyEdges W) := by
  have hzZ := hWZ (terminalFrontier_subset_vertexSet W hz)
  obtain ⟨P, hPZ, hPcard⟩ := exists_safeCurrentStageTargetPath_in_globalCarrier
    hkappa hGamma hseed C hC ⟨hzFrontier, hzZ⟩
  let X0 := (web C).vertexSet W ∪ Gamma.vertexSet P.ambientFamily
  have hXcard : #X0 ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hkappa hW.card_vertices hPcard)
  have hXZ : X0 ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed :=
    Set.union_subset hWZ hPZ
  obtain ⟨R, hRZ, _hlower⟩ := exists_endpointLimitClosure_within_globalCarrier
    hkappa hGamma hseed C hC C.newStage hXcard hXZ
  obtain ⟨T⟩ := NativePostClosureIntervalTransaction.exists_nativePostClosureIntervalTransaction
    C P (show Gamma.vertexSet P.ambientFamily ⊆ X0 from Set.subset_union_right)
      R.toLimitClosure hzFrontier hext
  obtain ⟨F⟩ := exists_splitProjectedOutsideFracturedWarp T.interval.ambientInterval R.closedSet
    T.interval.ambientInterval_linkage.isWarp T.interval.ambientInterval_linkage.finiteCharacter
  obtain ⟨A⟩ := T.exists_endpointReferenceAssignment F hsub
  obtain ⟨Q, hQ, hE, _hV, _hI, hkeepV, hkeepE, hkeepI, hQX, hPop,
      hStable, hReach, hFresh⟩ := A.exists_targetBlueprint hW
        (show (web C).vertexSet W ⊆ X0 from Set.subset_union_left) R.endpoint_closed hz
  exact ⟨R.later.stage, Q, R.later.mem_club, R.later.current_lt,
    hQ, hQX.trans hRZ, hkeepV, hkeepE, hkeepI, hPop, hStable, hReach,
    fun _ hx hxz hb ↦ A.old_terminal_retained hW
      (Set.subset_union_left.trans R.seed_subset) hQ.isWarp hkeepV hE hx hxz hb,
    hFresh⟩

/-- A stable contained blueprint can complete any selected carrier vertex
to the true target while retaining full accounting and predecessor refinement. -/
theorem exists_endpointAdvance_to_target
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    {W : Set (web C).DPath} (hW : IsBlueprint C C.newStage W)
    (hWZ : (web C).vertexSet W ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    (hstable : (web C).terminalFrontier W ∩ C.newSlice ⊆ C.persistent)
    (hext : _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
      Gamma kappa) (hsub : HasHereditarySubdivisionIncidence Gamma.graph)
    {s : V} (hs : s ∈ (web C).vertexSet W) :
    ∃ (b : Stage (succ kappa)) (Q : Set (web C).DPath),
      b ∈ C.club ∧ C.newStage < b ∧ IsBlueprint C b Q ∧
      (web C).vertexSet Q ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed ∧
      (web C).vertexSet W ⊆ (web C).vertexSet Q ∧
      RealEdges (Gamma := web C) Gamma.graph.Adj W ⊆
        RealEdges (Gamma := web C) Gamma.graph.Adj Q ∧
      (web C).initialSet W ⊆ (web C).initialSet Q ∧
      (web C).terminalFrontier Q ⊆ popular C ∧
      (web C).terminalFrontier Q ∩ C.ladder.frontier b ⊆ C.persistent ∧
      RealReaches Gamma (web C) Q s Gamma.target ∧
      FullAccount Gamma (web C) W Q Gamma.target ∧
      (∀ x, IsRealTerminal (Gamma := web C) Gamma.graph.Adj W x →
        IsRealTerminal (Gamma := web C) Gamma.graph.Adj Q x ∨
          RealReaches Gamma (web C) Q x Gamma.target) ∧
      SourcePredecessorRefines Gamma (web C) W Q := by
  obtain ⟨U, hU, hUZ, hadv, ⟨z, hzF, hzT, hsz, haccount⟩, _hterms, hpred⟩ :=
    hW.exists_realAdvance_to_frontier_within
      (endpoint_closedCarrier hkappa hGamma hseed C hC) hWZ C.new_mem_club hsub hs
  obtain ⟨b, Q, hb, hab, hQ, hQZ, hUQ, hUEQ, hUIQ, hPop, hStable, hzB, hretain, _hfresh⟩ :=
    exists_endpointOrdinaryExtension hkappa hGamma hseed C hC hU hUZ hzF hzT hext hsub
  have hreal : RealEdges (Gamma := web C) Gamma.graph.Adj U ⊆
      RealEdges (Gamma := web C) Gamma.graph.Adj Q := fun _ he ↦ ⟨hUEQ he.1, he.2⟩
  have hfull : FullAccount Gamma (web C) W Q Gamma.target := by
    apply haccount.promote_singleton hUQ hUEQ _ hzB
    rintro x ⟨⟨hxW, hxU⟩, hxz⟩
    apply hretain x hxU hxz
    by_cases hxF : x ∈ C.newSlice
    · exact Or.inr (hstable ⟨hxW, hxF⟩)
    · exact Or.inl hxF
  exact ⟨b, Q, hb, hab, hQ, hQZ, hadv.vertices.trans hUQ, hadv.edges.trans hreal,
    hadv.initials.trans hUIQ, hPop, hStable, (hsz.mono hUQ hreal).then_reaches hzB, hfull,
    fun _ hx ↦ hfull.realTerminal_pending_or_completed hQ.isWarp hx,
    hpred.trans (sourcePredecessorRefines_of_edge_initial_extension hU.isWarp hQ.isWarp hUEQ hUIQ)
      hadv.vertices hUQ hreal⟩

#print axioms exists_endpointOrdinaryExtension
#print axioms exists_endpointAdvance_to_target

end Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows
