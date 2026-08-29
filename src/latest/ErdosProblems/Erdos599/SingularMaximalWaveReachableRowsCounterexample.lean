/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMaximalWaveReachableRows
import ErdosProblems.Erdos599.SingularSafePathBoundaryCounterexample

/-!
# Literal selected-linkage resurrection is too strong

The safely deletable edge in the normalized one-source/two-target branching
web removes the only source.  Thus its residual web is unhindered and its
unique maximal wave is empty.  Nevertheless, adjoining the selected edge to
that empty residual wave does not make an ambient wave: the edge to the
other target avoids the selected terminal.

In fact no source--target linkage on the unique source can satisfy literal
maximal-wave resurrection.  This refutes unconditional selection of
`MaximalWaveResurrectingBatch`; the sound singular selector must permit a
wave-dependent resurrection (in this example, a trivial path at the deleted
source), or expose residual unhinderedness directly.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMaximalWaveReachableRowsCounterexample

open DWeb DirectedPath
open SingularMaximalWaveReachableRows
open SingularSafePathBoundaryCounterexample
open RegularRightBoundary.BranchingStage.Vertex

abbrev G : DWeb RegularRightBoundary.BranchingStage.Vertex :=
  RegularRightBoundary.BranchingStage.web

universe u

@[simp] theorem uc_support : uc.support =
    ({u, c} : Set RegularRightBoundary.BranchingStage.Vertex) := by
  ext x
  change x ∈ [u, c] ↔ _
  simp

/-- A linkage from the unique source in the two-target star cannot itself be
an ambient wave.  Its frontier is subsingleton, whereas the two direct target
edges force both distinct targets into the frontier of any wave. -/
theorem targetLinkage_not_isWave
    {P : Set G.DPath}
    (hP : IsLinkageBetween G ({u} : Set
      RegularRightBoundary.BranchingStage.Vertex) G.target P) :
    ¬ G.IsWave P := by
  intro hWave
  have hfrontierSubsingleton : (G.terminalFrontier P).Subsingleton :=
    terminalFrontier_subsingleton_of_initialSet_singleton
      hP.isWarp hP.initialSet_eq
  have hbFrontier : b ∈ G.terminalFrontier P := by
    obtain ⟨x, hxPath, hxFrontier⟩ := hWave.2.2
      (show u ∈ G.source by simp [G, RegularRightBoundary.BranchingStage.web])
      RegularRightBoundary.BranchingStage.ub
      ⟨rfl, by simp [G, RegularRightBoundary.BranchingStage.web,
        RegularRightBoundary.BranchingStage.ub]⟩
    have hxTarget : x ∈ G.target := hP.terminalFrontier_subset hxFrontier
    have hxb : x = b := by
      rcases x with _ | _ | _ <;>
        simp [G, RegularRightBoundary.BranchingStage.web,
          RegularRightBoundary.BranchingStage.ub_support] at hxPath hxTarget ⊢
    exact hxb ▸ hxFrontier
  have hcFrontier : c ∈ G.terminalFrontier P := by
    obtain ⟨x, hxPath, hxFrontier⟩ := hWave.2.2
      (show u ∈ G.source by simp [G, RegularRightBoundary.BranchingStage.web])
      uc
      ⟨rfl, by simp [G, RegularRightBoundary.BranchingStage.web, uc]⟩
    have hxTarget : x ∈ G.target := hP.terminalFrontier_subset hxFrontier
    have hxc : x = c := by
      rcases x with _ | _ | _ <;>
        simp [G, RegularRightBoundary.BranchingStage.web] at hxPath hxTarget ⊢
    exact hxc ▸ hxFrontier
  have hbc : b = c := hfrontierSubsingleton hbFrontier hcFrontier
  exact RegularRightBoundary.BranchingStage.Vertex.noConfusion hbc

/-- Every linkage from the unique source uses that source in its carrier,
so its carrier deletion has empty source. -/
theorem delete_targetLinkage_source_eq_empty
    {P : Set G.DPath}
    (hP : IsLinkageBetween G ({u} : Set
      RegularRightBoundary.BranchingStage.Vertex) G.target P) :
    (G.delete (G.vertexSet P)).source = ∅ := by
  have huInitial : u ∈ G.initialSet P := by
    rw [hP.initialSet_eq]
    exact Set.mem_singleton u
  obtain ⟨p, hpP, hpu⟩ := huInitial
  have huCarrier : u ∈ G.vertexSet P :=
    ⟨p, hpP, hpu ▸ p.initial_mem_support⟩
  ext x
  constructor
  · rintro ⟨hxSource, hxCarrier⟩
    have hxu : x = u := by
      simpa [G, RegularRightBoundary.BranchingStage.web] using hxSource
    subst x
    exact (hxCarrier huCarrier).elim
  · intro hx
    exact hx.elim

/-- The empty family is the maximal wave in the carrier deletion of any
such linkage. -/
def emptyResidualMaximalWave
    {P : Set G.DPath}
    (hP : IsLinkageBetween G ({u} : Set
      RegularRightBoundary.BranchingStage.Vertex) G.target P) :
    (G.delete (G.vertexSet P)).Wave := by
  refine ⟨∅, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact hp.elim
  · intro x hx
    obtain ⟨p, hp, _⟩ := hx
    exact hp.elim
  · rw [delete_targetLinkage_source_eq_empty hP]
    exact Set.empty_subset _

theorem emptyResidualMaximalWave_isMax
    {P : Set G.DPath}
    (hP : IsLinkageBetween G ({u} : Set
      RegularRightBoundary.BranchingStage.Vertex) G.target P) :
    IsMax (emptyResidualMaximalWave hP) := by
  intro M _hExtends
  have hMempty : M.1 = ∅ := by
    ext p
    constructor
    · intro hp
      have hpInitial : p.initial ∈
          (G.delete (G.vertexSet P)).initialSet M.1 := ⟨p, hp, rfl⟩
      have hpSource := M.2.2.1 hpInitial
      rw [delete_targetLinkage_source_eq_empty hP] at hpSource
      exact hpSource.elim
    · intro hp
      exact hp.elim
  have hMeq : M = emptyResidualMaximalWave hP := Subtype.ext hMempty
  subst M
  exact le_rfl

/-- No literal selected-linkage resurrection batch exists for the singleton
source of the branching web. -/
theorem no_maximalWaveResurrectingBatch :
    ¬ Nonempty (MaximalWaveResurrectingBatch G
      ({u} : Set RegularRightBoundary.BranchingStage.Vertex)) := by
  rintro ⟨B⟩
  let M := emptyResidualMaximalWave B.linkage
  have hMmax : IsMax M := emptyResidualMaximalWave_isMax B.linkage
  have hresurrect := B.resurrects M hMmax
  have hLiftEmpty : G.liftDeleteFamily (G.vertexSet B.paths) M.1 = ∅ := by
    change G.liftDeleteFamily (G.vertexSet B.paths) ∅ = ∅
    ext p
    constructor
    · rintro ⟨q, hq, _⟩
      exact hq.elim
    · intro hp
      exact hp.elim
  apply targetLinkage_not_isWave B.linkage
  rw [hLiftEmpty, Set.union_empty] at hresurrect
  exact hresurrect

/-- Consequently the local all-maximal *literal-linkage* selector is false
at every cardinal strictly above one, although the same web has the genuine
safe-batch selector (already at `aleph0`). -/
theorem not_maximalWaveResurrectionSelectionBelow
    {kappa : Cardinal} (hkappa : 1 < kappa) :
    ¬ MaximalWaveResurrectionSelectionBelow G kappa := by
  intro hselect
  have hresidual : (G.delete ∅).IsUnhindered := by
    simpa only [DWeb.delete_empty] using
      RegularRightBoundary.BranchingStage.isUnhindered
  have hsource : ({u} : Set
      RegularRightBoundary.BranchingStage.Vertex) ⊆ (G.delete ∅).source := by
    rw [DWeb.delete_empty]
    exact Set.Subset.rfl
  have hcard : Cardinal.mk ({u} : Set
      RegularRightBoundary.BranchingStage.Vertex) < kappa := by
    rw [Cardinal.mk_singleton]
    exact hkappa
  have hbatch := hselect ∅ {u} hresidual hsource hcard
  have : Nonempty (MaximalWaveResurrectingBatch G
      ({u} : Set RegularRightBoundary.BranchingStage.Vertex)) := by
    simpa only [DWeb.delete_empty] using hbatch
  exact no_maximalWaveResurrectingBatch this

#print axioms targetLinkage_not_isWave
#print axioms no_maximalWaveResurrectingBatch
#print axioms not_maximalWaveResurrectionSelectionBelow

end SingularMaximalWaveReachableRowsCounterexample
end CardinalInduction
end Erdos599
