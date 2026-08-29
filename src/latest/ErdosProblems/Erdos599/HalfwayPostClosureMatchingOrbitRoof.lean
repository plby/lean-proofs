/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureMatchingOrbit
import ErdosProblems.Erdos599.HalfwayDeferredReferenceRoofIncidence
import ErdosProblems.Erdos599.TwoWarpMatchingPrefixCompilation
import ErdosProblems.Erdos599.TwoWarpMatchingInfinitePrefixProjection

/-!
# Captured-roof geometry of the actual matching orbit

Forward steps lie on the captured interval row.  A backward step is a
limiting-reference edge traversed from its head to its tail.  The deferred
no-late-entry theorem says that any such edge whose head is already in the
captured roof was present at that stage; self-roofing then puts its tail in
the same roof.  Consequently every raw occurrence of the actual forward
orbit stays below the captured later frontier.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating
open _root_.Erdos599.TwoWarpMatchingTraversal

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

private theorem pathFamilyEdgeSet_eq_familyEdges
    (Gamma : DWeb V) (W : Set Gamma.DPath) :
    Gamma.pathFamilyEdgeSet W = familyEdges W := by
  ext e
  simp only [DWeb.pathFamilyEdgeSet, familyEdges, Set.mem_ofPred_eq,
    Set.mem_iUnion]
  constructor <;> rintro ⟨p, hp, he⟩ <;> exact ⟨p, hp, he⟩

theorem finiteInput_toFiniteTrace_vertexSet_subset
    (S : RunCompressor.FiniteInput Gamma.graph) :
    S.toFiniteRunWalk.toFiniteTrace.vertexSet ⊆
      S.vertex '' Set.Icc 0 S.lastEdge := by
  intro x hx
  simp only [FiniteTrace.vertexSet, Set.mem_iUnion] at hx
  obtain ⟨i, hxi⟩ := hx
  change x ∈ (S.toFiniteRunWalk.run i).link.path.support at hxi
  rw [S.toFiniteRunWalk_run_support i] at hxi
  obtain ⟨n, hn, rfl⟩ := hxi
  have hil : i.1 < S.runs.length := by
    have hil' : i.1 < S.toFiniteRunWalk.lastIndex + 1 := by
      simpa only [FiniteRunWalk.toFiniteTrace] using i.2
    change i.1 < S.runs.length - 1 + 1 at hil'
    rw [S.runCount_eq] at hil'
    exact hil'
  have hi := S.runUpper_le_lastEdge
    (⟨i.1, hil⟩ : Fin S.runs.length)
  rw [← RunCompressor.runLower_succ S.runs hil] at hi
  exact ⟨n, ⟨Nat.zero_le _, hn.2.trans hi⟩, rfl⟩

/-- One actual matching step preserves the captured roof.  The backward
case is the construction-specific deferred-reference incidence theorem, not
a false assertion that arbitrary graph edges preserve roofs backwards. -/
theorem matchingStep_preserves_capturedRoof
    {a b : Port V}
    (hab : Step T.interval.ambientInterval C.ladder.limitWarp a b)
    (ha : projectPort a ∈ Rlimit.capturedGeometry.outerRoof) :
    projectPort b ∈ Rlimit.capturedGeometry.outerRoof := by
  rcases step_cases hab with
    ⟨x, y, haPort, hbPort, hxy⟩ |
      ⟨x, y, haPort, hbPort, hxy⟩
  · subst a
    subst b
    simp only [projectPort_inl, projectPort_inr] at ha ⊢
    rcases hxy.1 with hRow | hIdentity
    · have hrow : Gamma.vertexSet T.interval.ambientInterval ⊆
          Rlimit.capturedGeometry.outerRoof := by
        rintro v ⟨p, hp, hvp⟩
        exact T.interval.ambientInterval_in_outerRoof p hp hvp
      exact hrow
        ((familyEdges_subset_vertexSet_prod
          T.interval.ambientInterval hRow).2)
    · exact hIdentity.1 ▸ ha
  · subst a
    subst b
    simp only [projectPort_inl, projectPort_inr] at ha ⊢
    rcases hxy.1 with hReference | hIdentity
    · change (x, y) ∈ familyEdges
          (C.ladder.accumulated (Ladder.finalStage (succ kappa))) at hReference
      rw [← pathFamilyEdgeSet_eq_familyEdges] at hReference
      have hStage : (x, y) ∈ Gamma.pathFamilyEdgeSet
          (C.ladder.warpAt Rlimit.later.stage) :=
        DWeb.KappaLadder.Deferred.pathFamilyEdgeSet_of_head_mem_roof_frontier
          C.legal Rlimit.later.stage (succ kappa).ord le_rfl
            Rlimit.later.stage.2.le hReference ha
      have hTail :=
        DWeb.KappaLadder.Deferred.edge_tail_mem_strictRoof_of_mem_warpAt
          C.legal Rlimit.later.stage hStage
      change x ∈ Gamma.roof (C.ladder.frontier Rlimit.later.stage)
      rw [C.ladder.frontier_eq_essential_terminalFrontier
        C.legal.roofsSourceAtStages, Gamma.roof_essential]
      exact hTail.1
    · exact hIdentity.1 ▸ ha

/-- Every raw occurrence of a finite actual orbit prefix is captured at the
same later club stage. -/
theorem finiteOrbit_projectedVertex_mem_capturedRoof
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : FinitePortPrefix T.interval.ambientInterval
      C.ladder.limitWarp x) :
    ∀ i, P.projectedVertex i ∈ Rlimit.capturedGeometry.outerRoof := by
  have hnat : ∀ (n : Nat) (hn : n ≤ P.lastIndex),
      projectPort (P.port ⟨n, Nat.lt_succ_of_le hn⟩) ∈
        Rlimit.capturedGeometry.outerRoof := by
    intro n hn
    induction n with
    | zero =>
        simpa [P.starts] using
          Rlimit.later.subset_roof (M.assignmentSource_mem_closedSet hx)
    | succ n ih =>
        let i : Fin P.lastIndex := ⟨n, by omega⟩
        have hprev : projectPort (P.port i.castSucc) ∈
            Rlimit.capturedGeometry.outerRoof := by
          simpa [i] using ih (by omega)
        simpa [i] using
          matchingStep_preserves_capturedRoof (P.steps i) hprev
  intro i
  exact hnat i.1 (Nat.le_of_lt_succ i.2)

/-- Loop erasure and run compression only retain raw projected occurrences,
so the compiled finite alternating path remains in the captured roof. -/
theorem finiteOrbit_altPath_vertexSet_subset_capturedRoof
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : FinitePortPrefix T.interval.ambientInterval
      C.ladder.limitWarp x)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0) :
    (P.altPath hrootUnique).vertexSet ⊆
      Rlimit.capturedGeometry.outerRoof := by
  intro v hv
  change v ∈ (P.compressorInput hrootUnique).toFiniteRunWalk.toFiniteTrace.vertexSet at hv
  obtain ⟨n, hn, rfl⟩ :=
    finiteInput_toFiniteTrace_vertexSet_subset
      (P.compressorInput hrootUnique) hv
  have hn' : n ≤ finiteLoopLength P.projectedVertex := by
    simpa only [FinitePortPrefix.compressorInput] using hn.2
  change finiteLoopVertex P.projectedVertex n ∈
    Rlimit.capturedGeometry.outerRoof
  rw [finiteLoopVertex_eq P.projectedVertex hn']
  exact M.finiteOrbit_projectedVertex_mem_capturedRoof hx P _

/-- Every raw occurrence of an infinite no-return actual orbit is likewise
captured at the same later club stage. -/
theorem infiniteOrbit_projectedVertex_mem_capturedRoof
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : InfinitePortPrefix T.interval.ambientInterval
      C.ladder.limitWarp x) :
    ∀ n, P.projectedVertex n ∈ Rlimit.capturedGeometry.outerRoof := by
  intro n
  induction n with
  | zero =>
      simpa [P.starts] using
        Rlimit.later.subset_roof (M.assignmentSource_mem_closedSet hx)
  | succ n ih =>
      exact matchingStep_preserves_capturedRoof (P.steps n) ih

/-- The occurrence-faithful infinite compiler likewise retains only
projected matching-orbit vertices, hence stays in the captured roof. -/
theorem infiniteOrbit_altPath_vertexSet_subset_capturedRoof
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : InfinitePortPrefix T.interval.ambientInterval
      C.ladder.limitWarp x)
    (houtside : ∀ n, 0 < n →
      P.projectedVertex n ∉ Rlimit.closedSet) :
    (P.altPath (M.assignmentSource_mem_closedSet hx) houtside
      T.interval.ambientInterval_linkage.isWarp
      T.interval.ambientInterval_linkage.finiteCharacter
      (C.legal.warpStages (Ladder.finalStage (succ kappa)))).vertexSet ⊆
        Rlimit.capturedGeometry.outerRoof := by
  exact P.altPath_vertexSet_subset_of_projectedVertex
    (M.assignmentSource_mem_closedSet hx) houtside
    T.interval.ambientInterval_linkage.isWarp
    T.interval.ambientInterval_linkage.finiteCharacter
    (C.legal.warpStages (Ladder.finalStage (succ kappa)))
    (M.infiniteOrbit_projectedVertex_mem_capturedRoof hx P)

#print axioms matchingStep_preserves_capturedRoof
#print axioms finiteOrbit_projectedVertex_mem_capturedRoof
#print axioms finiteOrbit_altPath_vertexSet_subset_capturedRoof
#print axioms infiniteOrbit_projectedVertex_mem_capturedRoof
#print axioms infiniteOrbit_altPath_vertexSet_subset_capturedRoof

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
