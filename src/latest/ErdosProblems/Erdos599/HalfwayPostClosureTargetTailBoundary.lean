/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureTargetTailDiamond

/-!
# Boundary properties of the final target-tail diamond

The complete selected safe path was inserted into the moving closure before
the later club stage was chosen.  Consequently its target tail finishes not
only on the captured frontier, but at a persistent vertex.  Appending that
tail by the literal diamond therefore preserves both terminal popularity and
stability.  This isolates the remaining terminal-boundary obligation to the
pre-tail, root-reachable attachment.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- Stable capture puts the endpoint of the stored target suffix in the
persistent frontier. -/
theorem tail_finish_mem_persistent :
    T.interval.tail.finish ∈ C.persistent := by
  have hclosed : T.interval.tail.finish ∈ Rlimit.closedSet :=
    tail_support_subset_closedSet T.interval.tail.finish_mem_support
  have hfrontier : T.interval.tail.finish ∈
      C.ladder.frontier Rlimit.later.stage := by
    simpa only [DynamicMoving931GlobalClosure.capturedGeometry_newSlice] using
      (tail_finish_mem_capturedSlice (T := T))
  have hpair : T.interval.tail.finish ∈
      Rlimit.closedSet ∩ C.ladder.frontier Rlimit.later.stage :=
    ⟨hclosed, hfrontier⟩
  rw [Rlimit.frontier_inter] at hpair
  exact hpair.2

/-- A literal diamond whose appended path finishes on the prescribed
terminal boundary preserves terminal popularity. -/
theorem terminals_popular_diamond
    (U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (q : FinitePath (imaginaryGraph Gamma C.ladder.limitWarp kappa))
    (hq : (.inl q : Path _) ∈ U.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : U.vertexSet ∩ P.support ⊆ {q.finish})
    (hpopular : U.terminalSet ⊆
      {u | IsPopular Gamma C.ladder.limitWarp C.persistent kappa u} ∪
        Rlimit.capturedGeometry.newSlice)
    (hfinish : P.finish ∈ Rlimit.capturedGeometry.newSlice) :
    (U.diamond q hq P hstart hfresh).terminalSet ⊆
      {u | IsPopular Gamma C.ladder.limitWarp C.persistent kappa u} ∪
        Rlimit.capturedGeometry.newSlice := by
  intro x hx
  rcases terminalSet_diamond_subset U q hq P hstart hfresh hx with
    hxOld | hxFinish
  · exact hpopular hxOld
  · right
    have hxEq : x = P.finish := Set.mem_singleton_iff.1 hxFinish
    simpa only [hxEq] using hfinish

/-- A literal diamond whose appended path finishes persistently preserves
stability at the captured frontier. -/
theorem stable_diamond
    (U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (q : FinitePath (imaginaryGraph Gamma C.ladder.limitWarp kappa))
    (hq : (.inl q : Path _) ∈ U.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : U.vertexSet ∩ P.support ⊆ {q.finish})
    (hstable : U.Stable Rlimit.capturedGeometry.newSlice C.persistent)
    (hfinish : P.finish ∈ C.persistent) :
    (U.diamond q hq P hstart hfresh).Stable
      Rlimit.capturedGeometry.newSlice C.persistent := by
  rintro x ⟨hxTerminal, hxFrontier⟩
  rcases terminalSet_diamond_subset U q hq P hstart hfresh hxTerminal with
    hxOld | hxFinish
  · exact hstable ⟨hxOld, hxFrontier⟩
  · have hxEq : x = P.finish := Set.mem_singleton_iff.1 hxFinish
    simpa only [hxEq] using hfinish

/-- Terminal accounting depends only on ordinary retention and the exact
carrier/edge unions of a tail attachment; it does not depend on the chosen
path-family presentation of the diamond. -/
theorem terminalSet_subset_of_tail_extension
    (U Vout : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (P : FinitePath Gamma.graph)
    (hUV : U.OrdinaryExtends Vout)
    (hV : Vout.vertexSet = U.vertexSet ∪ P.support)
    (hE : Vout.edgeSet = U.edgeSet ∪ P.edgeSet) :
    Vout.terminalSet ⊆ U.terminalSet ∪ {P.finish} := by
  intro x hxTerminal
  have hnoOut : ¬ ∃ y, (x, y) ∈ Vout.edgeSet :=
    isWarp_noOutgoing_familyEdges_of_mem_terminalFrontier
      Vout.isWarp hxTerminal
  have hxVertex : x ∈ Vout.vertexSet := by
    obtain ⟨p, hp, hpTerminal⟩ := hxTerminal
    exact ⟨p, hp,
      (imaginaryWeb Gamma C.ladder.limitWarp kappa).terminal_mem_support
        hpTerminal⟩
  rw [hV] at hxVertex
  rcases hxVertex with hxOld | hxTail
  · left
    change x ∈
      (imaginaryWeb Gamma C.ladder.limitWarp kappa).terminalFrontier U.paths
    rw [isWarp_terminalFrontier_eq_noOutgoing U.isWarp]
    refine ⟨hxOld, ?_⟩
    rintro ⟨y, hxy⟩
    exact hnoOut ⟨y, hUV.edges_mono hxy⟩
  · right
    rw [Set.mem_singleton_iff]
    by_contra hxFinish
    obtain ⟨y, hxy⟩ :=
      FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        P hxTail hxFinish
    apply hnoOut
    refine ⟨y, ?_⟩
    rw [hE]
    exact Or.inr hxy

/-- The actual target-tail constructor with its final terminal boundary.
Once the pre-tail output is popular and stable, the stored target suffix
preserves both properties automatically. -/
theorem exists_targetTailDiamond_with_terminalBoundary
    (M : PostClosureMacroCompressorAssignment T)
    (current A U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hzTerminal : z ∈ current.terminalSet)
    (hcurrentA : current.OrdinaryExtends A)
    (hAU : A.OrdinaryExtends U)
    (hAE : A.edgeSet =
      referencePrefixSeedEdges current Rlimit.closedSet)
    (hAV : A.vertexSet = current.vertexSet ∪ Gamma.vertexSet
      (activatedReferencePrefixes C current Rlimit.closedSet))
    (hUE : U.edgeSet = RootReachableRelation.edges
      (M.oldPriorityAttachedEdges A) A.initialSet)
    (hUV : U.vertexSet = RootReachableRelation.carrier
      (M.oldPriorityAttachedEdges A) A.initialSet)
    (hpopular : U.terminalSet ⊆
      {u | IsPopular Gamma C.ladder.limitWarp C.persistent kappa u} ∪
        Rlimit.capturedGeometry.newSlice)
    (hstable : U.Stable Rlimit.capturedGeometry.newSlice C.persistent) :
    ∃ Vout : LinkageBlueprint Gamma C.ladder.limitWarp kappa,
      U.OrdinaryExtends Vout ∧
      Vout.RealLinksTo z Gamma.target ∧
      Vout.vertexSet = U.vertexSet ∪ T.interval.tail.support ∧
      Vout.edgeSet = U.edgeSet ∪ T.interval.tail.edgeSet ∧
      Vout.initialSet = U.initialSet ∧
      U.realPart.terminals \ {T.interval.front.finish} ⊆
        Vout.realPart.terminals ∧
      T.interval.tail.finish ∈ Vout.terminalSet ∧
      Vout.terminalSet ⊆
        {u | IsPopular Gamma C.ladder.limitWarp C.persistent kappa u} ∪
          Rlimit.capturedGeometry.newSlice ∧
      Vout.Stable Rlimit.capturedGeometry.newSlice C.persistent := by
  obtain ⟨Vout, hOrdinary, htarget, hV, hE, hI, hrealTerminal,
      hfinishTerminal⟩ :=
    M.exists_targetTailDiamond current A U hcurrent hzTerminal hcurrentA hAU
      hAE hAV hUE hUV
  have hterminalSubset : Vout.terminalSet ⊆
      U.terminalSet ∪ {T.interval.tail.finish} :=
    terminalSet_subset_of_tail_extension U Vout T.interval.tail
      hOrdinary hV hE
  have hfinishCaptured := tail_finish_mem_capturedSlice (T := T)
  have hfinishPersistent := tail_finish_mem_persistent (T := T)
  have hpopularOut : Vout.terminalSet ⊆
      {u | IsPopular Gamma C.ladder.limitWarp C.persistent kappa u} ∪
        Rlimit.capturedGeometry.newSlice := by
    intro x hx
    rcases hterminalSubset hx with hxOld | hxFinish
    · exact hpopular hxOld
    · right
      have hxEq : x = T.interval.tail.finish :=
        Set.mem_singleton_iff.1 hxFinish
      simpa only [hxEq] using hfinishCaptured
  have hstableOut :
      Vout.Stable Rlimit.capturedGeometry.newSlice C.persistent := by
    rintro x ⟨hxTerminal, hxCaptured⟩
    rcases hterminalSubset hxTerminal with hxOld | hxFinish
    · exact hstable ⟨hxOld, hxCaptured⟩
    · have hxEq : x = T.interval.tail.finish :=
        Set.mem_singleton_iff.1 hxFinish
      simpa only [hxEq] using hfinishPersistent
  exact ⟨Vout, hOrdinary, htarget, hV, hE, hI, hrealTerminal,
    hfinishTerminal, hpopularOut, hstableOut⟩

#print axioms tail_finish_mem_persistent
#print axioms terminals_popular_diamond
#print axioms stable_diamond
#print axioms terminalSet_subset_of_tail_extension
#print axioms exists_targetTailDiamond_with_terminalBoundary

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
