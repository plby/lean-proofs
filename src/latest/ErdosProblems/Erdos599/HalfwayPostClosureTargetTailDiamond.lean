/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureTailFreshness
import ErdosProblems.Erdos599.Halfway930DiamondGeometry

/-!
# The final target-tail diamond of the post-closure transaction

The root-reachable closed-edge blueprint ends the scheduled real front at a
genuine terminal.  Its carrier meets the stored target suffix only at that
terminal.  We may therefore append the suffix by one literal diamond.  The
result retains the preceding blueprint, contains the complete selected safe
path as a real route to the ambient target, and has exact carrier, edge, and
terminal accounting.
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

/-- A terminal of a linkage blueprint is the finish of a finite member. -/
theorem exists_finiteMember_finish_eq_of_mem_terminalSet
    (U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {x : V} (hx : x ∈ U.terminalSet) :
    ∃ q : FinitePath (imaginaryGraph Gamma C.ladder.limitWarp kappa),
      (.inl q : Path _) ∈ U.paths ∧ q.finish = x := by
  obtain ⟨p, hp, hpTerminal⟩ := hx
  rcases p with q | r
  · refine ⟨q, hp, ?_⟩
    change some q.finish = some x at hpTerminal
    exact Option.some.inj hpTerminal
  · simp [DWeb.terminal?, DirectedPath.Path.terminal?] at hpTerminal

/-- Append the captured target suffix to the actual terminal reached by the
root-reachable scheduled front. -/
theorem exists_targetTailDiamond
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
      (M.oldPriorityAttachedEdges A) A.initialSet) :
    ∃ V : LinkageBlueprint Gamma C.ladder.limitWarp kappa,
      U.OrdinaryExtends V ∧
      V.RealLinksTo z Gamma.target ∧
      V.vertexSet = U.vertexSet ∪ T.interval.tail.support ∧
      V.edgeSet = U.edgeSet ∪ T.interval.tail.edgeSet ∧
      V.initialSet = U.initialSet ∧
      U.realPart.terminals \ {T.interval.front.finish} ⊆
        V.realPart.terminals ∧
      T.interval.tail.finish ∈ V.terminalSet := by
  have hfrontTerminal : T.interval.front.finish ∈ U.terminalSet :=
    M.front_finish_mem_terminalSet_rootReachableBlueprint
      current A U hcurrent hzTerminal hcurrentA hAU hAE hAV hUE hUV
  obtain ⟨q, hq, hqFinish⟩ :=
    exists_finiteMember_finish_eq_of_mem_terminalSet U hfrontTerminal
  have hstart : T.interval.tail.start = q.finish :=
    T.interval.tail_start.trans hqFinish.symm
  have hfresh : U.vertexSet ∩ T.interval.tail.support ⊆ {q.finish} := by
    simpa only [hstart] using
      M.rootReachableBlueprint_tail_inter_subset current A U
        hcurrent hAV hUV
  let Vout := U.diamond q hq T.interval.tail hstart hfresh
  have hUVordinary : U.OrdinaryExtends Vout :=
    ordinaryExtends_diamond U q hq T.interval.tail hstart hfresh
  have hfrontLink : U.RealLinksTo z {T.interval.front.finish} :=
    M.front_realLinksTo_finish_rootReachableBlueprint
      current A U hcurrent hzTerminal hcurrentA hAU hAE hAV hUE hUV
  have hfrontLinkOut : Vout.RealLinksTo z {T.interval.front.finish} :=
    realLinksTo_mono hUVordinary.realPart_extends hfrontLink
  have htailSupport : T.interval.tail.support ⊆ Vout.realPart.vertices := by
    change T.interval.tail.support ⊆
      (U.diamond q hq T.interval.tail hstart hfresh).vertexSet
    rw [vertexSet_diamond]
    exact Set.subset_union_right
  have htailEdges : T.interval.tail.edgeSet ⊆ Vout.realPart.edges := by
    intro e he
    exact Vout.mem_realPart_of_mem_edgeSet_of_original
      (by
        change e ∈ (U.diamond q hq T.interval.tail hstart hfresh).edgeSet
        rw [edgeSet_diamond]
        exact Or.inr he)
      (T.interval.tail.edgeSet_subset_adj he)
  have htailLink : Vout.RealLinksTo T.interval.front.finish Gamma.target := by
    refine ⟨T.interval.tail, ?_, T.interval.tail_boundary.2,
      htailSupport, htailEdges⟩
    exact T.interval.tail_start.trans rfl
  refine ⟨Vout, hUVordinary,
    realLinksTo_trans hfrontLinkOut htailLink, ?_, ?_, ?_, ?_, ?_⟩
  · exact vertexSet_diamond U q hq T.interval.tail hstart hfresh
  · exact edgeSet_diamond U q hq T.interval.tail hstart hfresh
  · exact initialSet_diamond U q hq T.interval.tail hstart hfresh
  · simpa only [hqFinish] using
      (realTerminals_diamond_preserved U q hq T.interval.tail hstart hfresh)
  · exact finish_mem_terminalSet_diamond
      U q hq T.interval.tail hstart hfresh

#print axioms exists_finiteMember_finish_eq_of_mem_terminalSet
#print axioms exists_targetTailDiamond

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
