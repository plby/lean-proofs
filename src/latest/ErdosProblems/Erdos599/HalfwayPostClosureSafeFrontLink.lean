/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureSafeTailIncidence

/-!
# The actual local link supplied by the scheduled safe front

The root-reachable post-closure blueprint contains the complete scheduled
front, and every edge of that front is an original edge.  It therefore
contains a real path from the scheduled terminal to the captured frontier.
This is the source-faithful local replacement for the overstrong claim that
the same captured-roof blueprint already links to the ambient target.
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

/-- The retained scheduled front is a real link to its own endpoint. -/
theorem front_realLinksTo_finish_rootReachableBlueprint
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
    U.RealLinksTo z {T.interval.front.finish} := by
  refine ⟨T.interval.front, T.interval.front_start, by simp, ?_, ?_⟩
  · rw [realPart_vertices]
    exact M.front_support_subset_rootReachableBlueprint
      current A U hcurrent hzTerminal hcurrentA hAU hAE hAV hUE hUV
  · intro e he
    exact U.mem_realPart_of_mem_edgeSet_of_original
      (M.front_edgeSet_subset_rootReachableBlueprint
        current A U hcurrent hzTerminal hcurrentA hAU hAE hAV hUE hUV he)
      (T.interval.front.edgeSet_subset_adj he)

/-- In particular, the actual local 9.31 construction links the scheduled
terminal to the captured later slice. -/
theorem front_realLinksTo_capturedSlice_rootReachableBlueprint
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
    U.RealLinksTo z Rlimit.capturedGeometry.newSlice := by
  refine ⟨T.interval.front, T.interval.front_start,
    T.interval.front_finish_mem, ?_, ?_⟩
  · rw [realPart_vertices]
    exact M.front_support_subset_rootReachableBlueprint
      current A U hcurrent hzTerminal hcurrentA hAU hAE hAV hUE hUV
  · intro e he
    exact U.mem_realPart_of_mem_edgeSet_of_original
      (M.front_edgeSet_subset_rootReachableBlueprint
        current A U hcurrent hzTerminal hcurrentA hAU hAE hAV hUE hUV he)
      (T.interval.front.edgeSet_subset_adj he)

#print axioms front_realLinksTo_finish_rootReachableBlueprint
#print axioms front_realLinksTo_capturedSlice_rootReachableBlueprint

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
