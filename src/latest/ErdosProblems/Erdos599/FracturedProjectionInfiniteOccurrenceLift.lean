/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedInfiniteTraversalBlocks

/-!
# Occurrence lifts of infinite compressor coordinates

Every forward raw coordinate of the concrete loop-erased infinite compressor
comes from one literal forward edge of the selected occurrence-level trace.
The theorem retains the exact upstairs link and edge, not only its projected
downstairs carrier.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

open Set DirectedPath _root_.Erdos599.Alternating
open Alternating.FracturedDuplication

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

namespace InfiniteTraversalFrontend

/-- A forward raw coordinate of the actual infinite projection compiler
lifts to a forward edge of its exact occurrence-level source link. -/
theorem loopErasedInput_forwardEdge_occurrenceLift
    (Z : FracturedWarp Gamma)
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (n : Nat)
    (hforward : ((edgeProvenance Z R hbracket hZfinite).loopErasedInput
      (omegaBlocks_vertex_finite Z R hbracket)).colour n = .forward) :
    ∃ (l : Link (web Gamma Z).graph),
      l ∈ (AltPath.infinite R).links ∧ l.direction = .forward ∧
      ∃ e ∈ l.path.edgeSet,
        project e.1 = ((edgeProvenance Z R hbracket hZfinite).loopErasedInput
          (omegaBlocks_vertex_finite Z R hbracket)).vertex n ∧
        project e.2 = ((edgeProvenance Z R hbracket hZfinite).loopErasedInput
          (omegaBlocks_vertex_finite Z R hbracket)).vertex (n + 1) := by
  let B := omegaBlocks Z R hbracket
  let P := edgeProvenance Z R hbracket hZfinite
  let hfinite := omegaBlocks_vertex_finite Z R hbracket
  let S := P.loopErasedInput hfinite
  let k := FracturedEdgeProvenance.retainedIndex hfinite n
  let a := rawEdgeTag Z R hbracket k
  let l := R.link (tagLinkIndex a)
  let t := rawStep Z R hbracket k
  have hcolour : P.colour (P.member k) = .forward := by
    change S.colour n = .forward at hforward
    exact hforward
  have hldir : l.direction = .forward := by
    exact hcolour
  have htmem : t ∈ linkSteps Z l := by
    exact rawStep_mem_tagLink Z R hbracket k
  have htdata := linkSteps_mem Z l htmem
  have htdir : t.direction = .forward := htdata.1.trans hldir
  have hv := rawVertex_eq_rawStep Z R hbracket k
  refine ⟨l, ⟨tagLinkIndex a, rfl⟩, hldir, t.edge, htdata.2.1, ?_, ?_⟩
  · change project t.edge.1 = B.rawVertex k
    have hv1 : B.rawVertex k = t.entry := hv.1
    rw [hv1]
    change project t.edge.1 =
      match t.direction with
      | .forward => project t.edge.1
      | .backward => project t.edge.2
    rw [htdir]
  · change project t.edge.2 = B.rawVertex
      (FracturedEdgeProvenance.retainedIndex hfinite (n + 1))
    have hjoin : B.rawVertex (k + 1) = B.rawVertex
        (FracturedEdgeProvenance.retainedIndex hfinite (n + 1)) := by
      change B.rawVertex (loopErasedIndex B.rawVertex hfinite n + 1) =
        B.rawVertex (loopErasedIndex B.rawVertex hfinite (n + 1))
      exact loopErasedIndex_join B.rawVertex hfinite n
    rw [← hjoin]
    have hv2 : B.rawVertex (k + 1) = t.exit := hv.2
    rw [hv2]
    change project t.edge.2 =
      match t.direction with
      | .forward => project t.edge.2
      | .backward => project t.edge.1
    rw [htdir]

/-- Every forward edge of the maximal-run compression of the actual
infinite frontend still has a literal occurrence lift upstairs. -/
theorem infiniteRunWalk_forwardEdge_occurrenceLift
    (Z : FracturedWarp Gamma)
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    {x y : V}
    (hxy : (x, y) ∈
      (let P := edgeProvenance Z R hbracket hZfinite
       let hfinite := omegaBlocks_vertex_finite Z R hbracket
       let S := P.loopErasedInput hfinite
       let hchange := P.loopErasedInput_changes Z.edgeWarp_isWarp
         (activeReference_isWarp Z hY) hfinite
         (edgeProvenance_carrier_finite Z R hbracket hZfinite
           hZedgeFinite hYfinite)
       (AltPath.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace
         ).directionEdges .forward)) :
    ∃ (l : Link (web Gamma Z).graph),
      l ∈ (AltPath.infinite R).links ∧ l.direction = .forward ∧
      ∃ e ∈ l.path.edgeSet, project e.1 = x ∧ project e.2 = y := by
  let P := edgeProvenance Z R hbracket hZfinite
  let hfinite := omegaBlocks_vertex_finite Z R hbracket
  let S := P.loopErasedInput hfinite
  let hchange := P.loopErasedInput_changes Z.edgeWarp_isWarp
    (activeReference_isWarp Z hY) hfinite
    (edgeProvenance_carrier_finite Z R hbracket hZfinite
      hZedgeFinite hYfinite)
  simp only [AltPath.directionEdges, AltPath.links, InfiniteTrace.links,
    Set.mem_iUnion, Set.mem_range] at hxy
  obtain ⟨l, ⟨i, rfl⟩, hdir, he⟩ := hxy
  have hrun : S.colour (RunCompressor.runBoundary S.colour hchange i) =
      .forward :=
    (S.toInfiniteRunWalk_run_direction hchange i).symm.trans hdir
  change (x, y) ∈ (S.projectedRun hchange i).link.path.edgeSet at he
  rw [S.projectedRun_edgeSet_eq_forward hchange i hrun] at he
  obtain ⟨n, hlo, hhi, hxyRaw⟩ := he
  have hnforward : S.colour n = .forward :=
    (RunCompressor.colour_eq_on_run S.colour hchange hlo hhi).trans hrun
  obtain ⟨l, hl, hldir, e, he, he1, he2⟩ :=
    loopErasedInput_forwardEdge_occurrenceLift Z R hbracket hZfinite n
      hnforward
  refine ⟨l, hl, hldir, e, he, ?_, ?_⟩
  · exact he1.trans (congrArg Prod.fst hxyRaw.symm)
  · exact he2.trans (congrArg Prod.snd hxyRaw.symm)

end InfiniteTraversalFrontend

namespace InfiniteTraversalBlocks

universe v

variable {Z : FracturedWarp Gamma}
variable {Q : AltPath (web Gamma Z).graph} {M : Type v}

/-- The path field of the infinite compiler is definitionally the maximal-run
compression of its retained loop-erased input. -/
theorem compile_path_eq_loopErasedInput
    (T : InfiniteTraversalBlocks (Y := Y) Z Q M)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.edgeWarp) :
    let S := T.provenance.loopErasedInput T.vertex_finite
    let hchange := T.provenance.loopErasedInput_changes Z.edgeWarp_isWarp
      (activeReference_isWarp Z hY) T.vertex_finite T.carrier_finite
    (T.compile hY hZfinite).path =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace := by
  rfl

end InfiniteTraversalBlocks

#print axioms InfiniteTraversalFrontend.loopErasedInput_forwardEdge_occurrenceLift
#print axioms InfiniteTraversalFrontend.infiniteRunWalk_forwardEdge_occurrenceLift
#print axioms InfiniteTraversalBlocks.compile_path_eq_loopErasedInput

end Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel
