/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalActiveSupply
import ErdosProblems.Erdos599.GroundingFiniteAlternatingRoot
import ErdosProblems.Erdos599.GroundingPathPrefix

/-!
# Root anchors for canonical equal-stage routes

Every auxiliary source of the equal-stage maximal family represents a
grounded inessential member of the limiting ladder.  The canonical decoded
route therefore has a finite original-web prefix from a genuine source to
its initial vertex.  This file packages that prefix and then applies the
finite alternating-root theorem to the actual retained forward vertices of
one canonical erased route.

The resulting reduction is intentionally exact: rooting a forward vertex
requires survival of the source prefix and of the prefixes ending at the
ambient starts of compressed backward links.  No point in a deleted
backward-run interior is declared rooted.
-/

noncomputable section

open Set

namespace Erdos599

universe u

open _root_.Erdos599.DirectedPath
open Alternating

variable {V : Type u} {Gamma : DWeb V}

/-! ## Source endpoints of the full decoder -/

namespace PopularAuxiliary.Input

/-- A full target decoder starting at an old source starts at the represented
original vertex. -/
theorem decodeFinitePath_initial_of_start_old
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (p : FinitePath J.lambda.graph)
    (hsource : p.start ∈ J.lambda.source)
    (htarget : p.finish ∈ J.lambda.target) (x : V)
    (hstart : p.start = .old x) :
    (J.decodeFinitePath p hsource htarget).initial = x := by
  classical
  unfold PopularAuxiliary.Input.decodeFinitePath
  split
  · rename_i y hy
    exact PopularAuxiliary.Input.LambdaVertex.old.inj
      (y.2.2.symm.trans hstart)
  · rename_i i hi
    exact False.elim (by
      have : (PopularAuxiliary.Input.LambdaVertex.proxy i.1 : J.LV) =
          .old x := i.2.symm.trans hstart
      cases this)

/-- A full target decoder starting at a proxy starts on the original path
represented by that proxy. -/
theorem decodeFinitePath_initial_mem_proxyPath_of_start_proxy
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (p : FinitePath J.lambda.graph)
    (hsource : p.start ∈ J.lambda.source)
    (htarget : p.finish ∈ J.lambda.target) (i : I)
    (hstart : p.start = .proxy i) :
    (J.decodeFinitePath p hsource htarget).initial ∈
      (J.proxyPath i).support := by
  classical
  unfold PopularAuxiliary.Input.decodeFinitePath
  split
  · rename_i x hx
    exact False.elim (by
      have : (PopularAuxiliary.Input.LambdaVertex.old x.1 : J.LV) =
          .proxy i := x.2.2.symm.trans hstart
      cases this)
  · rename_i j hj
    have hji : j.1 = i :=
      PopularAuxiliary.Input.LambdaVertex.proxy.inj
        (j.2.symm.trans hstart)
    subst i
    unfold PopularAuxiliary.Input.decodeFinitePathFromProxy
    exact (Classical.choose_spec
      (J.decodeWalkSteps_runs_from_eq_proxy p.walk j.2
        ((J.finish_old_gadget p
          (J.chooseTargetEndpoint p htarget).2.2).2))).1

namespace MicroTrace

/-- The canonical compression of a full target decoder remembers an owner
in the limiting ladder for each compressed backward link. -/
theorem erasedCompression_backwardLinksOn
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    {p : FinitePath J.lambda.graph} (T : J.MicroTrace p) :
    BackwardLinksOn J.ladder.paths T.erasedCompression.path := by
  apply T.runs.erasedSignedRoute.compressionOfValid_backwardLinksOn
    (fun {_s} hs ↦ T.valid _
      (T.runs.erasedSignedRoute.steps_sublist.subset hs))
    J.ladder.disjoint
  intro s hs hdir
  simpa [PopularAuxiliary.Input.familyEdges, Alternating.familyEdges] using
    T.backward_on_ladder s
      (T.runs.erasedSignedRoute.steps_sublist.subset hs) hdir

end MicroTrace
end PopularAuxiliary.Input

namespace DWeb

variable {kappa : Cardinal.{u}}

namespace KappaLadder

open GroundingEqualActiveSelection GroundingRootedReachabilityWarp

/-! ## A genuine source prefix for every canonical erased route -/

private theorem recorded_mem_limitWarp_inessential_routeRoot
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {a : Ladder.Stage kappa} {p : Gamma.DPath}
    (hp : L.chosen a = some p) :
    p ∈ Gamma.inessentialPaths L.limitWarp := by
  apply L.recorded_mem_inessential hlegal.recordedPathsPersist hp
  change a.1 + 1 ≤ kappa.ord
  exact (Order.add_one_le_iff).2 a.2

/-- The finite rooted prefix attached to one canonical decoded route. -/
structure CanonicalErasedRouteRootPrefix
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (p : WarpPath Q) where
  parent : Gamma.DPath
  path : FinitePath Gamma.graph
  parent_inessential : parent ∈ Gamma.inessentialPaths L.limitWarp
  parent_exposed : parent ∈
    GroundingSimultaneousDecode.exposedLadderPaths
      (EqualInput L hL) p.1
  start_eq_parent_initial : path.start = parent.initial
  start_mem_source : path.start ∈ Gamma.source
  finish_eq : path.finish =
    (canonicalErasedRoute (EqualInput L hL) Q p).initial
  support_subset : path.support ⊆ parent.support
  edgeSet_subset : path.edgeSet ⊆ parent.edgeSet

/-- Every canonical route in an arbitrary auxiliary target warp has a
finite prefix from an original source to its decoded initial vertex. -/
theorem exists_canonicalErasedRouteRootPrefix
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (p : WarpPath Q) :
    Nonempty (L.CanonicalErasedRouteRootPrefix hL Q p) := by
  let J := EqualInput L hL
  let T := J.decodeFinitePath p.1
    (Q.starts_in_source p.2) (Q.ends_in_target p.2)
  have hrouteInitial :
      (canonicalErasedRoute J Q p).initial = T.initial := by
    exact T.erasedCompression.initial_eq
  rcases J.start_of_mem_lambda_source p.1 (Q.starts_in_source p.2) with
      ⟨x, hxFinite, hstart⟩ | ⟨i, hstart⟩
  · let xs : L.groundedFiniteTerminalSet := ⟨x, hxFinite⟩
    let xs' : L.finiteTerminalSet :=
      ⟨x, L.groundedFiniteTerminalSet_subset_finiteTerminalSet hxFinite⟩
    obtain ⟨_hfinite, parent, hchosen, hterminal⟩ :=
      L.finiteTerminalStage_spec xs'
    have hstage : L.finiteTerminalStage xs' = L.finiteTerminalIndex xs := rfl
    rw [hstage] at hchosen
    have hground : L.finiteTerminalIndex xs ∈ L.phiGround :=
      L.finiteTerminalStage_mem_phiGround hL.legal xs
    have hparentSource : parent.initial ∈ Gamma.source := by
      obtain ⟨r, hrChosen, hrSource⟩ := hground
      have hparent : parent = r :=
        Option.some.inj (hchosen.symm.trans hrChosen)
      exact hparent ▸ hrSource
    have hTinitial : T.initial = x :=
      J.decodeFinitePath_initial_of_start_old p.1
        (Q.starts_in_source p.2) (Q.ends_in_target p.2) x hstart
    have htrace : (canonicalErasedRoute J Q p).initial ∈ parent.support := by
      rw [hrouteInitial, hTinitial]
      exact Gamma.terminal_mem_support hterminal
    obtain ⟨r, hrStart, hrFinish, hrSupport, hrEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix parent htrace
    have hparentInessential :
        parent ∈ Gamma.inessentialPaths L.limitWarp :=
      recorded_mem_limitWarp_inessential_routeRoot L hL.legal hchosen
    refine ⟨{
      parent := parent
      path := r
      parent_inessential := hparentInessential
      parent_exposed := ?_
      start_eq_parent_initial := hrStart
      start_mem_source := ?_
      finish_eq := hrFinish
      support_subset := hrSupport
      edgeSet_subset := hrEdges }⟩
    · apply Or.inl
      refine ⟨hparentInessential.1, ?_⟩
      refine ⟨(.old x : J.LV), ?_, ?_⟩
      · rw [← hstart]
        exact p.1.start_mem_support
      · exact Or.inl ⟨x, Gamma.terminal_mem_support hterminal, rfl⟩
    simpa only [hrStart] using hparentSource
  · have hspec := L.groundedInfiniteStage_spec i
    have hchosen : L.chosen (L.groundedInfiniteStage i) = some i.1 :=
      hspec.2
    have hparentSource : i.1.initial ∈ Gamma.source := by
      obtain ⟨r, hrChosen, hrSource⟩ := hspec.1.1
      have hir : i.1 = r := Option.some.inj (hchosen.symm.trans hrChosen)
      exact hir ▸ hrSource
    have hTinitial : T.initial ∈ i.1.support :=
      J.decodeFinitePath_initial_mem_proxyPath_of_start_proxy p.1
        (Q.starts_in_source p.2) (Q.ends_in_target p.2) i hstart
    have htrace : (canonicalErasedRoute J Q p).initial ∈ i.1.support := by
      rw [hrouteInitial]
      simpa only [J, EqualInput, KappaLadder.popularAuxiliaryInput,
        KappaLadder.groundedInfinitePath] using hTinitial
    obtain ⟨r, hrStart, hrFinish, hrSupport, hrEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix i.1 htrace
    have hparentInessential :
        i.1 ∈ Gamma.inessentialPaths L.limitWarp :=
      recorded_mem_limitWarp_inessential_routeRoot L hL.legal hchosen
    refine ⟨{
      parent := i.1
      path := r
      parent_inessential := hparentInessential
      parent_exposed := ?_
      start_eq_parent_initial := hrStart
      start_mem_source := ?_
      finish_eq := hrFinish
      support_subset := hrSupport
      edgeSet_subset := hrEdges }⟩
    · apply Or.inr
      simpa only [hstart, Set.mem_singleton_iff, J, EqualInput,
        KappaLadder.popularAuxiliaryInput,
        KappaLadder.groundedInfinitePath]
    simpa only [hrStart] using hparentSource

namespace CanonicalErasedRouteRootPrefix

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {Q : Popular.XSWarp
    (EqualInput L hL).lambda (EqualInput L hL).lambda.target}
  {p : WarpPath Q}

theorem parent_initial_mem_source
    (R : L.CanonicalErasedRouteRootPrefix hL Q p) :
    R.parent.initial ∈ Gamma.source := by
  simpa only [R.start_eq_parent_initial] using R.start_mem_source

/-- A root-prefix edge either survives the simultaneous repaired relation,
or one of the selected decoded carriers meets an endpoint of that edge.
This is the exact local invariant behind stopping at the first selected
route that collides with a grounded parent. -/
theorem pathEdge_mem_repaired_or_exists_decodedCarrier_contact
    (R : L.CanonicalErasedRouteRootPrefix hL Q p)
    (W : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    {e : V × V} (he : e ∈ R.path.edgeSet) :
    e ∈ canonicalErasedRepairedEdges (EqualInput L hL) W ∨
      ∃ q : WarpPath W,
        e.1 ∈ (EqualInput L hL).decodedVertexCarrier q.1 ∨
          e.2 ∈ (EqualInput L hL).decodedVertexCarrier q.1 := by
  let J := EqualInput L hL
  have heParent : e ∈ R.parent.edgeSet := R.edgeSet_subset he
  have heFamily : e ∈ J.familyEdges := by
    exact ⟨R.parent, R.parent_inessential.1, heParent⟩
  by_cases heRepaired : e ∈ canonicalErasedRepairedEdges J W
  · exact Or.inl heRepaired
  · right
    by_cases heBackward : e ∈ canonicalErasedBackwardEdges J W
    · simp only [canonicalErasedBackwardEdges, Set.mem_iUnion] at heBackward
      obtain ⟨q, hqe⟩ := heBackward
      have hends := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute J W q) hqe
      have hcarrier :=
        canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier J W q
      exact ⟨q, Or.inl (hcarrier hends.1)⟩
    · have heResidual : e ∈ canonicalErasedResidualEdges J W :=
        ⟨heFamily, heBackward⟩
      have heConflict : e ∈ canonicalErasedForwardConflictEdges J W := by
        by_contra heNotConflict
        apply heRepaired
        exact Or.inl ⟨heResidual, heNotConflict⟩
      obtain ⟨f, hfForward, htail | hhead⟩ := heConflict
      · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hfForward
        obtain ⟨q, hqf⟩ := hfForward
        have hends := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute J W q) hqf
        have hcarrier :=
          canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier J W q
        exact ⟨q, Or.inl (htail.symm ▸ hcarrier hends.1)⟩
      · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hfForward
        obtain ⟨q, hqf⟩ := hfForward
        have hends := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute J W q) hqf
        have hcarrier :=
          canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier J W q
        exact ⟨q, Or.inr (hhead.symm ▸ hcarrier hends.2)⟩

/-- Exact route-incidence strengthening of the preceding deletion
classifier.  If a root-prefix edge is removed, an endpoint of that edge is
an actual vertex of one of the canonical erased routes, not merely a point
of its broad decoded gadget carrier. -/
theorem pathEdge_mem_repaired_or_exists_routeVertex_contact
    (R : L.CanonicalErasedRouteRootPrefix hL Q p)
    (W : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    {e : V × V} (he : e ∈ R.path.edgeSet) :
    e ∈ canonicalErasedRepairedEdges (EqualInput L hL) W ∨
      ∃ q : WarpPath W,
        e.1 ∈ (canonicalErasedRoute (EqualInput L hL) W q).vertexSet ∨
          e.2 ∈ (canonicalErasedRoute (EqualInput L hL) W q).vertexSet := by
  let J := EqualInput L hL
  have heParent : e ∈ R.parent.edgeSet := R.edgeSet_subset he
  have heFamily : e ∈ J.familyEdges := by
    exact ⟨R.parent, R.parent_inessential.1, heParent⟩
  by_cases heRepaired : e ∈ canonicalErasedRepairedEdges J W
  · exact Or.inl heRepaired
  · right
    by_cases heBackward : e ∈ canonicalErasedBackwardEdges J W
    · simp only [canonicalErasedBackwardEdges, Set.mem_iUnion] at heBackward
      obtain ⟨q, hqe⟩ := heBackward
      have hends := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute J W q) hqe
      exact ⟨q, Or.inl hends.1⟩
    · have heResidual : e ∈ canonicalErasedResidualEdges J W :=
        ⟨heFamily, heBackward⟩
      have heConflict : e ∈ canonicalErasedForwardConflictEdges J W := by
        by_contra heNotConflict
        apply heRepaired
        exact Or.inl ⟨heResidual, heNotConflict⟩
      obtain ⟨f, hfForward, htail | hhead⟩ := heConflict
      · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hfForward
        obtain ⟨q, hqf⟩ := hfForward
        have hends := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute J W q) hqf
        exact ⟨q, Or.inl (htail.symm ▸ hends.1)⟩
      · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hfForward
        obtain ⟨q, hqf⟩ := hfForward
        have hends := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute J W q) hqf
        exact ⟨q, Or.inr (hhead.symm ▸ hends.2)⟩

/-- Parent-level form of the exact deletion classifier.  The stored finite
source prefix is not special: any edge of the protected grounded parent is
either retained, or one of its endpoints is an actual canonical-route
vertex of a selected route. -/
theorem parentEdge_mem_repaired_or_exists_routeVertex_contact
    (R : L.CanonicalErasedRouteRootPrefix hL Q p)
    (W : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    {e : V × V} (heParent : e ∈ R.parent.edgeSet) :
    e ∈ canonicalErasedRepairedEdges (EqualInput L hL) W ∨
      ∃ q : WarpPath W,
        e.1 ∈ (canonicalErasedRoute (EqualInput L hL) W q).vertexSet ∨
          e.2 ∈ (canonicalErasedRoute (EqualInput L hL) W q).vertexSet := by
  let J := EqualInput L hL
  have heFamily : e ∈ J.familyEdges := by
    exact ⟨R.parent, R.parent_inessential.1, heParent⟩
  by_cases heRepaired : e ∈ canonicalErasedRepairedEdges J W
  · exact Or.inl heRepaired
  · right
    by_cases heBackward : e ∈ canonicalErasedBackwardEdges J W
    · simp only [canonicalErasedBackwardEdges, Set.mem_iUnion] at heBackward
      obtain ⟨q, hqe⟩ := heBackward
      have hends := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute J W q) hqe
      exact ⟨q, Or.inl hends.1⟩
    · have heResidual : e ∈ canonicalErasedResidualEdges J W :=
        ⟨heFamily, heBackward⟩
      have heConflict : e ∈ canonicalErasedForwardConflictEdges J W := by
        by_contra heNotConflict
        apply heRepaired
        exact Or.inl ⟨heResidual, heNotConflict⟩
      obtain ⟨f, hfForward, htail | hhead⟩ := heConflict
      · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hfForward
        obtain ⟨q, hqf⟩ := hfForward
        have hends := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute J W q) hqf
        exact ⟨q, Or.inl (htail.symm ▸ hends.1)⟩
      · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hfForward
        obtain ⟨q, hqf⟩ := hfForward
        have hends := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute J W q) hqf
        exact ⟨q, Or.inr (hhead.symm ▸ hends.2)⟩

/-- If every selected actual erased route avoids the protected grounded
parent, then the complete parent edge set survives the repaired relation. -/
theorem parent_edgeSet_subset_repaired_of_routeVertices_disjoint
    (R : L.CanonicalErasedRouteRootPrefix hL Q p)
    (W : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (havoid : ∀ q : WarpPath W,
      Disjoint (canonicalErasedRoute (EqualInput L hL) W q).vertexSet
        R.parent.support) :
    R.parent.edgeSet ⊆ canonicalErasedRepairedEdges (EqualInput L hL) W := by
  intro e he
  rcases R.parentEdge_mem_repaired_or_exists_routeVertex_contact W he with
      heRepaired | ⟨q, hcontact⟩
  · exact heRepaired
  · exfalso
    have hends := R.parent.edgeSet_subset_support_prod he
    rcases hcontact with hcontact | hcontact
    · exact Set.disjoint_left.1 (havoid q) hcontact hends.1
    · exact Set.disjoint_left.1 (havoid q) hcontact hends.2

/-- If every selected canonical route avoids the grounded parent, the
entire finite root prefix survives.  This exact form avoids the broad
decoded-carrier overapproximation. -/
theorem path_edgeSet_subset_repaired_of_routeVertices_disjoint_parent
    (R : L.CanonicalErasedRouteRootPrefix hL Q p)
    (W : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (havoid : ∀ q : WarpPath W,
      Disjoint (canonicalErasedRoute (EqualInput L hL) W q).vertexSet
        R.parent.support) :
    R.path.edgeSet ⊆ canonicalErasedRepairedEdges (EqualInput L hL) W := by
  intro e he
  rcases R.pathEdge_mem_repaired_or_exists_routeVertex_contact W he with
      heRepaired | ⟨q, hcontact⟩
  · exact heRepaired
  · exfalso
    have hends := R.parent.edgeSet_subset_support_prod (R.edgeSet_subset he)
    rcases hcontact with hcontact | hcontact
    · exact Set.disjoint_left.1 (havoid q) hcontact hends.1
    · exact Set.disjoint_left.1 (havoid q) hcontact hends.2

/-- If every selected decoded carrier avoids the grounded parent, its
entire finite root prefix survives the repaired relation. -/
theorem path_edgeSet_subset_repaired_of_decodedCarriers_disjoint_parent
    (R : L.CanonicalErasedRouteRootPrefix hL Q p)
    (W : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (havoid : ∀ q : WarpPath W,
      Disjoint ((EqualInput L hL).decodedVertexCarrier q.1)
        R.parent.support) :
    R.path.edgeSet ⊆ canonicalErasedRepairedEdges (EqualInput L hL) W := by
  intro e he
  rcases R.pathEdge_mem_repaired_or_exists_decodedCarrier_contact W he with
      heRepaired | ⟨q, hcontact⟩
  · exact heRepaired
  · exfalso
    have hends := R.parent.edgeSet_subset_support_prod (R.edgeSet_subset he)
    rcases hcontact with hcontact | hcontact
    · exact Set.disjoint_left.1 (havoid q) hcontact hends.1
    · exact Set.disjoint_left.1 (havoid q) hcontact hends.2

/-- If the concrete source prefix survives in a relation, it roots the
initial vertex of the canonical erased route. -/
theorem reaches_initial
    (R : L.CanonicalErasedRouteRootPrefix hL Q p)
    {E : Set (V × V)} (hpath : R.path.edgeSet ⊆ E) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
        (canonicalErasedRoute (EqualInput L hL) Q p).initial := by
  refine ⟨R.path.start, R.start_mem_source, ?_⟩
  simpa only [R.finish_eq] using
    (finitePath_start_reaches_of_mem_support R.path hpath
      R.path.finish_mem_support)

end CanonicalErasedRouteRootPrefix

/-! ## Exact forward-vertex root transfer -/

/-- One route's forward edges belong to the simultaneous canonical repaired
relation. -/
theorem canonicalErasedRoute_forwardEdges_subset_repaired
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (p : WarpPath Q) :
    (canonicalErasedRoute J Q p).directionEdges .forward ⊆
      canonicalErasedRepairedEdges J Q := by
  intro e he
  exact Or.inr (Set.mem_iUnion.2 ⟨p, he⟩)

/-- Every actual forward-route vertex is rooted once the route initial and
the ambient starts of its compressed backward links are rooted.  These are
the only anchors left by chronological erasure. -/
theorem canonicalErasedRoute_forwardVertex_rooted_of_anchorReachability
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (p : WarpPath Q)
    {A : Set V}
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges J Q) a
        (canonicalErasedRoute J Q p).initial)
    (hbackward : ∀ (l : Link Gamma.graph),
      l ∈ (canonicalErasedRoute J Q p).links →
      l.direction = .backward →
      ∀ parent ∈ J.ladder.paths, l.path.IsSubpathOf parent →
        ∃ a ∈ A,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges J Q)
            a l.path.start)
    {x : V}
    (hx : x ∈ (canonicalErasedRoute J Q p).directionVertices .forward) :
    ∃ a ∈ A,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ canonicalErasedRepairedEdges J Q) a x := by
  let T := J.decodeFinitePath p.1
    (Q.starts_in_source p.2) (Q.ends_in_target p.2)
  have hback : BackwardLinksOn J.ladder.paths
      (canonicalErasedRoute J Q p) := by
    simpa only [canonicalErasedRoute, T] using
      T.erasedCompression_backwardLinksOn
  cases hroute : canonicalErasedRoute J Q p with
  | trivial v =>
      simp [AltPath.directionVertices, AltPath.links, hroute] at hx
  | finite F =>
      apply F.exists_root_reaching_forwardVertex
        (by simpa only [hroute] using hback)
        (by
          simpa only [hroute] using
            canonicalErasedRoute_forwardEdges_subset_repaired J Q p)
        (by simpa [hroute, AltPath.initial] using hinitial)
      · intro l hl hldir parent hparent hsub
        exact hbackward l (by simpa only [hroute] using hl) hldir
          parent hparent hsub
      · simpa only [hroute] using hx
  | infinite R =>
      have hterminal := T.erasedCompression.terminal_eq
      have hpath : T.erasedCompression.path = .infinite R := by
        simpa only [canonicalErasedRoute, T] using hroute
      rw [hpath] at hterminal
      simp at hterminal

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.exists_canonicalErasedRouteRootPrefix
#print axioms Erdos599.DWeb.KappaLadder.CanonicalErasedRouteRootPrefix.parent_initial_mem_source
#print axioms Erdos599.DWeb.KappaLadder.CanonicalErasedRouteRootPrefix.pathEdge_mem_repaired_or_exists_decodedCarrier_contact
#print axioms Erdos599.DWeb.KappaLadder.CanonicalErasedRouteRootPrefix.pathEdge_mem_repaired_or_exists_routeVertex_contact
#print axioms Erdos599.DWeb.KappaLadder.CanonicalErasedRouteRootPrefix.parentEdge_mem_repaired_or_exists_routeVertex_contact
#print axioms Erdos599.DWeb.KappaLadder.CanonicalErasedRouteRootPrefix.parent_edgeSet_subset_repaired_of_routeVertices_disjoint
#print axioms Erdos599.DWeb.KappaLadder.CanonicalErasedRouteRootPrefix.path_edgeSet_subset_repaired_of_routeVertices_disjoint_parent
#print axioms Erdos599.DWeb.KappaLadder.CanonicalErasedRouteRootPrefix.path_edgeSet_subset_repaired_of_decodedCarriers_disjoint_parent
#print axioms Erdos599.DWeb.KappaLadder.CanonicalErasedRouteRootPrefix.reaches_initial
#print axioms Erdos599.DWeb.KappaLadder.canonicalErasedRoute_forwardVertex_rooted_of_anchorReachability
