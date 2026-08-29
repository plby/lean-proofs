/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualMaximalSupply

/-!
# Original-source prefixes for grounded split equal routes

Every route in the grounded maximal split supply names a grounded
inessential ladder component.  Its decoded initial vertex lies on that
component, so the component has a finite prefix from a genuine original
source to the decoded route initial.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection

variable {kappa : Cardinal.{u}}

private abbrev SplitRouteRootInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

private theorem decodeFinitePath_initial_of_start_old
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

private theorem decodeFinitePath_initial_mem_proxyPath_of_start_proxy
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

/-- A finite original-source prefix ending at the initial vertex of one
canonical erased split route. -/
structure SplitCanonicalErasedRouteRootPrefix
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (Q : Popular.XSWarp
      (SplitRouteRootInput L hL).lambda
      (SplitRouteRootInput L hL).lambda.target)
    (p : WarpPath Q) where
  parentData : L.SplitReservedGroundedParent hL p.1
    (Q.starts_in_source p.2)
  path : FinitePath Gamma.graph
  start_eq_parent_initial : path.start = parentData.parent.initial
  start_mem_source : path.start ∈ Gamma.source
  finish_eq : path.finish =
    (canonicalErasedRoute (SplitRouteRootInput L hL) Q p).initial
  support_subset : path.support ⊆ parentData.parent.support
  edgeSet_subset : path.edgeSet ⊆ parentData.parent.edgeSet

/-- A grounded chronological source index constructs the original-source
prefix of the corresponding decoded route. -/
theorem exists_splitCanonicalErasedRouteRootPrefix
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (Q : Popular.XSWarp
      (SplitRouteRootInput L hL).lambda
      (SplitRouteRootInput L hL).lambda.target)
    (p : WarpPath Q)
    (hpground : (L.splitPopularAuxiliaryIndexed hL).f
      ⟨p.1.start, Q.starts_in_source p.2⟩ ∈ L.phiGround) :
    Nonempty (L.SplitCanonicalErasedRouteRootPrefix hL Q p) := by
  let J := SplitRouteRootInput L hL
  let T := J.decodeFinitePath p.1
    (Q.starts_in_source p.2) (Q.ends_in_target p.2)
  let R : L.SplitReservedGroundedParent hL p.1
      (Q.starts_in_source p.2) :=
    (L.splitReservedGroundedParent_nonempty hL p.1
      (Q.starts_in_source p.2) hpground).some
  have hrouteInitial :
      (canonicalErasedRoute J Q p).initial = T.initial :=
    T.erasedCompression.initial_eq
  have htrace :
      (canonicalErasedRoute J Q p).initial ∈ R.parent.support := by
    rcases R.source_represents with
        ⟨r, hparent, hstart⟩ | ⟨i, hparent, hstart⟩
    · have hTinitial : T.initial = r.finish :=
        decodeFinitePath_initial_of_start_old J p.1
          (Q.starts_in_source p.2) (Q.ends_in_target p.2)
          r.finish hstart
      rw [hrouteInitial, hTinitial, hparent]
      exact r.finish_mem_support
    · have hTinitial : T.initial ∈ (J.proxyPath i).support :=
        decodeFinitePath_initial_mem_proxyPath_of_start_proxy J p.1
          (Q.starts_in_source p.2) (Q.ends_in_target p.2)
          i hstart
      rw [hrouteInitial, hparent]
      exact hTinitial
  obtain ⟨r, hrStart, hrFinish, hrSupport, hrEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix R.parent htrace
  refine ⟨{
    parentData := R
    path := r
    start_eq_parent_initial := hrStart
    start_mem_source := ?_
    finish_eq := hrFinish
    support_subset := hrSupport
    edgeSet_subset := hrEdges }⟩
  simpa only [hrStart] using R.parent_initial_source

namespace SplitCanonicalErasedRouteRootPrefix

variable {L : Gamma.KappaLadder kappa}
  {hL : L.IsSplitKappaHindrance}
  {Q : Popular.XSWarp
    (SplitRouteRootInput L hL).lambda
    (SplitRouteRootInput L hL).lambda.target}
  {p : WarpPath Q}

/-- The represented parent is a limiting-ladder component. -/
theorem parent_mem_limitWarp
    (R : L.SplitCanonicalErasedRouteRootPrefix hL Q p) :
    R.parentData.parent ∈ L.limitWarp :=
  R.parentData.parent_inessential.1

/-- The represented parent is inessential in the limit. -/
theorem parent_inessential
    (R : L.SplitCanonicalErasedRouteRootPrefix hL Q p) :
    R.parentData.parent ∈ Gamma.inessentialPaths L.limitWarp :=
  R.parentData.parent_inessential

/-- The prefix starts at a genuine original-web source. -/
theorem parent_initial_mem_source
    (R : L.SplitCanonicalErasedRouteRootPrefix hL Q p) :
    R.parentData.parent.initial ∈ Gamma.source :=
  R.parentData.parent_initial_source

/-- A deleted root-prefix edge is incident with an actual canonical erased
route vertex. -/
theorem pathEdge_mem_repaired_or_exists_routeVertex_contact
    (R : L.SplitCanonicalErasedRouteRootPrefix hL Q p)
    (W : Popular.XSWarp
      (SplitRouteRootInput L hL).lambda
      (SplitRouteRootInput L hL).lambda.target)
    {e : V × V} (he : e ∈ R.path.edgeSet) :
    e ∈ canonicalErasedRepairedEdges (SplitRouteRootInput L hL) W ∨
      ∃ q : WarpPath W,
        e.1 ∈ (canonicalErasedRoute
          (SplitRouteRootInput L hL) W q).vertexSet ∨
        e.2 ∈ (canonicalErasedRoute
          (SplitRouteRootInput L hL) W q).vertexSet := by
  let J := SplitRouteRootInput L hL
  have heParent : e ∈ R.parentData.parent.edgeSet :=
    R.edgeSet_subset he
  have heFamily : e ∈ J.familyEdges := by
    exact ⟨R.parentData.parent, R.parentData.parent_inessential.1, heParent⟩
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
        exact heRepaired (Or.inl ⟨heResidual, heNotConflict⟩)
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

/-- If every actual selected route avoids the represented parent, the whole
root prefix survives. -/
theorem path_edgeSet_subset_repaired_of_routeVertices_disjoint_parent
    (R : L.SplitCanonicalErasedRouteRootPrefix hL Q p)
    (W : Popular.XSWarp
      (SplitRouteRootInput L hL).lambda
      (SplitRouteRootInput L hL).lambda.target)
    (havoid : ∀ q : WarpPath W,
      Disjoint
        (canonicalErasedRoute (SplitRouteRootInput L hL) W q).vertexSet
        R.parentData.parent.support) :
    R.path.edgeSet ⊆
      canonicalErasedRepairedEdges (SplitRouteRootInput L hL) W := by
  intro e he
  rcases R.pathEdge_mem_repaired_or_exists_routeVertex_contact W he with
      heRepaired | ⟨q, hcontact⟩
  · exact heRepaired
  · exfalso
    have hends :=
      R.parentData.parent.edgeSet_subset_support_prod (R.edgeSet_subset he)
    rcases hcontact with hcontact | hcontact
    · exact Set.disjoint_left.1 (havoid q) hcontact hends.1
    · exact Set.disjoint_left.1 (havoid q) hcontact hends.2

/-- In any simultaneous repaired relation, a grounded route initial is
already source-rooted or a selected route meets its grounded parent. -/
theorem sourceRooted_initial_or_routeContact_parent
    (R : L.SplitCanonicalErasedRouteRootPrefix hL Q p)
    (W : Popular.XSWarp
      (SplitRouteRootInput L hL).lambda
      (SplitRouteRootInput L hL).lambda.target) :
    (∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (SplitRouteRootInput L hL) W) a
        (canonicalErasedRoute (SplitRouteRootInput L hL) Q p).initial) ∨
    ∃ q : WarpPath W,
      ((canonicalErasedRoute
          (SplitRouteRootInput L hL) W q).vertexSet ∩
        R.parentData.parent.support).Nonempty := by
  by_cases hsurvive : R.path.edgeSet ⊆
      canonicalErasedRepairedEdges (SplitRouteRootInput L hL) W
  · left
    refine ⟨R.path.start, R.start_mem_source, ?_⟩
    simpa only [R.finish_eq] using
      (GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
        R.path hsurvive R.path.finish_mem_support)
  · right
    obtain ⟨e, hePath, heNot⟩ := Set.not_subset.mp hsurvive
    rcases R.pathEdge_mem_repaired_or_exists_routeVertex_contact W hePath with
        he | ⟨q, hq⟩
    · exact False.elim (heNot he)
    · refine ⟨q, ?_⟩
      have hends :=
        R.parentData.parent.edgeSet_subset_support_prod
          (R.edgeSet_subset hePath)
      rcases hq with hq | hq
      · exact ⟨e.1, hq, hends.1⟩
      · exact ⟨e.2, hq, hends.2⟩

/-- If the concrete prefix survives in a relation, it roots the erased
route initial. -/
theorem reaches_initial
    (R : L.SplitCanonicalErasedRouteRootPrefix hL Q p)
    {E : Set (V × V)} (hpath : R.path.edgeSet ⊆ E) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
        (canonicalErasedRoute (SplitRouteRootInput L hL) Q p).initial := by
  refine ⟨R.path.start, R.start_mem_source, ?_⟩
  simpa only [R.finish_eq] using
    (GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
      R.path hpath R.path.finish_mem_support)

end SplitCanonicalErasedRouteRootPrefix
end DWeb.KappaLadder
end Erdos599
