import ErdosProblems.Erdos599.SplitGroundingGroundedSeparatorGeometry
import ErdosProblems.Erdos599.GroundingPathPrefix
import ErdosProblems.Erdos599.GroundingEqualActiveSelection
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating GroundingEqualActiveSelection

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

variable {kappa : Cardinal.{u}}

private abbrev GroundedRouteRootInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private theorem grounded_decodeFinitePath_initial_of_start_old
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

private theorem grounded_decodeFinitePath_initial_mem_proxyPath_of_start_proxy
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
erased route in the grounded split auxiliary. -/
structure SplitGroundedErasedRouteRootPrefix
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (Q : Popular.XSWarp
      (GroundedRouteRootInput L hL).lambda
      (GroundedRouteRootInput L hL).lambda.target)
    (p : WarpPath Q) where
  parent : Gamma.DPath
  parent_inessential : parent ∈ Gamma.inessentialPaths L.limitWarp
  parent_exposed : parent ∈
    GroundingSimultaneousDecode.exposedLadderPaths
      (GroundedRouteRootInput L hL) p.1
  path : FinitePath Gamma.graph
  start_eq_parent_initial : path.start = parent.initial
  start_mem_source : path.start ∈ Gamma.source
  finish_eq : path.finish =
    (canonicalErasedRoute (GroundedRouteRootInput L hL) Q p).initial
  support_subset : path.support ⊆ parent.support
  edgeSet_subset : path.edgeSet ⊆ parent.edgeSet

/-- Every source of the grounded auxiliary names a grounded recorded
component, so no extra source-index hypothesis is needed. -/
theorem exists_splitGroundedErasedRouteRootPrefix
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (Q : Popular.XSWarp
      (GroundedRouteRootInput L hL).lambda
      (GroundedRouteRootInput L hL).lambda.target)
    (p : WarpPath Q) :
    Nonempty (L.SplitGroundedErasedRouteRootPrefix hL Q p) := by
  let J := GroundedRouteRootInput L hL
  let T := J.decodeFinitePath p.1
    (Q.starts_in_source p.2) (Q.ends_in_target p.2)
  have hrouteInitial :
      (canonicalErasedRoute J Q p).initial = T.initial :=
    T.erasedCompression.initial_eq
  rcases J.start_of_mem_lambda_source p.1 (Q.starts_in_source p.2) with
      ⟨x, hxFinite, hstart⟩ | ⟨i, hstart⟩
  · obtain ⟨a, ha, parent, hchosen, hterminal⟩ := hxFinite
    obtain ⟨groundedParent, hgroundedChosen, hsource⟩ := ha.1
    have hparent : groundedParent = parent :=
      Option.some.inj (hgroundedChosen.symm.trans hchosen)
    subst groundedParent
    rcases parent with q | r
    · have hfinish : q.finish = x := Option.some.inj hterminal
      have hinessential : (.inl q : Gamma.DPath) ∈
          Gamma.inessentialPaths L.limitWarp := by
        apply L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
        change a.1 + 1 ≤ kappa.ord
        exact (Order.add_one_le_iff).2 a.2
      have htrace :
          (canonicalErasedRoute J Q p).initial ∈
            DirectedPath.Path.support (Sum.inl q : Gamma.DPath) := by
        have hTinitial : T.initial = q.finish := by
          rw [hfinish]
          exact grounded_decodeFinitePath_initial_of_start_old J p.1
            (Q.starts_in_source p.2) (Q.ends_in_target p.2) x hstart
        rw [hrouteInitial, hTinitial]
        exact q.finish_mem_support
      obtain ⟨root, hrootStart, hrootFinish, hrootSupport, hrootEdges⟩ :=
        GroundingPathPrefix.exists_initialFinitePrefix
          (Sum.inl q : Gamma.DPath) htrace
      refine ⟨{
        parent := .inl q
        parent_inessential := hinessential
        parent_exposed := Or.inl ⟨hinessential.1, .old x, ?_,
          Or.inl ⟨x, by
            change x ∈ q.support
            rw [← hfinish]
            exact q.finish_mem_support, rfl⟩⟩
        path := root
        start_eq_parent_initial := hrootStart
        start_mem_source := ?_
        finish_eq := hrootFinish
        support_subset := hrootSupport
        edgeSet_subset := hrootEdges }⟩
      simpa only [hstart] using p.1.start_mem_support
      simpa only [hrootStart] using hsource
    · change (none : Option V) = some x at hterminal
      cases hterminal
  · obtain ⟨a, ha, hchosen⟩ := i.2
    obtain ⟨groundedParent, hgroundedChosen, hsource⟩ := ha.1
    have hiparent : groundedParent = i.1 :=
      Option.some.inj (hgroundedChosen.symm.trans hchosen)
    have hisource : i.1.initial ∈ Gamma.source := hiparent ▸ hsource
    have hiInessential : i.1 ∈ Gamma.inessentialPaths L.limitWarp := by
      apply L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
      change a.1 + 1 ≤ kappa.ord
      exact (Order.add_one_le_iff).2 a.2
    have htrace :
        (canonicalErasedRoute J Q p).initial ∈ i.1.support := by
      have hTinitial : T.initial ∈ (J.proxyPath i).support :=
        grounded_decodeFinitePath_initial_mem_proxyPath_of_start_proxy
          J p.1 (Q.starts_in_source p.2) (Q.ends_in_target p.2) i hstart
      rw [hrouteInitial]
      simpa only [J, GroundedRouteRootInput,
        splitGroundedPopularAuxiliaryInput, splitGroundedInfinitePath]
        using hTinitial
    obtain ⟨root, hrootStart, hrootFinish, hrootSupport, hrootEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix i.1 htrace
    refine ⟨{
      parent := i.1
      parent_inessential := hiInessential
      parent_exposed := by
        right
        simpa [GroundingSimultaneousDecode.exposedLadderPaths, hstart,
          J, GroundedRouteRootInput, splitGroundedPopularAuxiliaryInput,
          splitGroundedInfinitePath]
      path := root
      start_eq_parent_initial := hrootStart
      start_mem_source := ?_
      finish_eq := hrootFinish
      support_subset := hrootSupport
      edgeSet_subset := hrootEdges }⟩
    simpa only [hrootStart] using hisource

namespace SplitGroundedErasedRouteRootPrefix

variable {L : Gamma.KappaLadder kappa}
  {hL : L.IsSplitKappaHindrance}
  {Q : Popular.XSWarp
    (GroundedRouteRootInput L hL).lambda
    (GroundedRouteRootInput L hL).lambda.target}
  {p : WarpPath Q}

/-- Avoiding the complete auxiliary collision carrier of this route makes
the decoded carrier of another route disjoint from its grounded parent. -/
theorem decodedVertexCarrier_disjoint_parent
    (R : L.SplitGroundedErasedRouteRootPrefix hL Q p)
    (q : FinitePath (GroundedRouteRootInput L hL).lambda.graph)
    (hqsource : q.start ∈ (GroundedRouteRootInput L hL).lambda.source)
    (havoid : Disjoint q.support
      (GroundingEqualActiveSelection.collisionCarrier
        (GroundedRouteRootInput L hL) p.1)) :
    Disjoint
      ((GroundedRouteRootInput L hL).decodedVertexCarrier q)
      R.parent.support := by
  exact
    GroundingEqualActiveSelection.decodedVertexCarrier_disjoint_exposedLadderPath_of_support_disjoint
      (GroundedRouteRootInput L hL)
      (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
      q p.1 hqsource R.parent_exposed havoid

/-- A deleted grounded-prefix edge is incident with an actual erased-route
vertex.  Thus prefix deletion is witnessed by a concrete route contact, not
merely by membership in an auxiliary over-approximation. -/
theorem pathEdge_mem_repaired_or_exists_routeVertex_contact
    (R : L.SplitGroundedErasedRouteRootPrefix hL Q p)
    (W : Popular.XSWarp
      (GroundedRouteRootInput L hL).lambda
      (GroundedRouteRootInput L hL).lambda.target)
    {e : V × V} (he : e ∈ R.path.edgeSet) :
    e ∈ GroundingEqualActiveSelection.canonicalErasedRepairedEdges
        (GroundedRouteRootInput L hL) W ∨
      ∃ q : WarpPath W,
        e.1 ∈ (GroundingEqualActiveSelection.canonicalErasedRoute
          (GroundedRouteRootInput L hL) W q).vertexSet ∨
        e.2 ∈ (GroundingEqualActiveSelection.canonicalErasedRoute
          (GroundedRouteRootInput L hL) W q).vertexSet := by
  let J := GroundedRouteRootInput L hL
  have heParent : e ∈ R.parent.edgeSet := R.edgeSet_subset he
  have heFamily : e ∈ J.familyEdges :=
    ⟨R.parent, R.parent_inessential.1, heParent⟩
  by_cases heRepaired : e ∈
      GroundingEqualActiveSelection.canonicalErasedRepairedEdges J W
  · exact Or.inl heRepaired
  · right
    by_cases heBackward : e ∈
        GroundingEqualActiveSelection.canonicalErasedBackwardEdges J W
    · simp only [GroundingEqualActiveSelection.canonicalErasedBackwardEdges,
        Set.mem_iUnion] at heBackward
      obtain ⟨q, hqe⟩ := heBackward
      have hends := AltPath.directionEdge_endpoints_mem_vertexSet
        (GroundingEqualActiveSelection.canonicalErasedRoute J W q) hqe
      exact ⟨q, Or.inl hends.1⟩
    · have heResidual : e ∈
          GroundingEqualActiveSelection.canonicalErasedResidualEdges J W :=
        ⟨heFamily, heBackward⟩
      have heConflict : e ∈
          GroundingEqualActiveSelection.canonicalErasedForwardConflictEdges J W := by
        by_contra heNotConflict
        exact heRepaired (Or.inl ⟨heResidual, heNotConflict⟩)
      obtain ⟨f, hfForward, htail | hhead⟩ := heConflict
      · simp only [GroundingEqualActiveSelection.canonicalErasedForwardEdges,
          Set.mem_iUnion] at hfForward
        obtain ⟨q, hqf⟩ := hfForward
        have hends := AltPath.directionEdge_endpoints_mem_vertexSet
          (GroundingEqualActiveSelection.canonicalErasedRoute J W q) hqf
        exact ⟨q, Or.inl (htail.symm ▸ hends.1)⟩
      · simp only [GroundingEqualActiveSelection.canonicalErasedForwardEdges,
          Set.mem_iUnion] at hfForward
        obtain ⟨q, hqf⟩ := hfForward
        have hends := AltPath.directionEdge_endpoints_mem_vertexSet
          (GroundingEqualActiveSelection.canonicalErasedRoute J W q) hqf
        exact ⟨q, Or.inr (hhead.symm ▸ hends.2)⟩

/-- If every selected erased route avoids the grounded parent, the complete
finite original-source prefix survives in the canonical repaired relation. -/
theorem path_edgeSet_subset_repaired_of_routeVertices_disjoint_parent
    (R : L.SplitGroundedErasedRouteRootPrefix hL Q p)
    (W : Popular.XSWarp
      (GroundedRouteRootInput L hL).lambda
      (GroundedRouteRootInput L hL).lambda.target)
    (havoid : ∀ q : WarpPath W,
      Disjoint
        (GroundingEqualActiveSelection.canonicalErasedRoute
          (GroundedRouteRootInput L hL) W q).vertexSet
        R.parent.support) :
    R.path.edgeSet ⊆
      GroundingEqualActiveSelection.canonicalErasedRepairedEdges
        (GroundedRouteRootInput L hL) W := by
  intro e he
  rcases R.pathEdge_mem_repaired_or_exists_routeVertex_contact W he with
      heRepaired | ⟨q, hcontact⟩
  · exact heRepaired
  · exfalso
    have hends := R.parent.edgeSet_subset_support_prod
      (R.edgeSet_subset he)
    rcases hcontact with hcontact | hcontact
    · exact Set.disjoint_left.1 (havoid q) hcontact hends.1
    · exact Set.disjoint_left.1 (havoid q) hcontact hends.2

/-- Full collision-carrier avoidance is the exact auxiliary invariant which
protects a grounded source prefix from every route in a repaired family. -/
theorem path_edgeSet_subset_repaired_of_collisionCarrier_avoidance
    (R : L.SplitGroundedErasedRouteRootPrefix hL Q p)
    (W : Popular.XSWarp
      (GroundedRouteRootInput L hL).lambda
      (GroundedRouteRootInput L hL).lambda.target)
    (havoid : ∀ q ∈ W.paths,
      Disjoint q.support
        (GroundingEqualActiveSelection.collisionCarrier
          (GroundedRouteRootInput L hL) p.1)) :
    R.path.edgeSet ⊆
      GroundingEqualActiveSelection.canonicalErasedRepairedEdges
        (GroundedRouteRootInput L hL) W := by
  apply R.path_edgeSet_subset_repaired_of_routeVertices_disjoint_parent W
  intro q
  have hdecoded := R.decodedVertexCarrier_disjoint_parent q.1
    (W.starts_in_source q.2) (havoid q.1 q.2)
  exact Set.disjoint_of_subset_left
    (GroundingEqualActiveSelection.canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
      (GroundedRouteRootInput L hL) W q)
    hdecoded

/-- If the concrete parent prefix survives in a relation, it roots the
erased route initial at a genuine original source. -/
theorem reaches_initial
    (R : L.SplitGroundedErasedRouteRootPrefix hL Q p)
    {E : Set (V × V)} (hpath : R.path.edgeSet ⊆ E) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
        (canonicalErasedRoute (GroundedRouteRootInput L hL) Q p).initial := by
  refine ⟨R.path.start, R.start_mem_source, ?_⟩
  simpa only [R.finish_eq] using
    (GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
      R.path hpath R.path.finish_mem_support)

end SplitGroundedErasedRouteRootPrefix
end DWeb.KappaLadder
end Erdos599
