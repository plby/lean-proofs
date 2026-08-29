/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualOrderedRooting
import ErdosProblems.Erdos599.GroundingEqualTargetContactRoot

/-!
# Ordered source-rooted contact with an equal target component

Immediately before an ordered route `q` is switched, all of its grounded
backward owners are source-rooted in the repaired relation of the earlier
routes.  Adjoining the forward edges of `q` therefore roots either its
target marker or the entry of its first self-owned backward link.  In both
cases the rooted vertex lies on the hanging equal target component of `q`.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection

variable {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
variable {P : Popular.XSWarp
  (L.popularAuxiliaryInput hL.legal).lambda
  (L.popularAuxiliaryInput hL.legal).lambda.target}

namespace OrderedReservedStationaryDiagonalEqualSelection

/-- A finite reachability chain in `base ∪ inserted` either survives after
deleting `blocked` base edges, or has a first displayed blocked base step
whose tail is still reachable in the pruned relation. -/
theorem reflTransGen_union_prune_or_exists_conflict
    {base inserted blocked : Set (V × V)} {a b : V}
    (hab : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ base ∪ inserted) a b) :
    Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ (base \ blocked) ∪ inserted) a b ∨
      ∃ u v,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ (base \ blocked) ∪ inserted) a u ∧
        (u, v) ∈ base ∧ (u, v) ∈ blocked ∧
        (u, v) ∉ inserted := by
  induction hab using Relation.ReflTransGen.trans_induction_on with
  | refl => exact Or.inl .refl
  | single hab =>
      rename_i x y
      rcases hab with hbase | hinserted
      · by_cases hblocked : (x, y) ∈ blocked
        · by_cases hinserted : (x, y) ∈ inserted
          · exact Or.inl (.single (Or.inr hinserted))
          · exact Or.inr ⟨x, y, .refl, hbase, hblocked, hinserted⟩
        · exact Or.inl (.single (Or.inl ⟨hbase, hblocked⟩))
      · exact Or.inl (.single (Or.inr hinserted))
  | trans hab hbc ihab ihbc =>
      rcases ihab with hab' | ⟨u, v, hau, huvBase, huvBlocked, huvNotInserted⟩
      · rcases ihbc with hbc' |
          ⟨u, v, hbu, huvBase, huvBlocked, huvNotInserted⟩
        · exact Or.inl (hab'.trans hbc')
        · exact Or.inr
            ⟨u, v, hab'.trans hbu, huvBase, huvBlocked, huvNotInserted⟩
      · exact Or.inr
          ⟨u, v, hau, huvBase, huvBlocked, huvNotInserted⟩

/-- The reachability relation available while processing one ordered route:
the repaired relation of all lower-index routes, together with the forward
edges of the current route. -/
def orderedRouteReachabilityEdges
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes) : Set (V × V) :=
  canonicalErasedRepairedEdges
      (L.popularAuxiliaryInput hL.legal)
      (routesBeforeIndex S
        (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q)) ∪
    (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩).directionEdges .forward

/-- The ordered one-route reachability relation uses only original graph
edges. -/
theorem orderedRouteReachabilityEdges_subset_adj
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes) :
    S.orderedRouteReachabilityEdges q ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with he | he
  · exact S.routesBeforeIndex_repairedEdges_subset_adj
      (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q) he
  · simp only [AltPath.directionEdges, Set.mem_iUnion] at he
    obtain ⟨l, _hl, _hdir, hel⟩ := he
    exact l.path.edgeSet_subset_adj hel

/-- Earlier-stage edges which conflict in head or tail with a forward edge
of the current route. -/
def orderedRouteForwardConflictEdges
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes) : Set (V × V) :=
  {e | ∃ f ∈ (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩).directionEdges .forward,
    e.1 = f.1 ∨ e.2 = f.2}

/-- The valid one-route ordered transaction: delete every conflicting
earlier edge before inserting the current route's forward edges. -/
def orderedRouteSwitchEdges
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes) : Set (V × V) :=
  (canonicalErasedRepairedEdges
      (L.popularAuxiliaryInput hL.legal)
      (routesBeforeIndex S
        (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q)) \
    S.orderedRouteForwardConflictEdges q) ∪
  (canonicalErasedRoute
    (L.popularAuxiliaryInput hL.legal)
    ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
    ⟨q.1, S.routes_subset_equalBase q.2⟩).directionEdges .forward

theorem orderedRouteSwitchEdges_subset_reachabilityEdges
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes) :
    S.orderedRouteSwitchEdges q ⊆ S.orderedRouteReachabilityEdges q := by
  rintro e (he | he)
  · exact Or.inl he.1
  · exact Or.inr he

/-- The one-route ordered transaction uses only original graph edges. -/
theorem orderedRouteSwitchEdges_subset_adj
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes) :
    S.orderedRouteSwitchEdges q ⊆ {e | Gamma.graph.Adj e.1 e.2} :=
  S.orderedRouteSwitchEdges_subset_reachabilityEdges q |>.trans
    (S.orderedRouteReachabilityEdges_subset_adj q)

/-- The current route's forward relation is biunique.  It is a restriction
of the simultaneous forward relation of the decoded-carrier-disjoint final
family. -/
theorem route_forwardEdges_biUnique
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈
      (canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
        ⟨q.1, S.routes_subset_equalBase q.2⟩).directionEdges .forward) := by
  let J := L.popularAuxiliaryInput hL.legal
  have hfull := canonicalErasedForwardEdges_biUnique_of_decodedCarrierDisjoint
    J S.routes S.routes_decodedDisjoint
  have hmem : ∀ {e : V × V}, e ∈
      (canonicalErasedRoute J
        ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
        ⟨q.1, S.routes_subset_equalBase q.2⟩).directionEdges .forward →
      e ∈ canonicalErasedForwardEdges J S.routes := by
    intro e he
    simp only [canonicalErasedForwardEdges, Set.mem_iUnion]
    refine ⟨q, ?_⟩
    simpa only [canonicalErasedRoute] using he
  constructor
  · intro x y z hxz hyz
    exact hfull.1 (hmem hxz) (hmem hyz)
  · intro x y z hxy hxz
    exact hfull.2 (hmem hxy) (hmem hxz)

/-- Deleting all cross-head and cross-tail conflicts makes the ordered
one-route transaction biunique. -/
theorem orderedRouteSwitchEdges_biUnique
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ S.orderedRouteSwitchEdges q) := by
  let E₀ := canonicalErasedRepairedEdges
    (L.popularAuxiliaryInput hL.legal)
    (routesBeforeIndex S
      (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q))
  let F := (canonicalErasedRoute
    (L.popularAuxiliaryInput hL.legal)
    ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
    ⟨q.1, S.routes_subset_equalBase q.2⟩).directionEdges .forward
  have hbase : Relator.BiUnique (fun x y ↦
      (x, y) ∈ E₀ \ S.orderedRouteForwardConflictEdges q) := by
    have hE₀ := S.routesBeforeIndex_repairedEdges_biUnique
      (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q)
    constructor
    · intro x y z hxz hyz
      exact hE₀.1 hxz.1 hyz.1
    · intro x y z hxy hxz
      exact hE₀.2 hxy.1 hxz.1
  have hforward : Relator.BiUnique (fun x y ↦ (x, y) ∈ F) :=
    S.route_forwardEdges_biUnique q
  constructor
  · intro x y z hxz hyz
    rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
    · exact hbase.1 hxz hyz
    · exfalso
      exact hxz.2 ⟨(y, z), hyz, Or.inr rfl⟩
    · exfalso
      exact hyz.2 ⟨(x, z), hxz, Or.inr rfl⟩
    · exact hforward.1 hxz hyz
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact hbase.2 hxy hxz
    · exfalso
      exact hxy.2 ⟨(x, z), hxz, Or.inl rfl⟩
    · exfalso
      exact hxz.2 ⟨(x, y), hxy, Or.inl rfl⟩
    · exact hforward.2 hxy hxz

/-- A lower-stage edge conflicting with a current forward edge is a genuine
limiting-ladder edge.  It cannot be an earlier inserted forward edge,
because the two selected routes have disjoint decoded carriers. -/
theorem repairedBefore_mem_familyEdges_of_conflict_currentForward
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes) {e f : V × V}
    (he : e ∈ canonicalErasedRepairedEdges
      (L.popularAuxiliaryInput hL.legal)
      (routesBeforeIndex S
        (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q)))
    (hf : f ∈ (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩).directionEdges .forward)
    (hconflict : e.1 = f.1 ∨ e.2 = f.2) :
    e ∈ (L.popularAuxiliaryInput hL.legal).familyEdges := by
  let J := L.popularAuxiliaryInput hL.legal
  let a := warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q
  let W := routesBeforeIndex S a
  let Q := (L.popularAuxiliaryIndexed hL).equalSubwarp S.base
  let qQ : WarpPath Q := ⟨q.1, S.routes_subset_equalBase q.2⟩
  rcases he with heResidual | heForward
  · exact heResidual.1.1
  · exfalso
    simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at heForward
    obtain ⟨r, hre⟩ := heForward
    obtain ⟨hrRoutes, hrlt⟩ := r.2
    let rS : WarpPath S.routes := ⟨r.1, hrRoutes⟩
    have hrq : rS ≠ q := by
      intro hrq
      have hindex := congrArg
        (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes) hrq
      exact (ne_of_lt hrlt) hindex
    have hdisj : Disjoint (J.decodedVertexCarrier r.1)
        (J.decodedVertexCarrier q.1) := by
      exact S.routes_decodedDisjoint hrRoutes q.2
        (fun hval ↦ hrq (Subtype.ext hval))
    have hrEnds := AltPath.directionEdge_endpoints_mem_vertexSet
      (canonicalErasedRoute J W r) hre
    have hqEnds := AltPath.directionEdge_endpoints_mem_vertexSet
      (canonicalErasedRoute J Q qQ) hf
    have hrCarrier :=
      canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier J W r
    have hqCarrier :=
      canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier J Q qQ
    rcases hconflict with htail | hhead
    · have heq : e.1 ∈ J.decodedVertexCarrier q.1 := by
        rw [htail]
        exact hqCarrier hqEnds.1
      exact Set.disjoint_left.1 hdisj (hrCarrier hrEnds.1) heq
    · have heq : e.2 ∈ J.decodedVertexCarrier q.1 := by
        rw [hhead]
        exact hqCarrier hqEnds.2
      exact Set.disjoint_left.1 hdisj (hrCarrier hrEnds.2) heq

/-- At its ordered switch, every selected route reaches a source-rooted
point of its own hanging equal target component. -/
theorem route_exists_sourceRooted_targetComponentContact_atSwitch
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes)
    (R : L.CanonicalErasedRouteRootPrefix hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩)
    (T : L.EqualTargetComponent hL S.base q.1
      (S.routes_subset_equalBase q.2)) :
    ∃ x ∈ T.component.support, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ S.orderedRouteReachabilityEdges q) a x := by
  classical
  let J := L.popularAuxiliaryInput hL.legal
  let Q := (L.popularAuxiliaryIndexed hL).equalSubwarp S.base
  let qQ : WarpPath Q := ⟨q.1, S.routes_subset_equalBase q.2⟩
  let E := S.orderedRouteReachabilityEdges q
  have hinitial : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a
        (canonicalErasedRoute J Q qQ).initial := by
    obtain ⟨a, ha, hareach⟩ := S.route_initial_sourceRooted_beforeIndex q R
    refine ⟨a, ha, Relation.ReflTransGen.mono ?_ _ _ hareach⟩
    intro u v huv
    exact Or.inl huv
  have hforward :
      (canonicalErasedRoute J Q qQ).directionEdges .forward ⊆ E := by
    intro e he
    exact Or.inr he
  have hgroundedActual : ∀ (b : Link Gamma.graph),
      b ∈ (canonicalErasedRoute J Q qQ).links →
      b.direction = .backward →
      ∀ (parent : Gamma.DPath), parent ∈ J.ladder.paths →
      parent.initial ∈ Gamma.source → b.path.IsSubpathOf parent →
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a b.path.start := by
    intro b hb hbdir parent hparent hparentSource hsub
    obtain ⟨a, ha, hareach⟩ :=
      S.backwardOwner_start_sourceRooted_beforeIndex q b hb hbdir
        parent hparent hparentSource hsub
    refine ⟨a, ha, Relation.ReflTransGen.mono ?_ _ _ hareach⟩
    intro u v huv
    exact Or.inl huv
  let D := J.decodeFinitePath qQ.1
    (Q.starts_in_source qQ.2) (Q.ends_in_target qQ.2)
  have hterminal :
      (canonicalErasedRoute J Q qQ).terminal? = some T.marker.1 := by
    have hDterminal : D.terminal = T.marker.1 := by
      exact J.decodeFinitePath_terminal_of_finish_old qQ.1
        (Q.starts_in_source qQ.2) (Q.ends_in_target qQ.2)
        T.marker.1 T.finish_eq
    exact D.erasedCompression.terminal_eq.trans (congrArg some hDterminal)
  have hback : BackwardLinksOn J.ladder.paths
      (canonicalErasedRoute J Q qQ) := by
    change BackwardLinksOn J.ladder.paths D.erasedCompression.path
    exact D.erasedCompression_backwardLinksOn
  by_cases hself : ∃ l ∈ (canonicalErasedRoute J Q qQ).links,
      l.direction = .backward ∧ l.path.IsSubpathOf T.component
  · cases hroute : canonicalErasedRoute J Q qQ with
    | trivial v => simp [hroute, AltPath.links] at hself
    | finite F =>
        obtain ⟨l, hl, hlself, hfirstMin⟩ :=
          F.exists_first_link
            (fun l ↦ l.direction = .backward ∧
              l.path.IsSubpathOf T.component) (by
              simpa only [hroute] using hself)
        have hlroute : l ∈ (canonicalErasedRoute J Q qQ).links := by
          simpa only [hroute] using hl
        have hlroot : ∃ a ∈ Gamma.source,
            Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a l.entry := by
          apply canonicalErasedRoute_backwardLink_entry_rooted_of_priorBackward
            J Q qQ l hlroute hlself.1 hinitial hforward
          intro b hb hbdir _hbowner F' hroute' bi li hbi hli hlt
          obtain ⟨parent, hparent, hsub, hroot | hownerSelf⟩ :=
            L.strictCollisionFree_equalSubwarp_backwardLink_groundedOr_selfOwned
              hL S.base q (S.routes_targetPure q.1 q.2) T b hb hbdir
          · apply hgroundedActual b hb hbdir parent
            · simpa only [J, KappaLadder.popularAuxiliaryInput] using hparent
            · exact hroot
            · exact hsub
          · exfalso
            have hFF : F' = F := by
              rw [hroute] at hroute'
              exact AltPath.finite.inj hroute'.symm
            subst F'
            apply hfirstMin bi li hli hlt
            constructor
            · simpa only [hbi] using hbdir
            · rw [hbi]
              exact hownerSelf ▸ hsub
        refine ⟨l.entry, ?_, hlroot⟩
        exact canonicalErasedRoute_backwardLink_entry_mem_owner
          J Q qQ l hlroute hlself.1 T.component
          T.component_essential.1 hlself.2
    | infinite W =>
        rw [hroute] at hterminal
        simp [AltPath.terminal?] at hterminal
  · have hbackward : ∀ (l : Link Gamma.graph),
        l ∈ (canonicalErasedRoute J Q qQ).links →
        l.direction = .backward →
        ∀ parent ∈ J.ladder.paths, l.path.IsSubpathOf parent →
          ∃ a ∈ Gamma.source,
            Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E)
              a l.path.start := by
      intro l hl hldir parent hparent hsub
      obtain ⟨owner, howner, hownerSub, hroot | hownerSelf⟩ :=
        L.strictCollisionFree_equalSubwarp_backwardLink_groundedOr_selfOwned
          hL S.base q (S.routes_targetPure q.1 q.2) T l hl hldir
      · apply hgroundedActual l hl hldir owner
        · simpa only [J, KappaLadder.popularAuxiliaryInput] using howner
        · exact hroot
        · exact hownerSub
      · exfalso
        apply hself
        exact ⟨l, hl, hldir, hownerSelf ▸ hownerSub⟩
    have hmarkerRoot : ∃ a ∈ Gamma.source,
        Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E)
          a T.marker.1 := by
      cases hroute : canonicalErasedRoute J Q qQ with
      | trivial v =>
          have hvm : v = T.marker.1 := by
            simpa [hroute, AltPath.terminal?] using hterminal
          simpa [hroute, AltPath.initial, hvm] using hinitial
      | finite F =>
          have hroot := F.exists_root_reaching_terminal
            (by simpa only [hroute] using hback)
            (by simpa only [hroute] using hforward)
            (by simpa [hroute, AltPath.initial] using hinitial)
            (by
              intro l hl hldir parent hparent hsub
              exact hbackward l (by simpa only [hroute] using hl)
                hldir parent hparent hsub)
          have hFm : F.terminal = T.marker.1 := by
            simpa [hroute, AltPath.terminal?] using hterminal
          simpa only [hFm] using hroot
      | infinite W =>
          rw [hroute] at hterminal
          simp [AltPath.terminal?] at hterminal
    exact ⟨T.marker.1, T.marker_mem_support, hmarkerRoot⟩

/-- The rooted equal-target contact either survives in the valid biunique
one-route transaction, or the obstruction is displayed by an earlier edge
and a current forward edge sharing exactly a tail or a head. -/
theorem route_targetContact_rooted_or_exists_switchConflict
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes)
    (R : L.CanonicalErasedRouteRootPrefix hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩)
    (T : L.EqualTargetComponent hL S.base q.1
      (S.routes_subset_equalBase q.2)) :
    (∃ x ∈ T.component.support, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ S.orderedRouteSwitchEdges q) a x) ∨
    (∃ a ∈ Gamma.source, ∃ u v f,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ S.orderedRouteSwitchEdges q) a u ∧
      (u, v) ∈ canonicalErasedRepairedEdges
        (L.popularAuxiliaryInput hL.legal)
        (routesBeforeIndex S
          (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q)) ∧
      (u, v) ∈ (L.popularAuxiliaryInput hL.legal).familyEdges ∧
      (u, v) ∉ (canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
        ⟨q.1, S.routes_subset_equalBase q.2⟩).directionEdges .forward ∧
      f ∈ (canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
        ⟨q.1, S.routes_subset_equalBase q.2⟩).directionEdges .forward ∧
      (u = f.1 ∨ v = f.2)) := by
  obtain ⟨x, hxT, a, haSource, hax⟩ :=
    S.route_exists_sourceRooted_targetComponentContact_atSwitch q R T
  let base := canonicalErasedRepairedEdges
    (L.popularAuxiliaryInput hL.legal)
    (routesBeforeIndex S
      (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q))
  let inserted := (canonicalErasedRoute
    (L.popularAuxiliaryInput hL.legal)
    ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
    ⟨q.1, S.routes_subset_equalBase q.2⟩).directionEdges .forward
  let blocked := S.orderedRouteForwardConflictEdges q
  have hax' : Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ base ∪ inserted) a x := by
    simpa only [orderedRouteReachabilityEdges, base, inserted] using hax
  rcases reflTransGen_union_prune_or_exists_conflict hax' with
      hsurvives | ⟨u, v, hau, huvBase, huvBlocked, huvNotInserted⟩
  · left
    refine ⟨x, hxT, a, haSource, ?_⟩
    simpa only [orderedRouteSwitchEdges, base, inserted, blocked] using hsurvives
  · right
    obtain ⟨f, hf, htailOrHead⟩ := huvBlocked
    have huvFamily :=
      S.repairedBefore_mem_familyEdges_of_conflict_currentForward
        q huvBase hf htailOrHead
    refine ⟨a, haSource, u, v, f, ?_, huvBase, huvFamily,
      huvNotInserted, hf, htailOrHead⟩
    simpa only [orderedRouteSwitchEdges, base, inserted, blocked] using hau

end OrderedReservedStationaryDiagonalEqualSelection
end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.orderedRouteReachabilityEdges_subset_adj
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.orderedRouteSwitchEdges_subset_adj
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.orderedRouteSwitchEdges_biUnique
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.repairedBefore_mem_familyEdges_of_conflict_currentForward
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.route_exists_sourceRooted_targetComponentContact_atSwitch
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.route_targetContact_rooted_or_exists_switchConflict
