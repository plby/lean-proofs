/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualTargetComponent

/-!
# Stationary pruning of strict hanging collisions

A target-pure canonical route may meet a hanging limiting component whose
owner stage is weakly below the route's source stage.  The strict part is
nonstationary.  Indeed, pressing down makes the owner stage constant on a
stationary subfamily; marker uniqueness and disjointness identify one fixed
limiting component, while every corresponding auxiliary path meets its
countable Lambda ladder trace.

Thus an equal-stage closure may first discard all strict backward-owner
collisions.  The remaining hanging backward contacts are diagonal and are
handled by the ordered entry stopping theorem.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath
open Alternating Stationary
open GroundingEqualActiveSelection

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A concrete compressed backward link whose hanging owner is strictly
earlier than the source index of its auxiliary route. -/
structure StrictBackwardCollision
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (p : WarpPath P) where
  link : Link Gamma.graph
  link_mem : link ∈ (canonicalErasedRoute
    (L.popularAuxiliaryInput hL.legal) P p).links
  link_backward : link.direction = .backward
  parent : Gamma.DPath
  parent_mem : parent ∈ L.limitWarp
  parent_hanging : PopularAuxiliary.IsHangingPath Gamma parent
  link_subpath : link.path.IsSubpathOf parent
  stage_lt : L.hangingComponentStage hL.legal parent parent_mem
      parent_hanging <
    (L.popularAuxiliaryIndexed hL).f
      ⟨p.1.start, P.starts_in_source p.2⟩

/-- Paths of an auxiliary warp carrying at least one strict backward-owner
collision. -/
def strictBackwardCollisionPaths
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target) :
    Set (FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph) :=
  {p | ∃ hp : p ∈ P.paths,
    Nonempty (L.StrictBackwardCollision hL P ⟨p, hp⟩)}

theorem strictBackwardCollisionPaths_subset
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target) :
    L.strictBackwardCollisionPaths hL P ⊆ P.paths := by
  rintro p ⟨hp, _⟩
  exact hp

/-- The subwarp obtained by deleting every route carrying a strict
backward-owner collision. -/
def strictCollisionFreeSubwarp
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target) :
    Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target where
  paths := P.paths \ L.strictBackwardCollisionPaths hL P
  disjoint := by
    intro p hp q hq hpq
    exact P.disjoint hp.1 hq.1 hpq
  starts_in_source hp := P.starts_in_source hp.1
  ends_in_target hp := P.ends_in_target hp.1

@[simp] theorem mem_strictCollisionFreeSubwarp_paths
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (p : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph) :
    p ∈ (L.strictCollisionFreeSubwarp hL P).paths ↔
      p ∈ P.paths ∧ p ∉ L.strictBackwardCollisionPaths hL P := by
  rfl

theorem strictCollisionFreeSubwarp_paths_subset
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target) :
    (L.strictCollisionFreeSubwarp hL P).paths ⊆ P.paths := by
  intro p hp
  exact hp.1

theorem strictCollisionFreeSubwarp_has_no_strict_collision
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (p : WarpPath (L.strictCollisionFreeSubwarp hL P)) :
    IsEmpty (L.StrictBackwardCollision hL P
      ⟨p.1, (L.strictCollisionFreeSubwarp_paths_subset hL P p.2)⟩) := by
  refine ⟨fun hc ↦ p.2.2 ?_⟩
  exact ⟨p.2.1, ⟨hc⟩⟩

/-- On the collision-free subwarp, the weak chronology bound for a hanging
backward owner is automatically an equality. -/
theorem strictCollisionFreeSubwarp_backwardOwnerStage_eq_source
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (p : WarpPath (L.strictCollisionFreeSubwarp hL P))
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal) P
      ⟨p.1, L.strictCollisionFreeSubwarp_paths_subset hL P p.2⟩).links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma parent)
    (hsub : l.path.IsSubpathOf parent)
    (hle : L.hangingComponentStage hL.legal parent hparent hhang ≤
      (L.popularAuxiliaryIndexed hL).f
        ⟨p.1.start, P.starts_in_source
          (L.strictCollisionFreeSubwarp_paths_subset hL P p.2)⟩) :
    L.hangingComponentStage hL.legal parent hparent hhang =
      (L.popularAuxiliaryIndexed hL).f
        ⟨p.1.start, P.starts_in_source
          (L.strictCollisionFreeSubwarp_paths_subset hL P p.2)⟩ := by
  apply le_antisymm hle
  apply le_of_not_gt
  intro hlt
  have hempty :=
    L.strictCollisionFreeSubwarp_has_no_strict_collision hL P p
  exact hempty.false {
    link := l
    link_mem := hl
    link_backward := hldir
    parent := parent
    parent_mem := hparent
    parent_hanging := hhang
    link_subpath := hsub
    stage_lt := hlt }

/-- Two hanging limiting components with the same owner stage are the same
component. -/
theorem IsLegal.hangingComponent_eq_of_stage_eq
    {L : Gamma.KappaLadder kappa} (hL : L.IsLegal)
    {p q : Gamma.DPath} (hp : p ∈ L.limitWarp)
    (hpHang : PopularAuxiliary.IsHangingPath Gamma p)
    (hq : q ∈ L.limitWarp)
    (hqHang : PopularAuxiliary.IsHangingPath Gamma q)
    (hstage : L.hangingComponentStage hL p hp hpHang =
      L.hangingComponentStage hL q hq hqHang) :
    p = q := by
  have hpMarker := L.marker_hangingComponentStage hL p hp hpHang
  have hqMarker := L.marker_hangingComponentStage hL q hq hqHang
  rw [hstage] at hpMarker
  have hinitial : p.initial = q.initial :=
    Option.some.inj (hpMarker.symm.trans hqMarker)
  exact DWeb.IsWarp.eq_of_initial_eq Gamma
    (hL.warpStages (Ladder.finalStage kappa)) hp hq hinitial

/-- For an equal-stage route surviving strict-collision pruning, every
hanging backward owner satisfying the chronology bound is the route's own
target-marker component.  Thus the equality case is genuinely diagonal,
not merely an equality of ordinal labels. -/
theorem strictCollisionFree_equalSubwarp_backwardOwner_eq_targetComponent
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (p : WarpPath (L.strictCollisionFreeSubwarp hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P)))
    (T : L.EqualTargetComponent hL P p.1 p.2.1)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P)
      ⟨p.1, L.strictCollisionFreeSubwarp_paths_subset hL
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma parent)
    (hsub : l.path.IsSubpathOf parent)
    (hle : L.hangingComponentStage hL.legal parent hparent hhang ≤
      (L.popularAuxiliaryIndexed hL).f
        ⟨p.1.start,
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
            (L.strictCollisionFreeSubwarp_paths_subset hL
              ((L.popularAuxiliaryIndexed hL).equalSubwarp P) p.2)⟩) :
    parent = T.component := by
  have hparentSource :=
    L.strictCollisionFreeSubwarp_backwardOwnerStage_eq_source hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P) p l hl hldir
      parent hparent hhang hsub hle
  have hsourceProof :
      (⟨p.1.start,
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
          (L.strictCollisionFreeSubwarp_paths_subset hL
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P) p.2)⟩ :
          (L.popularAuxiliaryInput hL.legal).lambda.source) =
      ⟨p.1.start,
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
          p.2.1⟩ := Subtype.ext rfl
  have hparentIndex :
      L.hangingComponentStage hL.legal parent hparent hhang =
        (L.popularAuxiliaryIndexed hL).f
          ⟨p.1.start,
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
              p.2.1⟩ :=
    hparentSource.trans (congrArg (L.popularAuxiliaryIndexed hL).f
      hsourceProof)
  have hcomponentIndex :
      L.hangingComponentStage hL.legal T.component
          T.component_essential.1 T.component_hanging =
        (L.popularAuxiliaryIndexed hL).f
          ⟨p.1.start,
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
              p.2.1⟩ :=
    T.ownerStage_eq.trans T.sourceIndex_eq.symm
  exact hL.legal.hangingComponent_eq_of_stage_eq
    hparent hhang T.component_essential.1 T.component_hanging
    (hparentIndex.trans hcomponentIndex.symm)

/-- Every backward link of a target-pure equal route surviving the pruning
is owned either by an already grounded limiting component or by that same
route's target-marker component. -/
theorem strictCollisionFree_equalSubwarp_backwardLink_groundedOr_selfOwned
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (p : WarpPath (L.strictCollisionFreeSubwarp hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P)))
    (hpure : (L.popularAuxiliaryInput hL.legal).IsTargetPure p.1)
    (T : L.EqualTargetComponent hL P p.1 p.2.1)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P)
      ⟨p.1, L.strictCollisionFreeSubwarp_paths_subset hL
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).links)
    (hldir : l.direction = .backward) :
    ∃ parent ∈ L.limitWarp, l.path.IsSubpathOf parent ∧
      (parent.initial ∈ Gamma.source ∨ parent = T.component) := by
  classical
  let Q := (L.popularAuxiliaryIndexed hL).equalSubwarp P
  let pQ : WarpPath Q :=
    ⟨p.1, L.strictCollisionFreeSubwarp_paths_subset hL Q p.2⟩
  let D := (L.popularAuxiliaryInput hL.legal).decodeFinitePath pQ.1
    (Q.starts_in_source pQ.2) (Q.ends_in_target pQ.2)
  have hback : BackwardLinksOn
      (L.popularAuxiliaryInput hL.legal).ladder.paths
      (canonicalErasedRoute (L.popularAuxiliaryInput hL.legal) Q pQ) := by
    change BackwardLinksOn
      (L.popularAuxiliaryInput hL.legal).ladder.paths
      D.erasedCompression.path
    exact D.erasedCompression_backwardLinksOn
  obtain ⟨parent, hparentAux, hsub⟩ := hback l hl hldir
  have hparent : parent ∈ L.limitWarp := by
    simpa only [KappaLadder.popularAuxiliaryInput] using hparentAux
  refine ⟨parent, hparent, hsub, ?_⟩
  by_cases hhang : PopularAuxiliary.IsHangingPath Gamma parent
  · right
    have hle := L.canonicalErasedRoute_backwardLink_ownerStage_le_source
      hL Q pQ hpure l hl hldir parent hparent hhang hsub
    exact L.strictCollisionFree_equalSubwarp_backwardOwner_eq_targetComponent
      hL P p T l hl hldir parent hparent hhang hsub hle
  · left
    by_contra hnot
    exact hhang hnot

/-- Root the entry of the first self-owned backward link.  Earlier
backward links cannot be self-owned by `hfirst`, so the preceding theorem
forces their owners to be grounded; `hgrounded` supplies precisely those
earlier ambient anchors. -/
theorem strictCollisionFree_equalSubwarp_firstSelfOwnedEntry_rooted
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (p : WarpPath (L.strictCollisionFreeSubwarp hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P)))
    (hpure : (L.popularAuxiliaryInput hL.legal).IsTargetPure p.1)
    (T : L.EqualTargetComponent hL P p.1 p.2.1)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P)
      ⟨p.1, L.strictCollisionFreeSubwarp_paths_subset hL
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).links)
    (hldir : l.direction = .backward)
    (hfirst : ∀ (F : FiniteTrace Gamma.graph)
      (hroute : canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P)
        ⟨p.1, L.strictCollisionFreeSubwarp_paths_subset hL
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩ = .finite F)
      (bi li : Fin (F.lastIndex + 1)),
      F.link li = l → bi.1 < li.1 →
      (F.link bi).direction = .backward →
      ¬(F.link bi).path.IsSubpathOf T.component)
    {A : Set V} {E : Set (V × V)}
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
        (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P)
          ⟨p.1, L.strictCollisionFreeSubwarp_paths_subset hL
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).initial)
    (hforward : (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P)
      ⟨p.1, L.strictCollisionFreeSubwarp_paths_subset hL
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).directionEdges
          .forward ⊆ E)
    (hgrounded : ∀ (parent : Gamma.DPath), parent ∈ L.limitWarp →
      parent.initial ∈ Gamma.source →
      ∀ (b : Link Gamma.graph), b.path.IsSubpathOf parent →
        ∃ a ∈ A,
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
            a b.path.start) :
    ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a l.entry := by
  let Q := (L.popularAuxiliaryIndexed hL).equalSubwarp P
  let pQ : WarpPath Q :=
    ⟨p.1, L.strictCollisionFreeSubwarp_paths_subset hL Q p.2⟩
  apply canonicalErasedRoute_backwardLink_entry_rooted_of_priorBackward
    (L.popularAuxiliaryInput hL.legal) Q pQ l hl hldir
      hinitial hforward
  intro b hb hbdir _hbowner F hroute bi li hbi hli hlt
  obtain ⟨parent, hparent, hsub, hroot | hself⟩ :=
    L.strictCollisionFree_equalSubwarp_backwardLink_groundedOr_selfOwned
      hL P p hpure T b hb hbdir
  · exact hgrounded parent hparent hroot b hsub
  · exfalso
    apply hfirst F hroute bi li hli hlt
    · exact (congrArg (fun c : Link Gamma.graph ↦ c.direction) hbi).trans
        hbdir
    · rw [hbi]
      exact hself ▸ hsub

/-- The source-index set of all strict backward-owner collisions is
nonstationary. -/
theorem strictBackwardCollisionIndices_nonstationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target) :
    ¬ IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        (L.strictBackwardCollisionPaths hL P)
        (fun {_p} hp ↦ P.starts_in_source
          (L.strictBackwardCollisionPaths_subset hL P hp))) := by
  classical
  let J := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  let B := L.strictBackwardCollisionPaths hL P
  let hBsource : ∀ {p}, p ∈ B → p.start ∈ J.lambda.source :=
    fun {_p} hp ↦ P.starts_in_source
      (L.strictBackwardCollisionPaths_subset hL P hp)
  let BI : Set (Below kappa) :=
    Popular.initialIndicesOf U B hBsource
  intro hBI
  let chosenPath : (a : Below kappa) → a ∈ BI →
      FinitePath J.lambda.graph :=
    fun _a ha ↦ Classical.choose ha
  have chosenPath_mem (a : Below kappa) (ha : a ∈ BI) :
      chosenPath a ha ∈ B :=
    Classical.choose (Classical.choose_spec ha)
  have chosenPath_index (a : Below kappa) (ha : a ∈ BI) :
      U.f ⟨(chosenPath a ha).start,
        hBsource (chosenPath_mem a ha)⟩ = a :=
    Classical.choose_spec (Classical.choose_spec ha)
  let chosenWarpPath (a : Below kappa) (ha : a ∈ BI) : WarpPath P :=
    ⟨chosenPath a ha,
      L.strictBackwardCollisionPaths_subset hL P
        (chosenPath_mem a ha)⟩
  let chosenCollision (a : Below kappa) (ha : a ∈ BI) :
      L.StrictBackwardCollision hL P (chosenWarpPath a ha) :=
    by
      apply Classical.choice
      obtain ⟨hp, hc⟩ := chosenPath_mem a ha
      simpa only [chosenWarpPath] using hc
  have chosenCollision_stage_lt (a : Below kappa) (ha : a ∈ BI) :
      L.hangingComponentStage hL.legal
          (chosenCollision a ha).parent
          (chosenCollision a ha).parent_mem
          (chosenCollision a ha).parent_hanging < a := by
    have hindex :
        U.f ⟨(chosenWarpPath a ha).1.start,
          P.starts_in_source (chosenWarpPath a ha).2⟩ = a := by
      exact chosenPath_index a ha
    exact (chosenCollision a ha).stage_lt.trans_eq hindex
  let ownerIndex : Below kappa → Below kappa := fun a ↦
    if ha : a ∈ BI then
      L.hangingComponentStage hL.legal
        (chosenCollision a ha).parent
        (chosenCollision a ha).parent_mem
        (chosenCollision a ha).parent_hanging
    else a
  have hregressive : IsRegressiveOn BI ownerIndex := by
    intro a ha
    rw [show ownerIndex a =
        L.hangingComponentStage hL.legal
          (chosenCollision a ha).parent
          (chosenCollision a ha).parent_mem
          (chosenCollision a ha).parent_hanging by
      simp [ownerIndex, ha]]
    exact chosenCollision_stage_lt a ha
  obtain ⟨i, hi⟩ := pressingDown U.uncountable U.regular
    hBI hregressive
  obtain ⟨a, haBI, hai⟩ := hi.nonempty
  let d := chosenCollision a haBI
  have hdStage : L.hangingComponentStage hL.legal d.parent
      d.parent_mem d.parent_hanging = i := by
    have howner : ownerIndex a =
        L.hangingComponentStage hL.legal d.parent
          d.parent_mem d.parent_hanging := by
      have haBI' : a ∈ BI := haBI
      rw [show ownerIndex a = if ha : a ∈ BI then
          L.hangingComponentStage hL.legal
            (chosenCollision a ha).parent
            (chosenCollision a ha).parent_mem
            (chosenCollision a ha).parent_hanging else a by rfl]
      rw [dif_pos haBI']
    exact howner.symm.trans hai
  have hmeetingStationary : IsStationaryBelow kappa
      (Popular.initialIndicesOf U
        {p | p ∈ P.paths ∧
          (p.support ∩ PopularSwitching.ladderTrace J d.parent).Nonempty}
        (fun {_p} hp ↦ P.starts_in_source hp.1)) := by
    apply hi.mono
    rintro b ⟨hbBI, hbi⟩
    let e := chosenCollision b hbBI
    have heStage : L.hangingComponentStage hL.legal e.parent
        e.parent_mem e.parent_hanging = i := by
      have howner : ownerIndex b =
          L.hangingComponentStage hL.legal e.parent
            e.parent_mem e.parent_hanging := by
        have hbBI' : b ∈ BI := hbBI
        rw [show ownerIndex b = if hb : b ∈ BI then
            L.hangingComponentStage hL.legal
              (chosenCollision b hb).parent
              (chosenCollision b hb).parent_mem
              (chosenCollision b hb).parent_hanging else b by rfl]
        rw [dif_pos hbBI']
      exact howner.symm.trans hbi
    have hparent : e.parent = d.parent :=
      hL.legal.hangingComponent_eq_of_stage_eq
        e.parent_mem e.parent_hanging d.parent_mem d.parent_hanging
        (heStage.trans hdStage.symm)
    obtain ⟨y, hy⟩ :=
      _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        e.link.path e.link.path.start_mem_support e.link.nontrivial
    have hyRoute : (e.link.path.start, y) ∈
        (canonicalErasedRoute J P (chosenWarpPath b hbBI)).directionEdges
          .backward := by
      simp only [AltPath.directionEdges, Set.mem_iUnion]
      exact ⟨e.link, e.link_mem, e.link_backward, hy⟩
    have hgadget :
        (PopularAuxiliary.Input.LambdaVertex.edge e.link.path.start y : J.LV) ∈
          (chosenWarpPath b hbBI).1.support :=
      canonicalErasedRoute_backwardEdge_gadget_mem_support
        J P (chosenWarpPath b hbBI) hyRoute
    have hedgeParent : (e.link.path.start, y) ∈ d.parent.edgeSet := by
      rw [← hparent]
      exact e.link_subpath.2 hy
    have hmeet : ((chosenWarpPath b hbBI).1.support ∩
        PopularSwitching.ladderTrace J d.parent).Nonempty := by
      refine ⟨.edge e.link.path.start y, hgadget, ?_⟩
      exact Or.inr ⟨(e.link.path.start, y), hedgeParent, rfl⟩
    let hpMeet : (chosenWarpPath b hbBI).1 ∈
        {p | p ∈ P.paths ∧
          (p.support ∩ PopularSwitching.ladderTrace J d.parent).Nonempty} :=
      ⟨(chosenWarpPath b hbBI).2, hmeet⟩
    refine ⟨(chosenWarpPath b hbBI).1, hpMeet, ?_⟩
    have hs :
        (⟨(chosenWarpPath b hbBI).1.start,
          P.starts_in_source hpMeet.1⟩ : J.lambda.source) =
        ⟨(chosenWarpPath b hbBI).1.start,
          hBsource (chosenPath_mem b hbBI)⟩ := Subtype.ext rfl
    exact (congrArg U.f hs).trans (chosenPath_index b hbBI)
  exact (P.initialIndices_meeting_nonstationary U
    (PopularSwitching.ladderTrace_countable J d.parent))
      hmeetingStationary

/-- Deleting strict backward-owner collisions preserves stationarity. -/
theorem strictCollisionFreeSubwarp_initialIndices_isStationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hP : IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        P.paths P.starts_in_source)) :
    IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        (L.strictCollisionFreeSubwarp hL P).paths
        (L.strictCollisionFreeSubwarp hL P).starts_in_source) := by
  let U := L.popularAuxiliaryIndexed hL
  let B := L.strictBackwardCollisionPaths hL P
  let hBsource : ∀ {p}, p ∈ B →
      p.start ∈ (L.popularAuxiliaryInput hL.legal).lambda.source :=
    fun {_p} hp ↦ P.starts_in_source
      (L.strictBackwardCollisionPaths_subset hL P hp)
  let allIndices : Set (Below kappa) :=
    Popular.initialIndicesOf U P.paths P.starts_in_source
  let badIndices : Set (Below kappa) :=
    Popular.initialIndicesOf U B hBsource
  have hbad : ¬ IsStationaryBelow kappa badIndices := by
    exact L.strictBackwardCollisionIndices_nonstationary hL P
  have hdiff : IsStationaryBelow kappa (allIndices \ badIndices) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      U.regular U.uncountable hP hbad
  apply hdiff.mono
  rintro a ⟨⟨p, hpP, hpa⟩, haBad⟩
  have hpNotB : p ∉ B := by
    intro hpB
    apply haBad
    refine ⟨p, hpB, ?_⟩
    have hs :
        (⟨p.start, hBsource hpB⟩ :
          (L.popularAuxiliaryInput hL.legal).lambda.source) =
        ⟨p.start, P.starts_in_source hpP⟩ := Subtype.ext rfl
    exact (congrArg U.f hs).trans hpa
  let hpFree : p ∈ (L.strictCollisionFreeSubwarp hL P).paths :=
    ⟨hpP, hpNotB⟩
  refine ⟨p, hpFree, ?_⟩
  have hs :
      (⟨p.start,
        (L.strictCollisionFreeSubwarp hL P).starts_in_source hpFree⟩ :
          (L.popularAuxiliaryInput hL.legal).lambda.source) =
      ⟨p.start, P.starts_in_source hpP⟩ := Subtype.ext rfl
  exact (congrArg U.f hs).trans hpa

/-- The complete stationary selection needed by the diagonal equal-stage
closure.  `base` is the decoded-carrier-disjoint thinning; `routes` below
then removes its nonstationary strict-owner collisions. -/
structure StationaryDiagonalEqualSelection
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target) where
  base : Popular.XSWarp
    (L.popularAuxiliaryInput hL.legal).lambda
    (L.popularAuxiliaryInput hL.legal).lambda.target
  base_subset_equal :
    base.paths ⊆ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
  base_targetPure : ∀ p ∈ base.paths,
    (L.popularAuxiliaryInput hL.legal).IsTargetPure p
  base_decodedDisjoint : base.paths.PairwiseDisjoint
    (L.popularAuxiliaryInput hL.legal).decodedVertexCarrier
  routes_stationary : IsStationaryBelow kappa
    (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
      (L.strictCollisionFreeSubwarp hL
        ((L.popularAuxiliaryIndexed hL).equalSubwarp base)).paths
      (L.strictCollisionFreeSubwarp hL
        ((L.popularAuxiliaryIndexed hL).equalSubwarp base)).starts_in_source)

namespace StationaryDiagonalEqualSelection

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {P : Popular.XSWarp
    (L.popularAuxiliaryInput hL.legal).lambda
    (L.popularAuxiliaryInput hL.legal).lambda.target}

/-- The final stationary diagonal route family. -/
def routes (S : L.StationaryDiagonalEqualSelection hL P) :=
  L.strictCollisionFreeSubwarp hL
    ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)

theorem routes_subset_equalBase
    (S : L.StationaryDiagonalEqualSelection hL P) :
    S.routes.paths ⊆
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base).paths := by
  exact L.strictCollisionFreeSubwarp_paths_subset hL _

theorem routes_subset_base
    (S : L.StationaryDiagonalEqualSelection hL P) :
    S.routes.paths ⊆ S.base.paths := by
  exact S.routes_subset_equalBase.trans
    ((L.popularAuxiliaryIndexed hL).equalPaths_subset S.base)

theorem routes_subset_originalEqual
    (S : L.StationaryDiagonalEqualSelection hL P) :
    S.routes.paths ⊆
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths :=
  S.routes_subset_base.trans S.base_subset_equal

theorem routes_targetPure
    (S : L.StationaryDiagonalEqualSelection hL P) :
    ∀ p ∈ S.routes.paths,
      (L.popularAuxiliaryInput hL.legal).IsTargetPure p := by
  intro p hp
  exact S.base_targetPure p (S.routes_subset_base hp)

theorem routes_decodedDisjoint
    (S : L.StationaryDiagonalEqualSelection hL P) :
    S.routes.paths.PairwiseDisjoint
      (L.popularAuxiliaryInput hL.legal).decodedVertexCarrier := by
  intro p hp q hq hpq
  exact S.base_decodedDisjoint
    (S.routes_subset_base hp) (S.routes_subset_base hq) hpq

theorem routes_repairedEdges_biUnique
    (S : L.StationaryDiagonalEqualSelection hL P) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈
      canonicalErasedRepairedEdges
        (L.popularAuxiliaryInput hL.legal) S.routes) :=
  canonicalErasedRepairedEdges_biUnique
    (L.popularAuxiliaryInput hL.legal) S.routes
      S.routes_decodedDisjoint

theorem routes_repairedEdges_subset_adj
    (S : L.StationaryDiagonalEqualSelection hL P) :
    canonicalErasedRepairedEdges
      (L.popularAuxiliaryInput hL.legal) S.routes ⊆
        {e | Gamma.graph.Adj e.1 e.2} :=
  canonicalErasedRepairedEdges_subset_adj
    (L.popularAuxiliaryInput hL.legal) S.routes

theorem route_has_equalTargetComponent
    (S : L.StationaryDiagonalEqualSelection hL P)
    (p : WarpPath S.routes) :
    Nonempty (L.EqualTargetComponent hL S.base p.1
      (S.routes_subset_equalBase p.2)) :=
  L.exists_equalTargetComponent hL S.base p.1
    (S.routes_subset_equalBase p.2)

theorem route_has_no_strict_collision
    (S : L.StationaryDiagonalEqualSelection hL P)
    (p : WarpPath S.routes) :
    IsEmpty (L.StrictBackwardCollision hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨p.1, S.routes_subset_equalBase p.2⟩) :=
  L.strictCollisionFreeSubwarp_has_no_strict_collision hL _ p

end StationaryDiagonalEqualSelection

/-- Target-pure stationary equality always supplies the fully thinned
diagonal selection. -/
theorem exists_stationaryDiagonalEqualSelection
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hpure : ∀ p ∈ P.paths,
      (L.popularAuxiliaryInput hL.legal).IsTargetPure p)
    (hstat : IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    Nonempty (L.StationaryDiagonalEqualSelection hL P) := by
  obtain ⟨Q, hQsubset, hQpure, hQstationary, hQdisjoint⟩ :=
    L.exists_targetPure_stationary_decodedCarrierDisjoint_equalSubwarp
      hL P hpure hstat
  exact ⟨{
    base := Q
    base_subset_equal := hQsubset
    base_targetPure := hQpure
    base_decodedDisjoint := hQdisjoint
    routes_stationary :=
      L.strictCollisionFreeSubwarp_initialIndices_isStationary hL
        ((L.popularAuxiliaryIndexed hL).equalSubwarp Q) hQstationary }⟩

/-- A diagonal selection together with the prescribed untouched equal
route whose collision carrier is avoided by the whole selected base. -/
structure ReservedStationaryDiagonalEqualSelection
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    extends L.StationaryDiagonalEqualSelection hL P where
  reserved : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph
  reserved_mem_equal :
    reserved ∈ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
  base_avoids_reserved : ∀ p ∈ base.paths,
    Disjoint p.support
      (GroundingEqualActiveSelection.collisionCarrier
        (L.popularAuxiliaryInput hL.legal) reserved)

namespace ReservedStationaryDiagonalEqualSelection

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {P : Popular.XSWarp
    (L.popularAuxiliaryInput hL.legal).lambda
    (L.popularAuxiliaryInput hL.legal).lambda.target}

theorem routes_avoid_reserved
    (S : L.ReservedStationaryDiagonalEqualSelection hL P) :
    ∀ p ∈ S.routes.paths,
      Disjoint p.support
        (GroundingEqualActiveSelection.collisionCarrier
          (L.popularAuxiliaryInput hL.legal) S.reserved) := by
  intro p hp
  exact S.base_avoids_reserved p (S.routes_subset_base hp)

theorem reserved_start_mem_source
    (S : L.ReservedStationaryDiagonalEqualSelection hL P) :
    S.reserved.start ∈
      (L.popularAuxiliaryInput hL.legal).lambda.source :=
  ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
    S.reserved_mem_equal

theorem reservedGroundedParent_nonempty
    (S : L.ReservedStationaryDiagonalEqualSelection hL P) :
    Nonempty (L.ReservedGroundedParent hL S.reserved
      S.reserved_start_mem_source) :=
  L.reservedGroundedParent_nonempty hL S.reserved
    S.reserved_start_mem_source

theorem routes_decodedCarriers_disjoint_parent
    (S : L.ReservedStationaryDiagonalEqualSelection hL P)
    (R : L.ReservedGroundedParent hL S.reserved
      S.reserved_start_mem_source) :
    ∀ p ∈ S.routes.paths,
      Disjoint
        ((L.popularAuxiliaryInput hL.legal).decodedVertexCarrier p)
        R.parent.support :=
  R.decodedCarriers_disjoint S.routes S.routes_avoid_reserved

theorem routes_forwardEdges_endpoints_not_mem_parent
    (S : L.ReservedStationaryDiagonalEqualSelection hL P)
    (R : L.ReservedGroundedParent hL S.reserved
      S.reserved_start_mem_source)
    {e : V × V}
    (he : e ∈ canonicalErasedForwardEdges
      (L.popularAuxiliaryInput hL.legal) S.routes) :
    e.1 ∉ R.parent.support ∧ e.2 ∉ R.parent.support :=
  R.forwardEdges_endpoints_not_mem S.routes S.routes_avoid_reserved he

end ReservedStationaryDiagonalEqualSelection

/-- The reserved version of the complete diagonal selection, retaining the
unused-source collision avoidance needed by the final hindrance. -/
theorem exists_reservedStationaryDiagonalEqualSelection
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hpure : ∀ p ∈ P.paths,
      (L.popularAuxiliaryInput hL.legal).IsTargetPure p)
    (hstat : IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    Nonempty (L.ReservedStationaryDiagonalEqualSelection hL P) := by
  obtain ⟨q, hq, Q, hQsubset, hQpure, hQstationary,
      hQdisjoint, hQavoid⟩ :=
    L.exists_reserved_targetPure_stationary_equalSubwarp
      hL P hpure hstat
  exact ⟨{
    base := Q
    base_subset_equal := hQsubset
    base_targetPure := hQpure
    base_decodedDisjoint := hQdisjoint
    routes_stationary :=
      L.strictCollisionFreeSubwarp_initialIndices_isStationary hL
        ((L.popularAuxiliaryIndexed hL).equalSubwarp Q) hQstationary
    reserved := q
    reserved_mem_equal := hq
    base_avoids_reserved := hQavoid }⟩

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.strictBackwardCollisionIndices_nonstationary
#print axioms Erdos599.DWeb.KappaLadder.strictCollisionFreeSubwarp_initialIndices_isStationary
#print axioms Erdos599.DWeb.KappaLadder.strictCollisionFree_equalSubwarp_backwardOwner_eq_targetComponent
#print axioms Erdos599.DWeb.KappaLadder.strictCollisionFree_equalSubwarp_backwardLink_groundedOr_selfOwned
#print axioms Erdos599.DWeb.KappaLadder.strictCollisionFree_equalSubwarp_firstSelfOwnedEntry_rooted
#print axioms Erdos599.DWeb.KappaLadder.exists_stationaryDiagonalEqualSelection
#print axioms Erdos599.DWeb.KappaLadder.exists_reservedStationaryDiagonalEqualSelection
