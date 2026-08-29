/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualTargetComponent

/-!
# Stationary pruning of strict hanging collisions under split legality

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
structure SplitStrictBackwardCollision
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target)
    (p : WarpPath P) where
  link : Link Gamma.graph
  link_mem : link ∈ (canonicalErasedRoute
    (L.splitPopularAuxiliaryInput hL.legal) P p).links
  link_backward : link.direction = .backward
  parent : Gamma.DPath
  parent_mem : parent ∈ L.limitWarp
  parent_hanging : PopularAuxiliary.IsHangingPath Gamma parent
  link_subpath : link.path.IsSubpathOf parent
  stage_lt : L.splitHangingComponentStage hL.legal parent parent_mem
      parent_hanging <
    (L.splitPopularAuxiliaryIndexed hL).f
      ⟨p.1.start, P.starts_in_source p.2⟩

/-- Paths of an auxiliary warp carrying at least one strict backward-owner
collision. -/
def splitStrictBackwardCollisionPaths
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target) :
    Set (FinitePath (L.splitPopularAuxiliaryInput hL.legal).lambda.graph) :=
  {p | ∃ hp : p ∈ P.paths,
    Nonempty (L.SplitStrictBackwardCollision hL P ⟨p, hp⟩)}

theorem splitStrictBackwardCollisionPaths_subset
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target) :
    L.splitStrictBackwardCollisionPaths hL P ⊆ P.paths := by
  rintro p ⟨hp, _⟩
  exact hp

/-- The subwarp obtained by deleting every route carrying a strict
backward-owner collision. -/
def splitStrictCollisionFreeSubwarp
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target) :
    Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target where
  paths := P.paths \ L.splitStrictBackwardCollisionPaths hL P
  disjoint := by
    intro p hp q hq hpq
    exact P.disjoint hp.1 hq.1 hpq
  starts_in_source hp := P.starts_in_source hp.1
  ends_in_target hp := P.ends_in_target hp.1

@[simp] theorem mem_splitStrictCollisionFreeSubwarp_paths
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target)
    (p : FinitePath (L.splitPopularAuxiliaryInput hL.legal).lambda.graph) :
    p ∈ (L.splitStrictCollisionFreeSubwarp hL P).paths ↔
      p ∈ P.paths ∧ p ∉ L.splitStrictBackwardCollisionPaths hL P := by
  rfl

theorem splitStrictCollisionFreeSubwarp_paths_subset
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target) :
    (L.splitStrictCollisionFreeSubwarp hL P).paths ⊆ P.paths := by
  intro p hp
  exact hp.1

theorem splitStrictCollisionFreeSubwarp_has_no_strict_collision
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target)
    (p : WarpPath (L.splitStrictCollisionFreeSubwarp hL P)) :
    IsEmpty (L.SplitStrictBackwardCollision hL P
      ⟨p.1, (L.splitStrictCollisionFreeSubwarp_paths_subset hL P p.2)⟩) := by
  refine ⟨fun hc ↦ p.2.2 ?_⟩
  exact ⟨p.2.1, ⟨hc⟩⟩

/-- On the collision-free subwarp, the weak chronology bound for a hanging
backward owner is automatically an equality. -/
theorem splitStrictCollisionFreeSubwarp_backwardOwnerStage_eq_source
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target)
    (p : WarpPath (L.splitStrictCollisionFreeSubwarp hL P))
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute
      (L.splitPopularAuxiliaryInput hL.legal) P
      ⟨p.1, L.splitStrictCollisionFreeSubwarp_paths_subset hL P p.2⟩).links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma parent)
    (hsub : l.path.IsSubpathOf parent)
    (hle : L.splitHangingComponentStage hL.legal parent hparent hhang ≤
      (L.splitPopularAuxiliaryIndexed hL).f
        ⟨p.1.start, P.starts_in_source
          (L.splitStrictCollisionFreeSubwarp_paths_subset hL P p.2)⟩) :
    L.splitHangingComponentStage hL.legal parent hparent hhang =
      (L.splitPopularAuxiliaryIndexed hL).f
        ⟨p.1.start, P.starts_in_source
          (L.splitStrictCollisionFreeSubwarp_paths_subset hL P p.2)⟩ := by
  apply le_antisymm hle
  apply le_of_not_gt
  intro hlt
  have hempty :=
    L.splitStrictCollisionFreeSubwarp_has_no_strict_collision hL P p
  exact hempty.false {
    link := l
    link_mem := hl
    link_backward := hldir
    parent := parent
    parent_mem := hparent
    parent_hanging := hhang
    link_subpath := hsub
    stage_lt := hlt }

/-- For an equal-stage route surviving strict-collision pruning, every
hanging backward owner satisfying the chronology bound is the route's own
target-marker component.  Thus the equality case is genuinely diagonal,
not merely an equality of ordinal labels. -/
theorem splitStrictCollisionFree_equalSubwarp_backwardOwner_eq_targetComponent
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target)
    (p : WarpPath (L.splitStrictCollisionFreeSubwarp hL
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)))
    (T : L.SplitEqualTargetComponent hL P p.1 p.2.1)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute
      (L.splitPopularAuxiliaryInput hL.legal)
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)
      ⟨p.1, L.splitStrictCollisionFreeSubwarp_paths_subset hL
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma parent)
    (hsub : l.path.IsSubpathOf parent)
    (hle : L.splitHangingComponentStage hL.legal parent hparent hhang ≤
      (L.splitPopularAuxiliaryIndexed hL).f
        ⟨p.1.start,
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
            (L.splitStrictCollisionFreeSubwarp_paths_subset hL
              ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P) p.2)⟩) :
    parent = T.component := by
  have hparentSource :=
    L.splitStrictCollisionFreeSubwarp_backwardOwnerStage_eq_source hL
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P) p l hl hldir
      parent hparent hhang hsub hle
  have hsourceProof :
      (⟨p.1.start,
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
          (L.splitStrictCollisionFreeSubwarp_paths_subset hL
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P) p.2)⟩ :
          (L.splitPopularAuxiliaryInput hL.legal).lambda.source) =
      ⟨p.1.start,
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
          p.2.1⟩ := Subtype.ext rfl
  have hparentIndex :
      L.splitHangingComponentStage hL.legal parent hparent hhang =
        (L.splitPopularAuxiliaryIndexed hL).f
          ⟨p.1.start,
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
              p.2.1⟩ :=
    hparentSource.trans (congrArg (L.splitPopularAuxiliaryIndexed hL).f
      hsourceProof)
  have hcomponentIndex :
      L.splitHangingComponentStage hL.legal T.component
          T.component_essential.1 T.component_hanging =
        (L.splitPopularAuxiliaryIndexed hL).f
          ⟨p.1.start,
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
              p.2.1⟩ :=
    T.ownerStage_eq.trans T.sourceIndex_eq.symm
  exact hL.legal.hangingComponent_eq_of_splitStage_eq
    hparent hhang T.component_essential.1 T.component_hanging
    (hparentIndex.trans hcomponentIndex.symm)

/-- Every backward link of a target-pure equal route surviving the pruning
is owned either by an already grounded limiting component or by that same
route's target-marker component. -/
theorem splitStrictCollisionFree_equalSubwarp_backwardLink_groundedOr_selfOwned
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target)
    (p : WarpPath (L.splitStrictCollisionFreeSubwarp hL
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)))
    (hpure : (L.splitPopularAuxiliaryInput hL.legal).IsTargetPure p.1)
    (T : L.SplitEqualTargetComponent hL P p.1 p.2.1)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute
      (L.splitPopularAuxiliaryInput hL.legal)
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)
      ⟨p.1, L.splitStrictCollisionFreeSubwarp_paths_subset hL
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).links)
    (hldir : l.direction = .backward) :
    ∃ parent ∈ L.limitWarp, l.path.IsSubpathOf parent ∧
      (parent.initial ∈ Gamma.source ∨ parent = T.component) := by
  classical
  let Q := (L.splitPopularAuxiliaryIndexed hL).equalSubwarp P
  let pQ : WarpPath Q :=
    ⟨p.1, L.splitStrictCollisionFreeSubwarp_paths_subset hL Q p.2⟩
  let D := (L.splitPopularAuxiliaryInput hL.legal).decodeFinitePath pQ.1
    (Q.starts_in_source pQ.2) (Q.ends_in_target pQ.2)
  have hback : BackwardLinksOn
      (L.splitPopularAuxiliaryInput hL.legal).ladder.paths
      (canonicalErasedRoute (L.splitPopularAuxiliaryInput hL.legal) Q pQ) := by
    change BackwardLinksOn
      (L.splitPopularAuxiliaryInput hL.legal).ladder.paths
      D.erasedCompression.path
    apply D.runs.erasedSignedRoute.compressionOfValid_backwardLinksOn
      (fun {_s} hs ↦ D.valid _
        (D.runs.erasedSignedRoute.steps_sublist.subset hs))
      (L.splitPopularAuxiliaryInput hL.legal).ladder.disjoint
    intro s hs hdir
    simpa [PopularAuxiliary.Input.familyEdges, Alternating.familyEdges] using
      D.backward_on_ladder s
        (D.runs.erasedSignedRoute.steps_sublist.subset hs) hdir
  obtain ⟨parent, hparentAux, hsub⟩ := hback l hl hldir
  have hparent : parent ∈ L.limitWarp := by
    simpa only [KappaLadder.splitPopularAuxiliaryInput] using hparentAux
  refine ⟨parent, hparent, hsub, ?_⟩
  by_cases hhang : PopularAuxiliary.IsHangingPath Gamma parent
  · right
    have hle := L.splitCanonicalErasedRoute_backwardLink_ownerStage_le_source
      hL Q pQ hpure l hl hldir parent hparent hhang hsub
    exact L.splitStrictCollisionFree_equalSubwarp_backwardOwner_eq_targetComponent
      hL P p T l hl hldir parent hparent hhang hsub hle
  · left
    by_contra hnot
    exact hhang hnot

/-- The source-index set of all strict backward-owner collisions is
nonstationary. -/
theorem splitStrictBackwardCollisionIndices_nonstationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target) :
    ¬ IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
        (L.splitStrictBackwardCollisionPaths hL P)
        (fun {_p} hp ↦ P.starts_in_source
          (L.splitStrictBackwardCollisionPaths_subset hL P hp))) := by
  classical
  let J := L.splitPopularAuxiliaryInput hL.legal
  let U := L.splitPopularAuxiliaryIndexed hL
  let B := L.splitStrictBackwardCollisionPaths hL P
  let hBsource : ∀ {p}, p ∈ B → p.start ∈ J.lambda.source :=
    fun {_p} hp ↦ P.starts_in_source
      (L.splitStrictBackwardCollisionPaths_subset hL P hp)
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
      L.splitStrictBackwardCollisionPaths_subset hL P
        (chosenPath_mem a ha)⟩
  let chosenCollision (a : Below kappa) (ha : a ∈ BI) :
      L.SplitStrictBackwardCollision hL P (chosenWarpPath a ha) :=
    by
      apply Classical.choice
      obtain ⟨hp, hc⟩ := chosenPath_mem a ha
      simpa only [chosenWarpPath] using hc
  have chosenCollision_stage_lt (a : Below kappa) (ha : a ∈ BI) :
      L.splitHangingComponentStage hL.legal
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
      L.splitHangingComponentStage hL.legal
        (chosenCollision a ha).parent
        (chosenCollision a ha).parent_mem
        (chosenCollision a ha).parent_hanging
    else a
  have hregressive : IsRegressiveOn BI ownerIndex := by
    intro a ha
    rw [show ownerIndex a =
        L.splitHangingComponentStage hL.legal
          (chosenCollision a ha).parent
          (chosenCollision a ha).parent_mem
          (chosenCollision a ha).parent_hanging by
      simp [ownerIndex, ha]]
    exact chosenCollision_stage_lt a ha
  obtain ⟨i, hi⟩ := pressingDown U.uncountable U.regular
    hBI hregressive
  obtain ⟨a, haBI, hai⟩ := hi.nonempty
  let d := chosenCollision a haBI
  have hdStage : L.splitHangingComponentStage hL.legal d.parent
      d.parent_mem d.parent_hanging = i := by
    have howner : ownerIndex a =
        L.splitHangingComponentStage hL.legal d.parent
          d.parent_mem d.parent_hanging := by
      have haBI' : a ∈ BI := haBI
      rw [show ownerIndex a = if ha : a ∈ BI then
          L.splitHangingComponentStage hL.legal
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
    have heStage : L.splitHangingComponentStage hL.legal e.parent
        e.parent_mem e.parent_hanging = i := by
      have howner : ownerIndex b =
          L.splitHangingComponentStage hL.legal e.parent
            e.parent_mem e.parent_hanging := by
        have hbBI' : b ∈ BI := hbBI
        rw [show ownerIndex b = if hb : b ∈ BI then
            L.splitHangingComponentStage hL.legal
              (chosenCollision b hb).parent
              (chosenCollision b hb).parent_mem
              (chosenCollision b hb).parent_hanging else b by rfl]
        rw [dif_pos hbBI']
      exact howner.symm.trans hbi
    have hparent : e.parent = d.parent :=
      hL.legal.hangingComponent_eq_of_splitStage_eq
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
      L.splitCanonicalErasedRoute_backwardEdge_gadget_mem_support
        hL P (chosenWarpPath b hbBI) hyRoute
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
theorem splitStrictCollisionFreeSubwarp_initialIndices_isStationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target)
    (hP : IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
        P.paths P.starts_in_source)) :
    IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
        (L.splitStrictCollisionFreeSubwarp hL P).paths
        (L.splitStrictCollisionFreeSubwarp hL P).starts_in_source) := by
  let U := L.splitPopularAuxiliaryIndexed hL
  let B := L.splitStrictBackwardCollisionPaths hL P
  let hBsource : ∀ {p}, p ∈ B →
      p.start ∈ (L.splitPopularAuxiliaryInput hL.legal).lambda.source :=
    fun {_p} hp ↦ P.starts_in_source
      (L.splitStrictBackwardCollisionPaths_subset hL P hp)
  let allIndices : Set (Below kappa) :=
    Popular.initialIndicesOf U P.paths P.starts_in_source
  let badIndices : Set (Below kappa) :=
    Popular.initialIndicesOf U B hBsource
  have hbad : ¬ IsStationaryBelow kappa badIndices := by
    exact L.splitStrictBackwardCollisionIndices_nonstationary hL P
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
          (L.splitPopularAuxiliaryInput hL.legal).lambda.source) =
        ⟨p.start, P.starts_in_source hpP⟩ := Subtype.ext rfl
    exact (congrArg U.f hs).trans hpa
  let hpFree : p ∈ (L.splitStrictCollisionFreeSubwarp hL P).paths :=
    ⟨hpP, hpNotB⟩
  refine ⟨p, hpFree, ?_⟩
  have hs :
      (⟨p.start,
        (L.splitStrictCollisionFreeSubwarp hL P).starts_in_source hpFree⟩ :
          (L.splitPopularAuxiliaryInput hL.legal).lambda.source) =
      ⟨p.start, P.starts_in_source hpP⟩ := Subtype.ext rfl
  exact (congrArg U.f hs).trans hpa


end KappaLadder
end DWeb
end Erdos599
