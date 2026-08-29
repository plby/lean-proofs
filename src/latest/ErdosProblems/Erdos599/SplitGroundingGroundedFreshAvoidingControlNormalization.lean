/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingActiveNormalization
import ErdosProblems.Erdos599.GroundingInactiveControlRootTransfer

/-!
# Normalization for every fresh-avoiding control

An inactive control is met, in path order, by a retained forward vertex of
an earlier active request.  If that contact is rooted, a last deleted head
on the finite ambient segment to the inactive control embeds in the same
well-founded owner recursion.  Thus no blanket segment-survival premise is
used.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation GroundingErasedForwardConflict

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev FreshControlInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev FreshControlIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev FreshControlControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev FreshControlRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev FreshControlEdges :=
  L.splitGroundedFreshAvoidingCanonicalEdges hL hground hnotFresh S

private abbrev FreshControlSources :=
  Gamma.source \ {
    (FreshControlRecord (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)).record.initial}

/-- A retained forward point of an active request is rooted or reduces to a
normalized selected-owner failure. -/
theorem splitGroundedFreshAvoiding_activeForwardVertex_rooted_or_normalized
    (c : ActiveControlRequestAt
      (FreshControlIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshControlControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    {x : V}
    (hx : x ∈ (selectedErasedCompression
      (FreshControlIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshControlControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (chosenRequest c.1)).path.directionVertices .forward) :
    (∃ a ∈ FreshControlSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ FreshControlEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a x) ∨
      L.SplitGroundedFreshAvoidingBackwardNormalizedOutcome
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) := by
  let A := FreshControlSources (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let E := FreshControlEdges (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  by_cases hxRoot : ∃ a ∈ A,
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a x
  · exact Or.inl hxRoot
  · right
    by_cases hinitial : ∃ a ∈ A,
        Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a
          (selectedRequestTrace
            (FreshControlIndexed (L := L) (hL := hL) (hground := hground)) S
            (FreshControlControls (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S))
            (chosenRequest c.1)).initial
    · have hbackwardNot : ¬ ∀ (l : Link Gamma.graph),
          l ∈ (selectedErasedCompression
            (FreshControlIndexed (L := L) (hL := hL) (hground := hground)) S
            (FreshControlControls (L := L) (hL := hL)
              (hground := hground) (hnotFresh := hnotFresh) (S := S))
            (chosenRequest c.1)).path.links →
          l.direction = .backward →
          ∀ parent ∈ (FreshControlInput (L := L) (hL := hL)).ladder.paths,
            l.path.IsSubpathOf parent →
            ∃ a ∈ A, Relation.ReflTransGen
              (fun u v ↦ (u, v) ∈ E) a l.path.start := by
        intro hbackward
        apply hxRoot
        exact activeRequestAt_empty_forwardVertex_rooted_of_anchor_reachability
          (FreshControlIndexed (L := L) (hL := hL) (hground := hground)) S
          (FreshControlControls (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) c hinitial hbackward hx
      push_neg at hbackwardNot
      obtain ⟨l, hl, hldir, parent, hparent, hsub, hstartNot⟩ :=
        hbackwardNot
      have hparentLimit : parent ∈ L.limitWarp := by
        simpa only [splitGroundedPopularAuxiliaryInput, limitWarp]
          using hparent
      have hstartNot' : ¬ ∃ a ∈ A,
          Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E)
            a l.path.start := by
        rintro ⟨a, ha, hareach⟩
        exact hstartNot a ha hareach
      let data := Classical.choice
        (L.exists_splitGroundedFreshAvoidingBackwardDeletedData
          (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) (chosenRequest c.1) l hl hldir parent
          hparentLimit hsub hstartNot')
      exact (data.toRootState c l hl hldir parent hsub).normalizeBackward
    · let data := Classical.choice
        (L.exists_splitGroundedFreshAvoidingInitialDeletedData
          (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) (chosenRequest c.1) hinitial)
      exact (data.toRootState c).normalizeBackward

private theorem exists_unrootedLastDeletedHead_freshControl
    {E : Set (V × V)} {A : Set V}
    (p : FinitePath Gamma.graph)
    (hstart : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.start)
    (hfinish : ¬ ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.finish) :
    ∃ D : LastDeletedHead p E,
      ¬ ∃ a ∈ A,
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a D.head := by
  have hdeleted : ∃ e ∈ p.edgeSet, e ∉ E := by
    by_contra hnone
    apply hfinish
    obtain ⟨a, ha, hastart⟩ := hstart
    refine ⟨a, ha, hastart.trans ?_⟩
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ p.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E)
    · intro x y hxy
      by_contra hxyE
      exact hnone ⟨(x, y), hxy, hxyE⟩
    · exact Alternating.Walk.reflTransGen_edgeSet p.walk
  let D := (exists_lastDeletedHead p hdeleted).some
  refine ⟨D, ?_⟩
  rintro ⟨a, ha, haD⟩
  apply hfinish
  refine ⟨a, ha, haD.trans ?_⟩
  have hsuffix : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) D.suffix.start D.suffix.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ D.suffix.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E)
    · intro x y hxy
      exact D.suffix_edgeSet_subset hxy
    · exact Alternating.Walk.reflTransGen_edgeSet D.suffix.walk
  exact D.suffix_finish ▸ (D.suffix_start ▸ hsuffix)

private theorem finiteSegment_support_subset_parent
    (Y : Gamma.DPath) (p : FinitePath Gamma.graph)
    (hfinish : p.finish ∈ Y.support) (hedges : p.edgeSet ⊆ Y.edgeSet) :
    p.support ⊆ Y.support := by
  intro z hz
  by_cases hzFinish : z = p.finish
  · simpa only [hzFinish] using hfinish
  · obtain ⟨y, hzy⟩ :=
      p.walk.exists_outgoing_edge_of_mem_of_ne_finish hz hzFinish
    exact (Y.edgeSet_subset_support_prod (hedges hzy)).1

/-- Every control, active or inactive, is rooted in the canonical
fresh-avoiding pre-stopped relation or yields a normalized concrete leaf. -/
theorem splitGroundedFreshAvoiding_control_rooted_or_normalized
    (c : ControlRequest
      (FreshControlInput (L := L) (hL := hL)) S.cut) :
    (∃ a ∈ FreshControlSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ FreshControlEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a c.1) ∨
      L.SplitGroundedFreshAvoidingBackwardNormalizedOutcome
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) := by
  let U := FreshControlIndexed (L := L) (hL := hL) (hground := hground)
  let K := FreshControlControls (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let A := FreshControlSources (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let E := FreshControlEdges (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  by_cases hc : IsActiveControlAt U S K ∅ c
  · exact L.splitGroundedFreshAvoiding_activeControl_rooted_or_normalized
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) ⟨c, hc⟩
  · obtain ⟨d, _hdc, Y, hY, hcY, x, hx, hxY, hxc⟩ :=
      exists_active_absorberAt_of_not_active U S K ∅ c hc
    have hxForward : x ∈ (selectedErasedCompression U S K
        (chosenRequest d.1)).path.directionVertices .forward := by
      simpa only [retainedForwardVerticesAt_empty] using hx
    rcases L.splitGroundedFreshAvoiding_activeForwardVertex_rooted_or_normalized
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
        (S := S) d hxForward with hxRoot | houtcome
    · by_cases hcRoot : ∃ a ∈ A,
          Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a c.1
      · exact Or.inl hcRoot
      · right
        have hxcNe : x ≠ c.1 := by
          intro hEq
          apply hcRoot
          simpa only [hEq] using hxRoot
        obtain ⟨p, hpStart, hpFinish, hpY⟩ :=
          GroundingCutDecoder.exists_forward_segment_of_before ⟨hxc, hxcNe⟩
        have hpStartRoot : ∃ a ∈ A,
            Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a p.start := by
          simpa only [hpStart] using hxRoot
        have hpFinishNot : ¬ ∃ a ∈ A,
            Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a p.finish := by
          simpa only [hpFinish] using hcRoot
        obtain ⟨D, hDnot⟩ :=
          exists_unrootedLastDeletedHead_freshControl p hpStartRoot hpFinishNot
        have hYLadder : Y ∈
            (FreshControlInput (L := L) (hL := hL)).ladder.paths :=
          GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
            (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL) _ hY
        have hpFamily : p.edgeSet ⊆
            (FreshControlInput (L := L) (hL := hL)).familyEdges := by
          intro e he
          exact ⟨Y, hYLadder, hpY he⟩
        have hclass := D.exists_classified_deletedIncomingAt_split K
          (∅ : Set V) hpFamily
        have hclass' :
            (∃ u, (u, D.head) ∈ p.edgeSet ∧
              (u, D.head) ∈ GroundingCut.CE
                (FreshControlInput (L := L) (hL := hL)) S.cut) ∨
            (∃ u, (u, D.head) ∈ p.edgeSet ∧
              (u, D.head) ∈ erasedSelectedDirectionEdgesAt U S K ∅
                .backward) ∨
            (∃ u, (u, D.head) ∈ p.edgeSet ∧
              (u, D.head) ∈ forwardConflictCutEdgesAt U S K ∅) := by
          rcases hclass with hCE | hbackward | hconflict |
              ⟨u, _huParent, _huResidual, huEmpty⟩
          · exact Or.inl hCE
          · exact Or.inr (Or.inl hbackward)
          · exact Or.inr (Or.inr hconflict)
          · exact False.elim (by simpa using huEmpty)
        let state : L.SplitGroundedFreshAvoidingRootState
            (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) := {
          control := d
          parent := Y
          parent_exposed := hY
          rootPath := p
          rootPath_support := finiteSegment_support_subset_parent
            Y p (by simpa only [hpFinish] using hcY) hpY
          rootPath_edges := hpY
          deleted := D
          deleted_head_not_rooted := hDnot
          owner := L.splitGroundedFreshAvoiding_deletedOwnerOutcome
            d Y hY hpY D hclass' }
        exact state.normalizeBackward
    · exact Or.inr houtcome

/-- Pointwise normalization assembled over the complete finite/control
boundary family: either every old request control is rooted, or one concrete
normalized leaf is exposed. -/
theorem splitGroundedFreshAvoiding_controls_rooted_or_normalized :
    (∀ c : ControlRequest
        (FreshControlInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ FreshControlSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈ FreshControlEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a c.1) ∨
      L.SplitGroundedFreshAvoidingBackwardNormalizedOutcome
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) := by
  classical
  by_cases hall : ∀ c : ControlRequest
      (FreshControlInput (L := L) (hL := hL)) S.cut,
    ∃ a ∈ FreshControlSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ FreshControlEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a c.1
  · exact Or.inl hall
  · right
    push_neg at hall
    obtain ⟨c, hc⟩ := hall
    rcases L.splitGroundedFreshAvoiding_control_rooted_or_normalized
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
        (S := S) c with hroot | houtcome
    · obtain ⟨a, ha, hareach⟩ := hroot
      exact False.elim (hc a ha hareach)
    · exact houtcome

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoiding_control_rooted_or_normalized
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoiding_controls_rooted_or_normalized
