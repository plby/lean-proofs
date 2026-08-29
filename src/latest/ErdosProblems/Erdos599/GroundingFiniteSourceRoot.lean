/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAssertion822UnusedRecord
import ErdosProblems.Erdos599.AlternatingMacroChain

/-!
# Genuine roots represented by finite auxiliary sources

A finite source of the Section 8 auxiliary web is the terminal of a grounded
finite limiting-ladder record.  Thus its canonical parent automatically
supplies an original source root, exactly as an infinite proxy represents a
grounded recorded ray.

The final theorem appends the root exclusion furnished by the unused grounded
record.  It is the source-cut analogue of the selected-request provenance
theorem in `GroundingAssertion822UnusedRecord`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb

open Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- The head of every edge of a walk occurs after its initial support
vertex.  This elementary order fact is what makes a last deleted head leave
an entirely surviving suffix. -/
theorem walk_edge_head_mem_support_tail
    {x y : V} (w : _root_.Erdos599.DirectedPath.Walk Gamma.graph x y)
    {e : V × V} (he : e ∈ w.edgeSet) :
    e.2 ∈ w.support.tail := by
  induction w with
  | nil => simp at he
  | @cons x z y hxz w ih =>
      simp only [_root_.Erdos599.DirectedPath.Walk.edgeSet_cons,
        Set.mem_union, Set.mem_singleton_iff] at he
      simp only [_root_.Erdos599.DirectedPath.Walk.support_cons,
        List.tail_cons]
      rcases he with rfl | he
      · simpa only [w.head_support] using List.head_mem w.support_ne_nil
      · exact List.mem_of_mem_tail (ih he)

/-- A last deleted head on a finite path, bundled with the surviving suffix
which follows it.  This is an order-theoretic object; it makes no assumption
about why the relation deleted the incoming edge. -/
structure LastDeletedHead
    (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph)
    (E : Set (V × V)) where
  head : V
  suffix : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph
  suffix_start : suffix.start = head
  suffix_finish : suffix.finish = p.finish
  suffix_support_suffix : suffix.walk.support <:+ p.walk.support
  suffix_support_subset : suffix.support ⊆ p.support
  suffix_parent_edges_subset : suffix.edgeSet ⊆ p.edgeSet
  deleted_incoming : ∃ u, (u, head) ∈ p.edgeSet ∧ (u, head) ∉ E
  suffix_edgeSet_subset : suffix.edgeSet ⊆ E

/-- Every finite path containing a deleted edge has a last deleted head;
all edges after that head survive. -/
theorem exists_lastDeletedHead
    {E : Set (V × V)}
    (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph)
    (hdeleted : ∃ e ∈ p.edgeSet, e ∉ E) :
    Nonempty (LastDeletedHead p E) := by
  let D : Set V := {v | ∃ u, (u, v) ∈ p.edgeSet ∧ (u, v) ∉ E}
  obtain ⟨e, hep, heE⟩ := hdeleted
  have hmeet : p.walk.Meets D := by
    refine ⟨e.2, (p.edgeSet_subset_support_prod hep).2, ?_⟩
    exact ⟨e.1, hep, heE⟩
  let q := p.lastHit D hmeet
  have hqStart : q.start ∈ D := p.lastHit_start_mem D hmeet
  have hqEdges : q.edgeSet ⊆ E := by
    intro e heq
    by_contra heE
    have heParent : e ∈ p.edgeSet :=
      p.lastHit_edgeSet_subset D hmeet heq
    have heHeadD : e.2 ∈ D := ⟨e.1, heParent, heE⟩
    exact p.lastHit_no_mem_after D hmeet
      (walk_edge_head_mem_support_tail q.walk heq) heHeadD
  exact ⟨{
    head := q.start
    suffix := q
    suffix_start := rfl
    suffix_finish := rfl
    suffix_support_suffix := (p.walk.lastHit D hmeet).support_suffix
    suffix_support_subset := p.lastHit_support_subset D hmeet
    suffix_parent_edges_subset := p.lastHit_edgeSet_subset D hmeet
    deleted_incoming := hqStart
    suffix_edgeSet_subset := hqEdges }⟩

namespace LastDeletedHead

/-- The head of the surviving suffix is an actual vertex of the finite
parent path. -/
theorem head_mem_parent
    {E : Set (V × V)} {p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph}
    (D : LastDeletedHead p E) : D.head ∈ p.support := by
  obtain ⟨u, hu, _⟩ := D.deleted_incoming
  exact (p.edgeSet_subset_support_prod hu).2

/-- The suffix bundled by `LastDeletedHead` is the canonical ordered suffix
of its parent beginning at the deleted head.  In particular, its support is
not merely a subset of the parent support: it contains every later parent
vertex. -/
theorem suffix_support_eq_suffixFrom
    {E : Set (V × V)} {p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph}
    (D : LastDeletedHead p E) :
    D.suffix.walk.support =
      (p.suffixFrom D.head D.head_mem_parent).walk.support := by
  have hcanonical :
      (p.suffixFrom D.head D.head_mem_parent).walk.support <:+
        p.walk.support :=
    (p.walk.lastHit ({D.head} : Set V)
      ⟨D.head, D.head_mem_parent, Set.mem_singleton D.head⟩).support_suffix
  rcases List.suffix_total D.suffix_support_suffix hcanonical with h | h
  · apply List.Nodup.eq_of_head_mem_of_suffix
      (hne := (p.suffixFrom D.head D.head_mem_parent).walk.support_ne_nil) h
    · rw [(p.suffixFrom D.head D.head_mem_parent).walk.head_support,
        p.suffixFrom_start]
      rw [← D.suffix_start]
      exact D.suffix.start_mem_support
    · exact hcanonical.nodup p.isPath
  · exact (List.Nodup.eq_of_head_mem_of_suffix
      (hne := D.suffix.walk.support_ne_nil) h
      (by
        rw [D.suffix.walk.head_support, D.suffix_start]
        have hh := List.head_mem
          (p.suffixFrom D.head D.head_mem_parent).walk.support_ne_nil
        rw [(p.suffixFrom D.head D.head_mem_parent).walk.head_support] at hh
        simpa only [DirectedPath.FinitePath.suffixFrom_start] using hh)
      (D.suffix_support_suffix.nodup p.isPath)).symm

end LastDeletedHead

/-- Reach the end of a finite path by restarting only once, at its last
deleted head.  Unlike `exists_root_reaching_finish_of_deleted_heads_reachable`,
this requires no witnesses for earlier deleted edges. -/
theorem exists_root_reaching_finish_of_lastDeletedHead
    {E : Set (V × V)} {A : Set V}
    (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph)
    (hstart : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.start)
    (hrepair : ∀ D : LastDeletedHead p E,
      ∃ a ∈ A,
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a D.head) :
    ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.finish := by
  by_cases hdeleted : ∃ e ∈ p.edgeSet, e ∉ E
  · let D := Classical.choice (exists_lastDeletedHead p hdeleted)
    obtain ⟨a, ha, haD⟩ := hrepair D
    have hsuffix : Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ E) D.suffix.start D.suffix.finish := by
      exact Relation.ReflTransGen.mono
        (r := fun x y ↦ (x, y) ∈ D.suffix.edgeSet)
        (p := fun x y ↦ (x, y) ∈ E)
        (by
          intro x y hxy
          exact D.suffix_edgeSet_subset hxy)
        D.suffix.start D.suffix.finish
        (_root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet D.suffix.walk)
    exact ⟨a, ha, D.suffix_finish ▸
      haD.trans (D.suffix_start ▸ hsuffix)⟩
  · obtain ⟨a, ha, hap⟩ := hstart
    have hpEdges : p.edgeSet ⊆ E := by
      intro e he
      by_contra heE
      exact hdeleted ⟨e, he, heE⟩
    have hpReach : Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ E) p.start p.finish := by
      exact Relation.ReflTransGen.mono
        (r := fun x y ↦ (x, y) ∈ p.edgeSet)
        (p := fun x y ↦ (x, y) ∈ E)
        (by
          intro x y hxy
          exact hpEdges hxy)
        p.start p.finish
        (_root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet p.walk)
    exact ⟨a, ha, hap.trans hpReach⟩

/-- Exact reason a ladder-family edge can be absent from the literal
switched relation.  It is either represented by the auxiliary cut, used by
a selected route in the backward direction, or removed to resolve a
forward-connector conflict, or is the residual continuation leaving an old
request endpoint. -/
theorem familyEdge_deleted_classification
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    {e : V × V} (heFamily : e ∈ J.familyEdges)
    (heDeleted : e ∉
      GroundingErasedDecode.erasedSelectedSwitchedEdges U S K) :
    e ∈ GroundingCut.CE J S.cut ∨
      e ∈ GroundingErasedDecode.erasedSelectedDirectionEdges U S K
        .backward ∨
      e ∈ GroundingErasedDecode.forwardConflictCutEdges U S K ∨
      e ∈ GroundingErasedDecode.boundaryOutgoingCutEdges U S := by
  by_cases heCut : e ∈ GroundingCut.CE J S.cut
  · exact Or.inl heCut
  · have heResidual : e ∈
        GroundingErasedDecode.residualLadderEdges U S :=
      ⟨heFamily, heCut⟩
    have heToggle : e ∈
        GroundingErasedDecode.erasedSelectedToggleEdges U S K := by
      by_contra heNotToggle
      exact heDeleted (Or.inl ⟨heResidual, heNotToggle⟩)
    rcases heToggle with heBackward | heConflict | heOldExit
    · exact Or.inr (Or.inl heBackward)
    · exact Or.inr (Or.inr (Or.inl heConflict))
    · exact Or.inr (Or.inr (Or.inr heOldExit))

/-- Classify the incoming edge at a last deleted head.  This packages the
generic last-suffix construction with the exact four ways in which the
literal simultaneous switch can delete a ladder-family edge. -/
theorem LastDeletedHead.exists_classified_deletedIncoming
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    {p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph}
    (hpFamily : p.edgeSet ⊆ J.familyEdges)
    (D : LastDeletedHead p
      (GroundingErasedDecode.erasedSelectedSwitchedEdges U S K)) :
    ∃ u, (u, D.head) ∈ p.edgeSet ∧
      ((u, D.head) ∈ GroundingCut.CE J S.cut ∨
        (u, D.head) ∈
          GroundingErasedDecode.erasedSelectedDirectionEdges U S K
            .backward ∨
        (u, D.head) ∈
          GroundingErasedDecode.forwardConflictCutEdges U S K ∨
        (u, D.head) ∈
          GroundingErasedDecode.boundaryOutgoingCutEdges U S) := by
  obtain ⟨u, huParent, huDeleted⟩ := D.deleted_incoming
  exact ⟨u, huParent,
    familyEdge_deleted_classification K (hpFamily huParent) huDeleted⟩

/-- The same classification with the boundary-departure branch unfolded.
In that final branch the deleted edge is precisely a residual continuation
`u → D.head` whose tail lies in the current stopping boundary. -/
theorem LastDeletedHead.exists_classified_deletedIncoming_split
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    {p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph}
    (hpFamily : p.edgeSet ⊆ J.familyEdges)
    (D : LastDeletedHead p
      (GroundingErasedDecode.erasedSelectedSwitchedEdges U S K)) :
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈ GroundingCut.CE J S.cut) ∨
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.erasedSelectedDirectionEdges U S K
          .backward) ∨
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.forwardConflictCutEdges U S K) ∨
    (∃ u : V,
      (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.residualLadderEdges U S ∧
      u ∈ GroundingCut.BB J S.cut) := by
  obtain ⟨u, huParent, huCut | huBackward | huConflict | huOld⟩ :=
    D.exists_classified_deletedIncoming K hpFamily
  · exact Or.inl ⟨u, huParent, huCut⟩
  · exact Or.inr (Or.inl ⟨u, huParent, huBackward⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨u, huParent, huConflict⟩))
  · obtain ⟨huResidual, huBoundary⟩ := huOld
    exact Or.inr (Or.inr (Or.inr
      ⟨u, huParent, huResidual, huBoundary⟩))

/-- Concrete recorded-parent specialization of the split classification.
The chosen-stage equation puts the finite parent in the limiting ladder,
so every one of its edges is a `familyEdges` edge. -/
theorem classified_lastDeletedHead_of_recorded_finiteParent
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {a : Ladder.Stage kappa}
    {p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph}
    (hchosen : L.chosen a = some (.inl p : Gamma.DPath))
    (D : LastDeletedHead p
      (GroundingErasedDecode.erasedSelectedSwitchedEdges
        (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S))) :
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈ GroundingCut.CE
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.erasedSelectedDirectionEdges
          (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S) .backward) ∨
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.forwardConflictCutEdges
          (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S)) ∨
    (∃ u : V,
      (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.residualLadderEdges
          (L.popularAuxiliaryIndexed hL) S ∧
      u ∈ GroundingCut.BB
        (L.popularAuxiliaryInput hL.legal) S.cut) := by
  have hpLimit : (.inl p : Gamma.DPath) ∈ L.limitWarp :=
    (L.recorded_mem_limitWarp_inessential_sourceGeometry
      hL.legal hchosen).1
  have hpFamily : p.edgeSet ⊆
      (L.popularAuxiliaryInput hL.legal).familyEdges := by
    intro e he
    exact ⟨(.inl p : Gamma.DPath), hpLimit, he⟩
  exact D.exists_classified_deletedIncoming_split
    (L.groundedConcreteControls hL S) hpFamily

/-- Scan a finite directed path through a repaired relation.  A surviving
edge extends the current rooted chain; at a deleted edge it is enough to
restart from any allowed root which reaches the head of that edge.  This is
the exact finite prefix/suffix reduction needed when a switched relation
cuts several edges of one grounded finite parent. -/
theorem exists_root_reaching_finish_of_deleted_heads_reachable
    {E : Set (V × V)} {A : Set V}
    (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph)
    (hstart : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.start)
    (hrepair : ∀ e ∈ p.edgeSet, e ∉ E →
      ∃ a ∈ A,
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a e.2) :
    ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.finish := by
  let step : ∀ {x y : V}, (w : _root_.Erdos599.DirectedPath.Walk
      Gamma.graph x y) →
      (∃ a ∈ A,
        Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a x) →
      (∀ e ∈ w.edgeSet, e ∉ E →
        ∃ a ∈ A,
          Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a e.2) →
      ∃ a ∈ A,
        Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a y := by
    intro x y w
    induction w with
    | nil =>
        intro hx _hrepair
        exact hx
    | @cons x z y hxz w ih =>
        intro hx hrepair
        have hz : ∃ a ∈ A,
            Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a z := by
          by_cases he : (x, z) ∈ E
          · obtain ⟨a, ha, hax⟩ := hx
            exact ⟨a, ha, hax.tail he⟩
          · exact hrepair (x, z) (by simp) he
        apply ih hz
        intro e hew heE
        exact hrepair e (by simp [hew]) heE
  exact step p.walk hstart hrepair

/-- The finite recorded parent represented by a finite auxiliary source. -/
theorem exists_finiteParent_of_mem_finiteSource
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource) :
    ∃ (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
          some (.inl p : Gamma.DPath) ∧
        p.finish = b ∧
        (.inl p : Gamma.DPath) ∈
          Gamma.inessentialPaths L.limitWarp := by
  let x : L.groundedFiniteTerminalSet := ⟨b, hb⟩
  let x' : L.finiteTerminalSet :=
    ⟨b, L.groundedFiniteTerminalSet_subset_finiteTerminalSet hb⟩
  obtain ⟨_haFinite, parent, hchosen, hterminal⟩ :=
    L.finiteTerminalStage_spec x'
  have hindex : L.finiteTerminalIndex x = L.finiteTerminalStage x' := rfl
  rw [hindex]
  rcases parent with p | r
  · have hfinish : p.finish = b := by
      exact Option.some.inj hterminal
    exact ⟨p, hchosen, hfinish,
      L.recorded_mem_limitWarp_inessential_sourceGeometry
        hL.legal hchosen⟩
  · change (none : Option V) = some b at hterminal
    cases hterminal

/-- Every finite auxiliary source has a canonical finite parent with a
genuine original source root. -/
theorem exists_groundedFiniteParent_of_mem_finiteSource
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource) :
    ∃ (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
          some (.inl p : Gamma.DPath) ∧
        p.finish = b ∧
        p.start ∈ Gamma.source ∧
        (.inl p : Gamma.DPath) ∈
          Gamma.inessentialPaths L.limitWarp := by
  obtain ⟨p, hchosen, hfinish, hlimit⟩ :=
    L.exists_finiteParent_of_mem_finiteSource hL hb
  have hground : L.finiteTerminalIndex ⟨b, hb⟩ ∈ L.phiGround := by
    exact L.finiteTerminalStage_mem_phiGround hL.legal ⟨b, hb⟩
  obtain ⟨parent, hparentChosen, hparentSource⟩ := hground
  have hparent : parent = (.inl p : Gamma.DPath) := by
    exact Option.some.inj (hparentChosen.symm.trans hchosen)
  subst parent
  have hpSource : p.start ∈ Gamma.source := by
    exact hparentSource
  exact ⟨p, hchosen, hfinish, hpSource, hlimit⟩

/-- The old auxiliary source represented by a finite terminal has exactly
the canonical finite-stage index. -/
theorem finiteSource_index_eq_finiteTerminalIndex
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource) :
    (L.popularAuxiliaryIndexed hL).f
        ⟨PopularAuxiliary.Input.LambdaVertex.old b,
          ((L.popularAuxiliaryInput hL.legal).mem_lambda_source_old b).2 hb⟩ =
      L.finiteTerminalIndex ⟨b, hb⟩ := by
  rfl

/-- A grounded finite source already lying in the popular cut supplies a
canonical cut-source parent.  Its genuine root differs from the stationary
unused root. -/
theorem UnusedGroundedRecord.exists_cutFiniteSource_parent_with_root_ne
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut) :
    ∃ (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
          some (.inl p : Gamma.DPath) ∧
        p.finish = b ∧
        p.start ∈ Gamma.source ∧
        (.inl p : Gamma.DPath) ∈
          Gamma.inessentialPaths L.limitWarp ∧
        R.record.initial ≠ p.start := by
  obtain ⟨p, hchosen, hfinish, hsource, hlimit⟩ :=
    L.exists_groundedFiniteParent_of_mem_finiteSource hL hb
  let x : (L.popularAuxiliaryInput hL.legal).lambda.source :=
    ⟨PopularAuxiliary.Input.LambdaVertex.old b,
      ((L.popularAuxiliaryInput hL.legal).mem_lambda_source_old b).2 hb⟩
  have hindex :
      (L.popularAuxiliaryIndexed hL).f x =
        L.finiteTerminalIndex ⟨b, hb⟩ := by
    exact L.finiteSource_index_eq_finiteTerminalIndex hL hb
  have hroot : R.record.initial ≠ p.start := by
    exact R.record_initial_ne_cutSource_parent_initial x hbCut
      (L.finiteTerminalIndex ⟨b, hb⟩) (.inl p)
      hindex hchosen hlimit.1
  exact ⟨p, hchosen, hfinish, hsource, hlimit, hroot⟩

/-- Concrete reduction of the finite-source `BB` root case to the exact
switch-specific repair obligation.  Whenever the final switch deletes an
edge of the canonical grounded finite parent, it suffices to root the head
of that edge.  The finite scan then splices those replacement chains with
all surviving parent suffixes. -/
theorem UnusedGroundedRecord.exists_cutFiniteSource_rooted_of_deleted_heads
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut)
    (hrepair : ∀
      (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
          some (.inl p : Gamma.DPath) →
      ∀ e ∈ p.edgeSet,
        e ∉ GroundingErasedDecode.erasedSelectedSwitchedEdges
          (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S) →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈
              GroundingErasedDecode.erasedSelectedSwitchedEdges
                (L.popularAuxiliaryIndexed hL) S
                (L.groundedConcreteControls hL S)) a e.2) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdges
            (L.popularAuxiliaryIndexed hL) S
            (L.groundedConcreteControls hL S)) a b := by
  obtain ⟨p, hchosen, hfinish, hsource, _hlimit, hroot⟩ :=
    R.exists_cutFiniteSource_parent_with_root_ne hb hbCut
  let E := GroundingErasedDecode.erasedSelectedSwitchedEdges
    (L.popularAuxiliaryIndexed hL) S (L.groundedConcreteControls hL S)
  have hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.start := by
    refine ⟨p.start, ⟨hsource, ?_⟩, .refl⟩
    simpa only [Set.mem_singleton_iff] using hroot.symm
  obtain ⟨a, ha, hab⟩ :=
    exists_root_reaching_finish_of_deleted_heads_reachable p hstart
      (hrepair p hchosen)
  exact ⟨a, ha, hfinish ▸ hab⟩

/-- Minimal concrete finite-source reduction.  Only the last deleted head
of the canonical parent must be rooted; the bundled suffix is already a
path of the final switched relation.  Thus the remaining geometric lemma
can focus precisely on the final selected-route contact with that parent. -/
theorem UnusedGroundedRecord.exists_cutFiniteSource_rooted_of_lastDeletedHead
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut)
    (hrepair : ∀
      (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
          some (.inl p : Gamma.DPath) →
      ∀ D : LastDeletedHead p
        (GroundingErasedDecode.erasedSelectedSwitchedEdges
          (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S)),
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈
              GroundingErasedDecode.erasedSelectedSwitchedEdges
                (L.popularAuxiliaryIndexed hL) S
                (L.groundedConcreteControls hL S)) a D.head) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdges
            (L.popularAuxiliaryIndexed hL) S
            (L.groundedConcreteControls hL S)) a b := by
  obtain ⟨p, hchosen, hfinish, hsource, _hlimit, hroot⟩ :=
    R.exists_cutFiniteSource_parent_with_root_ne hb hbCut
  let E := GroundingErasedDecode.erasedSelectedSwitchedEdges
    (L.popularAuxiliaryIndexed hL) S (L.groundedConcreteControls hL S)
  have hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.start := by
    refine ⟨p.start, ⟨hsource, ?_⟩, .refl⟩
    simpa only [Set.mem_singleton_iff] using hroot.symm
  obtain ⟨a, ha, hab⟩ :=
    exists_root_reaching_finish_of_lastDeletedHead p hstart
      (hrepair p hchosen)
  exact ⟨a, ha, hfinish ▸ hab⟩

end KappaLadder
end DWeb
end Erdos599
