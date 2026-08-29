/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteSourceRootAt
import ErdosProblems.Erdos599.GroundingInactiveControlRootTransfer
import ErdosProblems.Erdos599.GroundingErasedCarrierRank
import ErdosProblems.Erdos599.GroundingStoppedRootReduction
import ErdosProblems.Erdos599.GroundingPreStoppedBlockingRoot
import ErdosProblems.Erdos599.GroundingReservedBackwardOwner

/-!
# Deleted-head root classification before boundary stopping

For the pre-stopped simultaneous switch the stopping frontier is empty.
Consequently a ladder-family edge can disappear for exactly three reasons:
it is represented by the auxiliary cut, it is selected backwards, or it is
removed by a forward-connector conflict.  This file specializes the general
frontier-parametric finite-source splice to that exact three-way split.

The three geometric repair callbacks remain explicit.  In particular, no
unproved claim that a cut head, backward-link head, or conflict head is rooted
is hidden in this specialization.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb

open Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- A represented cut edge supplies the untagged control request at its
head.  This is the exact bridge from the `CE` deleted-head branch to the
control-rooting branch of the grounding construction. -/
theorem exists_controlRequest_head_of_mem_CE
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    {C : Set J.LV} {e : V × V} (he : e ∈ GroundingCut.CE J C) :
    ∃ c : GroundingErasedDecode.ControlRequest J C, c.1 = e.2 := by
  let r : PopularGroundingBridge.Request J C :=
    .inr ⟨e, (GroundingCut.mem_CE.mp he).1⟩
  let c : GroundingErasedDecode.ControlRequest J C :=
    ⟨e.2, ⟨r, rfl⟩⟩
  exact ⟨c, rfl⟩

/-- Pointwise root transfer for a `CE` head.  Thus finite-parent cut-edge
repairs require no geometry beyond the already necessary control-rooting
statement. -/
theorem exists_root_reaching_head_of_mem_CE_of_controls_rooted
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    {C : Set J.LV} {E : Set (V × V)} {A : Set V}
    (hcontrol : ∀ c : GroundingErasedDecode.ControlRequest J C,
      ∃ a ∈ A, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ E) a c.1)
    {e : V × V} (he : e ∈ GroundingCut.CE J C) :
    ∃ a ∈ A, Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) a e.2 := by
  obtain ⟨c, hc⟩ := exists_controlRequest_head_of_mem_CE he
  simpa only [hc] using hcontrol c

/-- An unrooted head deleted by a forward conflict can only come from the
genuine same-tail branch of that conflict.  In the same-head branch the
competing retained forward edge itself puts the deleted head in the retained
forward carrier, contradicting pointwise rootedness of active retained
carriers.  This separates the harmless merge collision from the remaining
exchange obstruction without assuming that an arbitrary residual suffix
survives. -/
theorem forwardConflictCutEdge_sameTail_of_head_not_rooted
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S) (A : Set V)
    (hretainedRoot : ∀
      (c : GroundingErasedDecode.ActiveControlRequestAt U S K ∅) (x : V),
      x ∈ GroundingErasedDecode.retainedForwardVerticesAt ∅
          (GroundingErasedDecode.selectedErasedCompression U S K
            (GroundingErasedDecode.chosenRequest c.1)).path →
        ∃ a ∈ A, Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈
            GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
          a x)
    {e : V × V}
    (he : e ∈ GroundingErasedDecode.forwardConflictCutEdgesAt U S K ∅)
    (hheadNotRooted : ¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
      a e.2) :
    ∃ (c : GroundingErasedDecode.ActiveControlRequestAt U S K ∅)
        (f : V × V),
      f ∈ GroundingErasedDecode.retainedForwardEdgesAt ∅
        (GroundingErasedDecode.selectedErasedCompression U S K
          (GroundingErasedDecode.chosenRequest c.1)).path ∧
      e.1 = f.1 := by
  rcases he with ⟨_heResidual, f, hf, htail | hhead⟩
  · simp only [GroundingErasedDecode.erasedSelectedRetainedForwardEdgesAt,
      Set.mem_iUnion] at hf
    obtain ⟨c, hfc⟩ := hf
    exact ⟨c, f, hfc, htail⟩
  · exfalso
    apply hheadNotRooted
    simp only [GroundingErasedDecode.erasedSelectedRetainedForwardEdgesAt,
      Set.mem_iUnion] at hf
    obtain ⟨c, hfc⟩ := hf
    obtain ⟨a, ha, hareach⟩ := hretainedRoot c f.2
      (GroundingErasedDecode.retainedForwardEdgeAt_endpoints ∅ _ hfc).2
    exact ⟨a, ha, by simpa only [hhead] using hareach⟩

/-- Exact three-way classification of a last deleted family edge in the
pre-stopped (`T = ∅`) simultaneous switch. -/
theorem LastDeletedHead.exists_classified_deletedIncomingPreStopped
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    {p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph}
    (hpFamily : p.edgeSet ⊆ J.familyEdges)
    (D : LastDeletedHead p
      (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)) :
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈ GroundingCut.CE J S.cut) ∨
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.erasedSelectedDirectionEdgesAt
          U S K ∅ .backward) ∨
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.forwardConflictCutEdgesAt U S K ∅) := by
  rcases D.exists_classified_deletedIncomingAt_split K ∅ hpFamily with
      hCE | hbackward | hconflict | ⟨u, _huParent, _huResidual, huEmpty⟩
  · exact Or.inl hCE
  · exact Or.inr (Or.inl hbackward)
  · exact Or.inr (Or.inr hconflict)
  · exact False.elim (by simpa using huEmpty)

/-- Owner-refined provenance for a selected backward edge.  The witness
retains the active request, the concrete backward link of its erased route,
and the unique limiting-ladder path on which that link lies. -/
theorem exists_erasedSelectedBackwardEdge_ownerAt
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S) (T : Set V)
    {e : V × V}
    (he : e ∈ GroundingErasedDecode.erasedSelectedDirectionEdgesAt
      U S K T .backward) :
    ∃ (c : GroundingErasedDecode.ActiveControlRequestAt U S K T)
        (l : Alternating.Link Gamma.graph) (parent : Gamma.DPath),
      l ∈ (GroundingErasedDecode.selectedErasedCompression U S K
        (GroundingErasedDecode.chosenRequest c.1)).path.links ∧
      l.direction = .backward ∧ e ∈ l.path.edgeSet ∧
      parent ∈ J.ladder.paths ∧ l.path.IsSubpathOf parent := by
  simp only [GroundingErasedDecode.erasedSelectedDirectionEdgesAt,
    Set.mem_iUnion] at he
  obtain ⟨c, hec⟩ := he
  simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion] at hec
  obtain ⟨l, hl, hldir, hel⟩ := hec
  obtain ⟨parent, hparent, hsub⟩ :=
    GroundingErasedDecode.selectedErasedCompression_backwardLinksOn
      U S K (GroundingErasedDecode.chosenRequest c.1) l hl hldir
  exact ⟨c, l, parent, hl, hldir, hel, hparent, hsub⟩

/-- Reserved-control specialization of backward-edge provenance.  Its owner
is a limiting-ladder path different from the one excluded source record. -/
theorem UnusedGroundedRecord.exists_reservedSelectedBackwardEdge_ownerAt
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S) (T : Set V)
    {e : V × V}
    (he : e ∈ GroundingErasedDecode.erasedSelectedDirectionEdgesAt
      (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) T .backward) :
    ∃ (c : GroundingErasedDecode.ActiveControlRequestAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) T)
        (l : Alternating.Link Gamma.graph) (parent : Gamma.DPath),
      l ∈ (GroundingErasedDecode.selectedErasedCompression
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)
          (GroundingErasedDecode.chosenRequest c.1)).path.links ∧
      l.direction = .backward ∧ e ∈ l.path.edgeSet ∧
      parent ∈ L.limitWarp ∧ l.path.IsSubpathOf parent ∧
      parent ≠ R.record := by
  obtain ⟨c, l, parent, hl, hldir, hel, hparent, hsub⟩ :=
    exists_erasedSelectedBackwardEdge_ownerAt
      (L.reservedGroundedControls hL S R) T he
  have hparent' : parent ∈ L.limitWarp := hparent
  have hne : parent ≠ R.record :=
    R.backwardLink_parent_ne_record
      (GroundingErasedDecode.chosenRequest c.1) l hl hldir
        parent hparent' hsub
  exact ⟨c, l, parent, hl, hldir, hel, hparent', hsub, hne⟩

/-- Once cut heads and retained active-route vertices are rooted, an
unrooted last deleted head has only two exact forms: it is entered by a
selected backward edge, or its incoming parent edge shares its tail with a
concrete retained forward edge.  In particular the represented-cut and
same-head conflict alternatives are not genuine residual obstructions. -/
theorem LastDeletedHead.backward_or_sameTail_of_head_not_rootedPreStopped
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S) (A : Set V)
    {p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph}
    (hpFamily : p.edgeSet ⊆ J.familyEdges)
    (D : LastDeletedHead p
      (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅))
    (hcontrolRoot : ∀ c : GroundingErasedDecode.ControlRequest J S.cut,
      ∃ a ∈ A, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
        a c.1)
    (hretainedRoot : ∀
      (c : GroundingErasedDecode.ActiveControlRequestAt U S K ∅) (x : V),
      x ∈ GroundingErasedDecode.retainedForwardVerticesAt ∅
          (GroundingErasedDecode.selectedErasedCompression U S K
            (GroundingErasedDecode.chosenRequest c.1)).path →
        ∃ a ∈ A, Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈
            GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
          a x)
    (hheadNotRooted : ¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
      a D.head) :
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.erasedSelectedDirectionEdgesAt
          U S K ∅ .backward) ∨
    ∃ (u : V)
        (c : GroundingErasedDecode.ActiveControlRequestAt U S K ∅)
        (f : V × V),
      (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.forwardConflictCutEdgesAt U S K ∅ ∧
      f ∈ GroundingErasedDecode.retainedForwardEdgesAt ∅
        (GroundingErasedDecode.selectedErasedCompression U S K
          (GroundingErasedDecode.chosenRequest c.1)).path ∧
      u = f.1 := by
  rcases D.exists_classified_deletedIncomingPreStopped K hpFamily with
      ⟨u, huParent, huCE⟩ |
      ⟨u, huParent, huBackward⟩ |
      ⟨u, huParent, huConflict⟩
  · exfalso
    apply hheadNotRooted
    exact exists_root_reaching_head_of_mem_CE_of_controls_rooted
      hcontrolRoot huCE
  · exact Or.inl ⟨u, huParent, huBackward⟩
  · right
    obtain ⟨c, f, hf, htail⟩ :=
      forwardConflictCutEdge_sameTail_of_head_not_rooted
        K A hretainedRoot huConflict hheadNotRooted
    exact ⟨u, c, f, huParent, huConflict, hf, htail⟩

/-- Pre-stopped finite-path splice.  It suffices to reroot the last deleted
head in each of the three possible deletion classes; the remaining suffix is
already contained in the pre-stopped relation. -/
theorem exists_root_reaching_finishPreStopped_of_lastDeletedHead_cases
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S) (A : Set V)
    (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph)
    (hpFamily : p.edgeSet ⊆ J.familyEdges)
    (hstart : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
        a p.start)
    (hCE : ∀ (D : LastDeletedHead p
        (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)) u,
      (u, D.head) ∈ p.edgeSet →
      (u, D.head) ∈ GroundingCut.CE J S.cut →
      ∃ a ∈ A, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
        a D.head)
    (hbackward : ∀ (D : LastDeletedHead p
        (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)) u,
      (u, D.head) ∈ p.edgeSet →
      (u, D.head) ∈
        GroundingErasedDecode.erasedSelectedDirectionEdgesAt
          U S K ∅ .backward →
      ∃ a ∈ A, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
        a D.head)
    (hconflict : ∀ (D : LastDeletedHead p
        (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)) u,
      (u, D.head) ∈ p.edgeSet →
      (u, D.head) ∈
        GroundingErasedDecode.forwardConflictCutEdgesAt U S K ∅ →
      ∃ a ∈ A, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
        a D.head) :
    ∃ a ∈ A, Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
      a p.finish := by
  apply exists_root_reaching_finishAt_of_lastDeletedHead_cases
    K ∅ A p hpFamily hstart hCE hbackward hconflict
  intro D u _huParent _huResidual huEmpty
  exact False.elim (by simpa using huEmpty)

/-- An inactive control does not require the whole exposed-component segment
to survive.  Starting from the retained rooted contact, it is enough to
reroot the last deleted head of the finite segment to the inactive control;
the suffix following that head already survives. -/
theorem inactiveControlAt_empty_rooted_of_lastDeletedHead
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (A : Set V)
    (c : GroundingErasedDecode.ControlRequest J S.cut)
    (hc : ¬ GroundingErasedDecode.IsActiveControlAt U S K ∅ c)
    (hcontactRoot : ∀ d : GroundingErasedDecode.ActiveControlRequestAt
        U S K ∅, ∀ x,
      x ∈ GroundingErasedDecode.retainedForwardVerticesAt ∅
          (GroundingErasedDecode.selectedErasedCompression
            U S K (GroundingErasedDecode.chosenRequest d.1)).path →
        ∃ a ∈ A, Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈
            GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
              U S K ∅) a x)
    (hrepair : ∀
      (d : GroundingErasedDecode.ActiveControlRequestAt U S K ∅)
      (Y : Gamma.DPath),
      Y ∈ GroundingSimultaneousDecode.exposedLadderPaths J
        (GroundingSimultaneousDecode.strongSelectedPath U S K
          (GroundingErasedDecode.chosenRequest d.1)) →
      ∀ x,
      x ∈ GroundingErasedDecode.retainedForwardVerticesAt ∅
          (GroundingErasedDecode.selectedErasedCompression
            U S K (GroundingErasedDecode.chosenRequest d.1)).path →
      x ∈ Y.support → GroundingCut.BeforeEq Y x c.1 →
      ∀ p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph,
      p.start = x → p.finish = c.1 → p.edgeSet ⊆ Y.edgeSet →
      ∀ D : LastDeletedHead p
        (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅),
        ∃ a ∈ A, Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈
            GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
              U S K ∅) a D.head) :
    ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
      a c.1 := by
  obtain ⟨d, _hdc, Y, hY, _hcY, x, hx, hxY, hxc⟩ :=
    GroundingErasedDecode.exists_active_absorberAt_of_not_active
      U S K ∅ c hc
  obtain ⟨a, ha, hax⟩ := hcontactRoot d x hx
  by_cases hxcEq : x = c.1
  · exact ⟨a, ha, hxcEq ▸ hax⟩
  · obtain ⟨p, hpStart, hpFinish, hpY⟩ :=
      GroundingCutDecoder.exists_forward_segment_of_before
        ⟨hxc, hxcEq⟩
    have hstart : ∃ a ∈ A, Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
        a p.start := by
      exact ⟨a, ha, by simpa only [hpStart] using hax⟩
    obtain ⟨a', ha', hareach⟩ :=
      exists_root_reaching_finish_of_lastDeletedHead p hstart
        (hrepair d Y hY x hx hxY hxc p hpStart hpFinish hpY)
    exact ⟨a', ha', by simpa only [hpFinish] using hareach⟩

/-- Finite positive data behind failure to root an inactive control in the
pre-stopped switch.  It retains the absorbing active request and exposed
parent, the ordered contact segment, an unrooted last deleted head, and the
exact three-way reason for deletion. -/
structure InactivePreStoppedRootObstructionData
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (A : Set V)
    (c : GroundingErasedDecode.ControlRequest J S.cut) where
  absorber : GroundingErasedDecode.ActiveControlRequestAt U S K ∅
  parent : Gamma.DPath
  parent_exposed : parent ∈
    GroundingSimultaneousDecode.exposedLadderPaths J
      (GroundingSimultaneousDecode.strongSelectedPath U S K
        (GroundingErasedDecode.chosenRequest absorber.1))
  contact : V
  contact_retained : contact ∈
    GroundingErasedDecode.retainedForwardVerticesAt ∅
      (GroundingErasedDecode.selectedErasedCompression U S K
        (GroundingErasedDecode.chosenRequest absorber.1)).path
  contact_mem_parent : contact ∈ parent.support
  contact_before_control : GroundingCut.BeforeEq parent contact c.1
  segment : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph
  segment_start : segment.start = contact
  segment_finish : segment.finish = c.1
  segment_edges : segment.edgeSet ⊆ parent.edgeSet
  deleted : LastDeletedHead segment
    (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
  deleted_head_not_rooted : ¬ ∃ a ∈ A,
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
      a deleted.head
  deleted_class :
    (∃ u, (u, deleted.head) ∈ segment.edgeSet ∧
      (u, deleted.head) ∈ GroundingCut.CE J S.cut) ∨
    (∃ u, (u, deleted.head) ∈ segment.edgeSet ∧
      (u, deleted.head) ∈
        GroundingErasedDecode.erasedSelectedDirectionEdgesAt
          U S K ∅ .backward) ∨
    (∃ u, (u, deleted.head) ∈ segment.edgeSet ∧
      (u, deleted.head) ∈
        GroundingErasedDecode.forwardConflictCutEdgesAt U S K ∅)

/-- Negating inactive-control rootedness gives a concrete finite obstruction,
not a failure of an unbounded segment-containment premise. -/
theorem exists_inactivePreStoppedRootObstructionData
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful J)
    (A : Set V)
    (c : GroundingErasedDecode.ControlRequest J S.cut)
    (hc : ¬ GroundingErasedDecode.IsActiveControlAt U S K ∅ c)
    (hcontactRoot : ∀ d : GroundingErasedDecode.ActiveControlRequestAt
        U S K ∅, ∀ x,
      x ∈ GroundingErasedDecode.retainedForwardVerticesAt ∅
          (GroundingErasedDecode.selectedErasedCompression U S K
            (GroundingErasedDecode.chosenRequest d.1)).path →
        ∃ a ∈ A, Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈
            GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
              U S K ∅) a x)
    (hnotRooted : ¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
      a c.1) :
    Nonempty (InactivePreStoppedRootObstructionData S K A c) := by
  obtain ⟨d, _hdc, Y, hY, _hcY, x, hx, hxY, hxc⟩ :=
    GroundingErasedDecode.exists_active_absorberAt_of_not_active
      U S K ∅ c hc
  obtain ⟨a, ha, hax⟩ := hcontactRoot d x hx
  have hxcNe : x ≠ c.1 := by
    intro hEq
    apply hnotRooted
    exact ⟨a, ha, hEq ▸ hax⟩
  obtain ⟨p, hpStart, hpFinish, hpY⟩ :=
    GroundingCutDecoder.exists_forward_segment_of_before ⟨hxc, hxcNe⟩
  have hstart : ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
      a p.start :=
    ⟨a, ha, by simpa only [hpStart] using hax⟩
  have hfinishNot : ¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
      a p.finish := by
    simpa only [hpFinish] using hnotRooted
  obtain ⟨D, hDnot⟩ := exists_unrootedLastDeletedHead p hstart hfinishNot
  have hYLadder : Y ∈ J.ladder.paths :=
    GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
      hfaith _ hY
  have hpFamily : p.edgeSet ⊆ J.familyEdges := by
    intro e he
    exact ⟨Y, hYLadder, hpY he⟩
  exact ⟨{
    absorber := d
    parent := Y
    parent_exposed := hY
    contact := x
    contact_retained := hx
    contact_mem_parent := hxY
    contact_before_control := hxc
    segment := p
    segment_start := hpStart
    segment_finish := hpFinish
    segment_edges := hpY
    deleted := D
    deleted_head_not_rooted := hDnot
    deleted_class := D.exists_classified_deletedIncomingPreStopped
      K hpFamily }⟩

/-- Exact dichotomy for an unrooted inactive control.  Either an actual
retained contact of an active absorber is already unrooted, or the failure
moves strictly downstream to a classified last deleted head on the exposed
parent segment. -/
theorem inactiveControlAt_empty_unrooted_cases
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful J)
    (A : Set V)
    (c : GroundingErasedDecode.ControlRequest J S.cut)
    (hc : ¬ GroundingErasedDecode.IsActiveControlAt U S K ∅ c)
    (hnotRooted : ¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
      a c.1) :
    (∃ (d : GroundingErasedDecode.ActiveControlRequestAt U S K ∅)
        (x : V),
      x ∈ GroundingErasedDecode.retainedForwardVerticesAt ∅
          (GroundingErasedDecode.selectedErasedCompression U S K
            (GroundingErasedDecode.chosenRequest d.1)).path ∧
      ¬ ∃ a ∈ A, Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
        a x) ∨
    Nonempty (InactivePreStoppedRootObstructionData S K A c) := by
  classical
  by_cases hcontactRoot : ∀
      (d : GroundingErasedDecode.ActiveControlRequestAt U S K ∅) (x : V),
      x ∈ GroundingErasedDecode.retainedForwardVerticesAt ∅
          (GroundingErasedDecode.selectedErasedCompression U S K
            (GroundingErasedDecode.chosenRequest d.1)).path →
        ∃ a ∈ A, Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈
            GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
          a x
  · exact Or.inr <|
      exists_inactivePreStoppedRootObstructionData
        K hfaith A c hc hcontactRoot hnotRooted
  · left
    push_neg at hcontactRoot
    obtain ⟨d, x, hx, hnot⟩ := hcontactRoot
    refine ⟨d, x, hx, ?_⟩
    rintro ⟨a, ha, hareach⟩
    exact hnot a ha hareach

/-- An arbitrary unrooted control is therefore either itself active, has an
unrooted retained point on an active route, or yields the classified finite
inactive-segment obstruction above. -/
theorem controlAt_empty_unrooted_cases
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful J)
    (A : Set V)
    (c : GroundingErasedDecode.ControlRequest J S.cut)
    (hnotRooted : ¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
      a c.1) :
    GroundingErasedDecode.IsActiveControlAt U S K ∅ c ∨
    (∃ (d : GroundingErasedDecode.ActiveControlRequestAt U S K ∅)
        (x : V),
      x ∈ GroundingErasedDecode.retainedForwardVerticesAt ∅
          (GroundingErasedDecode.selectedErasedCompression U S K
            (GroundingErasedDecode.chosenRequest d.1)).path ∧
      ¬ ∃ a ∈ A, Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
        a x) ∨
    Nonempty (InactivePreStoppedRootObstructionData S K A c) := by
  by_cases hc : GroundingErasedDecode.IsActiveControlAt U S K ∅ c
  · exact Or.inl hc
  · exact Or.inr <|
      inactiveControlAt_empty_unrooted_cases
        K hfaith A c hc hnotRooted

/-- Recorded finite-parent specialization of the pre-stopped three-way
classification, for arbitrary simultaneous-selection controls. -/
theorem classified_lastDeletedHead_of_recorded_finiteParentPreStopped
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (K : GroundingSelection.Controls S)
    {a : Ladder.Stage kappa}
    {p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph}
    (hchosen : L.chosen a = some (.inl p : Gamma.DPath))
    (D : LastDeletedHead p
      (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
        (L.popularAuxiliaryIndexed hL) S K ∅)) :
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈ GroundingCut.CE
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.erasedSelectedDirectionEdgesAt
          (L.popularAuxiliaryIndexed hL) S K ∅ .backward) ∨
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.forwardConflictCutEdgesAt
          (L.popularAuxiliaryIndexed hL) S K ∅) := by
  rcases classified_lastDeletedHead_of_recorded_finiteParentAt
      K ∅ hchosen D with hCE | hbackward | hconflict |
        ⟨u, _huParent, _huResidual, huEmpty⟩
  · exact Or.inl hCE
  · exact Or.inr (Or.inl hbackward)
  · exact Or.inr (Or.inr hconflict)
  · exact False.elim (by simpa using huEmpty)

namespace Assertion822PreStoppedRootObstruction

/-- In the finite-source branch, a pre-stopped root obstruction gives an
unrooted last deleted head of the canonical grounded parent and its exact
three-way deletion class.  Unlike the stopped analogue there is no outgoing
boundary-tail alternative. -/
theorem exists_unrootedClassifiedLastDeletedHead_of_finiteSource
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    (hfinite : O.boundary ∈
      (L.popularAuxiliaryInput hL.legal).finiteSource)
    (hcut : PopularAuxiliary.Input.LambdaVertex.old O.boundary ∈ S.cut) :
    ∃ (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph)
        (_hchosen : L.chosen
          (L.finiteTerminalIndex ⟨O.boundary, hfinite⟩) =
            some (.inl p : Gamma.DPath))
        (D : LastDeletedHead p
          (L.assertion822ReservedPreStoppedEdges hL S R)),
      (¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R) a D.head) ∧
      ((∃ u, (u, D.head) ∈ p.edgeSet ∧
          (u, D.head) ∈ GroundingCut.CE
            (L.popularAuxiliaryInput hL.legal) S.cut) ∨
        (∃ u, (u, D.head) ∈ p.edgeSet ∧
          (u, D.head) ∈
            GroundingErasedDecode.erasedSelectedDirectionEdgesAt
              (L.popularAuxiliaryIndexed hL) S
              (L.reservedGroundedControls hL S R) ∅ .backward) ∨
        (∃ u, (u, D.head) ∈ p.edgeSet ∧
          (u, D.head) ∈
            GroundingErasedDecode.forwardConflictCutEdgesAt
              (L.popularAuxiliaryIndexed hL) S
              (L.reservedGroundedControls hL S R) ∅)) := by
  let E := L.assertion822ReservedPreStoppedEdges hL S R
  obtain ⟨p, hchosen, hfinish, hsource, _hlimit, hrootNe⟩ :=
    R.exists_cutFiniteSource_parent_with_root_ne hfinite hcut
  have hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.start := by
    refine ⟨p.start, ⟨hsource, ?_⟩, .refl⟩
    simpa only [Set.mem_singleton_iff] using hrootNe.symm
  have hfinishNot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.finish := by
    rintro ⟨a, ha, hap⟩
    apply O.not_rooted
    exact ⟨a, ha, hfinish ▸ hap⟩
  obtain ⟨D, hDnot⟩ :=
    exists_unrootedLastDeletedHead p hstart hfinishNot
  refine ⟨p, hchosen, D, hDnot, ?_⟩
  exact classified_lastDeletedHead_of_recorded_finiteParentPreStopped
    (L.reservedGroundedControls hL S R) hchosen D

/-- In the old-control branch, an unrooted pre-stopped boundary point is
reduced to the exact active/inactive control alternatives: the control is
active, an actual retained point of an active route is unrooted, or the
inactive ordered segment has the finite classified obstruction above. -/
theorem control_cases
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    (c : GroundingErasedDecode.ControlRequest
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (hc : c.1 = O.boundary) :
    GroundingErasedDecode.IsActiveControlAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) ∅ c ∨
    (∃ (d : GroundingErasedDecode.ActiveControlRequestAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) ∅)
        (x : V),
      x ∈ GroundingErasedDecode.retainedForwardVerticesAt ∅
        (GroundingErasedDecode.selectedErasedCompression
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (GroundingErasedDecode.chosenRequest d.1)).path ∧
      ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈
            L.assertion822ReservedPreStoppedEdges hL S R) a x) ∨
    Nonempty (InactivePreStoppedRootObstructionData S
      (L.reservedGroundedControls hL S R)
      (Gamma.source \ {R.record.initial}) c) := by
  have hnotRooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈
          L.assertion822ReservedPreStoppedEdges hL S R) a c.1 := by
    rintro ⟨a, ha, hareach⟩
    apply O.not_rooted
    exact ⟨a, ha, by simpa only [hc] using hareach⟩
  exact controlAt_empty_unrooted_cases
    (L.reservedGroundedControls hL S R)
    (L.popularAuxiliary_proxyPathsFaithful hL)
    (Gamma.source \ {R.record.initial}) c hnotRooted

/-- In the blocking-point branch, failure of pre-stopped rootedness is
localized to exactly one of three causes: the retained fragment initial is
already unrooted, a selected backward edge meets the canonical prefix, or a
forward-conflict edge meets that prefix. -/
theorem blocking_cases
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hPblockable : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (hboundary : GroundingCut.blockingPoint
      (L.popularAuxiliaryInput hL.legal) S.cut P = O.boundary) :
    (¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          L.assertion822ReservedPreStoppedEdges hL S R)
        a P.path.initial) ∨
    (∃ e,
      e ∈ (GroundingBlockingPrefix.data
        (L.popularAuxiliaryInput hL.legal) S.cut P hPblockable).path.edgeSet ∧
      e ∈ GroundingErasedDecode.erasedSelectedDirectionEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅ .backward) ∨
    ∃ e,
      e ∈ (GroundingBlockingPrefix.data
        (L.popularAuxiliaryInput hL.legal) S.cut P hPblockable).path.edgeSet ∧
      e ∈ GroundingErasedDecode.forwardConflictCutEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅ := by
  classical
  by_cases hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          L.assertion822ReservedPreStoppedEdges hL S R)
        a P.path.initial
  · right
    by_cases hbackward : Disjoint
        (GroundingBlockingPrefix.data
          (L.popularAuxiliaryInput hL.legal) S.cut P hPblockable).path.edgeSet
        (GroundingErasedDecode.erasedSelectedDirectionEdgesAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) ∅ .backward)
    · by_cases hconflict : Disjoint
          (GroundingBlockingPrefix.data
            (L.popularAuxiliaryInput hL.legal) S.cut P hPblockable).path.edgeSet
          (GroundingErasedDecode.forwardConflictCutEdgesAt
            (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R) ∅)
      · exfalso
        apply O.not_rooted
        obtain ⟨a, ha, hareach⟩ :=
          R.exists_blockingPoint_rooted_preStopped
            P hPblockable hstart hbackward hconflict
        exact ⟨a, ha, by simpa only [hboundary] using hareach⟩
      · exact Or.inr (Set.not_disjoint_iff.mp hconflict)
    · exact Or.inl (Set.not_disjoint_iff.mp hbackward)
  · exact Or.inl hstart

/-- Last-deleted-head refinement of `blocking_cases`.  When the fragment
initial is rooted but its blocking point is not, the downstream-most missing
edge of the canonical blocking prefix has an unrooted head.  In the
pre-stopped relation that edge is exactly a represented cut edge, a selected
backward edge, or a forward-conflict deletion.  Retaining the
`LastDeletedHead` witness is essential for the subsequent owner/exchange
argument: an arbitrary earlier deleted edge need not be responsible for the
root failure. -/
theorem blocking_lastDeletedHead_cases
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hPblockable : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (hboundary : GroundingCut.blockingPoint
      (L.popularAuxiliaryInput hL.legal) S.cut P = O.boundary) :
    (¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          L.assertion822ReservedPreStoppedEdges hL S R)
        a P.path.initial) ∨
    ∃ D : LastDeletedHead
        (GroundingBlockingPrefix.data
          (L.popularAuxiliaryInput hL.legal) S.cut P hPblockable).path
        (L.assertion822ReservedPreStoppedEdges hL S R),
      (¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R) a D.head) ∧
      ((∃ u,
          (u, D.head) ∈ (GroundingBlockingPrefix.data
            (L.popularAuxiliaryInput hL.legal) S.cut P
              hPblockable).path.edgeSet ∧
          (u, D.head) ∈ GroundingCut.CE
            (L.popularAuxiliaryInput hL.legal) S.cut) ∨
        (∃ u,
          (u, D.head) ∈ (GroundingBlockingPrefix.data
            (L.popularAuxiliaryInput hL.legal) S.cut P
              hPblockable).path.edgeSet ∧
          (u, D.head) ∈
            GroundingErasedDecode.erasedSelectedDirectionEdgesAt
              (L.popularAuxiliaryIndexed hL) S
              (L.reservedGroundedControls hL S R) ∅ .backward) ∨
        ∃ u,
          (u, D.head) ∈ (GroundingBlockingPrefix.data
            (L.popularAuxiliaryInput hL.legal) S.cut P
              hPblockable).path.edgeSet ∧
          (u, D.head) ∈
            GroundingErasedDecode.forwardConflictCutEdgesAt
              (L.popularAuxiliaryIndexed hL) S
              (L.reservedGroundedControls hL S R) ∅) := by
  let Q := GroundingBlockingPrefix.data
    (L.popularAuxiliaryInput hL.legal) S.cut P hPblockable
  let E := L.assertion822ReservedPreStoppedEdges hL S R
  by_cases hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a Q.path.start
  · right
    have hfinishNot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a Q.path.finish := by
      rintro ⟨a, ha, hareach⟩
      apply O.not_rooted
      refine ⟨a, ha, ?_⟩
      simpa only [Q, GroundingBlockingPrefix.Data.finish_eq,
        hboundary] using hareach
    obtain ⟨D, hDnot⟩ :=
      exists_unrootedLastDeletedHead Q.path hstart hfinishNot
    refine ⟨D, hDnot, ?_⟩
    apply D.exists_classified_deletedIncomingPreStopped
      (L.reservedGroundedControls hL S R)
    intro e he
    exact (Q.edgeSet_subset_residual he).1
  · left
    intro hroot
    apply hstart
    simpa only [Q, GroundingBlockingPrefix.Data.start_eq] using hroot

end Assertion822PreStoppedRootObstruction

/-- Reserved finite-source rooting for the pre-stopped relation, reduced to
the exact three possible classes of the final deleted canonical-parent edge.
The callbacks receive the recorded-parent equality as well as the edge
incidence, so construction-specific exchange arguments lose no provenance. -/
theorem UnusedGroundedRecord.exists_cutFiniteSource_rootedPreStopped_of_lastDeletedHead_cases
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    (K : GroundingSelection.Controls S)
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut)
    (hCE : ∀
      (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph)
      (hchosen : L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
        some (.inl p : Gamma.DPath))
      (D : LastDeletedHead p
        (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
          (L.popularAuxiliaryIndexed hL) S K ∅)) u,
      (u, D.head) ∈ p.edgeSet →
      (u, D.head) ∈ GroundingCut.CE
        (L.popularAuxiliaryInput hL.legal) S.cut →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
              (L.popularAuxiliaryIndexed hL) S K ∅) a D.head)
    (hbackward : ∀
      (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph)
      (hchosen : L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
        some (.inl p : Gamma.DPath))
      (D : LastDeletedHead p
        (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
          (L.popularAuxiliaryIndexed hL) S K ∅)) u,
      (u, D.head) ∈ p.edgeSet →
      (u, D.head) ∈
        GroundingErasedDecode.erasedSelectedDirectionEdgesAt
          (L.popularAuxiliaryIndexed hL) S K ∅ .backward →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
              (L.popularAuxiliaryIndexed hL) S K ∅) a D.head)
    (hconflict : ∀
      (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph)
      (hchosen : L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
        some (.inl p : Gamma.DPath))
      (D : LastDeletedHead p
        (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
          (L.popularAuxiliaryIndexed hL) S K ∅)) u,
      (u, D.head) ∈ p.edgeSet →
      (u, D.head) ∈
        GroundingErasedDecode.forwardConflictCutEdgesAt
          (L.popularAuxiliaryIndexed hL) S K ∅ →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
              (L.popularAuxiliaryIndexed hL) S K ∅) a D.head) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
            (L.popularAuxiliaryIndexed hL) S K ∅) a b := by
  apply R.exists_cutFiniteSource_rootedAt_of_lastDeletedHead K ∅ hb hbCut
  intro p hchosen D
  rcases classified_lastDeletedHead_of_recorded_finiteParentPreStopped
      K hchosen D with
      ⟨u, huParent, huCE⟩ |
      ⟨u, huParent, huBackward⟩ |
      ⟨u, huParent, huConflict⟩
  · exact hCE p hchosen D u huParent huCE
  · exact hbackward p hchosen D u huParent huBackward
  · exact hconflict p hchosen D u huParent huConflict

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.LastDeletedHead.exists_classified_deletedIncomingPreStopped
#print axioms Erdos599.DWeb.KappaLadder.exists_controlRequest_head_of_mem_CE
#print axioms Erdos599.DWeb.KappaLadder.exists_root_reaching_head_of_mem_CE_of_controls_rooted
#print axioms Erdos599.DWeb.KappaLadder.forwardConflictCutEdge_sameTail_of_head_not_rooted
#print axioms Erdos599.DWeb.KappaLadder.exists_erasedSelectedBackwardEdge_ownerAt
#print axioms Erdos599.DWeb.KappaLadder.UnusedGroundedRecord.exists_reservedSelectedBackwardEdge_ownerAt
#print axioms Erdos599.DWeb.KappaLadder.LastDeletedHead.backward_or_sameTail_of_head_not_rootedPreStopped
#print axioms Erdos599.DWeb.KappaLadder.exists_root_reaching_finishPreStopped_of_lastDeletedHead_cases
#print axioms Erdos599.DWeb.KappaLadder.inactiveControlAt_empty_rooted_of_lastDeletedHead
#print axioms Erdos599.DWeb.KappaLadder.exists_inactivePreStoppedRootObstructionData
#print axioms Erdos599.DWeb.KappaLadder.controlAt_empty_unrooted_cases
#print axioms Erdos599.DWeb.KappaLadder.classified_lastDeletedHead_of_recorded_finiteParentPreStopped
#print axioms Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.exists_unrootedClassifiedLastDeletedHead_of_finiteSource
#print axioms Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.control_cases
#print axioms Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.blocking_cases
#print axioms Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.blocking_lastDeletedHead_cases
#print axioms Erdos599.DWeb.KappaLadder.UnusedGroundedRecord.exists_cutFiniteSource_rootedPreStopped_of_lastDeletedHead_cases
