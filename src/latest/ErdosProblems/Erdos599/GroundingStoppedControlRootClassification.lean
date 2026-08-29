/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingActiveControls
import ErdosProblems.Erdos599.GroundingCutDecoder
import ErdosProblems.Erdos599.GroundingErasedCarrierRank
import ErdosProblems.Erdos599.GroundingFiniteSourceRootAt
import ErdosProblems.Erdos599.GroundingStoppedRootReduction

/-!
# Control-root classification at an arbitrary stopping frontier

The pre-stopped control classifier cannot be transported monotonically to a
nonempty stopping frontier: activity is recomputed from the retained prefixes,
and the final relation deletes residual edges leaving the frontier.  This file
instead repeats the finite obstruction argument in the actual relation stopped
at `T`.

If an inactive control is not rooted, either a retained point of its active
absorber is already unrooted, or the ordered finite ladder segment from that
point to the control has a last deleted head.  The latter keeps all four exact
deletion classes at `T`, including a literal residual edge whose tail belongs
to `T`.  No rootedness or monotonicity of controls is assumed.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath

universe u

variable {V I : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Positive finite obstruction data for an inactive control in the relation
stopped at `T`.  The fourth deletion class is essential: it records exactly
the case in which the absorber-to-control segment attempts to leave `T`. -/
structure InactiveStoppedRootObstructionDataAt
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T A : Set V)
    (c : GroundingErasedDecode.ControlRequest J S.cut) where
  absorber : GroundingErasedDecode.ActiveControlRequestAt U S K T
  absorber_rank_lt : GroundingErasedDecode.controlRank U S absorber.1 <
    GroundingErasedDecode.controlRank U S c
  parent : Gamma.DPath
  parent_exposed : parent ∈
    GroundingSimultaneousDecode.exposedLadderPaths J
      (GroundingSimultaneousDecode.strongSelectedPath U S K
        (GroundingErasedDecode.chosenRequest absorber.1))
  contact : V
  contact_retained : contact ∈
    GroundingErasedDecode.retainedForwardVerticesAt T
      (GroundingErasedDecode.selectedErasedCompression U S K
        (GroundingErasedDecode.chosenRequest absorber.1)).path
  /-- The retained absorber contact is rooted in the relation stopped at
  `T`.  This is the positive half of the inactive branch construction; it
  must be retained so the classified finite segment can enter the native
  deleted-head recursion. -/
  contact_rooted : ∃ a ∈ A, Relation.ReflTransGen
    (fun x y ↦ (x, y) ∈
      GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
    a contact
  contact_mem_parent : contact ∈ parent.support
  contact_before_control : GroundingCut.BeforeEq parent contact c.1
  segment : FinitePath Gamma.graph
  segment_start : segment.start = contact
  segment_finish : segment.finish = c.1
  segment_edges : segment.edgeSet ⊆ parent.edgeSet
  deleted : LastDeletedHead segment
    (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
  deleted_head_not_rooted : ¬ ∃ a ∈ A,
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
      a deleted.head
  deleted_class :
    (∃ x, (x, deleted.head) ∈ segment.edgeSet ∧
      (x, deleted.head) ∈ GroundingCut.CE J S.cut) ∨
    (∃ x, (x, deleted.head) ∈ segment.edgeSet ∧
      (x, deleted.head) ∈
        GroundingErasedDecode.erasedSelectedDirectionEdgesAt
          U S K T .backward) ∨
    (∃ x, (x, deleted.head) ∈ segment.edgeSet ∧
      (x, deleted.head) ∈
        GroundingErasedDecode.forwardConflictCutEdgesAt U S K T) ∨
    ∃ x, (x, deleted.head) ∈ segment.edgeSet ∧
      (x, deleted.head) ∈
        GroundingErasedDecode.residualLadderEdges U S ∧
      x ∈ T

/-- If every retained active contact is rooted but an inactive control is
not, the exact finite At-`T` obstruction data exists. -/
theorem exists_inactiveStoppedRootObstructionDataAt
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful J)
    (T A : Set V)
    (c : GroundingErasedDecode.ControlRequest J S.cut)
    (hc : ¬ GroundingErasedDecode.IsActiveControlAt U S K T c)
    (hcontactRoot : ∀ d : GroundingErasedDecode.ActiveControlRequestAt
        U S K T, ∀ x,
      x ∈ GroundingErasedDecode.retainedForwardVerticesAt T
          (GroundingErasedDecode.selectedErasedCompression U S K
            (GroundingErasedDecode.chosenRequest d.1)).path →
        ∃ a ∈ A, Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈
            GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
          a x)
    (hnotRooted : ¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
      a c.1) :
    Nonempty (InactiveStoppedRootObstructionDataAt S K T A c) := by
  obtain ⟨d, hdc, Y, hY, _hcY, x, hx, hxY, hxc⟩ :=
    GroundingErasedDecode.exists_active_absorberAt_of_not_active
      U S K T c hc
  obtain ⟨a, ha, hax⟩ := hcontactRoot d x hx
  have hxcNe : x ≠ c.1 := by
    intro hEq
    apply hnotRooted
    exact ⟨a, ha, hEq ▸ hax⟩
  obtain ⟨p, hpStart, hpFinish, hpY⟩ :=
    GroundingCutDecoder.exists_forward_segment_of_before ⟨hxc, hxcNe⟩
  have hstart : ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
      a p.start :=
    ⟨a, ha, by simpa only [hpStart] using hax⟩
  have hfinishNot : ¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
      a p.finish := by
    simpa only [hpFinish] using hnotRooted
  obtain ⟨D, hDnot⟩ :=
    exists_unrootedLastDeletedHead p hstart hfinishNot
  have hYLadder : Y ∈ J.ladder.paths :=
    GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
      hfaith _ hY
  have hpFamily : p.edgeSet ⊆ J.familyEdges := by
    intro e he
    exact ⟨Y, hYLadder, hpY he⟩
  exact ⟨{
    absorber := d
    absorber_rank_lt := hdc
    parent := Y
    parent_exposed := hY
    contact := x
    contact_retained := hx
    contact_rooted := ⟨a, ha, hax⟩
    contact_mem_parent := hxY
    contact_before_control := hxc
    segment := p
    segment_start := hpStart
    segment_finish := hpFinish
    segment_edges := hpY
    deleted := D
    deleted_head_not_rooted := hDnot
    deleted_class := D.exists_classified_deletedIncomingAt_split
      K T hpFamily }⟩

/-- Exact dichotomy for an unrooted inactive control in the relation stopped
at `T`: an active retained contact is already unrooted, or the finite
four-way obstruction above exists. -/
theorem inactiveControlAt_unrooted_cases
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful J)
    (T A : Set V)
    (c : GroundingErasedDecode.ControlRequest J S.cut)
    (hc : ¬ GroundingErasedDecode.IsActiveControlAt U S K T c)
    (hnotRooted : ¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
      a c.1) :
    (∃ (d : GroundingErasedDecode.ActiveControlRequestAt U S K T)
        (x : V),
      x ∈ GroundingErasedDecode.retainedForwardVerticesAt T
          (GroundingErasedDecode.selectedErasedCompression U S K
            (GroundingErasedDecode.chosenRequest d.1)).path ∧
      ¬ ∃ a ∈ A, Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
        a x) ∨
    Nonempty (InactiveStoppedRootObstructionDataAt S K T A c) := by
  classical
  by_cases hcontactRoot : ∀
      (d : GroundingErasedDecode.ActiveControlRequestAt U S K T) (x : V),
      x ∈ GroundingErasedDecode.retainedForwardVerticesAt T
          (GroundingErasedDecode.selectedErasedCompression U S K
            (GroundingErasedDecode.chosenRequest d.1)).path →
        ∃ a ∈ A, Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈
            GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
          a x
  · exact Or.inr <|
      exists_inactiveStoppedRootObstructionDataAt
        K hfaith T A c hc hcontactRoot hnotRooted
  · left
    push Not at hcontactRoot
    obtain ⟨d, x, hx, hnot⟩ := hcontactRoot
    refine ⟨d, x, hx, ?_⟩
    rintro ⟨a, ha, hareach⟩
    exact hnot a ha hareach

/-- An arbitrary unrooted control at `T` is active, exposes an unrooted
retained point of an active request, or has the finite four-way stopped
obstruction. -/
theorem controlAt_unrooted_cases
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful J)
    (T A : Set V)
    (c : GroundingErasedDecode.ControlRequest J S.cut)
    (hnotRooted : ¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
      a c.1) :
    GroundingErasedDecode.IsActiveControlAt U S K T c ∨
    (∃ (d : GroundingErasedDecode.ActiveControlRequestAt U S K T)
        (x : V),
      x ∈ GroundingErasedDecode.retainedForwardVerticesAt T
          (GroundingErasedDecode.selectedErasedCompression U S K
            (GroundingErasedDecode.chosenRequest d.1)).path ∧
      ¬ ∃ a ∈ A, Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
        a x) ∨
    Nonempty (InactiveStoppedRootObstructionDataAt S K T A c) := by
  by_cases hc : GroundingErasedDecode.IsActiveControlAt U S K T c
  · exact Or.inl hc
  · exact Or.inr <|
      inactiveControlAt_unrooted_cases
        K hfaith T A c hc hnotRooted

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.controlAt_unrooted_cases
