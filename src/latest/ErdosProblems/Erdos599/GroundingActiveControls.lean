/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedRouteCore
import ErdosProblems.Erdos599.GroundingPathPrefix
import ErdosProblems.Erdos599.AlternatingMacroChain

/-!
# Active controls in the simultaneous grounding switch

The source's recursive condition (a) is a condition on *grounded ladder
components*, not merely on the auxiliary supports of the chosen finite
paths.  A later control which already lies on a grounded component exposed
by an earlier active route is already covered and is not switched a second
time.  Otherwise its selected route misses every earlier active grounded
component, including at its endpoint.

This file implements that greedy active-control recursion.  It is kept
strictly before the erased decoder so that all global erased route unions
can be indexed by `ActiveControlRequest` without an import cycle.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingErasedDecode

open DirectedPath Stationary
open PopularAuxiliary PopularGroundingBridge
open GroundingSimultaneousDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- The orientation of an edge of a directed path agrees with the intrinsic
order on that path.  This is exported here because the ordered-contact
activity test needs the fact for represented edge gadgets. -/
theorem GroundingCut.beforeEq_of_mem_edgeSet {P : Gamma.DPath} {x y : V}
    (hxy : (x, y) ∈ P.edgeSet) : GroundingCut.BeforeEq P x y := by
  cases P with
  | inl p =>
      obtain ⟨n, hn, hnx, hny⟩ :=
        DirectedPath.Walk.exists_adjacent_getElem_of_mem_edgeSet p.walk hxy
      exact ⟨n, n + 1, ⟨by omega, hnx⟩, ⟨hn, hny⟩, by omega⟩
  | inr r =>
      obtain ⟨n, hn⟩ := hxy
      exact ⟨n, n + 1, (congrArg Prod.fst hn).symm,
        (congrArg Prod.snd hn).symm, by omega⟩

/-- The source's untagged control set `C tilde`. -/
abbrev ControlRequest (L : PopularAuxiliary.Input Gamma I) (C : Set L.LV) :=
  {x : V // x ∈ controlVertices L C}

/-- Choose one tagged auxiliary representative of each untagged control. -/
noncomputable def chosenRequest
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV}
    (c : ControlRequest L C) : Request L C :=
  Classical.choose c.2

@[simp] theorem requestVertex_chosenRequest
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV}
    (c : ControlRequest L C) : requestVertex (chosenRequest c) = c.1 :=
  Classical.choose_spec c.2

theorem chosenRequest_injective
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV} :
    Function.Injective (@chosenRequest V I Gamma L C) := by
  intro c d hcd
  apply Subtype.ext
  rw [← requestVertex_chosenRequest c, ← requestVertex_chosenRequest d, hcd]

/-- The inherited request chronology on untagged controls. -/
def controlRank
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) :
    ControlRequest L S.cut ↪ Stationary.Below kappa :=
  ⟨fun c ↦ GroundingAssembly.requestRank U S (chosenRequest c), by
    intro c d hcd
    exact chosenRequest_injective
      ((GroundingAssembly.requestRank U S).injective hcd)⟩

/-! ## Source-style pruning of decoded forward links -/

/-- A step along a decoded forward link is retained precisely while its
tail is outside the final boundary `BB`.  Consequently a retained prefix
may enter its first boundary vertex, but it cannot leave it. -/
def retainedForwardLinkStep
    {L : PopularAuxiliary.Input Gamma I} (C : Set L.LV)
    (l : Alternating.Link Gamma.graph) (x y : V) : Prop :=
  (x, y) ∈ l.path.edgeSet ∧ x ∉ GroundingCut.BB L C

/-- The vertices of the source-side prefix of every forward link.  The
reachability formulation is insensitive to the concrete finite-path
indexing and makes the first-boundary stopping property literal. -/
def retainedForwardVertices
    {L : PopularAuxiliary.Input Gamma I} (C : Set L.LV)
    (Q : Alternating.AltPath Gamma.graph) : Set V :=
  {x | ∃ l ∈ Q.links, l.direction = .forward ∧
    Relation.ReflTransGen (retainedForwardLinkStep C l) l.path.start x}

/-- The edges of the retained source-side forward prefixes.  An edge is
kept only if its tail is already reachable inside its own retained link
prefix. -/
def retainedForwardEdges
    {L : PopularAuxiliary.Input Gamma I} (C : Set L.LV)
    (Q : Alternating.AltPath Gamma.graph) : Set (V × V) :=
  {e | ∃ l ∈ Q.links, l.direction = .forward ∧
    e ∈ l.path.edgeSet ∧
    e.1 ∉ GroundingCut.BB L C ∧
    Relation.ReflTransGen (retainedForwardLinkStep C l)
      l.path.start e.1}

theorem retainedForwardEdges_subset_directionEdges
    {L : PopularAuxiliary.Input Gamma I} (C : Set L.LV)
    (Q : Alternating.AltPath Gamma.graph) :
    retainedForwardEdges C Q ⊆ Q.directionEdges .forward := by
  rintro e ⟨l, hl, hdir, he, _hold, _hreaches⟩
  simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion]
  exact ⟨l, hl, hdir, he⟩

private theorem retainedForwardLinkStep_reaches_support
    {L : PopularAuxiliary.Input Gamma I} (C : Set L.LV)
    (l : Alternating.Link Gamma.graph) {x : V}
    (hx : Relation.ReflTransGen (retainedForwardLinkStep C l)
      l.path.start x) :
    x ∈ l.path.support := by
  induction hx with
  | refl => exact l.path.start_mem_support
  | tail hab hbc _ih =>
      exact l.path.edgeSet_subset_support_prod hbc.1 |>.2

theorem retainedForwardVertices_subset_directionVertices
    {L : PopularAuxiliary.Input Gamma I} (C : Set L.LV)
    (Q : Alternating.AltPath Gamma.graph) :
    retainedForwardVertices C Q ⊆ Q.directionVertices .forward := by
  rintro x ⟨l, hl, hdir, hx⟩
  simp only [Alternating.AltPath.directionVertices, Set.mem_iUnion]
  exact ⟨l, hl, hdir,
    retainedForwardLinkStep_reaches_support C l hx⟩

/-- Both endpoints of every retained edge belong to the same retained
forward carrier. -/
theorem retainedForwardEdge_endpoints
    {L : PopularAuxiliary.Input Gamma I} (C : Set L.LV)
    (Q : Alternating.AltPath Gamma.graph) {e : V × V}
    (he : e ∈ retainedForwardEdges C Q) :
    e.1 ∈ retainedForwardVertices C Q ∧
      e.2 ∈ retainedForwardVertices C Q := by
  rcases he with ⟨l, hl, hdir, he, hold, hreach⟩
  constructor
  · exact ⟨l, hl, hdir, hreach⟩
  · exact ⟨l, hl, hdir,
      hreach.tail ⟨he, hold⟩⟩

/-- Every retained carrier point is reachable from its link start through
retained edges of that same alternating path. -/
theorem retainedForwardVertices_reachable
    {L : PopularAuxiliary.Input Gamma I} (C : Set L.LV)
    (Q : Alternating.AltPath Gamma.graph) {x : V}
    (hx : x ∈ retainedForwardVertices C Q) :
    ∃ l ∈ Q.links, l.direction = .forward ∧
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ retainedForwardEdges C Q)
        l.path.start x := by
  rcases hx with ⟨l, hl, hdir, hx⟩
  refine ⟨l, hl, hdir, ?_⟩
  induction hx with
  | refl => exact .refl
  | tail hab hbc ih =>
      exact ih.tail ⟨l, hl, hdir, hbc.1, hbc.2, hab⟩

/-- No retained forward prefix has an outgoing edge at a boundary point. -/
theorem boundary_noOutgoing_retainedForwardEdges
    {L : PopularAuxiliary.Input Gamma I} (C : Set L.LV)
    (Q : Alternating.AltPath Gamma.graph) {b : V}
    (hb : b ∈ GroundingCut.BB L C) :
    ¬ Alternating.HasOutgoing (retainedForwardEdges C Q) b := by
  rintro ⟨y, l, _hl, _hdir, _he, hbNot, _hreach⟩
  exact hbNot hb

/-- Compatibility specialization: every old request belongs to `CV ⊆ BB`. -/
theorem oldRequest_noOutgoing_retainedForwardEdges
    {L : PopularAuxiliary.Input Gamma I} (C : Set L.LV)
    (Q : Alternating.AltPath Gamma.graph) (r : oldRequests L C) :
    ¬ Alternating.HasOutgoing (retainedForwardEdges C Q) r.1 := by
  apply boundary_noOutgoing_retainedForwardEdges C Q
  exact GroundingCut.CV_subset_BB L C r.2.1

/-- A later control is genuinely absorbed by a limiting-ladder component
exposed by an earlier selected route only when there is an *actual forward*
contact of the chronologically loop-erased earlier route weakly before the
later control.  This condition is uniform for grounded and hanging ladder
components: an exposed grounded component may be met solely by a deleted
backward run, which does not by itself root the post-switch component.
Backward-run interiors are therefore deliberately excluded, and a contact
strictly downstream of the later control is excluded as well. -/
def HitsEarlierExposedComponent
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (earlier later : ControlRequest L S.cut) : Prop :=
  ∃ Y : Gamma.DPath,
    Y ∈ exposedLadderPaths L
      (strongSelectedPath U S K (chosenRequest earlier)) ∧
    later.1 ∈ Y.support ∧
      ∃ x ∈ retainedForwardVertices (L := L) S.cut
          (selectedErasedCompression U S K
            (chosenRequest earlier)).path,
        x ∈ Y.support ∧ GroundingCut.BeforeEq Y x later.1

/-- The older grounded-only hit predicate, retained as a useful
specialization of `HitsEarlierExposedComponent`. -/
def HitsEarlierGroundedComponent
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (earlier later : ControlRequest L S.cut) : Prop :=
  ∃ Y : Gamma.DPath,
    Y ∈ exposedLadderPaths L
      (strongSelectedPath U S K (chosenRequest earlier)) ∧
    IsGroundedPath Gamma Y ∧ later.1 ∈ Y.support

/-- Greedy activity, recursively along the inherited request rank.  A
control is active exactly when no earlier active control exposes a limiting
component containing it. -/
noncomputable def IsActiveControl
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    ControlRequest L S.cut → Prop :=
  WellFounded.fix
    (InvImage.wf (controlRank U S) wellFounded_lt)
    (fun c previous ↦
      ∀ d (hd : controlRank U S d < controlRank U S c),
        previous d hd → ¬ HitsEarlierExposedComponent U S K d c)

theorem isActiveControl_iff
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (c : ControlRequest L S.cut) :
    IsActiveControl U S K c ↔
      ∀ d (hd : controlRank U S d < controlRank U S c),
        IsActiveControl U S K d →
          ¬ HitsEarlierExposedComponent U S K d c := by
  unfold IsActiveControl
  rw [WellFounded.fix_eq
    (InvImage.wf (controlRank U S) wellFounded_lt)
    (fun c previous ↦
      ∀ d (hd : controlRank U S d < controlRank U S c),
        previous d hd → ¬ HitsEarlierExposedComponent U S K d c) c]

/-- The controls actually used by the simultaneous switch. -/
abbrev ActiveControlRequest
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :=
  {c : ControlRequest L S.cut // IsActiveControl U S K c}

/-- An inactive control is already located on a component exposed by a
strictly earlier active route. -/
theorem exists_active_earlier_of_not_active
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (c : ControlRequest L S.cut)
    (hc : ¬ IsActiveControl U S K c) :
    ∃ d : ControlRequest L S.cut,
      controlRank U S d < controlRank U S c ∧
      IsActiveControl U S K d ∧
      HitsEarlierExposedComponent U S K d c := by
  rw [isActiveControl_iff] at hc
  push_neg at hc
  obtain ⟨d, hd, hactive, hhit⟩ := hc
  exact ⟨d, hd, hactive, hhit⟩

/-- Distinct active controls are chronologically component-compatible in
the direction needed by source condition (a). -/
theorem active_not_hits_of_rank_lt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    {c d : ControlRequest L S.cut}
    (hc : IsActiveControl U S K c)
    (hd : IsActiveControl U S K d)
    (hcd : controlRank U S c < controlRank U S d) :
    ¬ HitsEarlierExposedComponent U S K c d :=
  (isActiveControl_iff U S K d).1 hd c hcd hc

/-! ## Flattened component and trace interfaces -/

/-- Membership of a request gadget in the trace of a ladder path forces
the untagged control vertex to lie on that path.  For an edge request this
uses the head endpoint of the represented edge. -/
theorem requestVertex_mem_support_of_requestAuxVertex_mem_ladderTrace
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV}
    (r : Request L C) (Y : Gamma.DPath)
    (h : requestAuxVertex r ∈ PopularSwitching.ladderTrace L Y) :
    requestVertex r ∈ Y.support := by
  rcases h with h | h
  · rcases h with ⟨x, hxY, hx⟩
    cases r with
    | inl z =>
        change z.1 ∈ Y.support
        have hzx : z.1 = x :=
          (PopularAuxiliary.Input.LambdaVertex.old.inj hx).symm
        exact hzx ▸ hxY
    | inr e => cases hx
  · rcases h with ⟨e, heY, he⟩
    cases r with
    | inl z => cases he
    | inr f =>
        have hhead : e.2 = f.1.2 :=
          (PopularAuxiliary.Input.LambdaVertex.edge.inj he).2
        change f.1.2 ∈ Y.support
        exact hhead ▸ (Y.edgeSet_subset_support_prod heY).2

/-- Flatten the inactive-control witness to the actual ladder component
which already contains the skipped control. -/
theorem exists_active_earlier_component_of_not_active
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (c : ControlRequest L S.cut)
    (hc : ¬ IsActiveControl U S K c) :
    ∃ d : ControlRequest L S.cut,
      controlRank U S d < controlRank U S c ∧
      IsActiveControl U S K d ∧
      ∃ Y : Gamma.DPath,
        Y ∈ exposedLadderPaths L
          (strongSelectedPath U S K (chosenRequest d)) ∧
        c.1 ∈ Y.support ∧
          ∃ x ∈ retainedForwardVertices (L := L) S.cut
              (selectedErasedCompression U S K
                (chosenRequest d)).path,
            x ∈ Y.support ∧ GroundingCut.BeforeEq Y x c.1 := by
  obtain ⟨d, hdc, hd, Y, hY, hcY, hground⟩ :=
    exists_active_earlier_of_not_active U S K c hc
  exact ⟨d, hdc, hd, Y, hY, hcY, hground⟩

/-- Subtype-packaged form of the inactive-control absorption witness.  This
is the interface used by the final switched-relation geometry: the owner is
already known to occur in the active route union, and the contact clause
retains the order needed to select the correct side of a switched ladder
component. -/
theorem exists_active_absorber_of_not_active
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (c : ControlRequest L S.cut)
    (hc : ¬ IsActiveControl U S K c) :
    ∃ d : ActiveControlRequest U S K,
      controlRank U S d.1 < controlRank U S c ∧
      ∃ Y : Gamma.DPath,
        Y ∈ exposedLadderPaths L
          (strongSelectedPath U S K (chosenRequest d.1)) ∧
        c.1 ∈ Y.support ∧
          ∃ x ∈ retainedForwardVertices (L := L) S.cut
              (selectedErasedCompression U S K
                (chosenRequest d.1)).path,
            x ∈ Y.support ∧ GroundingCut.BeforeEq Y x c.1 := by
  obtain ⟨d, hdc, hd, Y, hY, hcY, hcontact⟩ :=
    exists_active_earlier_component_of_not_active U S K c hc
  exact ⟨⟨d, hd⟩, hdc, Y, hY, hcY, hcontact⟩

/-! ## Boundary-parametric active controls

The final grounding construction first chooses a minimal separating subset
`T ⊆ BB`.  The selected routes must therefore stop at `T`, rather than at
all of `BB`; points of `BB \ T` remain pass-through points.  The definitions
below are the exact boundary-parametric counterparts of the compatibility
API above. -/

def retainedForwardLinkStepAt (T : Set V)
    (l : Alternating.Link Gamma.graph) (x y : V) : Prop :=
  (x, y) ∈ l.path.edgeSet ∧ x ∉ T

def retainedForwardVerticesAt (T : Set V)
    (Q : Alternating.AltPath Gamma.graph) : Set V :=
  {x | ∃ l ∈ Q.links, l.direction = .forward ∧
    Relation.ReflTransGen (retainedForwardLinkStepAt T l) l.path.start x}

def retainedForwardEdgesAt (T : Set V)
    (Q : Alternating.AltPath Gamma.graph) : Set (V × V) :=
  {e | ∃ l ∈ Q.links, l.direction = .forward ∧
    e ∈ l.path.edgeSet ∧ e.1 ∉ T ∧
    Relation.ReflTransGen (retainedForwardLinkStepAt T l)
      l.path.start e.1}

private theorem retainedForwardLinkStepAt_reaches_support
    (T : Set V) (l : Alternating.Link Gamma.graph) {x : V}
    (hx : Relation.ReflTransGen (retainedForwardLinkStepAt T l)
      l.path.start x) : x ∈ l.path.support := by
  induction hx with
  | refl => exact l.path.start_mem_support
  | tail _hab hbc _ih =>
      exact l.path.edgeSet_subset_support_prod hbc.1 |>.2

theorem retainedForwardVerticesAt_subset_directionVertices
    (T : Set V) (Q : Alternating.AltPath Gamma.graph) :
    retainedForwardVerticesAt T Q ⊆ Q.directionVertices .forward := by
  rintro x ⟨l, hl, hdir, hx⟩
  simp only [Alternating.AltPath.directionVertices, Set.mem_iUnion]
  exact ⟨l, hl, hdir,
    retainedForwardLinkStepAt_reaches_support T l hx⟩

theorem retainedForwardEdgesAt_subset_directionEdges
    (T : Set V) (Q : Alternating.AltPath Gamma.graph) :
    retainedForwardEdgesAt T Q ⊆ Q.directionEdges .forward := by
  rintro e ⟨l, hl, hdir, he, _hold, _hreaches⟩
  simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion]
  exact ⟨l, hl, hdir, he⟩

theorem retainedForwardEdgeAt_endpoints
    (T : Set V) (Q : Alternating.AltPath Gamma.graph) {e : V × V}
    (he : e ∈ retainedForwardEdgesAt T Q) :
    e.1 ∈ retainedForwardVerticesAt T Q ∧
      e.2 ∈ retainedForwardVerticesAt T Q := by
  rcases he with ⟨l, hl, hdir, he, hold, hreach⟩
  exact ⟨⟨l, hl, hdir, hreach⟩,
    ⟨l, hl, hdir, hreach.tail ⟨he, hold⟩⟩⟩

theorem retainedForwardVerticesAt_reachable
    (T : Set V) (Q : Alternating.AltPath Gamma.graph) {x : V}
    (hx : x ∈ retainedForwardVerticesAt T Q) :
    ∃ l ∈ Q.links, l.direction = .forward ∧
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ retainedForwardEdgesAt T Q)
        l.path.start x := by
  rcases hx with ⟨l, hl, hdir, hx⟩
  refine ⟨l, hl, hdir, ?_⟩
  induction hx with
  | refl => exact .refl
  | tail hab hbc ih =>
      exact ih.tail ⟨l, hl, hdir, hbc.1, hbc.2, hab⟩

theorem boundary_noOutgoing_retainedForwardEdgesAt
    (T : Set V) (Q : Alternating.AltPath Gamma.graph) {t : V}
    (ht : t ∈ T) :
    ¬ Alternating.HasOutgoing (retainedForwardEdgesAt T Q) t := by
  rintro ⟨y, l, _hl, _hdir, _he, htNot, _hreach⟩
  exact htNot ht

/-- With no stopping frontier, the retained carrier is the whole forward
direction carrier of the alternating path. -/
theorem retainedForwardVerticesAt_empty
    (Q : Alternating.AltPath Gamma.graph) :
    retainedForwardVerticesAt (∅ : Set V) Q =
      Q.directionVertices .forward := by
  apply Set.Subset.antisymm
  · exact retainedForwardVerticesAt_subset_directionVertices ∅ Q
  · intro x hx
    simp only [Alternating.AltPath.directionVertices,
      Set.mem_iUnion] at hx
    obtain ⟨l, hl, hdir, hxSupport⟩ := hx
    obtain ⟨q, hqStart, hqFinish, _hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix
        (.inl l.path : Gamma.DPath) hxSupport
    have hqStart' : q.start = l.path.start := by
      simpa [DirectedPath.Path.initial] using hqStart
    refine ⟨l, hl, hdir, ?_⟩
    have hreach : Relation.ReflTransGen
        (retainedForwardLinkStepAt (∅ : Set V) l) q.start q.finish :=
      Relation.ReflTransGen.mono
        (r := fun u v ↦ (u, v) ∈ q.edgeSet)
        (p := retainedForwardLinkStepAt (∅ : Set V) l)
        (fun _ _ he ↦ ⟨hqEdges he, by simp⟩) _ _
        (_root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet q.walk)
    simpa only [hqStart', hqFinish] using hreach

/-- With no stopping frontier, every forward edge is retained. -/
theorem retainedForwardEdgesAt_empty
    (Q : Alternating.AltPath Gamma.graph) :
    retainedForwardEdgesAt (∅ : Set V) Q =
      Q.directionEdges .forward := by
  apply Set.Subset.antisymm
  · exact retainedForwardEdgesAt_subset_directionEdges ∅ Q
  · intro e he
    simp only [Alternating.AltPath.directionEdges,
      Set.mem_iUnion] at he
    obtain ⟨l, hl, hdir, heEdge⟩ := he
    have heTail : e.1 ∈ l.path.support :=
      (l.path.edgeSet_subset_support_prod heEdge).1
    obtain ⟨q, hqStart, hqFinish, _hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix
        (.inl l.path : Gamma.DPath) heTail
    have hqStart' : q.start = l.path.start := by
      simpa [DirectedPath.Path.initial] using hqStart
    have hreach : Relation.ReflTransGen
        (retainedForwardLinkStepAt (∅ : Set V) l) l.path.start e.1 := by
      have hqReach : Relation.ReflTransGen
          (retainedForwardLinkStepAt (∅ : Set V) l) q.start q.finish :=
        Relation.ReflTransGen.mono
          (r := fun u v ↦ (u, v) ∈ q.edgeSet)
          (p := retainedForwardLinkStepAt (∅ : Set V) l)
          (fun _ _ he ↦ ⟨hqEdges he, by simp⟩) _ _
          (_root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet q.walk)
      simpa only [hqStart', hqFinish] using hqReach
    exact ⟨l, hl, hdir, heEdge, by simp, hreach⟩

def HitsEarlierExposedComponentAt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V)
    (earlier later : ControlRequest L S.cut) : Prop :=
  ∃ Y : Gamma.DPath,
    Y ∈ exposedLadderPaths L
      (strongSelectedPath U S K (chosenRequest earlier)) ∧
    later.1 ∈ Y.support ∧
      ∃ x ∈ retainedForwardVerticesAt T
          (selectedErasedCompression U S K
            (chosenRequest earlier)).path,
        x ∈ Y.support ∧ GroundingCut.BeforeEq Y x later.1

noncomputable def IsActiveControlAt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V) : ControlRequest L S.cut → Prop :=
  WellFounded.fix
    (InvImage.wf (controlRank U S) wellFounded_lt)
    (fun c previous ↦
      ∀ d (hd : controlRank U S d < controlRank U S c),
        previous d hd → ¬ HitsEarlierExposedComponentAt U S K T d c)

theorem isActiveControlAt_iff
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V) (c : ControlRequest L S.cut) :
    IsActiveControlAt U S K T c ↔
      ∀ d (hd : controlRank U S d < controlRank U S c),
        IsActiveControlAt U S K T d →
          ¬ HitsEarlierExposedComponentAt U S K T d c := by
  unfold IsActiveControlAt
  rw [WellFounded.fix_eq
    (InvImage.wf (controlRank U S) wellFounded_lt)
    (fun c previous ↦
      ∀ d (hd : controlRank U S d < controlRank U S c),
        previous d hd → ¬ HitsEarlierExposedComponentAt U S K T d c) c]

abbrev ActiveControlRequestAt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (T : Set V) :=
  {c : ControlRequest L S.cut // IsActiveControlAt U S K T c}

theorem activeAt_not_hits_of_rank_lt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V) {c d : ControlRequest L S.cut}
    (hc : IsActiveControlAt U S K T c)
    (hd : IsActiveControlAt U S K T d)
    (hcd : controlRank U S c < controlRank U S d) :
    ¬ HitsEarlierExposedComponentAt U S K T c d :=
  (isActiveControlAt_iff U S K T d).1 hd c hcd hc

/-- An inactive control for a chosen stopping frontier is already absorbed
by a strictly earlier active route. -/
theorem exists_active_earlierAt_of_not_active
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V) (c : ControlRequest L S.cut)
    (hc : ¬ IsActiveControlAt U S K T c) :
    ∃ d : ControlRequest L S.cut,
      controlRank U S d < controlRank U S c ∧
      IsActiveControlAt U S K T d ∧
      HitsEarlierExposedComponentAt U S K T d c := by
  rw [isActiveControlAt_iff] at hc
  push_neg at hc
  obtain ⟨d, hd, hactive, hhit⟩ := hc
  exact ⟨d, hd, hactive, hhit⟩

/-- Subtype-packaged ordered retained-contact witness for an inactive
control, relative to an arbitrary stopping frontier `T`. -/
theorem exists_active_absorberAt_of_not_active
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V) (c : ControlRequest L S.cut)
    (hc : ¬ IsActiveControlAt U S K T c) :
    ∃ d : ActiveControlRequestAt U S K T,
      controlRank U S d.1 < controlRank U S c ∧
      ∃ Y : Gamma.DPath,
        Y ∈ exposedLadderPaths L
          (strongSelectedPath U S K (chosenRequest d.1)) ∧
        c.1 ∈ Y.support ∧
          ∃ x ∈ retainedForwardVerticesAt T
              (selectedErasedCompression U S K
                (chosenRequest d.1)).path,
            x ∈ Y.support ∧ GroundingCut.BeforeEq Y x c.1 := by
  obtain ⟨d, hdc, hd, Y, hY, hcY, hcontact⟩ :=
    exists_active_earlierAt_of_not_active U S K T c hc
  exact ⟨⟨d, hd⟩, hdc, Y, hY, hcY, hcontact⟩

end GroundingErasedDecode
end Erdos599
