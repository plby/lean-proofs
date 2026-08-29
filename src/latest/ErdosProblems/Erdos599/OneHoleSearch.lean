/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OneHoleReroute

/-!
# The residual search for the one-hole augmentation theorem

This file isolates the residual directed relation used in the proof of the
one-hole principle.  An unused edge is traversed forwards and an edge of the
old warp is traversed backwards.  Reachability always starts in an uncovered
source.  The definitions are intentionally independent of any enumeration of
the vertices or edges of the ambient (possibly uncountable) graph.
-/

namespace Erdos599
namespace DWeb

open Set DirectedPath
open Alternating

universe u

variable {V : Type u}

/-- The residual relation of a path family.  Old family edges are available
backwards; every edge not used by the family is available forwards. -/
def OneHoleResidualStep (G : DWeb V) (J : Set G.DPath) (x y : V) : Prop :=
  (G.graph.Adj x y ∧ (x, y) ∉ familyEdges J) ∨
    (y, x) ∈ familyEdges J

/-- Vertices reached by a finite residual chain from an uncovered source. -/
def OneHoleReachable (G : DWeb V) (J : Set G.DPath) : Set V :=
  {x | ∃ a ∈ G.source \ G.initialSet J,
    Relation.ReflTransGen (G.OneHoleResidualStep J) a x}

theorem oneHole_sourceGap_subset_reachable (G : DWeb V)
    (J : Set G.DPath) :
    G.source \ G.initialSet J ⊆ G.OneHoleReachable J := by
  intro a ha
  exact ⟨a, ha, Relation.ReflTransGen.refl⟩

theorem oneHole_reachable_step (G : DWeb V) (J : Set G.DPath)
    {x y : V} (hx : x ∈ G.OneHoleReachable J)
    (hxy : G.OneHoleResidualStep J x y) :
    y ∈ G.OneHoleReachable J := by
  rcases hx with ⟨a, ha, hax⟩
  exact ⟨a, ha, hax.tail hxy⟩

theorem oneHole_reachable_forward_of_not_familyEdge
    (G : DWeb V) (J : Set G.DPath) {x y : V}
    (hx : x ∈ G.OneHoleReachable J) (hxy : G.graph.Adj x y)
    (hnot : (x, y) ∉ familyEdges J) :
    y ∈ G.OneHoleReachable J :=
  G.oneHole_reachable_step J hx (Or.inl ⟨hxy, hnot⟩)

theorem oneHole_reachable_backward_of_familyEdge
    (G : DWeb V) (J : Set G.DPath) {x y : V}
    (hy : y ∈ G.OneHoleReachable J)
    (hxy : (x, y) ∈ familyEdges J) :
    x ∈ G.OneHoleReachable J :=
  G.oneHole_reachable_step J hy (Or.inr hxy)

/-- Any edge leaving the residual reachable set is necessarily an old
family edge.  This is the first half of the last-hit boundary argument. -/
theorem oneHole_familyEdge_of_reachable_edge_not_reachable
    (G : DWeb V) (J : Set G.DPath) {x y : V}
    (hx : x ∈ G.OneHoleReachable J) (hxy : G.graph.Adj x y)
    (hy : y ∉ G.OneHoleReachable J) :
    (x, y) ∈ familyEdges J := by
  by_contra hnot
  exact hy (G.oneHole_reachable_forward_of_not_familyEdge J hx hxy hnot)

/-! ## Contact-marked residual states

The raw relation above is useful for elementary boundary calculations, but
it is deliberately not used for augmenting-trace extraction: a raw forward
walk may cross a vertex of `J` without cancelling the occupied vertex.  The
following two-state relation records such a contact.  From a pending contact
the search must first cancel an incoming `J`-edge before it is again allowed
to use a forward edge.  This is the vertex-capacity residual network written
without introducing a duplicated ambient graph.
-/

/-- A ready residual vertex, or a newly reached occupied vertex whose
incoming family edge still has to be cancelled. -/
inductive OneHoleResidualState (V : Type u)
  | ready : V → OneHoleResidualState V
  | pending : V → OneHoleResidualState V
  deriving DecidableEq

namespace OneHoleResidualState

def vertex : OneHoleResidualState V → V
  | .ready x => x
  | .pending x => x

@[simp] theorem vertex_ready (x : V) : (ready x : OneHoleResidualState V).vertex = x := rfl
@[simp] theorem vertex_pending (x : V) : (pending x : OneHoleResidualState V).vertex = x := rfl

end OneHoleResidualState

/-- Contact-normalized residual transition relation.

* unused edges ending outside the old warp remain ready;
* unused edges ending on the old warp create a pending contact;
* a pending contact must cancel its incoming family edge;
* after one cancellation, further family edges may be traversed backwards.
-/
def OneHoleMarkedStep (G : DWeb V) (J : Set G.DPath) :
    OneHoleResidualState V → OneHoleResidualState V → Prop
  | .ready x, .ready y =>
      (G.graph.Adj x y ∧ (x, y) ∉ familyEdges J ∧
          y ∉ G.vertexSet J) ∨
        (y, x) ∈ familyEdges J
  | .ready x, .pending y =>
      G.graph.Adj x y ∧ (x, y) ∉ familyEdges J ∧ y ∈ G.vertexSet J
  | .pending y, .ready x => (x, y) ∈ familyEdges J
  | .pending _, .pending _ => False

/-- Reachable marked states, always starting ready at an uncovered source. -/
def OneHoleMarkedStateReachable (G : DWeb V) (J : Set G.DPath) :
    Set (OneHoleResidualState V) :=
  {s | ∃ a ∈ G.source \ G.initialSet J,
    Relation.ReflTransGen (G.OneHoleMarkedStep J)
      (.ready a) s}

/-- The vertex projection of the marked reachable states. -/
def OneHoleMarkedReachable (G : DWeb V) (J : Set G.DPath) : Set V :=
  OneHoleResidualState.vertex '' G.OneHoleMarkedStateReachable J

/-- Ready vertices form the active frontier of the normalized search. -/
def OneHoleReadyReachable (G : DWeb V) (J : Set G.DPath) : Set V :=
  {x | (OneHoleResidualState.ready x) ∈
    G.OneHoleMarkedStateReachable J}

theorem oneHole_sourceGap_subset_readyReachable (G : DWeb V)
    (J : Set G.DPath) :
    G.source \ G.initialSet J ⊆ G.OneHoleReadyReachable J := by
  intro a ha
  exact ⟨a, ha, Relation.ReflTransGen.refl⟩

theorem oneHole_readyReachable_subset_markedReachable (G : DWeb V)
    (J : Set G.DPath) :
    G.OneHoleReadyReachable J ⊆ G.OneHoleMarkedReachable J := by
  intro x hx
  exact ⟨.ready x, hx, rfl⟩

theorem oneHole_markedState_step (G : DWeb V) (J : Set G.DPath)
    {s t : OneHoleResidualState V}
    (hs : s ∈ G.OneHoleMarkedStateReachable J)
    (hst : G.OneHoleMarkedStep J s t) :
    t ∈ G.OneHoleMarkedStateReachable J := by
  rcases hs with ⟨a, ha, has⟩
  exact ⟨a, ha, has.tail hst⟩

theorem oneHole_ready_forward (G : DWeb V) (J : Set G.DPath)
    {x y : V} (hx : x ∈ G.OneHoleReadyReachable J)
    (hxy : G.graph.Adj x y) (hnot : (x, y) ∉ familyEdges J) :
    y ∈ G.OneHoleMarkedReachable J := by
  by_cases hyJ : y ∈ G.vertexSet J
  · have hpending : (.pending y : OneHoleResidualState V) ∈
        G.OneHoleMarkedStateReachable J :=
      G.oneHole_markedState_step J hx ⟨hxy, hnot, hyJ⟩
    exact ⟨.pending y, hpending, rfl⟩
  · have hready : (.ready y : OneHoleResidualState V) ∈
        G.OneHoleMarkedStateReachable J :=
      G.oneHole_markedState_step J hx (Or.inl ⟨hxy, hnot, hyJ⟩)
    exact ⟨.ready y, hready, rfl⟩

theorem oneHole_ready_backward (G : DWeb V) (J : Set G.DPath)
    {x y : V} (hy : y ∈ G.OneHoleReadyReachable J)
    (hxy : (x, y) ∈ familyEdges J) :
    x ∈ G.OneHoleReadyReachable J := by
  exact G.oneHole_markedState_step J hy (Or.inr hxy)

theorem oneHole_pending_cancel (G : DWeb V) (J : Set G.DPath)
    {x y : V}
    (hy : (.pending y : OneHoleResidualState V) ∈
      G.OneHoleMarkedStateReachable J)
    (hxy : (x, y) ∈ familyEdges J) :
    x ∈ G.OneHoleReadyReachable J := by
  exact G.oneHole_markedState_step J hy hxy

private theorem oneHole_markedStep_pending_mem
    (G : DWeb V) (J : Set G.DPath) {s : OneHoleResidualState V} {x : V}
    (h : G.OneHoleMarkedStep J s (.pending x)) :
    x ∈ G.vertexSet J := by
  cases s with
  | ready y => exact h.2.2
  | pending y => exact h.elim

theorem oneHole_targetGap_marked_iff_ready
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsCleanFiniteWarp J)
    {b : V} (hb : b ∈ G.target \ G.terminalFrontier J) :
    b ∈ G.OneHoleMarkedReachable J ↔
      b ∈ G.OneHoleReadyReachable J := by
  constructor
  · rintro ⟨s, hs, hsv⟩
    cases s with
    | ready x =>
        have hxb : x = b := hsv
        subst b
        change (.ready x : OneHoleResidualState V) ∈
          G.OneHoleMarkedStateReachable J
        exact hs
    | pending x =>
        have hxb : x = b := hsv
        subst b
        have hxJ : x ∈ G.vertexSet J := by
          rcases hs with ⟨a, ha, hax⟩
          cases hax with
          | tail _ hstep =>
              exact oneHole_markedStep_pending_mem G J hstep
        exact False.elim
          (Set.disjoint_left.1 hJ.target_gap_disjoint_vertexSet hb hxJ)
  · intro hbReady
    exact ⟨.ready b, hbReady, rfl⟩

/-- The exact finite-chain augmentation statement needed by the residual
proof.  A finite marked route acts on the old warp by a finite
vertex-capacity symmetric difference.  In general this operation can split
across several paths and therefore need not be representable by one
compatible alternating trace; its invariant output is the resulting
one-point augmentation itself. -/
def OneHoleMarkedAugmentation (V : Type u) : Prop :=
  ∀ (G : DWeb V) (J : Set G.DPath), (hJ : G.IsCleanFiniteWarp J) →
    ∀ b ∈ G.target \ G.terminalFrontier J,
      b ∈ G.OneHoleReadyReachable J →
        ∃ Jplus, G.IsOnePointAugmentation J Jplus

/-- A vertex uncovered on both sides gives the one-point augmentation by
adjoining its trivial path. -/
theorem exists_onePointAugmentation_of_common_gap
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsCleanFiniteWarp J)
    {a : V} (ha : a ∈ G.source \ G.initialSet J)
    (hb : a ∈ G.target \ G.terminalFrontier J) :
    ∃ Jplus, G.IsOnePointAugmentation J Jplus := by
  let q := FinitePath.trivial G.graph a
  let Jplus : Set G.DPath := insert (.inl q : G.DPath) J
  refine ⟨Jplus, a, ha, a, hb, ?_, ?_, ?_, ?_⟩
  · apply DWeb.IsWarp.insert_finite_of_disjoint G hJ.isWarp q
    rw [Set.disjoint_left]
    intro x hx hxJ
    have hxa : x = a := by simpa [q] using hx
    subst x
    exact Set.disjoint_left.1 hJ.source_gap_disjoint_vertexSet ha hxJ
  · exact G.hasFiniteCharacter_insert_finite hJ.hasFiniteCharacter q
  · exact G.initialSet_insert_finite J q
  · exact G.terminalFrontier_insert_finite J q

/-- Unfolding the marked augmentation statement at a reached target. -/
theorem exists_onePointAugmentation_of_markedAugmentation
    (haugment : OneHoleMarkedAugmentation V)
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsCleanFiniteWarp J)
    {b : V} (hb : b ∈ G.target \ G.terminalFrontier J)
    (hreach : b ∈ G.OneHoleReadyReachable J) :
    ∃ Jplus, G.IsOnePointAugmentation J Jplus :=
  haugment G J hJ b hb hreach

/-- If a marked residual search reaches an uncovered target, it is already
in the augmenting branch. -/
theorem oneHole_augmentation_of_marked_target
    (haugment : OneHoleMarkedAugmentation V)
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsCleanFiniteWarp J)
    {b : V} (hb : b ∈ G.target \ G.terminalFrontier J)
    (hreach : b ∈ G.OneHoleMarkedReachable J) :
    ∃ Jplus, G.IsOnePointAugmentation J Jplus := by
  exact exists_onePointAugmentation_of_markedAugmentation
    haugment G hJ hb ((G.oneHole_targetGap_marked_iff_ready hJ hb).1 hreach)

end DWeb
end Erdos599
