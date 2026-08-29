/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedReachableWholeSourceDeletedHead

/-!
# Retargeting along an ambient source prefix

An ambient source prefix need not lie on an exposed limiting-ladder parent.
Consequently its first missing edge cannot be fed into the selected-owner
recursion.  There is nevertheless a canonical local repair: remove every old
edge incident with the prefix and insert the directed edges of the prefix.

The resulting relation is still contained in the ambient digraph and is
bi-unique.  It contains the whole prefix, has no incoming edge at its initial
vertex and no outgoing edge at its terminal vertex, and therefore roots the
displayed boundary point.  The price is exact and local: an old edge is lost
only when one of its endpoints lies on the prefix.  Thus the remaining global
exchange obligation is an incidence theorem for the other required boundary
components, rather than a false assertion that the arbitrary ambient prefix
is an exposed ladder path.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath
open GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Replace every old incidence on a finite path by the path itself.  Removing
both colours of old incidence is deliberate: it is the smallest completely
generic overwrite which needs no compatibility assumption between the
ambient prefix and the old bi-unique relation. -/
def ambientPrefixOverwriteEdges
    (E : Set (V × V)) (p : FinitePath Gamma.graph) : Set (V × V) :=
  (E \ (p.support ×ˢ (Set.univ : Set V) ∪
    (Set.univ : Set V) ×ˢ p.support)) ∪ p.edgeSet

/-- Old edges removed by the ambient-prefix overwrite. -/
def ambientPrefixDamagedEdges
    (E : Set (V × V)) (p : FinitePath Gamma.graph) : Set (V × V) :=
  E \ ambientPrefixOverwriteEdges E p

/-- Every edge of the inserted path is retained by the overwrite. -/
theorem FinitePath.edgeSet_subset_ambientPrefixOverwriteEdges
    (p : FinitePath Gamma.graph) (E : Set (V × V)) :
    p.edgeSet ⊆ ambientPrefixOverwriteEdges E p := by
  exact Set.subset_union_right

/-- An old edge disjoint from the prefix carrier survives the overwrite. -/
theorem mem_ambientPrefixOverwriteEdges_of_mem_of_endpoints_not_mem
    {E : Set (V × V)} {p : FinitePath Gamma.graph} {x y : V}
    (hxy : (x, y) ∈ E) (hx : x ∉ p.support) (hy : y ∉ p.support) :
    (x, y) ∈ ambientPrefixOverwriteEdges E p := by
  left
  refine ⟨hxy, ?_⟩
  rintro (hleft | hright)
  · exact hx hleft.1
  · exact hy hright.2

/-- Exact locality of the overwrite: every removed old edge is incident with
the inserted prefix. -/
theorem old_mem_or_incident_of_mem
    {E : Set (V × V)} {p : FinitePath Gamma.graph} {x y : V}
    (hxy : (x, y) ∈ E) :
    (x, y) ∈ ambientPrefixOverwriteEdges E p ∨
      x ∈ p.support ∨ y ∈ p.support := by
  by_cases hx : x ∈ p.support
  · exact Or.inr (Or.inl hx)
  · by_cases hy : y ∈ p.support
    · exact Or.inr (Or.inr hy)
    · exact Or.inl
        (mem_ambientPrefixOverwriteEdges_of_mem_of_endpoints_not_mem
          hxy hx hy)

/-- The outgoing old edges incident with a finite prefix form a finite set in
a right-unique relation. -/
theorem finite_oldEdges_with_tail_in_support
    {E : Set (V × V)} {p : FinitePath Gamma.graph}
    (hE : Relator.RightUnique (fun x y ↦ (x, y) ∈ E)) :
    {e | e ∈ E ∧ e.1 ∈ p.support}.Finite := by
  apply Set.Finite.of_finite_image
  · apply p.support_finite.subset
    rintro x ⟨e, he, rfl⟩
    exact he.2
  · intro e he f hf hefst
    apply Prod.ext hefst
    apply hE he.1 hf.1
    exact hefst

/-- The incoming old edges incident with a finite prefix form a finite set in
a left-unique relation. -/
theorem finite_oldEdges_with_head_in_support
    {E : Set (V × V)} {p : FinitePath Gamma.graph}
    (hE : Relator.LeftUnique (fun x y ↦ (x, y) ∈ E)) :
    {e | e ∈ E ∧ e.2 ∈ p.support}.Finite := by
  apply Set.Finite.of_finite_image
  · apply p.support_finite.subset
    rintro x ⟨e, he, rfl⟩
    exact he.2
  · intro e he f hf hefsnd
    apply Prod.ext
    · apply hE he.1 hf.1
      exact hefsnd
    · exact hefsnd

/-- A finite prefix damages only finitely many edges of a bi-unique old
relation.  This is the finite exchange datum needed after the local
overwrite; no cardinality assumption on the ambient graph is used. -/
theorem ambientPrefixDamagedEdges_finite
    {E : Set (V × V)} {p : FinitePath Gamma.graph}
    (hE : Relator.BiUnique (fun x y ↦ (x, y) ∈ E)) :
    (ambientPrefixDamagedEdges E p).Finite := by
  apply (finite_oldEdges_with_tail_in_support hE.2 |>.union
    (finite_oldEdges_with_head_in_support hE.1)).subset
  rintro e he
  have hinc := old_mem_or_incident_of_mem (p := p) he.1
  rcases hinc with hkept | htail | hhead
  · exact False.elim (he.2 hkept)
  · exact Or.inl ⟨he.1, htail⟩
  · exact Or.inr ⟨he.1, hhead⟩

/-- The overwrite stays inside the ambient digraph. -/
theorem ambientPrefixOverwriteEdges_subset_adj
    {E : Set (V × V)} {p : FinitePath Gamma.graph}
    (hE : E ⊆ {e | Gamma.graph.Adj e.1 e.2}) :
    ambientPrefixOverwriteEdges E p ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with he | he
  · exact hE he.1
  · exact p.edgeSet_subset_adj he

/-- Overwriting a bi-unique relation by a finite simple path is bi-unique.
The two cross-colour cases are impossible because every old edge incident
with a path vertex was removed. -/
theorem ambientPrefixOverwriteEdges_biUnique
    {E : Set (V × V)} {p : FinitePath Gamma.graph}
    (hE : Relator.BiUnique (fun x y ↦ (x, y) ∈ E)) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ ambientPrefixOverwriteEdges E p) := by
  have hp : Relator.BiUnique (fun x y ↦ (x, y) ∈ p.edgeSet) :=
    _root_.Erdos599.Alternating.Path.edgeSet_biUnique (.inl p)
  constructor
  · intro x y z hxz hyz
    rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
    · exact hE.1 hxz.1 hyz.1
    · have hz : z ∈ p.support :=
        (p.edgeSet_subset_support_prod hyz).2
      exact False.elim (hxz.2 (Or.inr ⟨Set.mem_univ x, hz⟩))
    · have hz : z ∈ p.support :=
        (p.edgeSet_subset_support_prod hxz).2
      exact False.elim (hyz.2 (Or.inr ⟨Set.mem_univ y, hz⟩))
    · exact hp.1 hxz hyz
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact hE.2 hxy.1 hxz.1
    · have hx : x ∈ p.support :=
        (p.edgeSet_subset_support_prod hxz).1
      exact False.elim (hxy.2 (Or.inl ⟨hx, Set.mem_univ y⟩))
    · have hx : x ∈ p.support :=
        (p.edgeSet_subset_support_prod hxy).1
      exact False.elim (hxz.2 (Or.inl ⟨hx, Set.mem_univ z⟩))
    · exact hp.2 hxy hxz

/-- The overwritten relation has no incoming edge at the prefix source. -/
theorem ambientPrefixOverwriteEdges_noIncoming_start
    (E : Set (V × V)) (p : FinitePath Gamma.graph) (x : V) :
    (x, p.start) ∉ ambientPrefixOverwriteEdges E p := by
  rintro (hold | hpath)
  · exact hold.2 (Or.inr ⟨Set.mem_univ x, p.start_mem_support⟩)
  · exact
      _root_.Erdos599.Alternating.FinitePath.no_incoming_edge_at_start
        p x hpath

/-- The overwritten relation stops at the endpoint of the prefix. -/
theorem ambientPrefixOverwriteEdges_noOutgoing_finish
    (E : Set (V × V)) (p : FinitePath Gamma.graph) (y : V) :
    (p.finish, y) ∉ ambientPrefixOverwriteEdges E p := by
  rintro (hold | hpath)
  · exact hold.2 (Or.inl ⟨p.finish_mem_support, Set.mem_univ y⟩)
  · exact
      _root_.Erdos599.Alternating.FinitePath.no_outgoing_edge_at_finish
        p y hpath

/-- Every overwrite edge stays on one side of the inserted path carrier. -/
theorem ambientPrefixOverwriteEdges_mem_support_iff
    {E : Set (V × V)} {p : FinitePath Gamma.graph} {x y : V}
    (hxy : (x, y) ∈ ambientPrefixOverwriteEdges E p) :
    x ∈ p.support ↔ y ∈ p.support := by
  rcases hxy with hold | hpath
  · have hx : x ∉ p.support := by
      intro hx
      exact hold.2 (Or.inl ⟨hx, Set.mem_univ y⟩)
    have hy : y ∉ p.support := by
      intro hy
      exact hold.2 (Or.inr ⟨Set.mem_univ x, hy⟩)
    exact iff_of_false hx hy
  · have hend := p.edgeSet_subset_support_prod hpath
    exact iff_of_true hend.1 hend.2

/-- Reachability in the overwritten relation cannot cross the carrier of the
inserted prefix. -/
theorem reflTransGen_ambientPrefixOverwriteEdges_mem_support_iff
    {E : Set (V × V)} {p : FinitePath Gamma.graph} {x y : V}
    (hxy : Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ ambientPrefixOverwriteEdges E p) x y) :
    x ∈ p.support ↔ y ∈ p.support := by
  induction hxy with
  | refl => exact Iff.rfl
  | tail hxy hyz ih =>
      exact ih.trans (ambientPrefixOverwriteEdges_mem_support_iff hyz)

/-- A reachability chain which starts outside the inserted carrier uses only
old edges. -/
theorem reflTransGen_old_of_ambientPrefixOverwriteEdges_of_start_not_mem
    {E : Set (V × V)} {p : FinitePath Gamma.graph} {x y : V}
    (hxy : Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ ambientPrefixOverwriteEdges E p) x y)
    (hx : x ∉ p.support) :
    Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) x y := by
  induction hxy with
  | refl => exact .refl
  | @tail y z hxy hyz ih =>
      have hy : y ∉ p.support := by
        intro hyMem
        have hside :=
          reflTransGen_ambientPrefixOverwriteEdges_mem_support_iff hxy
        exact hx (hside.mpr hyMem)
      have hyzOld : (y, z) ∈ E := by
        rcases hyz with hold | hpath
        · exact hold.1
        · exact False.elim
            (hy (p.edgeSet_subset_support_prod hpath).1)
      exact .tail ih hyzOld

/-- An old reachability antichain remains an antichain after the overwrite
provided the inserted prefix contains at most its displayed endpoint from
the boundary. -/
theorem isReachabilityAntichain_ambientPrefixOverwriteEdges
    {E : Set (V × V)} {p : FinitePath Gamma.graph} {B : Set V}
    (hanti : IsReachabilityAntichain E B)
    (hfirst : p.support ∩ B ⊆ {p.finish}) :
    IsReachabilityAntichain (ambientPrefixOverwriteEdges E p) B := by
  intro b hb c hc hbc
  by_cases hbPath : b ∈ p.support
  · have hcPath : c ∈ p.support :=
      (reflTransGen_ambientPrefixOverwriteEdges_mem_support_iff hbc).mp hbPath
    have hbf : b = p.finish := by
      simpa only [Set.mem_singleton_iff] using hfirst ⟨hbPath, hb⟩
    have hcf : c = p.finish := by
      simpa only [Set.mem_singleton_iff] using hfirst ⟨hcPath, hc⟩
    exact hbf.trans hcf.symm
  · exact hanti hb hc
      (reflTransGen_old_of_ambientPrefixOverwriteEdges_of_start_not_mem
        hbc hbPath)

/-- The inserted prefix gives a literal reachability chain in the overwritten
relation. -/
theorem FinitePath.start_reaches_finish_ambientPrefixOverwriteEdges
    (p : FinitePath Gamma.graph) (E : Set (V × V)) :
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ ambientPrefixOverwriteEdges E p)
      p.start p.finish := by
  apply Relation.ReflTransGen.mono
    (r := fun x y ↦ (x, y) ∈ p.edgeSet)
    (p := fun x y ↦ (x, y) ∈ ambientPrefixOverwriteEdges E p)
  · intro x y hxy
    exact FinitePath.edgeSet_subset_ambientPrefixOverwriteEdges p E hxy
  · exact _root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet p.walk

/-- A previously available finite root path survives whenever none of its
edges is incident with the overwritten prefix.  This is the exact local
premise needed to preserve roots of all other boundary components. -/
theorem FinitePath.start_reaches_finish_ambientPrefixOverwriteEdges_of_avoids
    {E : Set (V × V)} {p q : FinitePath Gamma.graph}
    (hqE : q.edgeSet ⊆ E)
    (havoid : ∀ e ∈ q.edgeSet,
      e.1 ∉ p.support ∧ e.2 ∉ p.support) :
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ ambientPrefixOverwriteEdges E p)
      q.start q.finish := by
  apply Relation.ReflTransGen.mono
    (r := fun x y ↦ (x, y) ∈ q.edgeSet)
    (p := fun x y ↦ (x, y) ∈ ambientPrefixOverwriteEdges E p)
  · intro x y hxy
    exact mem_ambientPrefixOverwriteEdges_of_mem_of_endpoints_not_mem
      (hqE hxy) (havoid (x, y) hxy).1 (havoid (x, y) hxy).2
  · exact _root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet q.walk

namespace Assertion822ReachableWholeSourceRootObstruction

/-- The precise local exchange supplied by the outside-ladder-family branch.
It is intentionally a relation-level certificate: global Assertion 8.22 still
requires proving that removing the old incidences on `path.support` does not
strand another required boundary component. -/
structure ExternalAmbientPrefixExchange
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822ReachableWholeSourceRootObstruction hL S R) where
  data : O.AmbientLastDeletedHeadData
  deleted_incoming_outside_family :
    (data.tail, data.deleted.head) ∉
      (L.popularAuxiliaryInput hL.legal).familyEdges

/-- Lossless split of the last ambient defect.  Only the first constructor
uses the ambient overwrite; the other constructors retain the exact
construction-specific deletion class for the existing owner recursion. -/
inductive AmbientDeletedHeadExchangeOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822ReachableWholeSourceRootObstruction hL S R)
    (data : O.AmbientLastDeletedHeadData) : Prop
  | external (exchange : O.ExternalAmbientPrefixExchange)
  | representedCut
      (edge_mem : (data.tail, data.deleted.head) ∈
        GroundingCut.CE (L.popularAuxiliaryInput hL.legal) S.cut)
  | selectedBackward
      (edge_mem : (data.tail, data.deleted.head) ∈
        GroundingErasedDecode.erasedSelectedDirectionEdgesAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) ∅ .backward)
  | forwardConflict
      (edge_mem : (data.tail, data.deleted.head) ∈
        GroundingErasedDecode.forwardConflictCutEdgesAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) ∅)

namespace ExternalAmbientPrefixExchange

/-- The relation obtained by routing the old pre-stopped relation along the
ambient prefix. -/
def edges
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822ReachableWholeSourceRootObstruction hL S R}
    (X : O.ExternalAmbientPrefixExchange) : Set (V × V) :=
  ambientPrefixOverwriteEdges
    (L.assertion822ReservedPreStoppedEdges hL S R) X.data.path

/-- The ambient-prefix exchange is a genuine subrelation of the graph. -/
theorem edges_subset_adj
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822ReachableWholeSourceRootObstruction hL S R}
    (X : O.ExternalAmbientPrefixExchange) :
    X.edges ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  apply ambientPrefixOverwriteEdges_subset_adj
  exact L.assertion822ReservedSwitchedEdgesAt_subset_adj hL S R ∅

/-- The ambient-prefix exchange remains bi-unique. -/
theorem edges_biUnique
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822ReachableWholeSourceRootObstruction hL S R}
    (X : O.ExternalAmbientPrefixExchange) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ X.edges) := by
  apply ambientPrefixOverwriteEdges_biUnique
  exact L.assertion822ReservedSwitchedEdgesAt_biUnique hL S R ∅

/-- The formerly unrooted boundary is rooted in the exchanged relation. -/
theorem boundary_rooted
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822ReachableWholeSourceRootObstruction hL S R}
    (X : O.ExternalAmbientPrefixExchange) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ X.edges)
        a O.obstruction.boundary := by
  refine ⟨X.data.path.start, X.data.path_start_source, ?_⟩
  rw [← X.data.path_finish_boundary]
  exact FinitePath.start_reaches_finish_ambientPrefixOverwriteEdges
    X.data.path (L.assertion822ReservedPreStoppedEdges hL S R)

/-- The repaired boundary point is a sink. -/
theorem boundary_noOutgoing
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822ReachableWholeSourceRootObstruction hL S R}
    (X : O.ExternalAmbientPrefixExchange) (y : V) :
    (O.obstruction.boundary, y) ∉ X.edges := by
  rw [← X.data.path_finish_boundary]
  exact ambientPrefixOverwriteEdges_noOutgoing_finish
    (L.assertion822ReservedPreStoppedEdges hL S R) X.data.path y

/-- Every old edge destroyed by the exchange is incident with the ambient
prefix.  This is the exact remaining incidence seam for a global repair. -/
theorem old_mem_or_incident
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822ReachableWholeSourceRootObstruction hL S R}
    (X : O.ExternalAmbientPrefixExchange) {x y : V}
    (hxy : (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R) :
    (x, y) ∈ X.edges ∨
      x ∈ X.data.path.support ∨ y ∈ X.data.path.support := by
  exact old_mem_or_incident_of_mem hxy

/-- Any old finite root route avoiding the ambient prefix remains a root
route after the exchange. -/
theorem old_rootPath_survives_of_avoids
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822ReachableWholeSourceRootObstruction hL S R}
    (X : O.ExternalAmbientPrefixExchange)
    (q : FinitePath Gamma.graph)
    (hqE : q.edgeSet ⊆ L.assertion822ReservedPreStoppedEdges hL S R)
    (havoid : ∀ e ∈ q.edgeSet,
      e.1 ∉ X.data.path.support ∧
        e.2 ∉ X.data.path.support) :
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈ X.edges)
      q.start q.finish := by
  exact
    FinitePath.start_reaches_finish_ambientPrefixOverwriteEdges_of_avoids
      hqE havoid

/-- Exact additional data under which the local ambient-prefix overwrite is
a global Assertion 8.22 repair.  Every other boundary point comes with an
old root path whose edges avoid the overwritten carrier.  This formulation
retains the actual paths and hence does not hide the outstanding incidence
lemma behind a bare reachability assumption. -/
structure IncidencePreservingBoundaryData
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822ReachableWholeSourceRootObstruction hL S R}
    (X : O.ExternalAmbientPrefixExchange) where
  allowedRoots : Set V
  boundary : Set V
  unused : V
  allowedRoots_subset_source : allowedRoots ⊆ Gamma.source
  unused_mem_source : unused ∈ Gamma.source
  unused_not_mem_allowedRoots : unused ∉ allowedRoots
  boundary_subset_BB : boundary ⊆
    GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut
  boundary_separates : Popular.IsSeparator Gamma boundary
  obstruction_mem_boundary : O.obstruction.boundary ∈ boundary
  prefix_meets_boundary_only :
    X.data.path.support ∩ boundary ⊆ {O.obstruction.boundary}
  old_reachabilityAntichain : IsReachabilityAntichain
    (L.assertion822ReservedPreStoppedEdges hL S R) boundary
  prefix_start_allowed : X.data.path.start ∈ allowedRoots
  other_rootPath : ∀ b ∈ boundary, b ≠ O.obstruction.boundary →
    ∃ q : FinitePath Gamma.graph,
      q.start ∈ allowedRoots ∧ q.finish = b ∧
      q.edgeSet ⊆ L.assertion822ReservedPreStoppedEdges hL S R ∧
      ∀ e ∈ q.edgeSet,
        e.1 ∉ X.data.path.support ∧ e.2 ∉ X.data.path.support

namespace IncidencePreservingBoundaryData

/-- All selected boundary points are rooted after the incidence-preserving
overwrite. -/
theorem boundary_rooted
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822ReachableWholeSourceRootObstruction hL S R}
    {X : O.ExternalAmbientPrefixExchange}
    (G : X.IncidencePreservingBoundaryData) :
    ∀ b ∈ G.boundary, ∃ a ∈ G.allowedRoots,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ X.edges) a b := by
  intro b hb
  by_cases hbo : b = O.obstruction.boundary
  · subst b
    refine ⟨X.data.path.start, G.prefix_start_allowed, ?_⟩
    rw [← X.data.path_finish_boundary]
    exact FinitePath.start_reaches_finish_ambientPrefixOverwriteEdges
      X.data.path (L.assertion822ReservedPreStoppedEdges hL S R)
  · obtain ⟨q, hqStart, hqFinish, hqE, hqAvoid⟩ :=
      G.other_rootPath b hb hbo
    refine ⟨q.start, hqStart, ?_⟩
    rw [← hqFinish]
    exact X.old_rootPath_survives_of_avoids q hqE hqAvoid

/-- The exact one-boundary-contact premise preserves the reachability
antichain. -/
theorem reachabilityAntichain
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822ReachableWholeSourceRootObstruction hL S R}
    {X : O.ExternalAmbientPrefixExchange}
    (G : X.IncidencePreservingBoundaryData) :
    IsReachabilityAntichain X.edges G.boundary := by
  apply isReachabilityAntichain_ambientPrefixOverwriteEdges
    G.old_reachabilityAntichain
  intro x hx
  have hx' : x ∈ X.data.path.support ∩ G.boundary := hx
  have hxo := G.prefix_meets_boundary_only hx'
  simpa only [Set.mem_singleton_iff, X.data.path_finish_boundary] using hxo

/-- Compile a genuinely incidence-preserving ambient-prefix exchange into
Assertion 8.22. -/
theorem assertion822Output
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822ReachableWholeSourceRootObstruction hL S R}
    {X : O.ExternalAmbientPrefixExchange}
    (G : X.IncidencePreservingBoundaryData) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) := by
  exact GroundingAssertion822Output.exists_of_rootedReachability
    (L.popularAuxiliaryInput hL.legal) S.cut X.edges
    G.allowedRoots G.boundary X.edges_subset_adj X.edges_biUnique
    G.allowedRoots_subset_source G.boundary_subset_BB G.boundary_separates
    G.reachabilityAntichain G.boundary_rooted G.unused
    G.unused_mem_source G.unused_not_mem_allowedRoots

end IncidencePreservingBoundaryData

end ExternalAmbientPrefixExchange

/-- Package the local overwrite exactly when the ambient last-deleted-head
edge is outside the limiting-ladder family. -/
def externalAmbientPrefixExchange
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822ReachableWholeSourceRootObstruction hL S R)
    (data : O.AmbientLastDeletedHeadData)
    (houtside : (data.tail, data.deleted.head) ∉
      (L.popularAuxiliaryInput hL.legal).familyEdges) :
    O.ExternalAmbientPrefixExchange :=
  ⟨data, houtside⟩

/-- Classify the ambient last-deleted-head branch, packaging the external
edge case as the canonical prefix overwrite. -/
theorem ambientDeletedHeadExchangeOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822ReachableWholeSourceRootObstruction hL S R)
    (data : O.AmbientLastDeletedHeadData) :
    O.AmbientDeletedHeadExchangeOutcome data := by
  rcases data.incoming_class with houtside | hcut | hback | hconflict
  · exact .external (O.externalAmbientPrefixExchange data houtside)
  · exact .representedCut hcut
  · exact .selectedBackward hback
  · exact .forwardConflict hconflict

end Assertion822ReachableWholeSourceRootObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.ambientPrefixOverwriteEdges_biUnique
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822ReachableWholeSourceRootObstruction.ExternalAmbientPrefixExchange.boundary_rooted
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822ReachableWholeSourceRootObstruction.ambientDeletedHeadExchangeOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822ReachableWholeSourceRootObstruction.ExternalAmbientPrefixExchange.IncidencePreservingBoundaryData.assertion822Output
