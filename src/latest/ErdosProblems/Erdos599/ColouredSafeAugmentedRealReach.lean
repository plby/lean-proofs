/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeLocalTransactionRealLedger
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# Finite real reachability in an arbitrary augmented web

The original and augmented webs are explicit independent parameters. No
particular imaginary-edge predicate is required. The relation-based
interface includes source carrier membership, even for
the reflexive case. It is equivalent to an actual finite original-graph
path with all edges and vertices in the augmented warp. Composition thus
uses loop erasure, not an unjustified disjoint concatenation.
-/

noncomputable section

namespace Erdos599.ColouredSafeAugmentedRealReach

open Set Cardinal DirectedPath Alternating
open ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma D : DWeb V}
variable {W U : Set D.DPath} {s t z : V} {T : Set V}

def RealReach (Gamma D : DWeb V) (W : Set D.DPath) (s t : V) : Prop :=
  s ∈ D.vertexSet W ∧
    Relation.ReflTransGen (fun x y ↦
      (x, y) ∈ RealEdges (Gamma := D) Gamma.graph.Adj W) s t

def RealReaches (Gamma D : DWeb V) (W : Set D.DPath) (s : V) (T : Set V) : Prop :=
  ∃ t ∈ T, RealReach Gamma D W s t

theorem RealReach.refl (hs : s ∈ D.vertexSet W) :
    RealReach Gamma D W s s := ⟨hs, .refl⟩

theorem RealReach.trans (hst : RealReach Gamma D W s t) (htz : RealReach Gamma D W t z) :
    RealReach Gamma D W s z := ⟨hst.1, hst.2.trans htz.2⟩

theorem RealReach.mono (hst : RealReach Gamma D W s t)
    (hV : D.vertexSet W ⊆
      D.vertexSet U)
    (hE : RealEdges (Gamma := D) Gamma.graph.Adj W ⊆
      RealEdges (Gamma := D) Gamma.graph.Adj U) :
    RealReach Gamma D U s t :=
  ⟨hV hst.1, Relation.ReflTransGen.mono (fun _ _ h ↦ hE h) _ _ hst.2⟩

theorem RealReach.of_path (p : FinitePath Gamma.graph)
    (hV : p.support ⊆ D.vertexSet W)
    (hE : p.edgeSet ⊆ familyEdges W) : RealReach Gamma D W p.start p.finish := by
  refine ⟨hV p.start_mem_support, ?_⟩
  exact Relation.ReflTransGen.mono
    (fun _ _ h ↦ ⟨hE h, p.edgeSet_subset_adj h⟩) _ _
    (Alternating.Walk.reflTransGen_edgeSet p.walk)

/-- Recover a literal finite path, including its carrier containment. -/
theorem RealReach.exists_path (h : RealReach Gamma D W s t) :
    ∃ p : FinitePath Gamma.graph, p.start = s ∧ p.finish = t ∧
      p.support ⊆ D.vertexSet W ∧
      p.edgeSet ⊆ familyEdges W := by
  obtain ⟨P⟩ := GroundingRootedReachabilityWarp.exists_rootedPath_of_reflTransGen
    (Gamma := Gamma) (E := RealEdges (Gamma := D) Gamma.graph.Adj W)
    (fun _ he ↦ he.2) (A := {s}) ⟨s, Set.mem_singleton s, h.2⟩
  have hstart : P.path.start = s := Set.mem_singleton_iff.mp P.start_mem
  refine ⟨P.path, hstart, P.finish_eq, ?_, fun _ he ↦ (P.edgeSet_subset he).1⟩
  intro x hx
  by_cases hxs : x = P.path.start
  · exact (hxs.trans hstart).symm ▸ h.1
  · obtain ⟨y, hy⟩ :=
      Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
        P.path hx hxs
    exact (familyEdges_subset_vertexSet_prod W (P.edgeSet_subset hy).1).2

theorem realReach_iff_exists_path : RealReach Gamma D W s t ↔
    ∃ p : FinitePath Gamma.graph, p.start = s ∧ p.finish = t ∧
      p.support ⊆ D.vertexSet W ∧
      p.edgeSet ⊆ familyEdges W := by
  constructor
  · exact RealReach.exists_path
  · rintro ⟨p, rfl, rfl, hV, hE⟩
    exact RealReach.of_path p hV hE

theorem RealReach.then_reaches (hst : RealReach Gamma D W s t) (htT : RealReaches Gamma D W t T) :
    RealReaches Gamma D W s T := by
  obtain ⟨z, hz, htz⟩ := htT
  exact ⟨z, hz, hst.trans htz⟩

theorem RealReaches.mono (h : RealReaches Gamma D W s T)
    (hV : D.vertexSet W ⊆
      D.vertexSet U)
    (hE : RealEdges (Gamma := D) Gamma.graph.Adj W ⊆
      RealEdges (Gamma := D) Gamma.graph.Adj U) :
    RealReaches Gamma D U s T := by
  obtain ⟨t, ht, hst⟩ := h
  exact ⟨t, ht, hst.mono hV hE⟩

theorem RealReaches.target_mono (h : RealReaches Gamma D W s T) {T' : Set V}
    (hTT' : T ⊆ T') : RealReaches Gamma D W s T' := by
  obtain ⟨t, ht, hst⟩ := h
  exact ⟨t, hTT' ht, hst⟩

/-- A nonreal outgoing edge in a warp makes its tail a real terminal;
out-degree uniqueness excludes a different real outgoing edge. -/
theorem isRealTerminal_of_nonreal_outgoing
    (hW : D.IsWarp W)
    (he : (s, t) ∈ familyEdges W) (hn : ¬Gamma.graph.Adj s t) :
    IsRealTerminal (Gamma := D) Gamma.graph.Adj W s := by
  refine ⟨(familyEdges_subset_vertexSet_prod W he).1, ?_⟩
  rintro ⟨y, hy, hreal⟩
  have hyt : y = t := (IsWarp.familyEdges_biUnique hW).2 hy he
  exact hn (hyt ▸ hreal)

/-- The monotone data retained while finitely resolving a native path.
Only full terminals in `T` may be added; real terminals are accounted for
separately, since several old ones can be processed in succession. -/
structure RealAdvance (Gamma D : DWeb V) (W U : Set D.DPath) (T : Set V) : Prop where
  initials : D.initialSet W ⊆
    D.initialSet U
  vertices : D.vertexSet W ⊆
    D.vertexSet U
  edges : RealEdges (Gamma := D) Gamma.graph.Adj W ⊆
    RealEdges (Gamma := D) Gamma.graph.Adj U
  terminals : D.terminalFrontier U ⊆
    D.terminalFrontier W ∪ T

theorem RealAdvance.refl (W : Set D.DPath) (T : Set V) :
    RealAdvance Gamma D W W T := ⟨Subset.rfl, Subset.rfl, Subset.rfl, Set.subset_union_left⟩

theorem RealAdvance.trans {U' : Set D.DPath}
    (h : RealAdvance Gamma D W U T) (h' : RealAdvance Gamma D U U' T) :
    RealAdvance Gamma D W U' T := by
  refine ⟨h.initials.trans h'.initials, h.vertices.trans h'.vertices,
    h.edges.trans h'.edges, ?_⟩
  intro x hx
  rcases h'.terminals hx with hx | hx
  · exact h.terminals hx
  · exact Or.inr hx

#print axioms realReach_iff_exists_path
#print axioms RealReach.trans
#print axioms RealReach.mono
#print axioms isRealTerminal_of_nonreal_outgoing
#print axioms RealAdvance.trans

end Erdos599.ColouredSafeAugmentedRealReach
