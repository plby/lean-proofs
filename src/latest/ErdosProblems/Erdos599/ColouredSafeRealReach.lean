/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeLocalTransactionRealLedger
import ErdosProblems.Erdos599.ColouredSafeShortcutGraph
import ErdosProblems.Erdos599.ColouredSafeAugmentedRealReach

/-!
# Finite real reachability in a native augmented warp

The relation-based interface includes source carrier membership, even for
the reflexive case. It is equivalent to an actual finite original-graph
path with all edges and vertices in the augmented warp. Composition thus
uses loop erasure, not an unjustified disjoint concatenation.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal DirectedPath Alternating
open ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {W U : Set (imaginaryWeb Y kappa).DPath} {s t z : V} {T : Set V}

abbrev RealReach (W : Set (imaginaryWeb Y kappa).DPath) (s t : V) : Prop :=
  ColouredSafeAugmentedRealReach.RealReach Gamma (imaginaryWeb Y kappa) W s t

abbrev RealReaches (W : Set (imaginaryWeb Y kappa).DPath) (s : V) (T : Set V) : Prop :=
  ColouredSafeAugmentedRealReach.RealReaches Gamma (imaginaryWeb Y kappa) W s T

theorem RealReach.refl (hs : s ∈ (imaginaryWeb Y kappa).vertexSet W) :
    RealReach W s s :=
  ColouredSafeAugmentedRealReach.RealReach.refl
    (D := imaginaryWeb Y kappa) hs

theorem RealReach.trans (hst : RealReach W s t) (htz : RealReach W t z) :
    RealReach W s z :=
  ColouredSafeAugmentedRealReach.RealReach.trans
    (D := imaginaryWeb Y kappa) hst htz

theorem RealReach.mono (hst : RealReach W s t)
    (hV : (imaginaryWeb Y kappa).vertexSet W ⊆
      (imaginaryWeb Y kappa).vertexSet U)
    (hE : RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj W ⊆
      RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj U) :
    RealReach U s t :=
  ColouredSafeAugmentedRealReach.RealReach.mono
    (D := imaginaryWeb Y kappa) hst hV hE

theorem RealReach.of_path (p : FinitePath Gamma.graph)
    (hV : p.support ⊆ (imaginaryWeb Y kappa).vertexSet W)
    (hE : p.edgeSet ⊆ familyEdges W) : RealReach W p.start p.finish :=
  ColouredSafeAugmentedRealReach.RealReach.of_path
    (D := imaginaryWeb Y kappa) p hV hE

/-- Recover a literal finite path, including its carrier containment. -/
theorem RealReach.exists_path (h : RealReach W s t) :
    ∃ p : FinitePath Gamma.graph, p.start = s ∧ p.finish = t ∧
      p.support ⊆ (imaginaryWeb Y kappa).vertexSet W ∧
      p.edgeSet ⊆ familyEdges W :=
  ColouredSafeAugmentedRealReach.RealReach.exists_path
    (D := imaginaryWeb Y kappa) h

theorem realReach_iff_exists_path : RealReach W s t ↔
    ∃ p : FinitePath Gamma.graph, p.start = s ∧ p.finish = t ∧
      p.support ⊆ (imaginaryWeb Y kappa).vertexSet W ∧
      p.edgeSet ⊆ familyEdges W :=
  ColouredSafeAugmentedRealReach.realReach_iff_exists_path
    (D := imaginaryWeb Y kappa)

theorem RealReach.then_reaches (hst : RealReach W s t) (htT : RealReaches W t T) :
    RealReaches W s T :=
  ColouredSafeAugmentedRealReach.RealReach.then_reaches
    (D := imaginaryWeb Y kappa) hst htT

theorem RealReaches.mono (h : RealReaches W s T)
    (hV : (imaginaryWeb Y kappa).vertexSet W ⊆
      (imaginaryWeb Y kappa).vertexSet U)
    (hE : RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj W ⊆
      RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj U) :
    RealReaches U s T :=
  ColouredSafeAugmentedRealReach.RealReaches.mono
    (D := imaginaryWeb Y kappa) h hV hE

theorem RealReaches.target_mono (h : RealReaches W s T) {T' : Set V}
    (hTT' : T ⊆ T') : RealReaches W s T' :=
  ColouredSafeAugmentedRealReach.RealReaches.target_mono
    (D := imaginaryWeb Y kappa) h hTT'

/-- A nonreal outgoing edge in a warp makes its tail a real terminal;
out-degree uniqueness excludes a different real outgoing edge. -/
theorem isRealTerminal_of_nonreal_outgoing
    (hW : (imaginaryWeb Y kappa).IsWarp W)
    (he : (s, t) ∈ familyEdges W) (hn : ¬Gamma.graph.Adj s t) :
    IsRealTerminal (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj W s :=
  ColouredSafeAugmentedRealReach.isRealTerminal_of_nonreal_outgoing
    (D := imaginaryWeb Y kappa) hW he hn

/-- The monotone data retained while finitely resolving a native path.
Only full terminals in `T` may be added; real terminals are accounted for
separately, since several old ones can be processed in succession. -/
structure RealAdvance (W U : Set (imaginaryWeb Y kappa).DPath) (T : Set V) : Prop where
  initials : (imaginaryWeb Y kappa).initialSet W ⊆
    (imaginaryWeb Y kappa).initialSet U
  vertices : (imaginaryWeb Y kappa).vertexSet W ⊆
    (imaginaryWeb Y kappa).vertexSet U
  edges : RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj W ⊆
    RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj U
  terminals : (imaginaryWeb Y kappa).terminalFrontier U ⊆
    (imaginaryWeb Y kappa).terminalFrontier W ∪ T

theorem RealAdvance.refl (W : Set (imaginaryWeb Y kappa).DPath) (T : Set V) :
    RealAdvance W W T := ⟨Subset.rfl, Subset.rfl, Subset.rfl, Set.subset_union_left⟩

theorem RealAdvance.trans {U' : Set (imaginaryWeb Y kappa).DPath}
    (h : RealAdvance W U T) (h' : RealAdvance U U' T) : RealAdvance W U' T := by
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

end Erdos599.Blueprint.ColouredSafeShortcutGraph
