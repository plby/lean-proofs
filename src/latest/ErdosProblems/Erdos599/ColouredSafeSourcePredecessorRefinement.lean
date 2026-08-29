/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeRealReach
import ErdosProblems.Erdos599.ColouredSafeAugmentedPredecessorRefinement
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite

/-!
# Incoming-edge refinement allowing a new original-source prefix

A strong splice can replace an incoming edge at the old head by a finite
real path starting at a newly touched original source. This is different
from subdividing the old edge, so that third alternative is explicit.
The invariant composes under monotone carriers and real edges. The concrete
one- and two-port criteria use actual inserted finite families.
-/

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal DirectedPath Alternating ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

abbrev SourcePredecessorRefines (W U : Set (imaginaryWeb Y kappa).DPath) : Prop :=
  ColouredSafeAugmentedRealReach.SourcePredecessorRefines Gamma (imaginaryWeb Y kappa) W U

theorem SourcePredecessorRefines.refl (W : Set (imaginaryWeb Y kappa).DPath) :
    SourcePredecessorRefines W W :=
  ColouredSafeAugmentedRealReach.SourcePredecessorRefines.refl
    (D := imaginaryWeb Y kappa) W

/-- An ordinary edge-preserving extension retaining old initials cannot
add a new predecessor at an old vertex. -/
theorem familyEdges_into_oldVertex_of_edge_initial_extension
    {W U : Set (imaginaryWeb Y kappa).DPath}
    (hW : (imaginaryWeb Y kappa).IsWarp W)
    (hU : (imaginaryWeb Y kappa).IsWarp U)
    (hE : familyEdges W ⊆ familyEdges U)
    (hI : (imaginaryWeb Y kappa).initialSet W ⊆
      (imaginaryWeb Y kappa).initialSet U)
    {x y : V} (hx : x ∈ (imaginaryWeb Y kappa).vertexSet W)
    (hyx : (y, x) ∈ familyEdges U) : (y, x) ∈ familyEdges W :=
  ColouredSafeAugmentedRealReach.familyEdges_into_oldVertex_of_edge_initial_extension
    (D := imaginaryWeb Y kappa) hW hU hE hI hx hyx

/-- The incoming-edge invariant follows from the actual ordinary-extension
data; it is not an additional hypothesis on the moving successor. -/
theorem sourcePredecessorRefines_of_edge_initial_extension
    {W U : Set (imaginaryWeb Y kappa).DPath}
    (hW : (imaginaryWeb Y kappa).IsWarp W)
    (hU : (imaginaryWeb Y kappa).IsWarp U)
    (hE : familyEdges W ⊆ familyEdges U)
    (hI : (imaginaryWeb Y kappa).initialSet W ⊆
      (imaginaryWeb Y kappa).initialSet U) : SourcePredecessorRefines W U :=
  ColouredSafeAugmentedRealReach.sourcePredecessorRefines_of_edge_initial_extension
    (D := imaginaryWeb Y kappa) hW hU hE hI

theorem SourcePredecessorRefines.trans
    {W U R : Set (imaginaryWeb Y kappa).DPath}
    (hWU : SourcePredecessorRefines W U) (hUR : SourcePredecessorRefines U R)
    (hWUvertices : (imaginaryWeb Y kappa).vertexSet W ⊆
      (imaginaryWeb Y kappa).vertexSet U)
    (hURvertices : (imaginaryWeb Y kappa).vertexSet U ⊆
      (imaginaryWeb Y kappa).vertexSet R)
    (hURreal : RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj U ⊆
      RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj R) :
    SourcePredecessorRefines W R :=
  ColouredSafeAugmentedRealReach.SourcePredecessorRefines.trans
    (D := imaginaryWeb Y kappa) hWU hUR hWUvertices hURvertices hURreal

/-- A finite inserted owner gives a literal real prefix to each of its
vertices, all in the same output warp. -/
theorem realReach_of_inserted_finitePath
    {U : Set (imaginaryWeb Y kappa).DPath} (p : FinitePath Gamma.graph)
    (hpV : p.support ⊆ (imaginaryWeb Y kappa).vertexSet U)
    (hpE : p.edgeSet ⊆ familyEdges U) {x : V} (hx : x ∈ p.support) :
    RealReach U p.start x :=
  ColouredSafeAugmentedRealReach.realReach_of_inserted_finitePath
    (D := imaginaryWeb Y kappa) p hpV hpE hx

/-- Concrete two-port criterion. Every genuinely new incoming edge at an
old vertex belongs to a finite inserted owner rooted at the cut tail or an
original source. Its head must be the old cut head. -/
theorem sourcePredecessorRefines_of_twoPortInsertion
    {W U : Set (imaginaryWeb Y kappa).DPath} {P : Set Gamma.DPath} {s t : V}
    (hP : Gamma.IsWarp P) (hPfinite : Gamma.HasFiniteCharacter P)
    (hsP : s ∈ Gamma.initialSet P)
    (hroots : Gamma.initialSet P ⊆ Gamma.source ∪ {s})
    (hcut : (s, t) ∈ familyEdges W)
    (hcap : Gamma.vertexSet P ∩ (imaginaryWeb Y kappa).vertexSet W ⊆ {s, t})
    (hUE : familyEdges U ⊆ familyEdges W ∪ familyEdges P)
    (hPE : familyEdges P ⊆ familyEdges U)
    (hPV : Gamma.vertexSet P ⊆ (imaginaryWeb Y kappa).vertexSet U) :
    SourcePredecessorRefines W U :=
  ColouredSafeAugmentedRealReach.sourcePredecessorRefines_of_twoPortInsertion
    (D := imaginaryWeb Y kappa) hP hPfinite hsP hroots hcut hcap hUE hPE hPV

/-- A one-port insertion cannot add an incoming edge at any old vertex. -/
theorem sourcePredecessorRefines_of_onePortInsertion
    {W U : Set (imaginaryWeb Y kappa).DPath} {P : Set Gamma.DPath} {s : V}
    (hP : Gamma.IsWarp P) (hsP : s ∈ Gamma.initialSet P)
    (hcap : Gamma.vertexSet P ∩ (imaginaryWeb Y kappa).vertexSet W ⊆ {s})
    (hUE : familyEdges U ⊆ familyEdges W ∪ familyEdges P) :
    SourcePredecessorRefines W U :=
  ColouredSafeAugmentedRealReach.sourcePredecessorRefines_of_onePortInsertion
    (D := imaginaryWeb Y kappa) hP hsP hcap hUE

/-- The exact edge and carrier equations of the native two-port splice
discharge all relation-inclusion premises of predecessor refinement. -/
theorem sourcePredecessorRefines_of_twoPortSplice
    {W U : Set (imaginaryWeb Y kappa).DPath} {P : Set Gamma.DPath} {s t : V}
    (hP : Gamma.IsWarp P) (hPfinite : Gamma.HasFiniteCharacter P)
    (hsP : s ∈ Gamma.initialSet P)
    (hroots : Gamma.initialSet P ⊆ Gamma.source ∪ {s})
    (hcut : (s, t) ∈ familyEdges W)
    (hcap : Gamma.vertexSet P ∩ (imaginaryWeb Y kappa).vertexSet W ⊆ {s, t})
    (hUE : familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges P)
    (hUV : (imaginaryWeb Y kappa).vertexSet U =
      (imaginaryWeb Y kappa).vertexSet W ∪ Gamma.vertexSet P) :
    SourcePredecessorRefines W U :=
  ColouredSafeAugmentedRealReach.sourcePredecessorRefines_of_twoPortSplice
    (D := imaginaryWeb Y kappa) hP hPfinite hsP hroots hcut hcap hUE hUV

#print axioms SourcePredecessorRefines.trans
#print axioms familyEdges_into_oldVertex_of_edge_initial_extension
#print axioms sourcePredecessorRefines_of_edge_initial_extension
#print axioms sourcePredecessorRefines_of_twoPortInsertion
#print axioms sourcePredecessorRefines_of_onePortInsertion
#print axioms sourcePredecessorRefines_of_twoPortSplice

end Erdos599.Blueprint.ColouredSafeShortcutGraph
