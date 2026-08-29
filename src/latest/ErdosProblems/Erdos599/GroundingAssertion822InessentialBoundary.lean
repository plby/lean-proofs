/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAssertion822Output
import ErdosProblems.Erdos599.GroundingPreStoppedRealization

/-!
# Assertion 8.22 from a nonessential rooted boundary point

The reserved-source compilers prove the missing-source conclusion by deleting
one source from the allowed root set.  That is unnecessarily strong when the
realized boundary warp already contains an inessential component.  This file
records the complementary, source-faithful compiler: all roots may lie in the
original source, and one nonessential point of the exact terminal boundary
certifies an inessential member of the constructed warp.

The proof uses the reachability-antichain premise twice.  It gives the disjoint
rooted warp, and it says that a selected path ending at `b` meets the boundary
only at `b`.  Hence, if `b` is not essential in that boundary, the selected
path misses the essential frontier and is itself inessential.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingAssertion822Output

open DirectedPath GroundingRootedReachabilityWarp

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Rooted reachability from the whole original source gives Assertion 8.22
as soon as one point of the exact separating boundary is nonessential in that
boundary.  No source has to be excluded from the root set. -/
theorem exists_of_rootedReachability_nonessentialBoundary
    (L : PopularAuxiliary.Input Gamma I) (C : Set L.LV)
    (E : Set (V × V)) (B : Set V)
    (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hBsubset : B ⊆ GroundingCut.BB L C)
    (hBseparator : Popular.IsSeparator Gamma B)
    (hanti : IsReachabilityAntichain E B)
    (hroot : ∀ b ∈ B, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b)
    (b : V) (hb : b ∈ B) (hbNonessential : b ∉ Gamma.essential B) :
    Nonempty (GroundingFinalAssembly.Assertion822Output L C) := by
  classical
  obtain ⟨P, hcover, hpaths⟩ :=
    exists_rootedReachabilityWarp hEadj hbi (Set.Subset.rfl) hanti hroot
  let W : Set Gamma.DPath := PopularSwitching.pathFamily P
  have hfrontier : Gamma.terminalFrontier W = B :=
    PopularSwitching.pathFamily_terminalFrontier_eq P hcover
  obtain ⟨p, hpP, hpFinish⟩ := hcover b hb
  have hpW : (Sum.inl p : Gamma.DPath) ∈ W := ⟨p, hpP, rfl⟩
  have hpInessential :
      (Sum.inl p : Gamma.DPath) ∈ Gamma.inessentialPaths W := by
    apply Gamma.mem_inessentialPaths_of_misses_essentialFrontier hpW
    rintro ⟨x, hxEssential, hxp⟩
    have hxEssentialB : x ∈ Gamma.essential B := by
      simpa only [hfrontier] using hxEssential
    have hxB : x ∈ B := Gamma.essential_subset B hxEssentialB
    have hxb : Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) x b := by
      rw [← hpFinish]
      exact finitePath_reaches_finish_of_mem_support p (hpaths p hpP).1 hxp
    have hxbEq : x = b := hanti hxB hb hxb
    exact hbNonessential (hxbEq ▸ hxEssentialB)
  have hwarp : Gamma.IsWarp W := PopularSwitching.pathFamily_isWarp P
  have hinitial : Gamma.initialSet W ⊆ Gamma.source :=
    PopularSwitching.pathFamily_initialSet_subset P
  have hwave : Gamma.IsWave W :=
    DWeb.isWave_of_terminalFrontier_isSeparator hwarp hinitial (by
      rw [hfrontier]
      exact hBseparator)
  refine ⟨{
    warp := W
    isWarp := hwarp
    initial_subset_source := hinitial
    frontier := B
    terminalFrontier_eq := hfrontier
    frontier_subset_BB := hBsubset
    frontier_separates := hBseparator
    essential_initial_ne_source :=
      (DWeb.essentialWarpPart_isHindrance_of_inessentialPath
        hwave hpInessential).2 }⟩

end GroundingAssertion822Output

namespace DWeb.KappaLadder

open GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Pre-stopped Assertion 8.22 compiler which permits the reserved record's
source as a genuine root.  The replacement for reserved-source exclusion is
an explicit nonessential member of the exact separating frontier. -/
theorem assertion822Output_of_preStoppedInessentialFrontierGeometry
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) (T : Set V)
    (hTsubset : T ⊆
      GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut)
    (hTseparator : Popular.IsSeparator Gamma T)
    (hanti : IsReachabilityAntichain
      (L.assertion822ReservedPreStoppedEdges hL S R) T)
    (hroot : ∀ t ∈ T, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦
          (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R) a t)
    (t : V) (ht : t ∈ T) (htNonessential : t ∉ Gamma.essential T) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) := by
  exact GroundingAssertion822Output.exists_of_rootedReachability_nonessentialBoundary
    (L.popularAuxiliaryInput hL.legal) S.cut
    (L.assertion822ReservedPreStoppedEdges hL S R) T
    (L.assertion822ReservedSwitchedEdgesAt_subset_adj hL S R ∅)
    (L.assertion822ReservedSwitchedEdgesAt_biUnique hL S R ∅)
    hTsubset hTseparator hanti hroot t ht htNonessential

/-- Literal-`BB` specialization of the nonessential-boundary compiler. -/
theorem assertion822Output_of_preStoppedInessentialBoundaryGeometry
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (hanti : IsReachabilityAntichain
      (L.assertion822ReservedPreStoppedEdges hL S R)
      (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut))
    (hroot : ∀ b ∈ GroundingCut.BB
        (L.popularAuxiliaryInput hL.legal) S.cut,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R) a b)
    (b : V)
    (hb : b ∈ GroundingCut.BB
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (hbNonessential : b ∉ Gamma.essential
      (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) := by
  exact L.assertion822Output_of_preStoppedInessentialFrontierGeometry
    hL S R
    (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut)
    Set.Subset.rfl
    (GroundingAssertion818Decoder.assertion8_18 L hL.legal S.cut S.separates)
    hanti hroot b hb hbNonessential

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.GroundingAssertion822Output.exists_of_rootedReachability_nonessentialBoundary
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_of_preStoppedInessentialFrontierGeometry
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_of_preStoppedInessentialBoundaryGeometry
