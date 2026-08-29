/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFinalAssembly
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp
import ErdosProblems.Erdos599.GroundingAssertion822UnusedRecord
import ErdosProblems.Erdos599.GroundingErasedForwardConflict
import ErdosProblems.Erdos599.GroundingBBGeometry
import ErdosProblems.Erdos599.GroundingBBAntichainReduction
import ErdosProblems.Erdos599.GroundingBlockingReachability

/-!
# Rooted-reachability assembly for Assertion 8.22

The simultaneous grounding relation need not have a global path/ray
decomposition: components irrelevant to the cut may contain reverse rays.
Assertion 8.22 only needs the finite components reaching `BB`.  This file
therefore compiles finite source-rooted reachability witnesses directly into
the exact output consumed by the final grounding theorem.

The set `A` records the genuine roots which the construction actually uses.
The stationary bookkeeping argument supplies a source outside `A`; hence it
is absent even from the initial set of the whole constructed warp, and a
fortiori from the initial set of its essential part.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingAssertion822Output

open DirectedPath Alternating
open GroundingRootedReachabilityWarp

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Finite rooted reachability to the antichain `BB`, together with one
unused original source, gives the exact geometric and missing-source output
of Assertion 8.22. -/
theorem exists_of_rootedReachability
    (L : PopularAuxiliary.Input Gamma I) (C : Set L.LV)
    (E : Set (V × V)) (A B : Set V)
    (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hAsource : A ⊆ Gamma.source)
    (hBsubset : B ⊆ GroundingCut.BB L C)
    (hBseparator : Popular.IsSeparator Gamma B)
    (hanti : IsReachabilityAntichain E B)
    (hroot : ∀ b ∈ B, ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b)
    (unused : V) (hunusedSource : unused ∈ Gamma.source)
    (hunused : unused ∉ A) :
    Nonempty (GroundingFinalAssembly.Assertion822Output L C) := by
  classical
  obtain ⟨P, hcover, hpaths⟩ :=
    exists_rootedReachabilityWarp hEadj hbi hAsource hanti hroot
  let W : Set Gamma.DPath := PopularSwitching.pathFamily P
  refine ⟨{
    warp := W
    isWarp := PopularSwitching.pathFamily_isWarp P
    initial_subset_source :=
      PopularSwitching.pathFamily_initialSet_subset P
    frontier := B
    terminalFrontier_eq :=
      PopularSwitching.pathFamily_terminalFrontier_eq P hcover
    frontier_subset_BB := hBsubset
    frontier_separates := hBseparator
    essential_initial_ne_source := ?_ }⟩
  intro heq
  have huInitial : unused ∈
      Gamma.initialSet (Gamma.essentialWarpPart W) :=
    heq.symm ▸ hunusedSource
  obtain ⟨p, hpEssential, hpInitial⟩ := huInitial
  obtain ⟨q, hqP, hpq⟩ := hpEssential.1
  cases hpq
  apply hunused
  have hqA : q.start ∈ A := (hpaths q hqP).2.1
  exact hpInitial ▸ hqA

end GroundingAssertion822Output

namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode
open GroundingErasedSwitchRelation GroundingErasedForwardConflict
open GroundingRootedReachabilityWarp

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The frontier-stopped switched relation with an explicit control package.
This is the integration point for control refinements, such as reserving one
grounded record before making the simultaneous choices. -/
abbrev assertion822SwitchedEdgesAtWithControls
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (K : GroundingSelection.Controls S) (T : Set V) : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt (L.popularAuxiliaryIndexed hL) S K T

/-- The concrete active-control switched relation used in the specialized
Assertion 8.22 assembly. -/
abbrev assertion822SwitchedEdges
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) :
    Set (V × V) :=
  erasedSelectedSwitchedEdges (L.popularAuxiliaryIndexed hL) S
    (L.groundedConcreteControls hL S)

/-- The repaired switched relation stopped at an arbitrary globally chosen
frontier `T`.  Points of `BB \ T` remain pass-through vertices. -/
abbrev assertion822SwitchedEdgesAt
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (T : Set V) : Set (V × V) :=
  L.assertion822SwitchedEdgesAtWithControls hL S
    (L.groundedConcreteControls hL S) T

/-- Concrete local bi-uniqueness of the active switched relation. -/
theorem assertion822SwitchedEdges_biUnique
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ L.assertion822SwitchedEdges hL S) := by
  exact erasedSelectedSwitchedEdges_biUnique
    (L.popularAuxiliaryIndexed hL) S (L.groundedConcreteControls hL S)
      (L.popularAuxiliary_proxyPathsFaithful hL)

/-- Bi-uniqueness for a frontier-stopped switch is uniform in the chosen
control package. -/
theorem assertion822SwitchedEdgesAtWithControls_biUnique
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (K : GroundingSelection.Controls S) (T : Set V) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ L.assertion822SwitchedEdgesAtWithControls hL S K T) := by
  exact erasedSelectedSwitchedEdgesAt_biUnique
    (L.popularAuxiliaryIndexed hL) S K T
      (L.popularAuxiliary_proxyPathsFaithful hL)

/-- Concrete bi-uniqueness for the switch stopped at `T`. -/
theorem assertion822SwitchedEdgesAt_biUnique
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (T : Set V) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ L.assertion822SwitchedEdgesAt hL S T) := by
  exact L.assertion822SwitchedEdgesAtWithControls_biUnique hL S
    (L.groundedConcreteControls hL S) T

/-- Every chosen stopping frontier is a reachability antichain, uniformly
in the controls used to build the switched relation. -/
theorem assertion822SwitchedEdgesAtWithControls_reachabilityAntichain
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (K : GroundingSelection.Controls S) (T : Set V) :
    IsReachabilityAntichain
      (L.assertion822SwitchedEdgesAtWithControls hL S K T) T := by
  intro b hb c _hc hbc
  exact GroundingBlockingReachability.eq_of_reflTransGen_of_noOutgoing
    (boundary_noOutgoing_switchedAt (L.popularAuxiliaryIndexed hL) S
      K T hb) hbc

/-- A chosen stopping frontier is automatically a reachability antichain. -/
theorem assertion822SwitchedEdgesAt_reachabilityAntichain
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (T : Set V) :
    IsReachabilityAntichain (L.assertion822SwitchedEdgesAt hL S T) T := by
  exact L.assertion822SwitchedEdgesAtWithControls_reachabilityAntichain
    hL S (L.groundedConcreteControls hL S) T

/-- Exact frontier compiler with an explicit control package.  All relation
geometry is uniform in `K`; the only construction-specific input is rooted
reachability of the selected frontier away from the reserved original
source. -/
theorem assertion822Output_of_frontierGeometryWithControls
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (K : GroundingSelection.Controls S)
    (T : Set V)
    (hTsubset : T ⊆
      GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut)
    (hTseparator : Popular.IsSeparator Gamma T)
    (hroot : ∀ t ∈ T,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈
              L.assertion822SwitchedEdgesAtWithControls hL S K T) a t) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) := by
  apply GroundingAssertion822Output.exists_of_rootedReachability
    (L.popularAuxiliaryInput hL.legal) S.cut
    (L.assertion822SwitchedEdgesAtWithControls hL S K T)
    (Gamma.source \ {R.record.initial}) T
    (erasedSelectedSwitchedEdgesAt_subset_adj
      (L.popularAuxiliaryIndexed hL) S K T)
    (L.assertion822SwitchedEdgesAtWithControls_biUnique hL S K T)
    Set.sdiff_subset hTsubset hTseparator
    (L.assertion822SwitchedEdgesAtWithControls_reachabilityAntichain
      hL S K T)
    hroot R.record.initial R.record_initial_mem_source
  simp

/-- Exact `T`-aware Assertion 8.22 compiler.  After global selection of a
separating sub-boundary, the only remaining geometric input is source-rooted
reachability of its points in the switch stopped at that same boundary. -/
theorem assertion822Output_of_frontierGeometry
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (T : Set V)
    (hTsubset : T ⊆
      GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut)
    (hTseparator : Popular.IsSeparator Gamma T)
    (hroot : ∀ t ∈ T,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822SwitchedEdgesAt hL S T) a t) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) := by
  exact L.assertion822Output_of_frontierGeometryWithControls hL S R
    (L.groundedConcreteControls hL S) T hTsubset hTseparator hroot

/-- Specialized final packaging once the two literal switched-relation
facts and the source-rooted reachability statement have been proved.  The
allowed root set is exactly the original source with the stationary unused
root removed. -/
theorem assertion822Output_of_switchedGeometry
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (hseparator : Popular.IsSeparator Gamma
      (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut))
    (hanti : IsReachabilityAntichain
      (L.assertion822SwitchedEdges hL S)
      (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut))
    (hroot : ∀ b ∈
        GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ L.assertion822SwitchedEdges hL S) a b) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) := by
  apply GroundingAssertion822Output.exists_of_rootedReachability
    (L.popularAuxiliaryInput hL.legal) S.cut
    (L.assertion822SwitchedEdges hL S)
    (Gamma.source \ {R.record.initial})
    (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut)
    (erasedSelectedSwitchedEdges_subset_adj
      (L.popularAuxiliaryIndexed hL) S (L.groundedConcreteControls hL S))
    (L.assertion822SwitchedEdges_biUnique hL S)
    Set.sdiff_subset Subset.rfl hseparator hanti hroot R.record.initial
    R.record_initial_mem_source
  simp

/-- Casewise concrete form of `assertion822Output_of_switchedGeometry`.
The three reachability premises correspond exactly to the literal
decomposition `BB = CV ∪ BL`: a finite old cut source, an actual old
request exit, or the blocking point of a retained fragment.  In the finite
source branch the original cut-membership proof is retained, rather than
discarded by a coarser trichotomy. -/
theorem assertion822Output_of_reachabilityCases
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (hseparator : Popular.IsSeparator Gamma
      (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut))
    (hanti : IsReachabilityAntichain
      (L.assertion822SwitchedEdges hL S)
      (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut))
    (hfinite : ∀ b,
      b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource →
      PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ L.assertion822SwitchedEdges hL S) a b)
    (hold : ∀ b
      (r : PopularGroundingBridge.Request
        (L.popularAuxiliaryInput hL.legal) S.cut),
      PopularGroundingBridge.requestAuxVertex r =
          PopularAuxiliary.Input.LambdaVertex.old b →
      GroundingErasedDecode.requestExit r = b →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ L.assertion822SwitchedEdges hL S) a b)
    (hblocking : ∀ P : (L.popularAuxiliaryInput hL.legal).Fragment,
      P ∈ GroundingCut.G0
          (L.popularAuxiliaryInput hL.legal) S.cut →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ L.assertion822SwitchedEdges hL S) a
            (GroundingCut.blockingPoint
              (L.popularAuxiliaryInput hL.legal) S.cut P)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) := by
  apply L.assertion822Output_of_switchedGeometry hL S R hseparator hanti
  intro b hb
  rcases hb with hbCV | hbBL
  · rcases GroundingBBGeometry.mem_CV_finiteSource_or_oldRequestExit hbCV with
      hbSource | ⟨r, hrOld, hrExit⟩
    · exact hfinite b hbSource (GroundingCut.mem_CV.1 hbCV)
    · exact hold b r hrOld hrExit
  · obtain ⟨P, hP, hPb⟩ := hbBL
    rw [← hPb]
    exact hblocking P hP

/-- Final concrete Assertion 8.22 compiler.  The reachability antichain is
not an independent geometric input: finite cut sources and old requests are
already sinks, so `bb_reachabilityAntichain_of_blocking` reduces it to the
single blocking-point rigidity statement below.  The other three premises
are precisely the rooted cases in the literal decomposition `BB = CV ∪ BL`.
-/
theorem assertion822Output_of_concreteGeometry
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (hseparator : Popular.IsSeparator Gamma
      (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut))
    (hantiBlocking : ∀
      P : (L.popularAuxiliaryInput hL.legal).Fragment,
      P ∈ GroundingCut.G0
          (L.popularAuxiliaryInput hL.legal) S.cut →
      GroundingCut.IsBlockable
          (L.popularAuxiliaryInput hL.legal) S.cut P →
      ∀ c ∈ GroundingCut.BB
          (L.popularAuxiliaryInput hL.legal) S.cut,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ L.assertion822SwitchedEdges hL S)
          (GroundingCut.blockingPoint
            (L.popularAuxiliaryInput hL.legal) S.cut P) c →
        GroundingCut.blockingPoint
          (L.popularAuxiliaryInput hL.legal) S.cut P = c)
    (hfinite : ∀ b,
      b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource →
      PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ L.assertion822SwitchedEdges hL S) a b)
    (hold : ∀ b
      (r : PopularGroundingBridge.Request
        (L.popularAuxiliaryInput hL.legal) S.cut),
      PopularGroundingBridge.requestAuxVertex r =
          PopularAuxiliary.Input.LambdaVertex.old b →
      GroundingErasedDecode.requestExit r = b →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ L.assertion822SwitchedEdges hL S) a b)
    (hblocking : ∀
      P : (L.popularAuxiliaryInput hL.legal).Fragment,
      P ∈ GroundingCut.G0
          (L.popularAuxiliaryInput hL.legal) S.cut →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ L.assertion822SwitchedEdges hL S) a
            (GroundingCut.blockingPoint
              (L.popularAuxiliaryInput hL.legal) S.cut P)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) := by
  apply L.assertion822Output_of_reachabilityCases hL S R hseparator
    (L.bb_reachabilityAntichain_of_blocking hL S hantiBlocking)
  · exact hfinite
  · exact hold
  · exact hblocking

/-- The current first-boundary switch makes the reachability-antichain
premise unconditional: every point of `BB` is a sink.  Consequently the
final Assertion 8.22 compiler only needs the three genuine rooting cases.
The blocking case is stated on `boundaryG0`, exactly the domain whose image
defines the normalized set `BL`. -/
theorem assertion822Output_of_rootedCases
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (hseparator : Popular.IsSeparator Gamma
      (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut))
    (hfinite : ∀ b,
      b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource →
      PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ L.assertion822SwitchedEdges hL S) a b)
    (hold : ∀ b
      (r : PopularGroundingBridge.Request
        (L.popularAuxiliaryInput hL.legal) S.cut),
      PopularGroundingBridge.requestAuxVertex r =
          PopularAuxiliary.Input.LambdaVertex.old b →
      GroundingErasedDecode.requestExit r = b →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ L.assertion822SwitchedEdges hL S) a b)
    (hblocking : ∀
      P : (L.popularAuxiliaryInput hL.legal).Fragment,
      P ∈ GroundingCut.G0
          (L.popularAuxiliaryInput hL.legal) S.cut →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ L.assertion822SwitchedEdges hL S) a
            (GroundingCut.blockingPoint
              (L.popularAuxiliaryInput hL.legal) S.cut P)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) := by
  apply L.assertion822Output_of_switchedGeometry hL S R hseparator
    (GroundingBlockingReachability.erasedSelectedSwitchedEdges_reachabilityAntichain
      (L.popularAuxiliaryIndexed hL) S (L.groundedConcreteControls hL S))
  intro b hb
  rcases hb with hbCV | hbBL
  · rcases GroundingBBGeometry.mem_CV_finiteSource_or_oldRequestExit hbCV with
      hbSource | ⟨r, hrOld, hrExit⟩
    · exact hfinite b hbSource (GroundingCut.mem_CV.1 hbCV)
    · exact hold b r hrOld hrExit
  · obtain ⟨P, hP, hPb⟩ := hbBL
    rw [← hPb]
    exact hblocking P hP

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.GroundingAssertion822Output.exists_of_rootedReachability
#print axioms Erdos599.DWeb.KappaLadder.assertion822SwitchedEdgesAtWithControls_biUnique
#print axioms Erdos599.DWeb.KappaLadder.assertion822Output_of_frontierGeometryWithControls
