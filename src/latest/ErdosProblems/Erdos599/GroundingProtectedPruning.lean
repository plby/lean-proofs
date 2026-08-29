/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingWarpPruning
import ErdosProblems.Erdos599.GroundingMinimalSeparatingBoundary

/-!
# Source-faithful protected-component pruning

Assertion 8.22 does not require every boundary-meeting component to start
away from the omitted source.  The source construction protects the omitted
grounded component itself and proves that, if it survives first-hit pruning,
its prefix is inessential.  This file isolates exactly that argument.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingProtectedPruning

open DirectedPath GroundingWarpPruning

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- If the component starting at `a` is protected from essential first-hit
pruning, then `a` is absent from the essential part of the pruned family.

The protection premise is vacuous when the component misses `B`.  When it
meets `B`, warp disjointness identifies it with the unique meeting component
whose pruned prefix could still start at `a`. -/
theorem protectedSource_not_mem_essentialInitial
    (W : Set Gamma.DPath) (B : Set V)
    (hW : Gamma.IsWarp W)
    (hsource : ∀ (q : Gamma.DPath), q ∈ W →
      (∃ x ∈ q.support, x ∈ B) → q.initial ∈ Gamma.source)
    (p : Gamma.DPath) (hpW : p ∈ W) (a : V)
    (hpInitial : p.initial = a)
    (hprotected : ∀ c : MeetingComponent W B, c.path = p →
      (Sum.inl c.firstHitPrefix : Gamma.DPath) ∈
        Gamma.inessentialPaths (prunedFamily W B hsource hW)) :
    a ∉ Gamma.initialSet
      (Gamma.essentialWarpPart (prunedFamily W B hsource hW)) := by
  rintro ⟨q, hqEssential, hqInitial⟩
  obtain ⟨q0, hq0, hqEq⟩ := hqEssential.1
  subst q
  obtain ⟨c, hcEq⟩ := hq0
  subst q0
  have hcInitial : c.path.initial = a := by
    rw [← MeetingComponent.firstHitPrefix_start c]
    exact hqInitial
  have hcp : c.path = p := by
    by_contra hne
    exact Set.disjoint_left.1 (hW c.mem hpW hne)
      c.path.initial_mem_support
      (by rw [hcInitial, ← hpInitial]; exact p.initial_mem_support)
  exact (hprotected c hcp).2 hqEssential

/-- Compile the paper's protected omitted-component invariant directly into
Assertion 8.22.  Unlike the older root-away-from-the-omitted-source wrapper,
this permits the protected component itself to meet the bookkeeping boundary;
only its first-hit prefix must be inessential. -/
theorem assertion822Output_of_protectedPreStoppedWarp
    {I : Type u} (L : PopularAuxiliary.Input Gamma I) (C : Set L.LV)
    (W : Set Gamma.DPath)
    (hW : Gamma.IsWarp W)
    (hsource : ∀ (q : Gamma.DPath), q ∈ W →
      (∃ x ∈ q.support, x ∈ GroundingCut.BB L C) →
        q.initial ∈ Gamma.source)
    (hcover : GroundingCut.BB L C ⊆ Gamma.vertexSet W)
    (hone : ∀ (q : Gamma.DPath), q ∈ W →
      (q.support ∩ GroundingCut.BB L C).Subsingleton)
    (hseparator : Popular.IsSeparator Gamma (GroundingCut.BB L C))
    (a : V) (haSource : a ∈ Gamma.source)
    (p : Gamma.DPath) (hpW : p ∈ W) (hpInitial : p.initial = a)
    (hprotected : ∀ c : MeetingComponent W (GroundingCut.BB L C),
      c.path = p →
        (Sum.inl c.firstHitPrefix : Gamma.DPath) ∈
          Gamma.inessentialPaths
            (prunedFamily W (GroundingCut.BB L C) hsource hW)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output L C) := by
  refine ⟨?_⟩
  apply GroundingWarpPruning.assertion822OutputOfPruning
    L C W hW hsource hcover hone hseparator a haSource
  exact protectedSource_not_mem_essentialInitial
    W (GroundingCut.BB L C) hW hsource p hpW a hpInitial hprotected

/-- Source-paper specialization of
`assertion822Output_of_protectedPreStoppedWarp`: an unused component of the
unpruned simultaneous warp which misses `BB` is discarded by first-hit
pruning.  Its original source is therefore absent from the essential part
of the pruned family. -/
theorem assertion822Output_of_unusedComponent_avoids_BB
    {I : Type u} (L : PopularAuxiliary.Input Gamma I) (C : Set L.LV)
    (W : Set Gamma.DPath)
    (hW : Gamma.IsWarp W)
    (hsource : ∀ (q : Gamma.DPath), q ∈ W →
      (∃ x ∈ q.support, x ∈ GroundingCut.BB L C) →
        q.initial ∈ Gamma.source)
    (hcover : GroundingCut.BB L C ⊆ Gamma.vertexSet W)
    (hone : ∀ (q : Gamma.DPath), q ∈ W →
      (q.support ∩ GroundingCut.BB L C).Subsingleton)
    (hseparator : Popular.IsSeparator Gamma (GroundingCut.BB L C))
    (a : V) (haSource : a ∈ Gamma.source)
    (p : Gamma.DPath) (hpW : p ∈ W) (hpInitial : p.initial = a)
    (hpAvoids : Disjoint p.support (GroundingCut.BB L C)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output L C) := by
  apply assertion822Output_of_protectedPreStoppedWarp
    L C W hW hsource hcover hone hseparator a haSource p hpW hpInitial
  intro c hcp
  exfalso
  obtain ⟨x, hxc, hxB⟩ := c.meets
  exact Set.disjoint_left.1 hpAvoids (hcp ▸ hxc) hxB

/-- The source-faithful final interface for Assertion 8.22.

The simultaneous construction need not root every boundary component away
from one distinguished source.  It is enough to construct a warp starting
in the original source, whose actual terminal frontier is a separating
subset of `BB`, and to preserve one component as inessential.  Essential
trimming then omits the initial vertex of that component automatically. -/
theorem assertion822Output_of_protectedInessentialWarp
    {I : Type u} (L : PopularAuxiliary.Input Gamma I) (C : Set L.LV)
    (W : Set Gamma.DPath)
    (hW : Gamma.IsWarp W)
    (hinitial : Gamma.initialSet W ⊆ Gamma.source)
    (T : Set V)
    (hfrontier : Gamma.terminalFrontier W = T)
    (hTsubset : T ⊆ GroundingCut.BB L C)
    (hTseparator : Popular.IsSeparator Gamma T)
    (p : Gamma.DPath)
    (hpInessential : p ∈ Gamma.inessentialPaths W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output L C) := by
  have hWave : Gamma.IsWave W :=
    ⟨hW, hinitial, by
      rw [hfrontier]
      exact (GroundingMinimalSeparatingBoundary.isSeparator_iff_source_subset_roof
        T).1 hTseparator⟩
  exact ⟨{
    warp := W
    isWarp := hW
    initial_subset_source := hinitial
    frontier := T
    terminalFrontier_eq := hfrontier
    frontier_subset_BB := hTsubset
    frontier_separates := hTseparator
    essential_initial_ne_source :=
      (DWeb.essentialWarpPart_isHindrance_of_inessentialPath
        hWave hpInessential).2 }⟩

end GroundingProtectedPruning
end Erdos599

#print axioms Erdos599.GroundingProtectedPruning.protectedSource_not_mem_essentialInitial
#print axioms Erdos599.GroundingProtectedPruning.assertion822Output_of_protectedPreStoppedWarp
#print axioms Erdos599.GroundingProtectedPruning.assertion822Output_of_unusedComponent_avoids_BB
#print axioms Erdos599.GroundingProtectedPruning.assertion822Output_of_protectedInessentialWarp
