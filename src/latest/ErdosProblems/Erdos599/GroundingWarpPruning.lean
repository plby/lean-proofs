/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.PopularSwitching
import ErdosProblems.Erdos599.SafeSwitchingAssembly
import ErdosProblems.Erdos599.GroundingFinalAssembly

/-!
# Pruning an arbitrary warp at a transversal

This file isolates the path-theoretic pruning used at the end of Assertion
8.22.  The input warp may contain both finite paths and rays.  We retain
exactly the components meeting a set `B`, truncate each retained component
at its first `B`-vertex, and obtain a finite source--`B` warp.

The equality of the new terminal frontier with all of `B` needs the actual
Assertion 8.21 hypothesis that each old component meets `B` at most once.
Without it, a component containing two points of `B` would contribute only
its first point after pruning.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingWarpPruning

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- An old warp component together with the fact that it meets `B`. -/
structure MeetingComponent (W : Set Gamma.DPath) (B : Set V) where
  path : Gamma.DPath
  mem : path ∈ W
  meets : ∃ x ∈ path.support, x ∈ B

namespace MeetingComponent

private theorem finiteMeets {B : Set V} (p : FinitePath Gamma.graph)
    (h : ∃ x ∈ Path.support (Sum.inl p : Gamma.DPath), x ∈ B) :
    p.walk.Meets B := by
  obtain ⟨x, hx, hxB⟩ := h
  exact ⟨x, hx, hxB⟩

private theorem rayMeets {B : Set V} (r : Ray Gamma.graph)
    (h : ∃ x ∈ Path.support (Sum.inr r : Gamma.DPath), x ∈ B) :
    ∃ x ∈ r.support, x ∈ B := by
  exact h

private theorem exists_rayHitIndex {B : Set V} (r : Ray Gamma.graph)
    (h : ∃ x ∈ r.support, x ∈ B) : ∃ n : ℕ, r n ∈ B := by
  obtain ⟨x, ⟨n, rfl⟩, hxB⟩ := h
  exact ⟨n, hxB⟩

/-- The first index at which a ray meeting `B` enters `B`. -/
noncomputable def rayHitIndex {B : Set V} (r : Ray Gamma.graph)
    (h : ∃ x ∈ r.support, x ∈ B) : ℕ := by
  classical
  exact Nat.find (exists_rayHitIndex r h)

theorem rayHitIndex_mem {B : Set V} (r : Ray Gamma.graph)
    (h : ∃ x ∈ r.support, x ∈ B) :
    r (rayHitIndex r h) ∈ B := by
  classical
  simpa only [rayHitIndex] using Nat.find_spec (exists_rayHitIndex r h)

theorem rayHitIndex_min {B : Set V} (r : Ray Gamma.graph)
    (h : ∃ x ∈ r.support, x ∈ B) {n : ℕ}
    (hn : n < rayHitIndex r h) : r n ∉ B := by
  classical
  apply Nat.find_min (exists_rayHitIndex r h)
  simpa only [rayHitIndex] using hn

/-- The finite first-hit prefix of a finite path or ray. -/
noncomputable def firstHitPrefix {W : Set Gamma.DPath} {B : Set V}
    (c : MeetingComponent W B) : FinitePath Gamma.graph := by
  rcases c with ⟨p | r, hp, hm⟩
  · exact p.firstHit B (finiteMeets p hm)
  · exact Alternating.SwitchingCore.rayPrefixPath r
      (rayHitIndex r (rayMeets r hm))

@[simp] theorem firstHitPrefix_start {W : Set Gamma.DPath} {B : Set V}
    (c : MeetingComponent W B) :
    c.firstHitPrefix.start = c.path.initial := by
  rcases c with ⟨p | r, hp, hm⟩
  · simp only [firstHitPrefix]
    rfl
  · simp only [firstHitPrefix]
    rfl

theorem rayPrefixPath_support_subset (r : Ray Gamma.graph) (n : ℕ) :
    (Alternating.SwitchingCore.rayPrefixPath r n).support ⊆ r.support := by
  intro x hx
  change x ∈ (Alternating.SwitchingCore.rayPrefixWalk r n).support at hx
  rw [Alternating.SwitchingCore.rayPrefixWalk_support, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact ⟨i, rfl⟩

theorem firstHitPrefix_support_subset {W : Set Gamma.DPath} {B : Set V}
    (c : MeetingComponent W B) :
    c.firstHitPrefix.support ⊆ c.path.support := by
  rcases c with ⟨p | r, hp, hm⟩
  · simp only [firstHitPrefix]
    exact p.firstHit_support_subset B (finiteMeets p hm)
  · simp only [firstHitPrefix]
    exact rayPrefixPath_support_subset r
      (rayHitIndex r (rayMeets r hm))

@[simp] theorem firstHitPrefix_finish_mem {W : Set Gamma.DPath} {B : Set V}
    (c : MeetingComponent W B) : c.firstHitPrefix.finish ∈ B := by
  rcases c with ⟨p | r, hp, hm⟩
  · simp only [firstHitPrefix]
    exact p.firstHit_finish_mem B (finiteMeets p hm)
  · simp only [firstHitPrefix]
    exact rayHitIndex_mem r (rayMeets r hm)

end MeetingComponent

/-- The set of all finite first-hit prefixes of components of `W` meeting
`B`.  The set quotient automatically identifies definitionally equal
prefixes, although warp disjointness below shows that distinct components
cannot produce intersecting prefixes. -/
def prunedPaths (W : Set Gamma.DPath) (B : Set V) :
    Set (FinitePath Gamma.graph) :=
  Set.range (fun c : MeetingComponent W B ↦ c.firstHitPrefix)

theorem prunedPaths_disjoint {W : Set Gamma.DPath} {B : Set V}
    (hW : Gamma.IsWarp W) :
    (prunedPaths W B).PairwiseDisjoint FinitePath.support := by
  rintro q ⟨c, rfl⟩ r ⟨d, rfl⟩ hqr
  have hcd : c.path ≠ d.path := by
    intro hpath
    have hcomp : c = d := by
      cases c
      cases d
      simp_all
    exact hqr (congrArg MeetingComponent.firstHitPrefix hcomp)
  exact (hW c.mem d.mem hcd).mono
    c.firstHitPrefix_support_subset d.firstHitPrefix_support_subset

/-- Pruning at first hits gives a finite source--`B` warp. -/
noncomputable def prunedXSWarp (W : Set Gamma.DPath) (B : Set V)
    (hsource : ∀ (p : Gamma.DPath), p ∈ W →
      (∃ x ∈ p.support, x ∈ B) → p.initial ∈ Gamma.source)
    (hW : Gamma.IsWarp W) : Popular.XSWarp Gamma B where
  paths := prunedPaths W B
  disjoint := prunedPaths_disjoint hW
  starts_in_source := by
    rintro p ⟨c, rfl⟩
    rw [c.firstHitPrefix_start]
    exact hsource c.path c.mem c.meets
  ends_in_target := by
    rintro p ⟨c, rfl⟩
    exact c.firstHitPrefix_finish_mem

theorem mem_prunedXSWarp_iff (W : Set Gamma.DPath) (B : Set V)
    (hsource : ∀ (p : Gamma.DPath), p ∈ W →
      (∃ x ∈ p.support, x ∈ B) → p.initial ∈ Gamma.source)
    (hW : Gamma.IsWarp W) {q : FinitePath Gamma.graph} :
    q ∈ (prunedXSWarp W B hsource hW).paths ↔
      ∃ c : MeetingComponent W B, c.firstHitPrefix = q := by
  rfl

/-- If every old component meets `B` in at most one vertex and `B` is
covered by the old warp, every point of `B` is the terminal of one pruned
prefix. -/
theorem prunedXSWarp_covers (W : Set Gamma.DPath) (B : Set V)
    (hsource : ∀ (p : Gamma.DPath), p ∈ W →
      (∃ x ∈ p.support, x ∈ B) → p.initial ∈ Gamma.source)
    (hW : Gamma.IsWarp W)
    (hcover : B ⊆ Gamma.vertexSet W)
    (hone : ∀ (p : Gamma.DPath), p ∈ W →
      (p.support ∩ B).Subsingleton) :
    ∀ b ∈ B, ∃ q ∈ (prunedXSWarp W B hsource hW).paths,
      q.finish = b := by
  intro b hb
  obtain ⟨p, hpW, hbp⟩ := hcover hb
  let c : MeetingComponent W B :=
    ⟨p, hpW, ⟨b, hbp, hb⟩⟩
  refine ⟨c.firstHitPrefix, ⟨c, rfl⟩, ?_⟩
  apply hone p hpW
  · exact ⟨c.firstHitPrefix_support_subset
      c.firstHitPrefix.finish_mem_support,
      c.firstHitPrefix_finish_mem⟩
  · exact ⟨hbp, hb⟩

/-- Family-valued form of pruning.  This is the object expected by the
ordinary-web output of Assertion 8.22. -/
def prunedFamily (W : Set Gamma.DPath) (B : Set V)
    (hsource : ∀ (p : Gamma.DPath), p ∈ W →
      (∃ x ∈ p.support, x ∈ B) → p.initial ∈ Gamma.source)
    (hW : Gamma.IsWarp W) : Set Gamma.DPath :=
  PopularSwitching.pathFamily (prunedXSWarp W B hsource hW)

theorem prunedFamily_isWarp (W : Set Gamma.DPath) (B : Set V)
    (hsource : ∀ (p : Gamma.DPath), p ∈ W →
      (∃ x ∈ p.support, x ∈ B) → p.initial ∈ Gamma.source)
    (hW : Gamma.IsWarp W) :
    Gamma.IsWarp (prunedFamily W B hsource hW) :=
  PopularSwitching.pathFamily_isWarp (prunedXSWarp W B hsource hW)

theorem prunedFamily_initialSet_subset (W : Set Gamma.DPath) (B : Set V)
    (hsource : ∀ (p : Gamma.DPath), p ∈ W →
      (∃ x ∈ p.support, x ∈ B) → p.initial ∈ Gamma.source)
    (hW : Gamma.IsWarp W) :
    Gamma.initialSet (prunedFamily W B hsource hW) ⊆ Gamma.source :=
  PopularSwitching.pathFamily_initialSet_subset
    (prunedXSWarp W B hsource hW)

/-- The initial-set estimate for first-hit pruning with an arbitrary set of
allowed roots.  This is the form needed in Assertion 8.22 after reserving
one original source: only components which actually meet the boundary are
retained, so it is enough to control the initial vertex of those components. -/
theorem prunedFamily_initialSet_subset_of (W : Set Gamma.DPath) (B A : Set V)
    (hsource : ∀ (p : Gamma.DPath), p ∈ W →
      (∃ x ∈ p.support, x ∈ B) → p.initial ∈ Gamma.source)
    (hW : Gamma.IsWarp W)
    (hroot : ∀ (p : Gamma.DPath), p ∈ W →
      (∃ x ∈ p.support, x ∈ B) → p.initial ∈ A) :
    Gamma.initialSet (prunedFamily W B hsource hW) ⊆ A := by
  rintro x ⟨p, ⟨q, hq, hpq⟩, hpx⟩
  cases hpq
  obtain ⟨c, rfl⟩ := hq
  change c.firstHitPrefix.start = x at hpx
  rw [MeetingComponent.firstHitPrefix_start] at hpx
  exact hpx ▸ hroot c.path c.mem c.meets

theorem prunedFamily_terminalFrontier_eq (W : Set Gamma.DPath) (B : Set V)
    (hsource : ∀ (p : Gamma.DPath), p ∈ W →
      (∃ x ∈ p.support, x ∈ B) → p.initial ∈ Gamma.source)
    (hW : Gamma.IsWarp W)
    (hcover : B ⊆ Gamma.vertexSet W)
    (hone : ∀ (p : Gamma.DPath), p ∈ W →
      (p.support ∩ B).Subsingleton) :
    Gamma.terminalFrontier (prunedFamily W B hsource hW) = B := by
  apply PopularSwitching.pathFamily_terminalFrontier_eq
  exact prunedXSWarp_covers W B hsource hW hcover hone

/-- Every retained component contributes its first-hit prefix to the pruned
family. -/
theorem MeetingComponent.firstHitPrefix_mem_prunedFamily
    (W : Set Gamma.DPath) (B : Set V)
    (hsource : ∀ (p : Gamma.DPath), p ∈ W →
      (∃ x ∈ p.support, x ∈ B) → p.initial ∈ Gamma.source)
    (hW : Gamma.IsWarp W) (c : MeetingComponent W B) :
    (Sum.inl c.firstHitPrefix : Gamma.DPath) ∈
      prunedFamily W B hsource hW := by
  exact ⟨c.firstHitPrefix, ⟨c, rfl⟩, rfl⟩

/-- A retained prefix which misses the essential part of `B` is an
inessential member of the final pruned family. -/
theorem MeetingComponent.firstHitPrefix_mem_inessentialPaths
    (W : Set Gamma.DPath) (B : Set V)
    (hsource : ∀ (p : Gamma.DPath), p ∈ W →
      (∃ x ∈ p.support, x ∈ B) → p.initial ∈ Gamma.source)
    (hW : Gamma.IsWarp W)
    (hcover : B ⊆ Gamma.vertexSet W)
    (hone : ∀ (p : Gamma.DPath), p ∈ W →
      (p.support ∩ B).Subsingleton)
    (c : MeetingComponent W B)
    (hmiss : ¬ (Gamma.essential B ∩ c.firstHitPrefix.support).Nonempty) :
    (Sum.inl c.firstHitPrefix : Gamma.DPath) ∈
      Gamma.inessentialPaths (prunedFamily W B hsource hW) := by
  apply Gamma.mem_inessentialPaths_of_misses_essentialFrontier
    (c.firstHitPrefix_mem_prunedFamily W B hsource hW)
  rw [prunedFamily_terminalFrontier_eq W B hsource hW hcover hone]
  exact hmiss

/-- Clean bundled specification used by Assertion 8.22. -/
theorem exists_prunedFamily (W : Set Gamma.DPath) (B : Set V)
    (hW : Gamma.IsWarp W)
    (hsource : ∀ (p : Gamma.DPath), p ∈ W →
      (∃ x ∈ p.support, x ∈ B) → p.initial ∈ Gamma.source)
    (hcover : B ⊆ Gamma.vertexSet W)
    (hone : ∀ (p : Gamma.DPath), p ∈ W →
      (p.support ∩ B).Subsingleton) :
    ∃ P : Popular.XSWarp Gamma B,
      Gamma.IsWarp (PopularSwitching.pathFamily P) ∧
      Gamma.initialSet (PopularSwitching.pathFamily P) ⊆ Gamma.source ∧
      Gamma.terminalFrontier (PopularSwitching.pathFamily P) = B := by
  let P := prunedXSWarp W B hsource hW
  refine ⟨P, PopularSwitching.pathFamily_isWarp P,
    PopularSwitching.pathFamily_initialSet_subset P, ?_⟩
  apply PopularSwitching.pathFamily_terminalFrontier_eq
  exact prunedXSWarp_covers W B hsource hW hcover hone

/-- Bundle the generic pruning construction directly as the geometric
output required by Assertion 8.22.  The final hypotheses identify an
original source omitted by the essential part of the pruned family.  This
is the source-faithful post-8.22 conclusion: a component not meeting `BB`
may be discarded by first-hit pruning, but its source is nevertheless
absent from the essential part. -/
noncomputable def assertion822OutputOfPruning
    {I : Type u} (L : PopularAuxiliary.Input Gamma I) (C : Set L.LV)
    (W : Set Gamma.DPath)
    (hW : Gamma.IsWarp W)
    (hsource : ∀ (p : Gamma.DPath), p ∈ W →
      (∃ x ∈ p.support, x ∈ GroundingCut.BB L C) →
        p.initial ∈ Gamma.source)
    (hcover : GroundingCut.BB L C ⊆ Gamma.vertexSet W)
    (hone : ∀ (p : Gamma.DPath), p ∈ W →
      (p.support ∩ GroundingCut.BB L C).Subsingleton)
    (hseparator : Popular.IsSeparator Gamma (GroundingCut.BB L C))
    (a : V) (haSource : a ∈ Gamma.source)
    (haMissing : a ∉ Gamma.initialSet
      (Gamma.essentialWarpPart
        (prunedFamily W (GroundingCut.BB L C) hsource hW))) :
    GroundingFinalAssembly.Assertion822Output L C where
  warp := prunedFamily W (GroundingCut.BB L C) hsource hW
  isWarp := prunedFamily_isWarp W (GroundingCut.BB L C) hsource hW
  initial_subset_source :=
    prunedFamily_initialSet_subset W (GroundingCut.BB L C) hsource hW
  frontier := GroundingCut.BB L C
  terminalFrontier_eq :=
    prunedFamily_terminalFrontier_eq W (GroundingCut.BB L C)
      hsource hW hcover hone
  frontier_subset_BB := Subset.rfl
  frontier_separates := hseparator
  essential_initial_ne_source := by
    intro heq
    exact haMissing (heq.symm ▸ haSource)

end GroundingWarpPruning
end Erdos599
