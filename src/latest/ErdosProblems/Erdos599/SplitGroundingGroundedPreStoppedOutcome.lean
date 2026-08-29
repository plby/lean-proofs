/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedSeparatorOutput

/-!
# Exact pre-stopped outcomes for the grounded split separator

This is the split-legal, final-control analogue of the source's honest
Assertion 8.22 trichotomy.  It does not assert that the raw boundary is an
antichain or that every boundary point is rooted.  Failure of either fact is
retained as a concrete witness for the construction-specific normalization.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open GroundingErasedDecode GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev GroundedOutcomeInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev GroundedOutcomeIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- A raw boundary point with no source root after the reserved source has
been removed. -/
structure SplitGroundedPreStoppedRootObstruction
    (R : L.SplitGroundedUnusedRecord hL hground S K) where
  boundary : V
  boundary_mem : boundary ∈ GroundingCut.BB
    (GroundedOutcomeInput (L := L) (hL := hL)) S.cut
  not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
        (GroundedOutcomeIndexed (L := L) (hL := hL)
          (hground := hground)) S K ∅) a boundary

/-- Two distinct raw boundary points occurring in order in one directed
pre-stopped component. -/
structure SplitGroundedPreStoppedBoundaryObstruction
    (R : L.SplitGroundedUnusedRecord hL hground S K) where
  earlier : V
  later : V
  earlier_mem : earlier ∈ GroundingCut.BB
    (GroundedOutcomeInput (L := L) (hL := hL)) S.cut
  later_mem : later ∈ GroundingCut.BB
    (GroundedOutcomeInput (L := L) (hL := hL)) S.cut
  distinct : earlier ≠ later
  reaches : Relation.ReflTransGen
    (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
      (GroundedOutcomeIndexed (L := L) (hL := hL)
        (hground := hground)) S K ∅) earlier later

/-- If all raw boundary points are rooted, either 8.22 is complete or a
specific ordered pair witnesses failure of the antichain condition. -/
theorem splitGroundedAssertion822Output_or_preStoppedBoundaryObstruction
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hroot : ∀ b ∈ GroundingCut.BB
        (GroundedOutcomeInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedOutcomeIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a b) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (GroundedOutcomeInput (L := L) (hL := hL)) S.cut) ∨
      Nonempty (L.SplitGroundedPreStoppedBoundaryObstruction R) := by
  classical
  by_cases hanti : IsReachabilityAntichain
      (erasedSelectedSwitchedEdgesAt
        (GroundedOutcomeIndexed (L := L) (hL := hL)
          (hground := hground)) S K ∅)
      (GroundingCut.BB
        (GroundedOutcomeInput (L := L) (hL := hL)) S.cut)
  · exact Or.inl
      (L.splitGroundedAssertion822Output_of_preStoppedRootedAntichain_withControls
        R hanti hroot)
  · right
    by_contra hnone
    apply hanti
    intro b hb c hc hbc
    by_contra hne
    exact hnone ⟨{
      earlier := b
      later := c
      earlier_mem := hb
      later_mem := hc
      distinct := hne
      reaches := hbc }⟩

/-- Total, assumption-free logical reduction for fixed final controls and
reserved record.  The two obstruction records are the only remaining
geometric branches. -/
theorem splitGroundedAssertion822Output_or_preStoppedObstruction
    (R : L.SplitGroundedUnusedRecord hL hground S K) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (GroundedOutcomeInput (L := L) (hL := hL)) S.cut) ∨
      Nonempty (L.SplitGroundedPreStoppedRootObstruction R) ∨
      Nonempty (L.SplitGroundedPreStoppedBoundaryObstruction R) := by
  classical
  by_cases hroot : ∀ b ∈ GroundingCut.BB
      (GroundedOutcomeInput (L := L) (hL := hL)) S.cut,
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedOutcomeIndexed (L := L) (hL := hL)
            (hground := hground)) S K ∅) a b
  · rcases L.splitGroundedAssertion822Output_or_preStoppedBoundaryObstruction
      R hroot with houtput | hboundary
    · exact Or.inl houtput
    · exact Or.inr (Or.inr hboundary)
  · right
    left
    by_contra hnone
    apply hroot
    intro b hb
    by_contra hnotRooted
    exact hnone ⟨{
      boundary := b
      boundary_mem := hb
      not_rooted := hnotRooted }⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedAssertion822Output_or_preStoppedObstruction
