/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReachableOutcome

/-!
# Reserved-source reduction on the reachable grounded boundary

If the reachable boundary is an antichain and the reserved-root point is
nonessential in that boundary, the whole-source rooted relation already
gives Assertion 8.22: the component ending at the nonessential point is an
inessential path in the resulting wave.  Otherwise we retain either an
essential reserved-root point or an ordered boundary pair.  This removes
all nonessential bookkeeping from the reserved-source obstruction without
depending on the legacy ordinary-legality compiler.
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

/-- The genuinely construction-specific reserved-root leaf: its displayed
source-relevant boundary point is essential in the exact reachable
separator. -/
structure SplitGroundedReachableEssentialReservedRootObstruction where
  obstruction : L.SplitGroundedReachableReservedRootObstruction
    (L.splitGroundedCanonicalUnusedRecord hL hground S)
  boundary_essential : obstruction.boundary ∈ Gamma.essential
    (L.splitGroundedReachableBB hL hground S)

private theorem assertion822Output_of_reachable_nonessential
    (R : L.SplitGroundedUnusedRecord hL hground S
      (L.splitGroundedCanonicalControls hL hground S))
    (hanti : IsReachabilityAntichain
      (L.splitGroundedCanonicalSwitchedEdgesAt hL hground S ∅)
      (L.splitGroundedReachableBB hL hground S))
    (hroot : ∀ b ∈ L.splitGroundedReachableBB hL hground S,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.splitGroundedCanonicalSwitchedEdgesAt hL hground S ∅) a b)
    (b : V) (hb : b ∈ L.splitGroundedReachableBB hL hground S)
    (hbNonessential : b ∉ Gamma.essential
      (L.splitGroundedReachableBB hL hground S)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) := by
  classical
  let E := L.splitGroundedCanonicalSwitchedEdgesAt hL hground S ∅
  let B := L.splitGroundedReachableBB hL hground S
  obtain ⟨P, hcover, hpaths⟩ :=
    GroundingRootedReachabilityWarp.exists_rootedReachabilityWarp
      (L.splitGroundedCanonicalSwitchedEdgesAt_subset_adj
        hL hground S ∅)
      (L.splitGroundedCanonicalSwitchedEdgesAt_biUnique
        hL hground S ∅)
      (Set.Subset.rfl : Gamma.source ⊆ Gamma.source) hanti hroot
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
    ⟨hwarp, hinitial, by
      intro x hx q hq
      rw [hfrontier]
      exact L.splitGroundedReachableBB_isSeparator hL hground S q
        (hq.1 ▸ hx) hq.2⟩
  refine ⟨{
    warp := W
    isWarp := hwarp
    initial_subset_source := hinitial
    frontier := B
    terminalFrontier_eq := hfrontier
    frontier_subset_BB := L.splitGroundedReachableBB_subset_BB
      hL hground S
    frontier_separates := L.splitGroundedReachableBB_isSeparator
      hL hground S
    essential_initial_ne_source :=
      (DWeb.essentialWarpPart_isHindrance_of_inessentialPath
        hwave hpInessential).2 }⟩

/-- Every reserved-source root obstruction either already gives Assertion
8.22, is essential in the exact source-relevant separator, or exposes two
distinct ordered source-relevant boundary points. -/
theorem SplitGroundedReachableReservedRootObstruction.output_or_essential_or_boundary
    (O : L.SplitGroundedReachableReservedRootObstruction
      (L.splitGroundedCanonicalUnusedRecord hL hground S)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) ∨
      Nonempty (L.SplitGroundedReachableEssentialReservedRootObstruction
        (hL := hL) (hground := hground) (S := S)) ∨
      Nonempty (L.SplitGroundedReachableBoundaryObstruction
        (L.splitGroundedCanonicalUnusedRecord hL hground S)) := by
  classical
  let E := L.splitGroundedCanonicalSwitchedEdgesAt hL hground S ∅
  let B := L.splitGroundedReachableBB hL hground S
  by_cases hanti : IsReachabilityAntichain E B
  · by_cases hbEssential : O.boundary ∈ Gamma.essential B
    · exact Or.inr (Or.inl ⟨{
        obstruction := O
        boundary_essential := hbEssential }⟩)
    · exact Or.inl (assertion822Output_of_reachable_nonessential
        (L.splitGroundedCanonicalUnusedRecord hL hground S)
        hanti O.all_boundary_rooted_from_source O.boundary
        O.boundary_mem hbEssential)
  · right
    right
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
      reaches := hbc
      earlier_rooted := O.all_boundary_rooted_from_source b hb
      later_rooted := O.all_boundary_rooted_from_source c hc }⟩

/-- Canonical source-faithful dispatcher after nonessential reserved roots
have been eliminated.  These are the three genuinely geometric failure
classes left for the grounded split branch. -/
theorem splitGroundedCanonicalAssertion822Output_or_reachableEssentialObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) ∨
      Nonempty (L.SplitGroundedReachableEssentialReservedRootObstruction
        (hL := hL) (hground := hground) (S := S)) ∨
      Nonempty (L.SplitGroundedReachableWholeSourceRootObstruction
        (L.splitGroundedCanonicalUnusedRecord hL hground S)) ∨
      Nonempty (L.SplitGroundedReachableBoundaryObstruction
        (L.splitGroundedCanonicalUnusedRecord hL hground S)) := by
  rcases L.splitGroundedCanonicalAssertion822Output_or_reachableObstruction
      hL hground S with houtput | hreserved | hwhole | hboundary
  · exact Or.inl houtput
  · rcases hreserved.some.output_or_essential_or_boundary with
        houtput | hessential | hboundary
    · exact Or.inl houtput
    · exact Or.inr (Or.inl hessential)
    · exact Or.inr (Or.inr (Or.inr hboundary))
  · exact Or.inr (Or.inr (Or.inl hwhole))
  · exact Or.inr (Or.inr (Or.inr hboundary))

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReachableReservedRootObstruction.output_or_essential_or_boundary
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedCanonicalAssertion822Output_or_reachableEssentialObstruction
