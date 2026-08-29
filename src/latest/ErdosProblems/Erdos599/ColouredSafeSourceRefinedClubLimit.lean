/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeSourceRefinedWarpLimit
import ErdosProblems.Erdos599.IndexedRelationLimitHitSource
import ErdosProblems.Erdos599.HalfwayClubRangeSup
import ErdosProblems.Erdos599.DeferredLegalLimitHitClosure

/-!
# Native structural limits at the actual club supremum

Ladder hit closure transports retained-reference source coverage to a
supremum even when the limiting reference contains rays. The exact native
relation-limit warp then has the size, roof, closed-carrier, and source
fields at the actual bounded club supremum. Strong rays and terminal
legality are not asserted here and remain separate proof obligations.
-/

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-- A single native warp covering all earlier slices covers their
supremum. The reference need not have finite character. -/
theorem coversSource_at_lub_of_limitHitClosure
    {I : Type v} [LinearOrder I] [Nonempty I]
    (L : Gamma.KappaLadder theta) {Sigma : Set (Ladder.Stage theta)}
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (index : I → Ladder.Stage theta) (hmono : Monotone index)
    {a : Ladder.Stage theta} (hLUB : IsLUB (Set.range index) a)
    (hSigma : ∀ i, index i ∈ Sigma)
    (hY : Gamma.IsWarp Y) (hYlimit : Y ⊆ L.limitWarp)
    {U : Set (imaginaryWeb Y kappa).DPath}
    (hcover : ∀ i, CoversSource U (L.frontier (index i))) :
    CoversSource U (L.frontier a) := by
  classical
  intro source hsource
  by_cases hroot : source ∈ (imaginaryWeb Y kappa).initialSet U
  · exact Or.inl hroot
  · have hretained : ∀ i,
        source ∈ retainedReferenceInitials U (L.frontier (index i)) :=
      fun i ↦ (hcover i hsource).resolve_left hroot
    let i₀ : I := Classical.choice inferInstance
    obtain ⟨p, hp, hpa⟩ := hretained i₀
    have hmeet : ∀ i, (p.support ∩ L.frontier (index i)).Nonempty := by
      intro i
      obtain ⟨q, hq, hqa⟩ := hretained i
      have hqp : q = p := DWeb.IsWarp.eq_of_mem_support hY hq.1.1 hp.1.1
        (hqa ▸ q.initial_mem_support) (hpa ▸ p.initial_mem_support)
      exact hqp ▸ hq.1.2
    have hlimit := DWeb.KappaLadder.Deferred.limitWarp_meets_frontier_at_iSup
      hHit index hmono hLUB hSigma (hYlimit hp.1.1) hmeet
    exact Or.inr ⟨p, ⟨⟨hp.1.1, hlimit⟩, hp.2⟩, hpa⟩

namespace RealStageChain

variable {I : Type u} [LinearOrder I]

theorem mk_vertexUnion_le
    {frontier : I → Set V} (R : RealStageChain Gamma Y kappa I frontier)
    (hkappa : aleph0 ≤ kappa) (hindex : #I ≤ kappa)
    (hstage : ∀ i, #(R.stage i) ≤ kappa) : #R.vertexUnion ≤ kappa := by
  refine (Cardinal.mk_iUnion_le
    (fun i ↦ (imaginaryWeb Y kappa).vertexSet (R.stage i))).trans ?_
  apply Cardinal.mul_le_of_le hkappa hindex
  apply ciSup_le'
  intro i
  exact CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
    hkappa (R.stage i) (hstage i)

/-- Construct the bounded native structural limit at its actual club
index. This deliberately leaves out the two unproved blueprint fields
concerning new rays and terminal popularity. -/
theorem exists_structuralLimit_at_clubSup
    [Nonempty I]
    (G : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    (index : I → Ladder.Stage (succ kappa)) (hmono : Monotone index)
    (hclub : ∀ i, index i ∈ G.club)
    (R : RealStageChain Gamma G.ladder.limitWarp kappa I
      (fun i ↦ G.ladder.frontier (index i)))
    (hrefine : ∀ {i j}, i ≤ j → SourcePredecessorRefines (R.stage i) (R.stage j))
    (hI : Monotone fun i ↦ (imaginaryWeb G.ladder.limitWarp kappa).initialSet (R.stage i))
    (hindex : #I ≤ kappa) (closed : I → Set V) (Z persistent : Set V)
    (hstage : ∀ i, IsLinkageBlueprint (R.stage i)
      (G.ladder.frontier (index i)) (closed i) persistent)
    (hclosed : ∀ i, closed i ⊆ Z) :
    ∃ a ∈ G.club, IsLUB (Set.range index) a ∧
      ∃ U : Set (imaginaryWeb G.ladder.limitWarp kappa).DPath,
        (imaginaryWeb G.ladder.limitWarp kappa).IsWarp U ∧
        (imaginaryWeb G.ladder.limitWarp kappa).vertexSet U = R.vertexUnion ∧
        familyEdges U = R.eventualEdges ∧
        CoversSource U (G.ladder.frontier a) ∧
        (imaginaryWeb G.ladder.limitWarp kappa).vertexSet U ⊆
          Gamma.roof (G.ladder.frontier a) ∧
        (imaginaryWeb G.ladder.limitWarp kappa).vertexSet U ⊆ Z ∧
        #U ≤ kappa ∧
        ∀ i, (imaginaryWeb G.ladder.limitWarp kappa).initialSet (R.stage i) ⊆
          (imaginaryWeb G.ladder.limitWarp kappa).initialSet U := by
  obtain ⟨D⟩ := HalfwayClubRangeSup.exists_data G.capacity_infinite
    (by simpa using hindex) G.club_isClub index hmono hclub
  have hY : Gamma.IsWarp G.ladder.limitWarp :=
    G.legal.warpStages (Ladder.finalStage (succ kappa))
  obtain ⟨U, hU, hUV, hUE, hInitials, hCoverage⟩ :=
    R.exists_eventualWarp_with_oldCoverage hY hrefine hI
  have hcover : CoversSource U (G.ladder.frontier D.supIndex) :=
    coversSource_at_lub_of_limitHitClosure G.ladder G.limitHitClosure
      index hmono D.range_isLUB hclub hY Set.Subset.rfl hCoverage
  refine ⟨D.supIndex, D.supIndex_mem, D.range_isLUB, U, hU, hUV, hUE,
    hcover, ?_, ?_, ?_, hInitials⟩
  · rw [hUV]
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rcases (D.previous_le i).lt_or_eq with hlt | heq
    · exact Gamma.roof_cut (G.legal.frontierChronology hlt)
        ((hstage i).vertices_roofed hi)
    · exact heq ▸ (hstage i).vertices_roofed hi
  · rw [hUV]
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hclosed i ((hstage i).vertices_closed hi)
  · apply (mk_paths_le_vertexSet hU).trans
    rw [hUV]
    exact R.mk_vertexUnion_le G.capacity_infinite hindex (fun i ↦ (hstage i).card_paths)

#print axioms mk_vertexUnion_le
#print axioms exists_structuralLimit_at_clubSup

end RealStageChain

#print axioms coversSource_at_lub_of_limitHitClosure

end Erdos599.Blueprint.ColouredSafeShortcutGraph
