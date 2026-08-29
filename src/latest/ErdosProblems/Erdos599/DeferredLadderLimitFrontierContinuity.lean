/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredLimitMiss
import ErdosProblems.Erdos599.DeferredRegularGeometry

/-!
# Continuity of deferred-ladder frontiers at genuine limits

For a cofinal monotone family of earlier ladder stages, put
`R_i = roof (frontier i)` and `D_i = strictRoof (frontier i)`.  The
set-theoretic boundary `(⋃ i, R_i) \ ⋃ i, D_i` is contained in the
frontier at the supremum stage.

The nontrivial point is that a vertex which is essential at every stage
of a cofinal tail cannot become inessential for the first time at the
limit.  Genuine threadwise limits first produce the finite limit component
ending at that vertex.  If it were inessential at the limit, persistence
would put it in the final ladder warp.  The directed-supremum closure of
its hit stages would then force it to meet the limit frontier, a
contradiction.

This one-sided continuity statement is exactly the direction needed to
transport moving-frontier source coverage.  It does not assert the
unsupported converse, which would require every new limit-frontier vertex
to occur below the limit.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

universe u v

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}
variable {L : G.KappaLadder kappa}
variable {I : Type v} [LinearOrder I] [Nonempty I]

private theorem roof_frontier_mono
    (hL : HalfwayGeometry L) {a b : Ladder.Stage kappa}
    (hab : a ≤ b) :
    G.roof (L.frontier a) ⊆ G.roof (L.frontier b) := by
  rcases hab.lt_or_eq with hab | rfl
  · exact G.roof_cut (hL.frontierChronology hab)
  · exact Set.Subset.rfl

private theorem frontier_hit_at_lub_of_closed
    {Sigma : Set (Ladder.Stage kappa)}
    (stageIndex : I → Ladder.Stage kappa) (a : Ladder.Stage kappa)
    (hmono : Monotone stageIndex)
    (hLUB : IsLUB (Set.range stageIndex) a)
    {p : G.DPath}
    (hclosed : DirSupClosed (L.hitStages Sigma p))
    (hhit : ∀ i, stageIndex i ∈ L.hitStages Sigma p) :
    a ∈ L.hitStages Sigma p := by
  let d : Set (Ladder.Stage kappa) := Set.range stageIndex
  have hd : d ⊆ L.hitStages Sigma p := by
    rintro _ ⟨i, rfl⟩
    exact hhit i
  have hdne : d.Nonempty := by
    let i : I := Classical.choice inferInstance
    exact ⟨stageIndex i, ⟨i, rfl⟩⟩
  have hddir : DirectedOn (· ≤ ·) d := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    refine ⟨stageIndex (max i j), ⟨max i j, rfl⟩, ?_, ?_⟩
    · exact hmono (le_max_left i j)
    · exact hmono (le_max_right i j)
  exact hclosed hd hdne hddir hLUB

/-- The boundary of a cofinal monotone family of earlier deferred-ladder
frontiers is contained in the frontier at its genuine limit stage. -/
theorem iUnion_roof_sdiff_iUnion_strictRoof_subset_frontier
    (hL : HalfwayGeometry L)
    {Sigma : Set (Ladder.Stage kappa)}
    (hHit : LimitHitClosure G L Sigma)
    (stageIndex : I → Ladder.Stage kappa)
    (hmono : Monotone stageIndex)
    {a : Ladder.Stage kappa}
    (haLimit : Order.IsSuccLimit a.1)
    (hindex : ∀ i, stageIndex i < a)
    (hLUB : IsLUB (Set.range stageIndex) a)
    (hSigma : ∀ i, stageIndex i ∈ Sigma) :
    (⋃ i, G.roof (L.frontier (stageIndex i))) \
        (⋃ i, G.strictRoof (L.frontier (stageIndex i))) ⊆
      L.frontier a := by
  classical
  intro x hxBoundary
  obtain ⟨i₀, hxRoof₀⟩ := Set.mem_iUnion.1 hxBoundary.1
  have hxNotStrict : ∀ i,
      x ∉ G.strictRoof (L.frontier (stageIndex i)) := by
    intro i hxi
    exact hxBoundary.2 (Set.mem_iUnion.2 ⟨i, hxi⟩)
  have hxFrontierAbove : ∀ (b : Ladder.Stage kappa),
      stageIndex i₀ ≤ b → b < a → x ∈ L.frontier b := by
    intro b hi₀b hba
    have hxRoofB : x ∈ G.roof (L.frontier b) :=
      roof_frontier_mono hL hi₀b hxRoof₀
    obtain ⟨_, ⟨j, rfl⟩, hbj⟩ :=
      (lt_isLUB_iff hLUB).mp hba
    have hxNotStrictB : x ∉ G.strictRoof (L.frontier b) := by
      intro hxStrictB
      exact hxNotStrict j
        (hL.strictRoof_frontier_mono hbj.le hxStrictB)
    have hxEssential : x ∈ G.essential (L.frontier b) := by
      by_contra hxNotEssential
      exact hxNotStrictB ⟨hxRoofB, hxNotEssential⟩
    rw [hL.frontiersEssential b] at hxEssential
    exact hxEssential

  let ae : Ladder.ExtendedStage kappa := Ladder.Stage.toExtended a
  obtain ⟨C, hstage, hlimit⟩ := hL.limitStages ae haLimit
  letI : Nonempty (Set.Iio ae.1) := haLimit.nonempty_Iio.to_subtype
  let b₀ : Set.Iio ae.1 := ⟨(stageIndex i₀).1, hindex i₀⟩
  have hxTerminalLiminf : x ∈ WarpLimits.setLiminf
      (fun b : Set.Iio ae.1 ↦ G.terminalFrontier (C.stage b)) := by
    apply (WarpLimits.mem_setLiminf _ _).2
    refine ⟨b₀, ?_⟩
    intro b hb₀b
    let bs : Ladder.Stage kappa :=
      ⟨b.1, show b.1 < kappa.ord from b.2.trans a.2⟩
    have hi₀bs : stageIndex i₀ ≤ bs := hb₀b
    have hbsA : bs < a := b.2
    have hxFrontierB : x ∈ L.frontier bs :=
      hxFrontierAbove bs hi₀bs hbsA
    have hxTerminalB : x ∈ G.terminalFrontier (L.warpAt bs) := by
      rw [L.frontier_eq_essential_terminalFrontier
        hL.roofsSourceAtStages bs] at hxFrontierB
      exact G.essential_subset _ hxFrontierB
    rw [hstage b]
    simpa only [KappaLadder.warpAt, Ladder.Stage.toExtended] using
      hxTerminalB
  have hxTerminalLimit :
      x ∈ G.terminalFrontier (C.limitPaths G) :=
    C.setLiminf_terminalFrontier_subset_limitPaths hxTerminalLiminf
  have hxTerminalA : x ∈ G.terminalFrontier (L.warpAt a) := by
    rw [KappaLadder.warpAt, hlimit]
    exact hxTerminalLimit
  by_contra hxNotFrontierA
  obtain ⟨p, hpA, hpTerminal⟩ := hxTerminalA
  have hpInessential : p ∈ G.inessentialPaths (L.warpAt a) := by
    refine ⟨hpA, ?_⟩
    rintro ⟨_, y, hpTerminalY, hyEssential⟩
    have hyx : y = x :=
      Option.some.inj (hpTerminalY.symm.trans hpTerminal)
    apply hxNotFrontierA
    rw [L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages a]
    exact hyx ▸ hyEssential
  have hpLimit : p ∈ L.limitWarp :=
    hL.mem_limitWarp_of_mem_inessential hpInessential

  let Tail := Set.Ici i₀
  let tailIndex : Tail → Ladder.Stage kappa := fun i ↦ stageIndex i.1
  have htailMono : Monotone tailIndex := by
    intro i j hij
    exact hmono hij
  have htailLUB : IsLUB (Set.range tailIndex) a := by
    constructor
    · rintro _ ⟨i, rfl⟩
      exact (hindex i.1).le
    · intro b hb
      apply hLUB.2
      rintro _ ⟨i, rfl⟩
      rcases le_total i i₀ with hii₀ | hi₀i
      · exact (hmono hii₀).trans (hb ⟨⟨i₀, le_rfl⟩, rfl⟩)
      · exact hb ⟨⟨i, hi₀i⟩, rfl⟩
  have htailHit : ∀ i : Tail,
      tailIndex i ∈ L.hitStages Sigma p := by
    intro i
    have hxFrontierI : x ∈ L.frontier (tailIndex i) :=
      hxFrontierAbove (tailIndex i) (hmono i.2) (hindex i.1)
    exact ⟨hSigma i.1, x, hxFrontierI,
      G.terminal_mem_support hpTerminal⟩
  have haHit : a ∈ L.hitStages Sigma p :=
    frontier_hit_at_lub_of_closed tailIndex a htailMono htailLUB
      (hHit p hpLimit) htailHit
  obtain ⟨q, hqEssential, hpq⟩ :=
    hL.limitWarp_hitStages_essential_prefix hpLimit Sigma a haHit
  exact (G.not_mem_inessentialPaths_of_intersects_essential
    (hL.warpStages (Ladder.Stage.toExtended a)) hqEssential hpq)
      hpInessential

/-- Club-specialized form of limit-frontier continuity. -/
theorem iUnion_roof_sdiff_iUnion_strictRoof_subset_frontier_of_club
    (hL : HalfwayGeometry L)
    {Sigma : Set (Ladder.Stage kappa)}
    (hSigmaClub : Stationary.IsClubBelow kappa Sigma)
    (hmarkerOutside : MarkersOutsideCurrentWarp G L)
    (hmiss : LimitMissesAreInessential G L Sigma)
    (havoid : Disjoint Sigma (phi L))
    (stageIndex : I → Ladder.Stage kappa)
    (hmono : Monotone stageIndex)
    {a : Ladder.Stage kappa}
    (haLimit : Order.IsSuccLimit a.1)
    (hindex : ∀ i, stageIndex i < a)
    (hLUB : IsLUB (Set.range stageIndex) a)
    (hSigma : ∀ i, stageIndex i ∈ Sigma) :
    (⋃ i, G.roof (L.frontier (stageIndex i))) \
        (⋃ i, G.strictRoof (L.frontier (stageIndex i))) ⊆
      L.frontier a :=
  iUnion_roof_sdiff_iUnion_strictRoof_subset_frontier hL
    (limitHitClosure_of_club hL Sigma hSigmaClub hmarkerOutside hmiss havoid)
    stageIndex hmono haLimit hindex hLUB hSigma

/-- The source-faithful continuity theorem for the actual canonical
deferred ladder.  The only extra construction input is the usual club
avoidance of the deferred obstruction set. -/
theorem canonicalDeferredLadder_iUnion_roof_sdiff_iUnion_strictRoof_subset_frontier
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular)
    (huncountable : Cardinal.aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {Sigma : Set (Ladder.Stage kappa)}
    (hSigmaClub : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma
      (phi (canonicalDeferredLadder G kappa preferred)))
    (stageIndex : I → Ladder.Stage kappa)
    (hmono : Monotone stageIndex)
    {a : Ladder.Stage kappa}
    (haLimit : Order.IsSuccLimit a.1)
    (hindex : ∀ i, stageIndex i < a)
    (hLUB : IsLUB (Set.range stageIndex) a)
    (hSigma : ∀ i, stageIndex i ∈ Sigma) :
    (⋃ i, G.roof
        ((canonicalDeferredLadder G kappa preferred).frontier
          (stageIndex i))) \
      (⋃ i, G.strictRoof
        ((canonicalDeferredLadder G kappa preferred).frontier
          (stageIndex i))) ⊆
      (canonicalDeferredLadder G kappa preferred).frontier a := by
  let L := canonicalDeferredLadder G kappa preferred
  have hL : HalfwayGeometry L :=
    canonicalDeferredLadder_isDeferredLegal preferred hkappa
      huncountable hNoEnter
  apply iUnion_roof_sdiff_iUnion_strictRoof_subset_frontier_of_club
    (stageIndex := stageIndex) hL hSigmaClub
  · intro b y hy
    exact canonicalDeferredLadder_marker_not_mem_currentVertexSet
      preferred hNoEnter b y hy
  · exact canonicalDeferredLadder_limitMissesAreInessential
      preferred hkappa huncountable hNoEnter Sigma
  · exact havoid
  · exact hmono
  · exact haLimit
  · exact hindex
  · exact hLUB
  · exact hSigma

end Deferred
end KappaLadder
end DWeb
end Erdos599
