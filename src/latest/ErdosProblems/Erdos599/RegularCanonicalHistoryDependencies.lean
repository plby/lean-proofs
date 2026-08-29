/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderSliceLimitHitClosure
import ErdosProblems.Erdos599.RegularOrdinaryThreadLimit
import ErdosProblems.Erdos599.RegularLimitIndices
import ErdosProblems.Erdos599.RegularSplitLegality

/-!
# Exact base and limit dependencies for canonical regular histories

This file isolates the two path constructors used by the canonical
completed/pending history.  The zero row is the literal trivial-path family
on the registered sources.  At a genuine limit, cofinal exact ladder
prefixes converge to the exact prefix at the limiting stage.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace SliceSpliceConstructor

open DirectedPath RegularCardinal SliceSpliceSource

universe u v

variable {V : Type u}

/-- Compatibility name for the cardinal estimate used by all three history
base variants. -/
theorem mk_Iio_stage_lt_lift {kappa : Cardinal.{u}}
    (i : Ladder.Stage kappa) :
    #(Set.Iio i) < Cardinal.lift.{u + 1, u} kappa :=
  LocalConstruction.mk_Iio_stage_lt_lift i

/-- The exact data needed from the genuine zero row. -/
structure InitialTrackedPartialState
    {kappa : Cardinal.{u}} (Gamma : DWeb V)
    (L : Gamma.KappaLadder kappa) (Z : Set V)
    (hregular : kappa.IsRegular) where
  family : Set Gamma.DPath
  tight : TightLinkageBetween Gamma (Gamma.source ∩ Z)
    (L.frontier ⟨0, hregular.ord_pos⟩) family
  vertices_closed : Gamma.vertexSet family ⊆ Z
  below_roof : Gamma.vertexSet family ⊆
    Gamma.roof (L.frontier ⟨0, hregular.ord_pos⟩)
  status : ∀ p ∈ family,
    ReachesTarget Gamma p ∨
      IsStagePrefix Gamma L ⟨0, hregular.ord_pos⟩ p ∨
      ∃ x ∈ (∅ : Set V), Gamma.terminal? p = some x

private theorem trivialPaths_tightLinkageBetween
    (Gamma : DWeb V) {A C : Set V} (hAC : A ⊆ C) :
    TightLinkageBetween Gamma A C (Gamma.trivialPath '' A) := by
  have hlink : IsLinkageBetween Gamma A C (Gamma.trivialPath '' A) := by
    refine ⟨Gamma.isWarp_trivialPaths A, ?_,
      Gamma.initialSet_trivialPaths A, ?_, ?_⟩
    · rintro p ⟨a, ha, rfl⟩
      exact ⟨FinitePath.trivial Gamma.graph a, rfl⟩
    · rw [Gamma.terminalFrontier_trivialPaths]
      exact hAC
    · rintro p ⟨a, ha, rfl⟩
      refine ⟨FinitePath.trivial Gamma.graph a, rfl, ?_, ?_⟩
      · simp only [FinitePath.support_trivial, FinitePath.trivial_start,
          FinitePath.trivial_finish]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_union,
          Set.mem_singleton_iff, Set.mem_insert_iff]
        constructor
        · intro hx
          exact Or.inl hx.1
        · intro hx
          rcases hx with hxa | hxa <;> subst x
          · exact ⟨rfl, Or.inl ha⟩
          · exact ⟨rfl, Or.inl ha⟩
      · simp only [FinitePath.support_trivial, FinitePath.trivial_start]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · exact fun hx ↦ hx.1
        · intro hx
          subst x
          exact ⟨rfl, ha⟩
  refine ⟨hlink, ?_⟩
  rintro p ⟨a, _ha, rfl⟩ x hxp _hxC
  have hxa : x = a := by
    simpa only [Gamma.support_trivialPath, Set.mem_singleton_iff] using hxp
  subst x
  exact Gamma.terminal?_trivialPath a

/-- The genuine zero row is the trivial-path family on the registered
sources.  Every member is already the exact stage-zero ladder prefix. -/
noncomputable def initialTrackedPartialState_zero
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    (hNorm : Gamma.IsNormalized) (hUnhindered : Gamma.IsUnhindered)
    (hL : L.SliceGeometry) (Z : Set V) :
    InitialTrackedPartialState Gamma L Z hL.regular := by
  let zero : Ladder.Stage kappa := ⟨0, hL.regular.ord_pos⟩
  let A : Set V := Gamma.source ∩ Z
  let W : Set Gamma.DPath := Gamma.trivialPath '' A
  have hfrontier : L.frontier zero = Gamma.source :=
    frontier_zero_eq_source_of_initialStage hNorm hUnhindered
      hL.regular hL.initialStage
  have hess : Gamma.essential Gamma.source = Gamma.source :=
    essential_source_eq_of_isNormalized_of_reachable hNorm
      (source_subset_reachableToTarget_of_isUnhindered hUnhindered)
  have hprefix : ∀ p ∈ W, IsStagePrefix Gamma L zero p := by
    rintro p ⟨a, ha, rfl⟩
    refine ⟨FinitePath.trivial Gamma.graph a, rfl, ?_, ?_⟩
    · change (Sum.inl (FinitePath.trivial Gamma.graph a) : Gamma.DPath) ∈
        Gamma.essentialWarpPart (L.accumulated (Ladder.zeroStage kappa))
      rw [hL.initialStage]
      refine ⟨⟨a, ha.1, rfl⟩, a, Gamma.terminal?_trivialPath a, ?_⟩
      rw [Gamma.terminalFrontier_trivialWave, hess]
      exact ha.1
    · change a ∈ L.frontier zero
      rw [hfrontier]
      exact ha.1
  refine
    { family := W
      tight := ?_
      vertices_closed := ?_
      below_roof := ?_
      status := ?_ }
  · apply trivialPaths_tightLinkageBetween
    rw [hfrontier]
    exact Set.inter_subset_left
  · rw [Gamma.vertexSet_trivialPaths]
    exact Set.inter_subset_right
  · rw [Gamma.vertexSet_trivialPaths]
    intro x hx
    apply Gamma.subset_roof (L.frontier zero)
    rw [hfrontier]
    exact hx.1
  · intro p hp
    exact Or.inr (Or.inl (hprefix p hp))

/-- A final-ladder component which misses the frontier at the supremum of
earlier hits is already inessential at that supremum. -/
theorem limitMissIsInessential_of_limitWarp
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} (hL : L.SliceGeometry)
    (Sigma : Set (Ladder.Stage kappa)) {p : Gamma.DPath}
    (hp : p ∈ L.limitWarp) :
    L.LimitMissIsInessential Sigma p := by
  intro d a hd hdn _hdir ha hmiss
  obtain ⟨c, hc⟩ := hdn
  have hca : c ≤ a := ha.1 hc
  obtain ⟨q, hqEssential, hpq⟩ :=
    hL.limitWarp_hitStages_essential_prefix hp Sigma c (hd hc)
  have hfinalLimit : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨C, hstage, hlimit⟩ :=
    hL.limitStages (Ladder.finalStage kappa) hfinalLimit
  let ci : Set.Iio kappa.ord := ⟨c.1, c.2⟩
  let ai : Set.Iio kappa.ord := ⟨a.1, a.2⟩
  have hqC : q ∈ C.stage ci := by
    rw [hstage ci]
    exact hqEssential.1
  obtain ⟨r, hrC, hqr⟩ := C.grows (show ci ≤ ai from hca) q hqC
  have hrA : r ∈ L.warpAt a := by
    have hrC' := hrC
    rw [hstage ai] at hrC'
    exact hrC'
  obtain ⟨s, hsC, hrs⟩ := C.grows_limitPaths Gamma ai r hrC
  have hsFinal : s ∈ L.limitWarp := by
    change s ∈ L.accumulated (Ladder.finalStage kappa)
    rw [hlimit]
    exact hsC
  have hspMeet : (s.support ∩ p.support).Nonempty := by
    obtain ⟨x, hxp, hxq⟩ := hpq
    exact ⟨x, Gamma.support_mono_of_extends hrs
      (Gamma.support_mono_of_extends hqr hxq), hxp⟩
  have hsp : s = p := by
    by_contra hne
    obtain ⟨x, hxs, hxp⟩ := hspMeet
    exact Set.disjoint_left.1
      (hL.warpStages (Ladder.finalStage kappa) hsFinal hp hne) hxs hxp
  have hrpExtends : Gamma.Extends r p := by
    rwa [hsp] at hrs
  have hmissEssential :
      ¬ (Gamma.essential (Gamma.terminalFrontier (L.warpAt a)) ∩
          p.support).Nonempty := by
    rw [L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages a] at hmiss
    exact hmiss
  have hmissR :
      ¬ (Gamma.essential (Gamma.terminalFrontier (L.warpAt a)) ∩
          r.support).Nonempty := by
    rintro ⟨x, hxEssential, hxr⟩
    exact hmissEssential ⟨x, hxEssential,
      Gamma.support_mono_of_extends hrpExtends hxr⟩
  have hrIE : r ∈ Gamma.inessentialPaths (L.warpAt a) :=
    Gamma.mem_inessentialPaths_of_misses_essentialFrontier hrA hmissR
  have hrFinal : r ∈ L.limitWarp :=
    hL.mem_limitWarp_of_mem_inessential hrIE
  have hrpMeet : (r.support ∩ p.support).Nonempty := by
    obtain ⟨x, hxp, hxq⟩ := hpq
    exact ⟨x, Gamma.support_mono_of_extends hqr hxq, hxp⟩
  have hrp : r = p := by
    by_contra hne
    obtain ⟨x, hxr, hxp⟩ := hrpMeet
    exact Set.disjoint_left.1
      (hL.warpStages (Ladder.finalStage kappa) hrFinal hp hne) hxr hxp
  rwa [← hrp]

/-- A cofinal growing chain of exact accumulated-ladder prefixes converges
to the exact accumulated-ladder prefix at the limiting stage. -/
theorem threadLimit_isStagePrefix_of_stagePrefixes
    {I : Type v} [LinearOrder I] [Nonempty I]
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {A : Set V}
    (hL : L.SliceGeometry)
    (C : Gamma.GrowingWarpChain I)
    (stageIndex : I → Ladder.Stage kappa)
    (beta : Ladder.Stage kappa) (hbeta : Order.IsSuccLimit beta.1)
    (hindex : ∀ i, stageIndex i < beta)
    (hindexSigma : ∀ i, stageIndex i ∈ Sigma)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (hmono : Monotone stageIndex)
    (hLUB : IsLUB (Set.range stageIndex) beta)
    (hcofinal : ∀ b : Set.Iio beta.1,
      ∃ i, b.1 ≤ (stageIndex i).1)
    (htight : ∀ i, TightLinkageBetween Gamma A
      (L.frontier (stageIndex i)) (C.stage i))
    (_hroof : ∀ i, Gamma.vertexSet (C.stage i) ⊆
      Gamma.roof (L.frontier (stageIndex i)))
    (a : C.initialUnion) (haA : a.1 ∈ A)
    (hprefix : ∀ i p, p ∈ C.stage i → p.initial = a.1 →
      IsStagePrefix Gamma L (stageIndex i) p) :
    IsStagePrefix Gamma L beta (C.threadLimit Gamma a) := by
  let y := C.threadLimit Gamma a
  have hyStage : y ∈ L.warpAt beta :=
    threadLimit_mem_warpAt_of_cofinal_stagePrefix hL.limitStages C
      stageIndex beta hbeta hindex hmono hcofinal a hprefix
  have hfinalLimit : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨s, hsLimit, hys⟩ := hL.limitStages.grows_to_limit
    (Ladder.finalStage kappa) hfinalLimit
      (⟨beta.1, beta.2⟩ : Set.Iio kappa.ord) y hyStage
  have hhit : ∀ i, stageIndex i ∈ L.hitStages Sigma s := by
    intro i
    obtain ⟨p, hp, hpinitial, x, hxFrontier, hpterminal⟩ :=
      exists_member_terminal_of_linkage (htight i).1 haA
    have hpThread : p ∈ C.thread Gamma a.1 := ⟨i, hp, hpinitial⟩
    have hpy : Gamma.Extends p y :=
      DirectedPath.Path.extends_chainLimit (C.thread Gamma a.1)
        (C.thread_nonempty Gamma a) (C.thread_isChain Gamma a.1) hpThread
    exact ⟨hindexSigma i, x, hxFrontier,
      Gamma.support_mono_of_extends
        (DirectedPath.Path.extends_trans hpy hys)
        (Gamma.terminal_mem_support hpterminal)⟩
  have hclosed : DirSupClosed (L.hitStages Sigma s) :=
    hL.hitStages_isClosed Sigma s hSigma
      (hL.limitWarp_hitStages_essential_prefix hsLimit Sigma)
      (limitMissIsInessential_of_limitWarp hL Sigma hsLimit) havoid
  obtain ⟨x, hxFrontier, hxs⟩ :=
    frontier_hit_at_lub_of_closed stageIndex beta hmono hLUB hclosed hhit
  have hxEssential :
      x ∈ Gamma.essential (Gamma.terminalFrontier (L.warpAt beta)) := by
    rwa [← L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages beta]
  have hxTerminal : x ∈ Gamma.terminalFrontier
      (Gamma.essentialWarpPart (L.warpAt beta)) := by
    rwa [Gamma.terminalFrontier_essentialWarpPart]
  obtain ⟨q, hqEssential, hqterminal⟩ := hxTerminal
  have hqs : Gamma.Extends q s :=
    hL.extends_limitWarp_of_stage_intersects hqEssential.1 hsLimit
      ⟨x, Gamma.terminal_mem_support hqterminal, hxs⟩
  have hqy : q = y :=
    DWeb.IsWarp.eq_of_initial_eq Gamma
      (hL.warpStages (Ladder.Stage.toExtended beta))
      hqEssential.1 hyStage
      ((Gamma.extends_initial hqs).trans
        (Gamma.extends_initial hys).symm)
  rcases q with f | r
  · refine ⟨f, hqy.symm, hqEssential, ?_⟩
    have hfx : f.finish = x := Option.some.inj hqterminal
    exact hfx.symm ▸ hxFrontier
  · simp at hqterminal

end SliceSpliceConstructor
end CardinalInduction
end Erdos599
