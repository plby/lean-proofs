/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ControlledSlices
import ErdosProblems.Erdos599.LadderConstruction
import ErdosProblems.Erdos599.SliceHalfwayCore
import ErdosProblems.Erdos599.SliceAuxiliaryCore
import ErdosProblems.Erdos599.SliceSplice
import ErdosProblems.Erdos599.SliceSpliceSource
import ErdosProblems.Erdos599.AlternatingComponents
import ErdosProblems.Erdos599.QuotientMaximal
import ErdosProblems.Erdos599.LadderSuccessorBridge

/-!
# Height-roof transport for the regular-cardinal construction

This file formalizes the source-side content of Assertion 9.9.  A wave in a
quotient of a ladder stage has terminal frontier below every sufficiently
later ladder frontier, provided that the quotienting set was already below
an intermediate frontier.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

open DirectedPath

universe u

variable {V : Type u}

namespace SliceCandidate

/-- The construction laws used by Assertions 9.8--9.9.  They are
independent of the ladder's record-selection bookkeeping, and hence apply
equally to the legacy and deferred canonical ladders. -/
structure HeightRoofGeometry {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) : Prop where
  waveRungs : L.HasWaveRungs
  roofMaximalRungs : L.HasRoofMaximalRungs
  exactSuccessorArrows : L.HasExactSuccessorArrows
  roofsSourceAtStages : L.RoofsSourceAtStages
  frontierChronology : L.HasFrontierChronology

theorem HeightRoofGeometry.ofLegal {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.IsLegal) :
    HeightRoofGeometry L :=
  ⟨hL.waveRungs, hL.roofMaximalRungs, hL.exactSuccessorArrows,
    hL.roofsSourceAtStages, hL.frontierChronology⟩

theorem HeightRoofGeometry.ofSplitLegal
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal) :
    HeightRoofGeometry L :=
  ⟨hL.waveRungs, hL.roofMaximalRungs, hL.exactSuccessorArrows,
    hL.roofsSourceAtStages, hL.frontierChronology⟩

/-- Roofing is contravariant in the edge relation when the target is fixed. -/
theorem roof_subset_of_adj_imp
    (G H : DWeb V) (hTarget : H.target = G.target)
    (hAdj : ∀ {x y : V}, H.graph.Adj x y → G.graph.Adj x y)
    (S : Set V) :
    G.roof S ⊆ H.roof S := by
  intro x hx p hp
  let q : DirectedPath.FinitePath G.graph := p.lift hAdj
  have hqTarget : G.IsTargetPathFrom x q := by
    refine ⟨?_, ?_⟩
    · change p.start = x
      exact hp.1
    · change p.finish ∈ G.target
      rw [← hTarget]
      exact hp.2
  obtain ⟨z, hzq, hzS⟩ := hx q hqTarget
  refine ⟨z, ?_, hzS⟩
  simpa [q] using hzq

theorem essential_terminalFrontier_castWebWave
    {G H : DWeb V} (h : G = H) (W : G.Wave) :
    H.essential (H.terminalFrontier (h ▸ W).1) =
      G.essential (G.terminalFrontier W.1) := by
  cases h
  rfl

/-- Passing to the target-reachable induced subweb does not change roofs. -/
theorem roof_essentialPart (G : DWeb V) (S : Set V) :
    G.essentialPart.roof S = G.roof S := by
  apply Set.Subset.antisymm
  · intro x hx p hp
    have hreach : p.support ⊆ G.reachableToTarget :=
      G.finitePath_support_subset_reachableToTarget p hp.2
    let hrestrict : ∀ {a b : V}, G.graph.Adj a b →
        a ∈ p.support → b ∈ p.support →
          G.essentialPart.graph.Adj a b :=
      fun e ha hb ↦ ⟨e, hreach ha, hreach hb⟩
    let q : DirectedPath.FinitePath G.essentialPart.graph :=
      p.restrictGraphOnSupport hrestrict
    have hqTarget : G.essentialPart.IsTargetPathFrom x q := by
      refine ⟨?_, ?_⟩
      · change p.start = x
        exact hp.1
      · change q.finish ∈ G.target
        change p.finish ∈ G.target
        exact hp.2
    obtain ⟨z, hzq, hzS⟩ := hx q hqTarget
    refine ⟨z, ?_, hzS⟩
    have hsupp : q.support = p.support :=
      DirectedPath.FinitePath.support_restrictGraphOnSupport p hrestrict
    rwa [hsupp] at hzq
  · exact roof_subset_of_adj_imp G G.essentialPart rfl
      (fun {_ _} h ↦ G.essentialPart_adj_imp h) S

theorem essential_essentialPart (G : DWeb V) (S : Set V) :
    G.essentialPart.essential S = G.essential S := by
  ext x
  change (x ∈ S ∧ x ∉ G.essentialPart.roof (S \ {x})) ↔
    (x ∈ S ∧ x ∉ G.roof (S \ {x}))
  rw [roof_essentialPart G]

theorem strictRoof_essentialPart (G : DWeb V) (S : Set V) :
    G.essentialPart.strictRoof S = G.strictRoof S := by
  unfold DWeb.strictRoof
  rw [roof_essentialPart G, essential_essentialPart G]

theorem essentialPart_quotient_adj_iff (G : DWeb V) (S : Set V)
    {x y : V} :
    (G.essentialPart.quotient S).graph.Adj x y ↔
      (G.quotient S).graph.Adj x y ∧
        x ∈ G.reachableToTarget ∧ y ∈ G.reachableToTarget := by
  change ((G.graph.Adj x y ∧ x ∈ G.reachableToTarget ∧
      y ∈ G.reachableToTarget) ∧
      x ∉ G.essentialPart.strictRoof S ∧
      y ∉ G.essentialPart.strictRoof S ∧ y ∉ S) ↔
    (G.graph.Adj x y ∧ x ∉ G.strictRoof S ∧
      y ∉ G.strictRoof S ∧ y ∉ S) ∧
      x ∈ G.reachableToTarget ∧ y ∈ G.reachableToTarget
  rw [strictRoof_essentialPart G]
  aesop

theorem reachableToTarget_essentialPart_quotient
    (G : DWeb V) (S : Set V) :
    (G.essentialPart.quotient S).reachableToTarget =
      (G.quotient S).reachableToTarget := by
  ext x
  constructor
  · rintro ⟨p, hp⟩
    let q : DirectedPath.FinitePath (G.quotient S).graph :=
      p.lift (fun {_ _} h ↦
        (essentialPart_quotient_adj_iff G S).1 h |>.1)
    refine ⟨q, ?_⟩
    refine ⟨?_, ?_⟩
    · change p.start = x
      exact hp.1
    · change p.finish ∈ G.target
      exact hp.2
  · rintro ⟨p, hp⟩
    let pG : DirectedPath.FinitePath G.graph :=
      p.lift (fun {_ _} h ↦ G.quotient_adj_imp h)
    have hpGTarget : pG.finish ∈ G.target := by
      change p.finish ∈ G.target
      exact hp.2
    have hreach : p.support ⊆ G.reachableToTarget := by
      intro z hzp
      have hzpG : z ∈ pG.support := by simpa [pG] using hzp
      exact G.finitePath_support_subset_reachableToTarget pG hpGTarget hzpG
    let hrestrict : ∀ {a b : V}, (G.quotient S).graph.Adj a b →
        a ∈ p.support → b ∈ p.support →
          (G.essentialPart.quotient S).graph.Adj a b :=
      fun e ha hb ↦
        (essentialPart_quotient_adj_iff G S).2
          ⟨e, hreach ha, hreach hb⟩
    let q : DirectedPath.FinitePath
        (G.essentialPart.quotient S).graph :=
      p.restrictGraphOnSupport hrestrict
    refine ⟨q, ?_⟩
    refine ⟨?_, ?_⟩
    · change p.start = x
      exact hp.1
    · change p.finish ∈ G.target
      exact hp.2

theorem reachableToTarget_quotient_subset (G : DWeb V) (S : Set V) :
    (G.quotient S).reachableToTarget ⊆ G.reachableToTarget := by
  rintro x ⟨p, hp⟩
  let q : DirectedPath.FinitePath G.graph :=
    p.lift (fun {_ _} h ↦ G.quotient_adj_imp h)
  refine ⟨q, ?_⟩
  refine ⟨?_, ?_⟩
  · change p.start = x
    exact hp.1
  · change p.finish ∈ G.target
    exact hp.2

theorem finitePath_support_subset_reachable_of_finish
    (G : DWeb V) (p : DirectedPath.FinitePath G.graph)
    (hfinish : p.finish ∈ G.reachableToTarget) :
    p.support ⊆ G.reachableToTarget := by
  intro x hxp
  obtain ⟨q, hq⟩ := hfinish
  let s := p.suffixFrom x hxp
  have hqStart : q.start = s.finish := by
    exact hq.1.trans (p.suffixFrom_finish x hxp).symm
  let q' : DirectedPath.Walk G.graph s.finish q.finish :=
    RelationalRoof.castStart G.graph.Adj hqStart q.walk
  let w : DirectedPath.Walk G.graph s.start q.finish := s.walk.append q'
  obtain ⟨r, hr⟩ :=
    RelationalRoof.exists_pathTo_support_subset (R := G.graph.Adj) w
  let r' : DirectedPath.FinitePath G.graph :=
    { start := s.start
      finish := q.finish
      walk := r.1
      isPath := r.2 }
  refine ⟨r', ?_⟩
  refine ⟨?_, ?_⟩
  · exact p.suffixFrom_start x hxp
  · change q.finish ∈ G.target
    exact hq.2

theorem essential_subset_reachableToTarget
    (G : DWeb V) (S : Set V) :
    G.essential S ⊆ G.reachableToTarget := by
  intro x hx
  obtain ⟨p, hp, -⟩ := (G.not_mem_roof_iff (S \ {x}) x).1 hx.2
  exact ⟨p, hp⟩

theorem essentialWarpPart_member_support_reachable
    (G : DWeb V) {U : Set G.DPath} {p : G.DPath}
    (hp : p ∈ G.essentialWarpPart U) :
    p.support ⊆ G.reachableToTarget := by
  obtain ⟨hpU, t, hpt, ht⟩ := hp
  rcases p with p | r
  · apply finitePath_support_subset_reachable_of_finish G p
    have htReach := essential_subset_reachableToTarget G
      (G.terminalFrontier U) ht
    have hfinish : p.finish = t := Option.some.inj hpt
    rw [hfinish]
    exact htReach
  · simp at hpt

noncomputable def restrictEssentialWarpPartFamily
    (G : DWeb V) (U : Set G.DPath) : Set G.essentialPart.DPath :=
  Set.range (fun p : ↑(G.essentialWarpPart U) ↦
    G.restrictEssentialPartPath p.1
      (essentialWarpPart_member_support_reachable G p.2))

@[simp]
theorem terminal_restrictEssentialPartPath
    (G : DWeb V) (p : G.DPath)
    (hreach : p.support ⊆ G.reachableToTarget) :
    G.essentialPart.terminal?
      (G.restrictEssentialPartPath p hreach) = G.terminal? p := by
  rcases p with p | r <;> rfl

@[simp]
theorem initial_restrictEssentialPartPath
    (G : DWeb V) (p : G.DPath)
    (hreach : p.support ⊆ G.reachableToTarget) :
    (G.restrictEssentialPartPath p hreach).initial = p.initial := by
  rcases p with p | r <;> rfl

theorem terminalFrontier_restrictEssentialWarpPartFamily
    (G : DWeb V) (U : Set G.DPath) :
    G.essentialPart.terminalFrontier
        (restrictEssentialWarpPartFamily G U) =
      G.terminalFrontier (G.essentialWarpPart U) := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, rfl⟩, hqx⟩
    refine ⟨p.1, p.2, ?_⟩
    rw [terminal_restrictEssentialPartPath] at hqx
    exact hqx
  · rintro ⟨p, hp, hpx⟩
    let q := G.restrictEssentialPartPath p
      (essentialWarpPart_member_support_reachable G hp)
    refine ⟨q, ⟨⟨p, hp⟩, rfl⟩, ?_⟩
    rw [terminal_restrictEssentialPartPath]
    exact hpx

/-- Every wave restricts to a wave in the target-reachable induced
subweb after discarding its inessential terminal components. -/
theorem isWave_restrictEssentialWarpPartFamily
    (G : DWeb V) {U : Set G.DPath} (hU : G.IsWave U) :
    G.essentialPart.IsWave (restrictEssentialWarpPartFamily G U) := by
  have hUE : G.IsWave (G.essentialWarpPart U) := hU.essentialWarpPart
  refine ⟨?_, ?_, ?_⟩
  · rintro q ⟨p, rfl⟩ r ⟨s, rfl⟩ hne
    have hps : p.1 ≠ s.1 := by
      intro h
      have hsub : p = s := Subtype.ext h
      subst s
      exact hne rfl
    have hdisj := hUE.1 p.2 s.2 hps
    simpa only [G.support_restrictEssentialPartPath,
      Set.disjoint_left] using hdisj
  · rintro x ⟨q, ⟨p, rfl⟩, hqx⟩
    have hxInitial : x = p.1.initial := by
      exact hqx.symm.trans (initial_restrictEssentialPartPath G _ _)
    rw [hxInitial]
    refine ⟨hUE.2.1 ⟨p.1, p.2, rfl⟩, ?_⟩
    exact essentialWarpPart_member_support_reachable G p.2
      p.1.initial_mem_support
  · intro x hx p hp
    let q : DirectedPath.FinitePath G.graph :=
      p.lift (fun {_ _} h ↦ G.essentialPart_adj_imp h)
    have hqTarget : G.IsTargetPathFrom x q := by
      refine ⟨?_, ?_⟩
      · change p.start = x
        exact hp.1
      · change p.finish ∈ G.target
        exact hp.2
    obtain ⟨z, hzq, hzT⟩ := hUE.2.2 hx.1 q hqTarget
    refine ⟨z, ?_, ?_⟩
    · simpa [q] using hzq
    · rw [terminalFrontier_restrictEssentialWarpPartFamily]
      exact hzT

/-- Quotienting the target-reachable induced subweb and then taking its
essential part agrees with quotienting first and then taking the essential
part, as soon as the commitment roofs the essential source. -/
theorem essentialPart_quotient_essentialPart_eq
    (G : DWeb V) (S : Set V)
    (hSource : G.essentialPart.source ⊆ G.essentialPart.roof S) :
    (G.essentialPart.quotient S).essentialPart =
      (G.quotient S).essentialPart := by
  have hGSource : G.source ⊆ G.roof S := by
    intro x hx
    by_cases hreach : x ∈ G.reachableToTarget
    · have hxEP : x ∈ G.essentialPart.source := ⟨hx, hreach⟩
      rw [← roof_essentialPart G]
      exact hSource hxEP
    · intro p hp
      exact (hreach ⟨p, hp⟩).elim
  have hSourceLeft : (G.essentialPart.quotient S).source =
      G.essentialPart.essential S := by
    rw [DWeb.quotient_source, Set.union_comm]
    exact RelationalRoof.essential_union_eq_of_subset_roof
      G.essentialPart.graph.Adj G.essentialPart.target hSource
  have hSourceRight : (G.quotient S).source = G.essential S := by
    rw [DWeb.quotient_source, Set.union_comm]
    exact RelationalRoof.essential_union_eq_of_subset_roof
      G.graph.Adj G.target hGSource
  have hReach := reachableToTarget_essentialPart_quotient G S
  rw [DWeb.mk.injEq]
  refine ⟨?_, ?_, rfl⟩
  · ext x y
    change ((G.essentialPart.quotient S).graph.Adj x y ∧
        x ∈ (G.essentialPart.quotient S).reachableToTarget ∧
        y ∈ (G.essentialPart.quotient S).reachableToTarget) ↔
      ((G.quotient S).graph.Adj x y ∧
        x ∈ (G.quotient S).reachableToTarget ∧
        y ∈ (G.quotient S).reachableToTarget)
    rw [essentialPart_quotient_adj_iff G S, hReach]
    constructor
    · rintro ⟨⟨hxy, -, -⟩, hx, hy⟩
      exact ⟨hxy, hx, hy⟩
    · rintro ⟨hxy, hx, hy⟩
      exact ⟨⟨hxy, reachableToTarget_quotient_subset G S hx,
        reachableToTarget_quotient_subset G S hy⟩, hx, hy⟩
  · change (G.essentialPart.quotient S).source ∩
        (G.essentialPart.quotient S).reachableToTarget =
      (G.quotient S).source ∩ (G.quotient S).reachableToTarget
    rw [hSourceLeft, hSourceRight, essential_essentialPart G, hReach]

/-- If `X` is already roofed by `T`, adding `X` to the commitment does
not change the normalized quotient, provided `T` roofs the old source. -/
theorem quotient_union_eq_right_of_subset_roof
    (G : DWeb V) {X T : Set V}
    (hSource : G.source ⊆ G.roof T) (hX : X ⊆ G.roof T) :
    G.quotient (X ∪ T) = G.quotient T := by
  have hSourceUnion : G.source ⊆ G.roof (X ∪ T) :=
    hSource.trans (G.roof_mono Set.subset_union_right)
  calc
    G.quotient (X ∪ T) = G.quotient (G.essential (X ∪ T)) :=
      (G.quotient_essential_eq_of_subset_roof (X ∪ T) hSourceUnion).symm
    _ = G.quotient (G.essential T) := by
      have hEss : G.essential (X ∪ T) = G.essential T := by
        rw [Set.union_comm X T]
        exact RelationalRoof.essential_union_eq_of_subset_roof
          G.graph.Adj G.target hX
      rw [hEss]
    _ = G.quotient T :=
      G.quotient_essential_eq_of_subset_roof T hSource

/-- Iterating first by `X` and then by an already-roofing set `T` is just
the quotient by `T`.  This is the quotient identity used in source 9.9. -/
theorem quotient_quotient_eq_right_of_subset_roof
    (G : DWeb V) (hNoEnter : G.NoEdgeEnters G.source) {X T : Set V}
    (hSource : G.source ⊆ G.roof T) (hX : X ⊆ G.roof T) :
    (G.quotient X).quotient T = G.quotient T := by
  rw [G.quotient_quotient_eq_union X T hNoEnter]
  exact quotient_union_eq_right_of_subset_roof G hSource hX

/-- Every terminal of a legal rung is the terminal of its exact successor
arrow.  This is ladder geometry, so the height-roof bridge records it
directly rather than importing the unrelated grounding development. -/
theorem rung_terminalFrontier_subset_successorFrontier_heightBridge
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : HeightRoofGeometry L)
    (a : Ladder.Stage kappa) :
    (L.stageWeb a).terminalFrontier (L.rung a) ⊆
      Gamma.terminalFrontier (L.successorWarp a) := by
  intro t ht
  obtain ⟨r, hr, hrt⟩ := ht
  have hrInitial : r.initial ∈ (L.stageWeb a).source :=
    (hL.waveRungs a).2.1 ⟨r, hr, rfl⟩
  have hOldRoof :
      Gamma.source ⊆ Gamma.roof
        (Gamma.terminalFrontier (L.warpAt a)) :=
    hL.roofsSourceAtStages (Ladder.Stage.toExtended a)
  obtain ⟨p, hpEssential, hpTerminal⟩ :=
    Gamma.exists_essentialWarpPart_terminal_of_mem_quotientEssentialPart_source
      hOldRoof hrInitial
  obtain ⟨q, hq, _hqunique⟩ : ∃! q : Gamma.DPath,
      (q ∈ L.successorWarp a ∧ q ∉ L.markerPathSet a) ∧
        L.IsRungArrowPair a p q := by
    simpa only [DWeb.KappaLadder.arrowPart, Set.mem_sdiff] using
      (hL.exactSuccessorArrows a).1.1 p hpEssential.1
  refine ⟨q, hq.1.1, ?_⟩
  rcases hq.2 with hRay | ⟨z, hpz, hcontinue | hfixed⟩
  · rw [hpTerminal] at hRay
    simp at hRay
  · have hz : z = r.initial := Option.some.inj (hpz.symm.trans hpTerminal)
    obtain ⟨r', hr'Initial, hr'Rung, _hpTerminal, _hextends,
      _hsupport, _hedges, hqTerminal⟩ := hcontinue
    have hrr' : r' = r := by
      apply DWeb.IsWarp.eq_of_initial_eq (L.stageWeb a)
        (hL.waveRungs a).1 hr'Rung hr
      exact hr'Initial.trans hz
    rw [hqTerminal, hrr', L.terminal?_liftStagePath, hrt]
  · have hz : z = r.initial := Option.some.inj (hpz.symm.trans hpTerminal)
    exfalso
    apply hfixed.1
    exact ⟨r, hr, hz.symm⟩

/-- Source Assertion 9.8 at the immediate successor, before replacing the
raw successor terminal frontier by its essential ladder frontier. -/
theorem stageWave_terminalFrontier_subset_successorRoof
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : HeightRoofGeometry L)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (alpha : Ladder.Stage kappa)
    {W : Set (L.stageWeb alpha).DPath}
    (hW : (L.stageWeb alpha).IsWave W) :
    (L.stageWeb alpha).terminalFrontier W ⊆
      Gamma.roof (Gamma.terminalFrontier (L.successorWarp alpha)) := by
  let T := Gamma.terminalFrontier (L.warpAt alpha)
  let Q := Gamma.quotient T
  let R : Set Q.essentialPart.DPath := L.rung alpha
  let U : Set Q.DPath := Q.liftEssentialPartFamily R
  have hU : Q.IsWave U :=
    Q.isWave_liftEssentialPartFamily (hL.waveRungs alpha)
  have hmax : (L.stageWeb alpha).RoofLE W (L.rung alpha) :=
    hL.roofMaximalRungs alpha W hW
  intro x hx
  have hxStage : x ∈ (L.stageWeb alpha).roof
      ((L.stageWeb alpha).terminalFrontier (L.rung alpha)) :=
    hmax ((L.stageWeb alpha).subset_roof _ hx)
  have hxQ : x ∈ Q.roof (Q.essentialPart.terminalFrontier R) := by
    rw [← roof_essentialPart Q]
    exact hxStage
  have hxQU : x ∈ Q.roof (Q.terminalFrontier U) := by
    rw [show U = Q.liftEssentialPartFamily R from rfl,
      Q.terminalFrontier_liftEssentialPartFamily]
    exact hxQ
  have hxGamma : x ∈ Gamma.roof
      ((L.stageWeb alpha).terminalFrontier (L.rung alpha)) := by
    have hx' := Gamma.quotientWave_roof_subset_original_roof_general
      hNoEnter hU hxQU
    change x ∈ Gamma.roof (Q.terminalFrontier U) at hx'
    rw [show U = Q.liftEssentialPartFamily R from rfl,
      Q.terminalFrontier_liftEssentialPartFamily] at hx'
    exact hx'
  exact Gamma.roof_mono
    (rung_terminalFrontier_subset_successorFrontier_heightBridge hL alpha)
    hxGamma

/-- Source Assertion 9.8: every wave at a ladder stage is roofed by every
strictly later ladder frontier. -/
theorem stageWave_terminalFrontier_subset_laterFrontierRoof
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : HeightRoofGeometry L)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    {alpha beta : Ladder.Stage kappa} (hab : alpha < beta)
    {W : Set (L.stageWeb alpha).DPath}
    (hW : (L.stageWeb alpha).IsWave W) :
    (L.stageWeb alpha).terminalFrontier W ⊆
      Gamma.roof (L.frontier beta) := by
  have habOrd : alpha.1 < beta.1 := hab
  have hsuccLe : alpha.1 + 1 ≤ beta.1 :=
    Order.add_one_le_iff.mpr habOrd
  have hsuccLt : alpha.1 + 1 < kappa.ord :=
    hsuccLe.trans_lt beta.property
  let succ : Ladder.Stage kappa := ⟨alpha.1 + 1, hsuccLt⟩
  have hsuccBeta : succ ≤ beta := by
    change alpha.1 + 1 ≤ beta.1
    exact hsuccLe
  have hwarp : L.warpAt succ = L.successorWarp alpha := by
    apply congrArg L.accumulated
    apply Subtype.ext
    rfl
  intro x hx
  have hxRaw : x ∈ Gamma.roof
      (Gamma.terminalFrontier (L.successorWarp alpha)) :=
    stageWave_terminalFrontier_subset_successorRoof hL hNoEnter alpha hW hx
  have hxSucc : x ∈ Gamma.roof (L.frontier succ) := by
    rw [L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages succ, Gamma.roof_essential, hwarp]
    exact hxRaw
  rcases hsuccBeta.lt_or_eq with hlt | heq
  · exact Gamma.roof_cut (hL.frontierChronology hlt) hxSucc
  · rwa [heq] at hxSucc

/-- The precise stage-quotient identity needed in source Assertion 9.9.
The extra `essentialPart` is mathematically harmless and is exactly what
turns the iterated quotient back into the later ladder stage. -/
theorem stageWeb_quotient_essentialPart_eq_of_geometry
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : HeightRoofGeometry L)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    {delta zeta : Ladder.Stage kappa} (hdz : delta < zeta) :
    ((L.stageWeb delta).quotient (L.frontier zeta)).essentialPart =
      L.stageWeb zeta := by
  let A := Gamma.terminalFrontier (L.warpAt delta)
  let B := Gamma.terminalFrontier (L.warpAt zeta)
  let K := Gamma.quotient A
  let Q := K.essentialPart
  let S := L.frontier zeta
  have hQSource : Q.source ⊆ Q.roof S := by
    intro x hx
    have hxGamma : x ∈ Gamma.roof S := by
      apply Gamma.roof_cut (hL.frontierChronology hdz)
      exact Gamma.subset_roof (L.frontier delta) hx
    exact roof_subset_of_adj_imp Gamma Q rfl
      (fun {_ _} h ↦ Gamma.quotient_adj_imp
        (K.essentialPart_adj_imp h)) S hxGamma
  have hSourceS : Gamma.source ⊆ Gamma.roof S := by
    dsimp only [S, B]
    rw [L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages zeta, Gamma.roof_essential]
    exact hL.roofsSourceAtStages (Ladder.Stage.toExtended zeta)
  have hAS : A ⊆ Gamma.roof S := by
    intro x hx
    have hxOld : x ∈ Gamma.roof (L.frontier delta) := by
      dsimp only [A] at hx
      rw [L.frontier_eq_essential_terminalFrontier
        hL.roofsSourceAtStages delta, Gamma.roof_essential]
      exact Gamma.subset_roof _ hx
    exact Gamma.roof_cut (hL.frontierChronology hdz) hxOld
  have hIter : K.quotient S = Gamma.quotient S := by
    exact quotient_quotient_eq_right_of_subset_roof Gamma hNoEnter
      hSourceS hAS
  have hSB : S = Gamma.essential B := by
    dsimp only [S, B]
    exact L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages zeta
  have hSourceB : Gamma.source ⊆ Gamma.roof B :=
    hL.roofsSourceAtStages (Ladder.Stage.toExtended zeta)
  calc
    ((L.stageWeb delta).quotient (L.frontier zeta)).essentialPart =
        (K.quotient S).essentialPart := by
      exact essentialPart_quotient_essentialPart_eq K S hQSource
    _ = (Gamma.quotient S).essentialPart := by rw [hIter]
    _ = (Gamma.quotient B).essentialPart := by
      rw [hSB]
      rw [Gamma.quotient_essential_eq_of_subset_roof B hSourceB]
    _ = L.stageWeb zeta := by rfl

/-- Split-legality compatibility form of the exact stage-quotient
identity. -/
theorem stageWeb_quotient_essentialPart_eq
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    {delta zeta : Ladder.Stage kappa} (hdz : delta < zeta) :
    ((L.stageWeb delta).quotient (L.frontier zeta)).essentialPart =
      L.stageWeb zeta :=
  stageWeb_quotient_essentialPart_eq_of_geometry
    (HeightRoofGeometry.ofSplitLegal hL) hNoEnter hdz

/-- Source Assertion 9.9 in terminal-frontier form.  A wave in the stage
quotient by a set already roofed at `zeta` is roofed by every later ladder
frontier. -/
theorem quotientStageWave_terminalFrontier_subset_laterFrontierRoof_of_geometry
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : HeightRoofGeometry L)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    {delta zeta beta : Ladder.Stage kappa}
    (hdz : delta < zeta) (hzb : zeta < beta)
    {X : Set V}
    (hX : X ⊆ (L.stageWeb delta).roof (L.frontier zeta))
    {R : Set ((L.stageWeb delta).quotient X).DPath}
    (hR : ((L.stageWeb delta).quotient X).IsWave R) :
    (L.stageWeb delta).terminalFrontier
        ((L.stageWeb delta).liftQuotientFamily X R) ⊆
      (L.stageWeb delta).roof (L.frontier beta) := by
  let Q := L.stageWeb delta
  let T := L.frontier zeta
  let H := Q.quotient X
  have hNoEnterQ : Q.NoEdgeEnters Q.source := by
    intro x y hxy hy
    let K := Gamma.quotient
      (Gamma.terminalFrontier (L.warpAt delta))
    have hKNo : K.NoEdgeEnters K.source :=
      DWeb.NoEdgeEnters.quotient (G := Gamma) hNoEnter
    exact hKNo (K.essentialPart_adj_imp hxy) hy.1
  have hQSource : Q.source ⊆ Q.roof T := by
    intro x hx
    have hxGamma : x ∈ Gamma.roof T := by
      apply Gamma.roof_cut (hL.frontierChronology hdz)
      exact Gamma.subset_roof (L.frontier delta) hx
    exact roof_subset_of_adj_imp Gamma Q rfl
      (fun {_ _} e ↦ Gamma.quotient_adj_imp
        ((Gamma.quotient
          (Gamma.terminalFrontier (L.warpAt delta))).essentialPart_adj_imp e))
      T hxGamma
  have hIter : H.quotient T = Q.quotient T :=
    quotient_quotient_eq_right_of_subset_roof Q hNoEnterQ hQSource hX
  let U0 : (H.quotient T).Wave :=
    ⟨H.generalWaveQuotient T R,
      H.isWave_generalWaveQuotient hNoEnterQ.quotient hR⟩
  let U1 : (Q.quotient T).Wave := hIter ▸ U0
  let E : Set (Q.quotient T).essentialPart.DPath :=
    restrictEssentialWarpPartFamily (Q.quotient T) U1.1
  have hE : (Q.quotient T).essentialPart.IsWave E :=
    isWave_restrictEssentialWarpPartFamily (Q.quotient T) U1.2
  have hStage : (Q.quotient T).essentialPart = L.stageWeb zeta := by
    exact stageWeb_quotient_essentialPart_eq_of_geometry hL hNoEnter hdz
  let Wz : (L.stageWeb zeta).Wave := hStage ▸ ⟨E, hE⟩
  have hWzRoof : (L.stageWeb zeta).terminalFrontier Wz.1 ⊆
      Gamma.roof (L.frontier beta) :=
    stageWave_terminalFrontier_subset_laterFrontierRoof
      hL hNoEnter hzb Wz.2
  have htfWz : (L.stageWeb zeta).terminalFrontier Wz.1 =
      (Q.quotient T).essential
        ((Q.quotient T).terminalFrontier U1.1) := by
    calc
      (L.stageWeb zeta).terminalFrontier Wz.1 =
          (Q.quotient T).essentialPart.terminalFrontier E := by
        exact DWeb.terminalFrontier_castWebWave hStage ⟨E, hE⟩
      _ = (Q.quotient T).essential
          ((Q.quotient T).terminalFrontier U1.1) := by
        dsimp only [E]
        rw [terminalFrontier_restrictEssentialWarpPartFamily,
          (Q.quotient T).terminalFrontier_essentialWarpPart]
  have hEssGamma : (Q.quotient T).essential
      ((Q.quotient T).terminalFrontier U1.1) ⊆
        Gamma.roof (L.frontier beta) := by
    rw [← htfWz]
    exact hWzRoof
  have hessCast : (Q.quotient T).essential
      ((Q.quotient T).terminalFrontier U1.1) =
      (H.quotient T).essential
        ((H.quotient T).terminalFrontier U0.1) := by
    exact essential_terminalFrontier_castWebWave hIter U0
  have hEss0Gamma : (H.quotient T).essential
      ((H.quotient T).terminalFrontier U0.1) ⊆
        Gamma.roof (L.frontier beta) := by
    rw [← hessCast]
    exact hEssGamma
  have hEss0H : (H.quotient T).essential
      ((H.quotient T).terminalFrontier U0.1) ⊆
        H.roof (L.frontier beta) := by
    exact hEss0Gamma.trans
      (roof_subset_of_adj_imp Gamma H rfl
        (fun {_ _} e ↦ Gamma.quotient_adj_imp
          ((Gamma.quotient
            (Gamma.terminalFrontier (L.warpAt delta))).essentialPart_adj_imp
              (Q.quotient_adj_imp e)))
        (L.frontier beta))
  have hU0E : (H.quotient T).IsWave
      ((H.quotient T).essentialWarpPart U0.1) :=
    U0.2.essentialWarpPart
  have hFullToEss : (H.quotient T).terminalFrontier U0.1 ⊆
      H.roof ((H.quotient T).essential
        ((H.quotient T).terminalFrontier U0.1)) := by
    intro x hx
    rw [← (H.quotient T).terminalFrontier_essentialWarpPart U0.1]
    apply H.quotientWave_roof_subset_original_roof_general
      hNoEnterQ.quotient hU0E
    rw [(H.quotient T).terminalFrontier_essentialWarpPart,
      (H.quotient T).roof_essential]
    exact (H.quotient T).subset_roof _ hx
  have hTfU0H : (H.quotient T).terminalFrontier U0.1 ⊆
      H.roof (L.frontier beta) :=
    hFullToEss.trans (H.roof_cut hEss0H)
  have hExtend : H.roof (H.terminalFrontier R) ⊆
      H.roof ((H.quotient T).terminalFrontier U0.1) := by
    exact H.roof_terminalFrontier_subset_generalWaveQuotient
      hNoEnterQ.quotient hR
  have hTfRH : H.terminalFrontier R ⊆ H.roof (L.frontier beta) := by
    intro x hx
    exact H.roof_cut hTfU0H
      (hExtend (H.subset_roof _ hx))
  have hTbetaQ : T ⊆ Q.roof (L.frontier beta) := by
    intro x hx
    have hxGamma : x ∈ Gamma.roof (L.frontier beta) :=
      Gamma.roof_cut (hL.frontierChronology hzb)
        (Gamma.subset_roof T hx)
    exact roof_subset_of_adj_imp Gamma Q rfl
      (fun {_ _} e ↦ Gamma.quotient_adj_imp
        ((Gamma.quotient
          (Gamma.terminalFrontier (L.warpAt delta))).essentialPart_adj_imp e))
      (L.frontier beta) hxGamma
  have hXbeta : X ⊆ Q.roof (L.frontier beta) :=
    hX.trans (Q.roof_cut hTbetaQ)
  have hEssX : Q.essential X ⊆ Q.roof (L.frontier beta) :=
    (Q.essential_subset X).trans hXbeta
  rw [Q.terminalFrontier_liftQuotientFamily]
  intro x hx
  have hxH : x ∈ H.roof (L.frontier beta) := hTfRH hx
  by_cases hxStrict : x ∈ Q.strictRoof X
  · exact Q.roof_cut hXbeta hxStrict.1
  · exact Q.quotient_roof_subset_original_roof_of_essential
      X (L.frontier beta) hEssX ⟨hxH, hxStrict⟩

/-- Split-legality compatibility form of Assertion 9.9. -/
theorem quotientStageWave_terminalFrontier_subset_laterFrontierRoof
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    {delta zeta beta : Ladder.Stage kappa}
    (hdz : delta < zeta) (hzb : zeta < beta)
    {X : Set V}
    (hX : X ⊆ (L.stageWeb delta).roof (L.frontier zeta))
    {R : Set ((L.stageWeb delta).quotient X).DPath}
    (hR : ((L.stageWeb delta).quotient X).IsWave R) :
    (L.stageWeb delta).terminalFrontier
        ((L.stageWeb delta).liftQuotientFamily X R) ⊆
      (L.stageWeb delta).roof (L.frontier beta) :=
  quotientStageWave_terminalFrontier_subset_laterFrontierRoof_of_geometry
    (HeightRoofGeometry.ofSplitLegal hL) hNoEnter hdz hzb hX hR

end SliceCandidate
end CardinalInduction
end Erdos599
