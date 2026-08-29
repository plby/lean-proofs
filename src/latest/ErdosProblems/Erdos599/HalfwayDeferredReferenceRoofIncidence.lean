/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayDeferredStageIntervalBridge
import ErdosProblems.Erdos599.HalfwayGlobalLocalReferenceSafety
import ErdosProblems.Erdos599.DeferredLadderRoofTransport
import ErdosProblems.Erdos599.GroundingHangingCollisionSplit

/-!
# Limiting-reference incidence inside a deferred ladder roof

At a selected stage, a limiting-reference component which meets the stage
roof has a component prefix already present at that stage.  Every point of
the limiting component which is still in the roof lies on that prefix.
Consequently such a point either belongs to the selected essential reference
or to the carrier of the inessential stage components.  At a club stage
outside the deferred obstruction, the latter carrier has size at most the
induction cardinal.  This is the literal bounded exceptional family used in
the source's good-hammock argument.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DWeb.DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Exact successor arrows give exhaustive component provenance for a
deferred-legal ladder; bookkeeping is irrelevant to this fact. -/
theorem successorComponentProvenance
    {L : Gamma.KappaLadder kappa} (hL : HalfwayGeometry L)
    (a : Stage kappa) (q : Gamma.DPath) (hq : q ∈ L.successorWarp a) :
    (∃ p ∈ L.warpAt a, L.IsRungArrowPair a p q) ∨
      ∃ y : V, L.marker a = some y ∧ q = Gamma.trivialPath y := by
  rw [(hL.exactSuccessorArrows a).2] at hq
  rcases hq with hq | hq
  · exact Or.inl ((hL.exactSuccessorArrows a).1.2 q hq)
  · cases hmarker : L.marker a with
    | none => simp [markerPathSet, hmarker] at hq
    | some y =>
        refine Or.inr ⟨y, rfl, ?_⟩
        simpa [markerPathSet, hmarker] using hq

/-- At a deferred self-roofing stage, the tail of each accumulated edge is
strictly roofed by the raw stage terminal frontier. -/
theorem edge_tail_mem_strictRoof_of_mem_warpAt
    {L : Gamma.KappaLadder kappa} (hL : HalfwayGeometry L)
    (a : Stage kappa) {u v : V}
    (he : (u, v) ∈ Gamma.pathFamilyEdgeSet (L.warpAt a)) :
    u ∈ Gamma.strictRoof (Gamma.terminalFrontier (L.warpAt a)) := by
  rcases he with ⟨p, hp, hep⟩
  have huSupport : u ∈ p.support :=
    (p.edgeSet_subset_support_prod hep).1
  refine ⟨Deferred.vertexSet_warpAt_subset_roof_terminalFrontier hL a
    ⟨p, hp, huSupport⟩, ?_⟩
  intro huEssential
  obtain ⟨q, hq, hqTerminal⟩ := huEssential.1
  have hpq : p = q := by
    by_contra hpq
    exact Set.disjoint_left.1
      (hL.warpStages (Stage.toExtended a) hp hq hpq)
      huSupport (Gamma.terminal_mem_support hqTerminal)
  subst q
  rcases p with p | r
  · exact _root_.Erdos599.Alternating.FinitePath.source_ne_finish_of_mem_edgeSet
      p hep (Option.some.inj hqTerminal).symm
  · simp at hqTerminal

/-- No limiting-family edge can first enter an earlier roof after the
selected stage.  This is the deferred-bookkeeping version of the standard
successor/limit recursion; it uses only exact arrows and direct limits. -/
theorem pathFamilyEdgeSet_of_head_mem_roof_frontier
    {L : Gamma.KappaLadder kappa} (hL : HalfwayGeometry L)
    (c : Stage kappa) :
    ∀ (o : Ordinal.{u}) (ho : o ≤ kappa.ord), c.1 ≤ o →
      ∀ {u v : V},
        (u, v) ∈ Gamma.pathFamilyEdgeSet
            (L.accumulated (⟨o, ho⟩ : ExtendedStage kappa)) →
        v ∈ Gamma.roof (L.frontier c) →
        (u, v) ∈ Gamma.pathFamilyEdgeSet (L.warpAt c) := by
  intro o
  induction o using Ordinal.limitRecOn with
  | zero =>
      intro ho hc u v he _hv
      have hc0 : c.1 = 0 := le_antisymm hc bot_le
      have hstage : (⟨0, ho⟩ : ExtendedStage kappa) =
          Stage.toExtended c := Subtype.ext hc0.symm
      rwa [hstage] at he
  | add_one o ih =>
      intro ho hc u v he hv
      rcases hc.lt_or_eq with hc | hc
      · have hoKappa : o < kappa.ord :=
          (show o < o + 1 by
            rw [← Order.succ_eq_add_one]
            exact Order.lt_succ o).trans_le ho
        let a : Stage kappa := ⟨o, hoKappa⟩
        have hca : c ≤ a := by
          change c.1 ≤ o
          exact (Order.lt_add_one_iff).1 hc
        have hsucc : (⟨o + 1, ho⟩ : ExtendedStage kappa) =
            Stage.succExtended a := Subtype.ext rfl
        have heSuccessor : (u, v) ∈
            Gamma.pathFamilyEdgeSet (L.successorWarp a) := by
          change (u, v) ∈ Gamma.pathFamilyEdgeSet
            (L.accumulated (Stage.succExtended a))
          rwa [← hsucc]
        rcases heSuccessor with ⟨q, hq, heq⟩
        rcases successorComponentProvenance hL a q hq with
            hArrow | hMarker
        · rcases hArrow with ⟨p, hp, hpq⟩
          rcases hpq with ⟨_hpRay, rfl⟩ |
              ⟨x, _hpTerminal, hcontinue | hfixed⟩
          · exact ih hoKappa.le hca ⟨q, hp, heq⟩ hv
          · rcases hcontinue with ⟨r, _hrInitial,
                _hrMem, _hrTerminal, _hextends, _hsupport,
                hedge, _hqTerminal⟩
            change (u, v) ∈ pathEdgeSet q at heq
            rw [hedge] at heq
            rcases heq with heOld | heNew
            · exact ih hoKappa.le hca ⟨p, hp, heOld⟩ hv
            · have hvRoofA : v ∈ Gamma.roof (L.frontier a) := by
                rcases hca.lt_or_eq with hca | rfl
                · exact Gamma.roof_cut (hL.frontierChronology hca) hv
                · exact hv
              have hvRaw : v ∈ Gamma.roof
                  (Gamma.terminalFrontier (L.warpAt a)) := by
                rw [L.frontier_eq_essential_terminalFrontier
                    hL.roofsSourceAtStages,
                  Gamma.roof_essential] at hvRoofA
                exact hvRoofA
              exact (_root_.Erdos599.DWeb.KappaLadder.liftStagePath_edge_head_not_mem_roof
                L a r heNew
                hvRaw).elim
          · rcases hfixed with ⟨_hno, rfl⟩
            exact ih hoKappa.le hca ⟨q, hp, heq⟩ hv
        · rcases hMarker with ⟨y, _hy, rfl⟩
          change (u, v) ∈ (∅ : Set (V × V)) at heq
          exact heq.elim
      · have hcEq : (⟨o + 1, ho⟩ : ExtendedStage kappa) =
            Stage.toExtended c := Subtype.ext hc.symm
        rwa [hcEq] at he
  | limit o hoLimit ih =>
      intro ho hc u v he hv
      rcases hc.lt_or_eq with hc | hc
      · let oe : ExtendedStage kappa := ⟨o, ho⟩
        obtain ⟨C, hstage, hlimit⟩ := hL.limitStages oe hoLimit
        have heLimit : (u, v) ∈
            Gamma.pathFamilyEdgeSet (C.limitPaths Gamma) := by
          rw [← hlimit]
          exact he
        rw [C.pathFamilyEdgeSet_limitPaths Gamma] at heLimit
        obtain ⟨b, heb⟩ := Set.mem_iUnion.1 heLimit
        let ci : Set.Iio o := ⟨c.1, hc⟩
        obtain ⟨d, hbd, hcd⟩ := exists_ge_ge b ci
        have hed : (u, v) ∈ Gamma.pathFamilyEdgeSet (C.stage d) :=
          C.pathFamilyEdgeSet_mono Gamma hbd heb
        have hedAccumulated : (u, v) ∈ Gamma.pathFamilyEdgeSet
            (L.accumulated
              (⟨d.1, d.2.le.trans ho⟩ : ExtendedStage kappa)) := by
          rwa [← hstage d]
        exact ih d.1 d.2 (d.2.le.trans ho) hcd hedAccumulated hv
      · have hcEq : (⟨o, ho⟩ : ExtendedStage kappa) =
            Stage.toExtended c := Subtype.ext hc.symm
        rwa [hcEq] at he

/-- Roof membership of a support point on a limiting component propagates
back to the component initial. -/
theorem limitComponent_initial_mem_roof_of_support_mem
    {L : Gamma.KappaLadder kappa} (hL : HalfwayGeometry L)
    (c : Stage kappa) {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    {v : V} (hvp : v ∈ p.support)
    (hvRoof : v ∈ Gamma.roof (L.frontier c)) :
    p.initial ∈ Gamma.roof (L.frontier c) := by
  have hback : ∀ {x y : V}, (x, y) ∈ p.edgeSet →
      y ∈ Gamma.roof (L.frontier c) →
      x ∈ Gamma.roof (L.frontier c) := by
    intro x y hxy hyRoof
    have hxyLimit : (x, y) ∈
        Gamma.pathFamilyEdgeSet L.limitWarp := ⟨p, hp, hxy⟩
    have hxyStage : (x, y) ∈
        Gamma.pathFamilyEdgeSet (L.warpAt c) :=
      pathFamilyEdgeSet_of_head_mem_roof_frontier hL c
        kappa.ord le_rfl c.2.le hxyLimit hyRoof
    have hxRaw := edge_tail_mem_strictRoof_of_mem_warpAt hL c hxyStage
    rw [L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages, Gamma.roof_essential]
    exact hxRaw.1
  rcases p with p | r
  · apply _root_.Erdos599.DWeb.KappaLadder.Walk.start_mem_of_meets_of_backwardClosed
      (w := p.walk) (R := Gamma.roof (L.frontier c))
    · intro x y hxy hy
      exact hback hxy hy
    · exact ⟨v, hvp, hvRoof⟩
  · obtain ⟨n, hn⟩ := hvp
    subst v
    change r.initial ∈ Gamma.roof (L.frontier c)
    change r 0 ∈ Gamma.roof (L.frontier c)
    have hprefix : ∀ n : ℕ,
        r n ∈ Gamma.roof (L.frontier c) →
          r 0 ∈ Gamma.roof (L.frontier c) := by
      intro n
      induction n with
      | zero => exact fun h ↦ h
      | succ n ih =>
          intro hnRoof
          apply ih
          apply hback
          · exact ⟨n, rfl⟩
          · exact hnRoof
    exact hprefix n hvRoof

/-- If the initial vertex of a limiting component is already below an
ordinary-stage frontier, then that component has a prefix in the accumulated
warp at that stage.  Source initials start at stage zero; marker initials
start at the marker successor, which must precede the displayed stage by
marker freshness. -/
theorem exists_warpAt_prefix_of_limitComponent_initial_mem_roof
    {L : Gamma.KappaLadder kappa} (hL : HalfwayGeometry L)
    (c : Stage kappa) {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    (hpRoof : p.initial ∈ Gamma.roof (L.frontier c)) :
    ∃ q ∈ L.warpAt c, Gamma.Extends q p := by
  have finish
      {q : Gamma.DPath} (hq : q ∈ L.warpAt c)
      (hqi : q.initial = p.initial) :
      ∃ q ∈ L.warpAt c, Gamma.Extends q p := by
    refine ⟨q, hq, ?_⟩
    apply hL.extends_limitWarp_of_stage_intersects hq hp
    exact ⟨p.initial, by simpa only [hqi] using q.initial_mem_support,
      p.initial_mem_support⟩
  rcases hL.accumulatedInitialProvenance
      (Ladder.finalStage kappa) p hp with hpSource | ⟨b, _hbFinal, hbMarker⟩
  · let z : Stage kappa := ⟨0, hL.regular.ord_pos⟩
    have hzPath : Gamma.trivialPath p.initial ∈ L.warpAt z := by
      change Gamma.trivialPath p.initial ∈
        L.accumulated (Stage.toExtended z)
      have hz : Stage.toExtended z = Ladder.zeroStage kappa :=
        Subtype.ext rfl
      rw [hz, hL.initialStage]
      exact ⟨p.initial, hpSource, rfl⟩
    have hzc : z ≤ c := by
      change (0 : Ordinal.{u}) ≤ c.1
      exact bot_le
    obtain ⟨q, hq, hzq⟩ :=
      _root_.Erdos599.CardinalInduction.DeferredStageInterval.warpAt_grows_of_le hL
        (delta := z) (beta := c) hzc
        (Gamma.trivialPath p.initial) hzPath
    apply finish hq
    simpa using (Gamma.extends_initial hzq).symm
  · have hbc : b < c := by
      by_contra hnot
      have hcb : c ≤ b := le_of_not_gt hnot
      have hpRoofB : p.initial ∈ Gamma.roof (L.frontier b) := by
        rcases hcb.lt_or_eq with hcb | hcb
        · exact Gamma.roof_cut (hL.frontierChronology hcb) hpRoof
        · rwa [hcb] at hpRoof
      exact marker_not_mem_roof_frontier L hL hbMarker hpRoofB
    have hsuccle : successorStage L hL b ≤ c :=
      (successorStage_le_iff_lt L hL).2 hbc
    have hmarkerSuccessor :
        Gamma.trivialPath p.initial ∈ L.successorWarp b :=
      hL.markerInserted b p.initial hbMarker
    have hmarkerStage : Gamma.trivialPath p.initial ∈
        L.warpAt (successorStage L hL b) := by
      change Gamma.trivialPath p.initial ∈ L.successorWarp b
      exact hmarkerSuccessor
    obtain ⟨q, hq, hqext⟩ :=
      _root_.Erdos599.CardinalInduction.DeferredStageInterval.warpAt_grows_of_le
        hL hsuccle
        (Gamma.trivialPath p.initial) hmarkerStage
    apply finish hq
    simpa using (Gamma.extends_initial hqext).symm

/-- Every point of the limiting component which remains below the displayed
frontier already lies on its stage prefix.  A noninitial point has an incoming
edge; the no-late-entry lemma supplies its stage component, and uniqueness in
the stage warp identifies that component with the chosen prefix. -/
theorem limitComponent_support_inter_roof_subset_prefix
    {L : Gamma.KappaLadder kappa} (hL : HalfwayGeometry L)
    (c : Stage kappa) {p q : Gamma.DPath}
    (hp : p ∈ L.limitWarp) (hq : q ∈ L.warpAt c)
    (hqp : Gamma.Extends q p) :
    p.support ∩ Gamma.roof (L.frontier c) ⊆ q.support := by
  rintro x ⟨hxp, hxRoof⟩
  by_cases hxi : x = p.initial
  · rw [hxi, ← Gamma.extends_initial hqp]
    exact q.initial_mem_support
  · obtain ⟨y, hyx⟩ : ∃ y, (y, x) ∈ p.edgeSet := by
      rcases p with f | r
      · exact _root_.Erdos599.Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
          f hxp hxi
      · obtain ⟨n, hn⟩ := hxp
        have hnpos : 0 < n := by
          by_contra hnzero
          have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnzero
          apply hxi
          change x = r 0
          simpa only [hn0] using hn.symm
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
          (Nat.ne_of_gt hnpos)
        exact ⟨r m, ⟨m, by exact Prod.ext rfl hn.symm⟩⟩
    have hyxLimit : (y, x) ∈ Gamma.pathFamilyEdgeSet L.limitWarp :=
      ⟨p, hp, hyx⟩
    have hyxStage : (y, x) ∈ Gamma.pathFamilyEdgeSet (L.warpAt c) :=
      pathFamilyEdgeSet_of_head_mem_roof_frontier hL c
        kappa.ord le_rfl c.2.le hyxLimit hxRoof
    obtain ⟨r, hr, hyr⟩ := hyxStage
    have hrp : Gamma.Extends r p := by
      apply hL.extends_limitWarp_of_stage_intersects hr hp
      exact ⟨x, (r.edgeSet_subset_support_prod hyr).2, hxp⟩
    have hrq : r = q := by
      apply DWeb.IsWarp.eq_of_initial_eq Gamma
        (hL.warpStages (Stage.toExtended c)) hr hq
      exact (Gamma.extends_initial hrp).trans
        (Gamma.extends_initial hqp).symm
    rw [← hrq]
    exact (r.edgeSet_subset_support_prod hyr).2

/-- Inside a stage roof the limiting reference is covered by the selected
essential stage reference together with the genuinely inessential stage
components.  This is the exact geometric decomposition behind the source's
bounded discard; it does not identify the limiting and selected warps. -/
theorem vertexSet_limitWarp_inter_roof_subset_essential_or_inessential
    {L : Gamma.KappaLadder kappa} (hL : HalfwayGeometry L)
    (c : Stage kappa) :
    Gamma.vertexSet L.limitWarp ∩ Gamma.roof (L.frontier c) ⊆
      Gamma.vertexSet (Gamma.essentialWarpPart (L.warpAt c)) ∪
        Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt c)) := by
  rintro x ⟨⟨p, hp, hxp⟩, hxRoof⟩
  have hpInitialRoof : p.initial ∈ Gamma.roof (L.frontier c) :=
    limitComponent_initial_mem_roof_of_support_mem hL c hp hxp hxRoof
  obtain ⟨q, hq, hqp⟩ :=
    exists_warpAt_prefix_of_limitComponent_initial_mem_roof
      hL c hp hpInitialRoof
  have hxq : x ∈ q.support :=
    limitComponent_support_inter_roof_subset_prefix hL c hp hq hqp
      ⟨hxp, hxRoof⟩
  by_cases hqEssential : q ∈ Gamma.essentialWarpPart (L.warpAt c)
  · exact Or.inl ⟨q, hqEssential, hxq⟩
  · exact Or.inr ⟨q, Gamma.mem_inessentialPaths.2 ⟨hq, hqEssential⟩, hxq⟩

/-- At a selected club stage outside `phi`, the discarded carrier in the
preceding decomposition has cardinality at most the predecessor cardinal. -/
theorem mk_vertexSet_inessentialWarpAt_le_of_not_mem_phi
    {L : Gamma.KappaLadder (succ kappa)} (hL : HalfwayGeometry L)
    (hkappa : aleph0 ≤ kappa) (c : Stage (succ kappa))
    (hc : c ∉ phi L) :
    #(Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt c))) ≤ kappa := by
  apply CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
    hkappa
  exact lt_succ_iff.mp (mk_inessentialWarpAt_lt_of_not_mem_phi hL c hc)

#print axioms pathFamilyEdgeSet_of_head_mem_roof_frontier
#print axioms limitComponent_initial_mem_roof_of_support_mem
#print axioms exists_warpAt_prefix_of_limitComponent_initial_mem_roof
#print axioms limitComponent_support_inter_roof_subset_prefix
#print axioms vertexSet_limitWarp_inter_roof_subset_essential_or_inessential
#print axioms mk_vertexSet_inessentialWarpAt_le_of_not_mem_phi

end Deferred
end KappaLadder
end DWeb

namespace Blueprint.LinkageBlueprint
namespace ladderReference

open DirectedPath Ladder Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Ladder.Stage kappa}

/-- A route contained in the selected roof and avoiding the inessential
stage carrier has no unseen contact with the global limiting reference.
This packages the preceding geometric decomposition in the exact form used
by the local-to-global safeness transport. -/
theorem referenceContactConfined_of_subset_roof_of_disjoint_inessential
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Q : AltPath Gamma.graph}
    (hQRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a))
    (hQbad : Disjoint Q.vertexSet
      (Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a)))) :
    ReferenceContactConfined (L := L) (a := a) Q := by
  rintro x ⟨hxQ, hxLimit⟩
  have hxCases :=
    DWeb.KappaLadder.Deferred.vertexSet_limitWarp_inter_roof_subset_essential_or_inessential
      hL a ⟨hxLimit, hQRoof hxQ⟩
  rcases hxCases with hxLocal | hxBad
  · simpa only [ladderReference] using hxLocal
  · exact (Set.disjoint_left.1 hQbad hxQ hxBad).elim

/-- Exposed endpoints below the selected frontier are globally admissible
as soon as they avoid the bounded inessential carrier.  This is the weaker,
source-exact hypothesis needed by alternation: internal forward contacts do
not need to be confined. -/
theorem referenceEndpointConfined_of_roof_of_not_mem_inessential
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Q : AltPath Gamma.graph}
    (hinitialRoof : Q.initial ∈ Gamma.roof (L.frontier a))
    (hinitialBad : Q.initial ∉
      Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a)))
    (hterminalRoof : ∀ t, Q.terminal? = some t →
      t ∈ Gamma.roof (L.frontier a))
    (hterminalBad : ∀ t, Q.terminal? = some t →
      t ∉ Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a))) :
    ReferenceEndpointConfined (L := L) (a := a) Q := by
  have endpointLocal {x : V}
      (hxRoof : x ∈ Gamma.roof (L.frontier a))
      (hxBad : x ∉ Gamma.vertexSet
        (Gamma.inessentialPaths (L.warpAt a)))
      (hxLimit : x ∈ Gamma.vertexSet L.limitWarp) :
      x ∈ Gamma.vertexSet (ladderReference L a) := by
    have hxCases :=
      DWeb.KappaLadder.Deferred.vertexSet_limitWarp_inter_roof_subset_essential_or_inessential
        hL a ⟨hxLimit, hxRoof⟩
    rcases hxCases with hxLocal | hxInessential
    · simpa only [ladderReference] using hxLocal
    · exact (hxBad hxInessential).elim
  refine ⟨?_, ?_⟩
  · intro _hfirst hglobal
    exact endpointLocal hinitialRoof hinitialBad hglobal
  · intro t ht _hlast hglobal
    exact endpointLocal (hterminalRoof t ht) (hterminalBad t ht) hglobal

/-- Consequently a locally safe route with the same concrete roof
confinement and avoidance is safe for the possibly infinite limiting
reference. -/
theorem isSafe_limitWarp_of_subset_roof_of_disjoint_inessential
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Q : AltPath Gamma.graph}
    (hlocal : IsSafe (ladderReference L a) Q)
    (hQRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a))
    (hQbad : Disjoint Q.vertexSet
      (Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a)))) :
    IsSafe L.limitWarp Q := by
  exact isSafe_limitWarp_of_contactConfined hL hlocal
    (referenceContactConfined_of_subset_roof_of_disjoint_inessential
      hL hQRoof hQbad)

/-- Endpoint-only form of the preceding safeness transport. -/
theorem isSafe_limitWarp_of_endpoint_roof_of_not_mem_inessential
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Q : AltPath Gamma.graph}
    (hlocal : IsSafe (ladderReference L a) Q)
    (hinitialRoof : Q.initial ∈ Gamma.roof (L.frontier a))
    (hinitialBad : Q.initial ∉
      Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a)))
    (hterminalRoof : ∀ t, Q.terminal? = some t →
      t ∈ Gamma.roof (L.frontier a))
    (hterminalBad : ∀ t, Q.terminal? = some t →
      t ∉ Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a))) :
    IsSafe L.limitWarp Q := by
  exact isSafe_limitWarp_of_endpointConfined hL hlocal
    (referenceEndpointConfined_of_roof_of_not_mem_inessential
      hL hinitialRoof hinitialBad hterminalRoof hterminalBad)

#print axioms referenceContactConfined_of_subset_roof_of_disjoint_inessential
#print axioms referenceEndpointConfined_of_roof_of_not_mem_inessential
#print axioms isSafe_limitWarp_of_subset_roof_of_disjoint_inessential
#print axioms isSafe_limitWarp_of_endpoint_roof_of_not_mem_inessential

end ladderReference

namespace ClubStageGeometry

open DirectedPath Ladder Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The literal exceptional carrier at the selected later club stage. -/
def limitingReferenceException
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) : Set V :=
  Gamma.vertexSet
    (Gamma.inessentialPaths (C.ladder.warpAt C.newStage))

/-- Club avoidance of the deferred obstruction makes the literal exception
carrier `kappa`-small. -/
theorem mk_limitingReferenceException_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) :
    #C.limitingReferenceException ≤ kappa := by
  apply DWeb.KappaLadder.Deferred.mk_vertexSet_inessentialWarpAt_le_of_not_mem_phi
    C.legal C.capacity_infinite C.newStage
  intro hphi
  exact Set.disjoint_left.1 C.club_avoids_phi C.new_mem_club hphi

/-- Concrete selected-stage form of the limiting-reference incidence
decomposition. -/
theorem limitWarp_inter_outerRoof_subset_selected_or_exception
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) :
    Gamma.vertexSet C.ladder.limitWarp ∩ C.outerRoof ⊆
      Gamma.vertexSet C.selectedReference ∪
        C.limitingReferenceException := by
  simpa only [outerRoof, newSlice, selectedReference,
    ladderReference, limitingReferenceException] using
    (DWeb.KappaLadder.Deferred.vertexSet_limitWarp_inter_roof_subset_essential_or_inessential
      C.legal C.newStage)

/-- A selected-reference safe path contained in the concrete transaction
roof becomes limiting-reference safe after avoiding the actual club-stage
exception carrier. -/
theorem isSafe_limitWarp_of_outerRoof_of_disjoint_exception
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {Q : AltPath Gamma.graph}
    (hlocal : IsSafe C.selectedReference Q)
    (hroof : Q.vertexSet ⊆ C.outerRoof)
    (havoid : Disjoint Q.vertexSet C.limitingReferenceException) :
    IsSafe C.ladder.limitWarp Q := by
  exact ladderReference.isSafe_limitWarp_of_subset_roof_of_disjoint_inessential
    C.legal hlocal hroof havoid

/-- Endpoint-only version used by the 9.30 hammock selection. -/
theorem isSafe_limitWarp_of_endpoint_outerRoof_of_not_mem_exception
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {Q : AltPath Gamma.graph}
    (hlocal : IsSafe C.selectedReference Q)
    (hinitialRoof : Q.initial ∈ C.outerRoof)
    (hinitialBad : Q.initial ∉ C.limitingReferenceException)
    (hterminalRoof : ∀ t, Q.terminal? = some t → t ∈ C.outerRoof)
    (hterminalBad : ∀ t, Q.terminal? = some t →
      t ∉ C.limitingReferenceException) :
    IsSafe C.ladder.limitWarp Q := by
  exact ladderReference.isSafe_limitWarp_of_endpoint_roof_of_not_mem_inessential
    C.legal hlocal hinitialRoof hinitialBad hterminalRoof hterminalBad

/-- A selected-reference hammock transfers to the limiting reference after
the source construction excludes its fixed exposed endpoints from the
literal exceptional carrier.  Every nonconfined route then has an interior
exception contact; disjoint hammock interiors inject the bad routes into the
`kappa`-small inessential stage family. -/
theorem hasHammockCard_limitWarp_of_endpoints_disjoint_exception
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {u : V} {e : AltEnd V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (hlarge : HasHammockCard Gamma C.selectedReference u e (succ kappa))
    (hendpoints : Disjoint (hammockEndpoints u e)
      C.limitingReferenceException) :
    HasHammockCard Gamma C.ladder.limitWarp u e (succ kappa) := by
  let P : Set Gamma.DPath :=
    Gamma.inessentialPaths (C.ladder.warpAt C.newStage)
  have hP : #P ≤ kappa := by
    exact lt_succ_iff.mp
      (DWeb.KappaLadder.Deferred.mk_inessentialWarpAt_lt_of_not_mem_phi
        C.legal C.newStage (by
          intro hphi
          exact Set.disjoint_left.1 C.club_avoids_phi C.new_mem_club hphi))
  apply ladderReference.hasHammockCard_limitWarp_of_small_contactCarrier
    C.legal C.capacity_infinite hlarge P hP
  intro K hK Q hQ hnotConfined
  have hnotSubset : ¬ (Q.vertexSet ∩
      Gamma.vertexSet C.ladder.limitWarp ⊆
        Gamma.vertexSet C.selectedReference) := hnotConfined
  obtain ⟨x, ⟨hxQ, hxLimit⟩, hxNotSelected⟩ :=
    Set.not_subset.mp hnotSubset
  have hxRoof : x ∈ C.outerRoof := hSafeRoof Q (hK.1 Q hQ).1 hxQ
  have hxCases := C.limitWarp_inter_outerRoof_subset_selected_or_exception
    ⟨hxLimit, hxRoof⟩
  have hxException : x ∈ C.limitingReferenceException := by
    rcases hxCases with hxSelected | hxException
    · exact False.elim (hxNotSelected hxSelected)
    · exact hxException
  refine ⟨x, ⟨hxQ, ?_⟩, hxException⟩
  intro hxEndpoint
  exact Set.disjoint_left.1 hendpoints hxEndpoint hxException

/-- Local imaginary edges whose two exposed endpoints avoid the selected
stage exception are genuine imaginary edges for the global limiting
reference. -/
theorem isImaginaryEdge_limitWarp_of_endpoints_disjoint_exception
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {u v : V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (hlocal : IsImaginaryEdge Gamma C.selectedReference kappa u v)
    (hendpoints : Disjoint ({u, v} : Set V)
      C.limitingReferenceException) :
    IsImaginaryEdge Gamma C.ladder.limitWarp kappa u v := by
  apply C.hasHammockCard_limitWarp_of_endpoints_disjoint_exception
    hSafeRoof hlocal
  simpa only [hammockEndpoints] using hendpoints

/-- The analogous popularity transport; the persistent branch is unchanged
and the infinite-hammock branch uses the singleton exposed endpoint. -/
theorem isPopular_limitWarp_of_endpoint_disjoint_exception
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {persistent : Set V} {u : V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (hlocal : IsPopular Gamma C.selectedReference persistent kappa u)
    (hu : u ∉ C.limitingReferenceException) :
    IsPopular Gamma C.ladder.limitWarp persistent kappa u := by
  rcases hlocal with hpersistent | hhammock
  · exact Or.inl hpersistent
  · apply Or.inr
    apply C.hasHammockCard_limitWarp_of_endpoints_disjoint_exception
      hSafeRoof hhammock
    simpa only [hammockEndpoints, Set.disjoint_singleton_left]

#print axioms mk_limitingReferenceException_le
#print axioms limitWarp_inter_outerRoof_subset_selected_or_exception
#print axioms isSafe_limitWarp_of_outerRoof_of_disjoint_exception
#print axioms isSafe_limitWarp_of_endpoint_outerRoof_of_not_mem_exception
#print axioms hasHammockCard_limitWarp_of_endpoints_disjoint_exception
#print axioms isImaginaryEdge_limitWarp_of_endpoints_disjoint_exception
#print axioms isPopular_limitWarp_of_endpoint_disjoint_exception

end ClubStageGeometry
end Blueprint.LinkageBlueprint
end Erdos599
