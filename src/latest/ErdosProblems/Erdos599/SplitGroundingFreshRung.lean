/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitSameStageRecord
import ErdosProblems.Erdos599.HindranceGrounding
import ErdosProblems.Erdos599.GroundingFreshTerminalNoise
import ErdosProblems.Erdos599.GroundingFreshReroute

/-!
# Fresh grounded records and the successor rung

A selected ray which is genuinely new at its successor stage cannot come
from an old ray (old rays are already inessential), nor from the finite
marker singleton.  Hence it is obtained by continuing an old finite
component along a ray of the current rung.  That rung ray witnesses a
hindrance in the quotient-stage web.  For the canonical ladder, whose rung
is the chosen maximal hindrance whenever the stage web is hindered, the
stage consequently belongs to `phiHindrance`.

This is a local classification result.  It does not claim that the quotient
hindrance is already grounded in the ambient web; that is the remaining
global Section 8 obligation.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- Split-legal form of terminal provenance at a full rung.  The proof uses
only successor-component provenance and the geometric wave fields, not the
legacy strict hanging-origin field. -/
theorem IsSplitLegal.successorTerminal_mem_rung_or_marker_or_strictOld
    {L : G.KappaLadder kappa} (hL : L.IsSplitLegal)
    {a : Ladder.Stage kappa}
    (hfull : (L.stageWeb a).initialSet (L.rung a) =
      (L.stageWeb a).source)
    {x : V} (hx : x ∈ G.terminalFrontier (L.successorWarp a)) :
    x ∈ (L.stageWeb a).terminalFrontier (L.rung a) ∨
      (∃ y, L.marker a = some y ∧ x = y) ∨
      x ∈ G.strictRoof (G.terminalFrontier (L.warpAt a)) := by
  obtain ⟨q, hqSuccessor, hqx⟩ := hx
  rcases hL.successorComponentProvenance a q hqSuccessor with
      ⟨p, hpOld, hpq⟩ | ⟨y, hyMarker, rfl⟩
  · rcases hpq with ⟨hpRay, rfl⟩ |
        ⟨z, hpTerminal, hcontinue | hfixed⟩
    · rw [hpRay] at hqx
      cases hqx
    · obtain ⟨r, hrInitial, hrRung, _hpTerminal, _hextends,
          _hsupport, _hedges, hqTerminal⟩ := hcontinue
      left
      refine ⟨r, hrRung, ?_⟩
      exact (L.terminal?_liftStagePath a r).symm.trans
        (hqTerminal.symm.trans hqx)
    · obtain ⟨hnoRung, hqp⟩ := hfixed
      rw [hqp] at hqx
      right
      right
      have hpx : G.terminal? p = some x := hqx
      have hzx : z = x :=
        Option.some.inj (hpTerminal.symm.trans hpx)
      subst z
      have hpNotEssential :
          p ∉ G.essentialWarpPart (L.warpAt a) := by
        intro hpEssential
        have hxEssential :
            x ∈ G.essential (G.terminalFrontier (L.warpAt a)) := by
          obtain ⟨_hpOld, t, hpt, ht⟩ := hpEssential
          have htx : t = x := Option.some.inj (hpt.symm.trans hpx)
          exact htx ▸ ht
        have hxSource : x ∈ (L.stageWeb a).source := by
          change x ∈ L.frontier a
          rw [L.frontier_eq_essential_terminalFrontier
            hL.roofsSourceAtStages a]
          exact hxEssential
        have hxInitial :
            x ∈ (L.stageWeb a).initialSet (L.rung a) := by
          rw [hfull]
          exact hxSource
        obtain ⟨r, hrRung, hrInitial⟩ := hxInitial
        exact hnoRung ⟨r, hrRung, hrInitial⟩
      exact G.terminal_mem_strictRoof_of_mem_inessentialPaths
        ⟨hpOld, hpNotEssential⟩ hpx
  · right
    left
    refine ⟨y, hyMarker, ?_⟩
    simpa using hqx.symm

/-- Every terminal of a split-legal rung is an actual terminal of the exact
successor arrow. -/
theorem IsSplitLegal.rung_terminalFrontier_subset_successorFrontier
    {L : G.KappaLadder kappa} (hL : L.IsSplitLegal)
    (a : Ladder.Stage kappa) :
    (L.stageWeb a).terminalFrontier (L.rung a) ⊆
      G.terminalFrontier (L.successorWarp a) := by
  intro t ht
  obtain ⟨r, hr, hrt⟩ := ht
  have hrInitial : r.initial ∈ (L.stageWeb a).source :=
    (hL.waveRungs a).2.1 ⟨r, hr, rfl⟩
  have hOldRoof :
      G.source ⊆ G.roof (G.terminalFrontier (L.warpAt a)) :=
    hL.roofsSourceAtStages (Ladder.Stage.toExtended a)
  obtain ⟨p, hpEssential, hpTerminal⟩ :=
    G.exists_essentialWarpPart_terminal_of_mem_quotientEssentialPart_source
      hOldRoof hrInitial
  obtain ⟨q, hq, _hqunique⟩ := by
    simpa only [arrowPart, Set.mem_sdiff] using
      (hL.exactSuccessorArrows a).1.1 p hpEssential.1
  refine ⟨q, hq.1.1, ?_⟩
  rcases hq.2 with hRay | ⟨z, hpz, hcontinue | hfixed⟩
  · rw [hpTerminal] at hRay
    simp at hRay
  · have hz : z = r.initial := Option.some.inj (hpz.symm.trans hpTerminal)
    obtain ⟨r', hr'Initial, hr'Rung, _hpTerminal, _hextends,
      _hsupport, _hedges, hqTerminal⟩ := hcontinue
    have hrr' : r' = r := by
      apply IsWarp.eq_of_initial_eq (L.stageWeb a) (hL.waveRungs a).1
        hr'Rung hr
      exact hr'Initial.trans hz
    rw [hqTerminal, hrr', L.terminal?_liftStagePath, hrt]
  · have hz : z = r.initial := Option.some.inj (hpz.symm.trans hpTerminal)
    exfalso
    apply hfixed.1
    exact ⟨r, hr, hz.symm⟩

/-- In an unhindered web every member of a full wave is essential. -/
theorem mem_essentialWarpPart_of_isUnhindered_of_fullWave
    (Q : DWeb V) (hQ : Q.IsUnhindered)
    {W : Set Q.DPath} (hW : Q.IsWave W)
    (hfull : Q.initialSet W = Q.source)
    {r : Q.DPath} (hr : r ∈ W) :
    r ∈ Q.essentialWarpPart W := by
  have htrim : Q.IsWave (Q.essentialWarpPart W) := hW.essentialWarpPart
  have htrimFull :
      Q.initialSet (Q.essentialWarpPart W) = Q.source :=
    Q.isUnhindered_iff.mp hQ _ htrim
  have hrSource : r.initial ∈ Q.source := by
    rw [← hfull]
    exact ⟨r, hr, rfl⟩
  have hrTrimInitial :
      r.initial ∈ Q.initialSet (Q.essentialWarpPart W) := by
    rw [htrimFull]
    exact hrSource
  obtain ⟨s, hs, hsInitial⟩ := hrTrimInitial
  have hsr : s = r := by
    by_contra hne
    exact Set.disjoint_left.1 (hW.1 hs.1 hr hne)
      (hsInitial ▸ s.initial_mem_support) r.initial_mem_support
  exact hsr ▸ hs

/-- Marker roof exclusion using only split legality. -/
theorem IsSplitLegal.marker_not_mem_roof_frontier
    {L : G.KappaLadder kappa} (hL : L.IsSplitLegal)
    {a : Ladder.Stage kappa} {y : V} (hy : L.marker a = some y) :
    y ∉ G.roof (L.frontier a) := by
  have hyCandidate : y ∈ L.markerCandidates a :=
    (hL.freshMarkers.2 a y hy).1
  have hyNotFrontier : y ∉ L.frontier a := by
    intro hyFrontier
    exact hyCandidate.2 (Or.inl hyFrontier)
  have hyNotStrictOld :
      y ∉ G.strictRoof (G.terminalFrontier (L.warpAt a)) :=
    hyCandidate.1.2
  intro hyRoof
  have hyNotEssential : y ∉ G.essential (L.frontier a) := by
    rw [hL.frontiersEssential a]
    exact hyNotFrontier
  have hyStrict : y ∈ G.strictRoof (L.frontier a) :=
    ⟨hyRoof, hyNotEssential⟩
  apply hyNotStrictOld
  rw [L.frontier_eq_essential_terminalFrontier
    hL.roofsSourceAtStages, G.strictRoof_essential] at hyStrict
  exact hyStrict

/-- A genuinely successor-new selected ray makes the current quotient-stage
web hindered.  Only the sound split legality fields are used. -/
theorem freshInessentialRecord_ray_stageWeb_not_isUnhindered
    (L : G.KappaLadder kappa) (hL : L.IsSplitLegal)
    {a : Ladder.Stage kappa} {r : DirectedPath.Ray G.graph}
    (ha : a ∈ L.freshInessentialRecordStages)
    (hrChosen : L.chosen a = some (Sum.inr r : G.DPath)) :
    ¬ (L.stageWeb a).IsUnhindered := by
  obtain ⟨p, hpChosen, hpNext, hpNotCurrent, _hpNotRecorded⟩ :=
    L.freshInessentialRecordStages_spec hL.validBookkeeping ha
  have hpr : p = (Sum.inr r : G.DPath) :=
    Option.some.inj (hpChosen.symm.trans hrChosen)
  subst p
  rcases hL.successorComponentProvenance a (Sum.inr r : G.DPath) hpNext.1 with
      ⟨q, hqCurrent, hqr⟩ | ⟨y, _hyMarker, hyr⟩
  · rcases hqr with hqRay | ⟨x, hqx, hcontinue | hfixed⟩
    · obtain ⟨_hqTerminal, hqr⟩ := hqRay
      subst q
      exact False.elim (hpNotCurrent (G.ray_mem_inessentialPaths hqCurrent))
    · obtain ⟨s, _hsInitial, hsRung, _hsTerminal, _hextends,
          _hsupport, _hedges, hterminal⟩ := hcontinue
      have hsRay : (L.stageWeb a).terminal? s = none := by
        have hnone : G.terminal? (Sum.inr r : G.DPath) = none := rfl
        rw [hterminal, L.terminal?_liftStagePath] at hnone
        exact hnone
      intro hunhindered
      apply hunhindered
      rcases s with s | s
      · simp at hsRay
      · refine ⟨(L.stageWeb a).essentialWarpPart (L.rung a), ?_⟩
        apply essentialWarpPart_isHindrance_of_inessentialPath
          (hL.waveRungs a)
        exact (L.stageWeb a).ray_mem_inessentialPaths hsRung
    · obtain ⟨_hnoRung, hqr⟩ := hfixed
      subst q
      simp at hqx
  · have hterminal := congrArg G.terminal? hyr
    simp at hterminal

/-- A genuinely successor-new *grounded finite* record also forces a
hindered quotient stage.  Groundedness rules out the newly inserted marker
singleton.  If the stage were unhindered, its maximal rung would be full;
maximality then keeps every essential rung terminal essential after adjoining
the optional marker, contradicting that the selected successor component is
inessential. -/
theorem freshInessentialRecord_finite_stageWeb_not_isUnhindered
    (L : G.KappaLadder kappa) (hL : L.IsSplitLegal)
    {a : Ladder.Stage kappa} {p : G.DPath} {x : V}
    (ha : a ∈ L.freshInessentialRecordStages)
    (hpChosen : L.chosen a = some p)
    (hpSource : p.initial ∈ G.source)
    (hpTerminal : G.terminal? p = some x) :
    ¬ (L.stageWeb a).IsUnhindered := by
  obtain ⟨q, hqChosen, hqNext, hqNotCurrent, _hqNotRecorded⟩ :=
    L.freshInessentialRecordStages_spec hL.validBookkeeping ha
  have hqp : q = p := Option.some.inj (hqChosen.symm.trans hpChosen)
  subst q
  intro hstage
  have hfull : (L.stageWeb a).initialSet (L.rung a) =
      (L.stageWeb a).source :=
    (L.stageWeb a).isUnhindered_iff.mp hstage _ (hL.waveRungs a)
  have hsourceRoof : G.source ⊆ G.roof (L.frontier a) := by
    rw [L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages, G.roof_essential]
    exact hL.roofsSourceAtStages (Ladder.Stage.toExtended a)
  rcases hL.successorComponentProvenance a p hqNext.1 with
      ⟨q, hqCurrent, hqpArrow⟩ | ⟨y, hyMarker, hpy⟩
  · rcases hqpArrow with hqRay | ⟨z, hqTerminal, hcontinue | hfixed⟩
    · obtain ⟨_hqTerminal, hqp⟩ := hqRay
      subst q
      rw [_hqTerminal] at hpTerminal
      cases hpTerminal
    · obtain ⟨r, _hrInitial, hrRung, _hqTerminal, _hextends,
          _hsupport, _hedges, hpLiftTerminal⟩ := hcontinue
      have hrTerminal : (L.stageWeb a).terminal? r = some x := by
        rw [← L.terminal?_liftStagePath]
        exact hpLiftTerminal.symm.trans hpTerminal
      have hrEssential :
          r ∈ (L.stageWeb a).essentialWarpPart (L.rung a) :=
        mem_essentialWarpPart_of_isUnhindered_of_fullWave
          (L.stageWeb a) hstage (hL.waveRungs a) hfull hrRung
      have hxStageTerminal :
          x ∈ (L.stageWeb a).terminalFrontier (L.rung a) :=
        ⟨r, hrRung, hrTerminal⟩
      have hxStageEssential :
          x ∈ (L.stageWeb a).essential
            ((L.stageWeb a).terminalFrontier (L.rung a)) := by
        obtain ⟨_, t, hrt, ht⟩ := hrEssential
        have htx : t = x := Option.some.inj (hrt.symm.trans hrTerminal)
        exact htx ▸ ht
      have hxQuotient : x ∈ G.quotientVertexSet
          (G.terminalFrontier (L.warpAt a)) := by
        rcases r with r | r
        · have hrSource : r.start ∈ (L.stageWeb a).source := by
            rw [← hfull]
            exact ⟨Sum.inl r, hrRung, rfl⟩
          have hrStartQuotient : r.start ∈ G.quotientVertexSet
              (G.terminalFrontier (L.warpAt a)) := by
            have hrEssentialSource : r.start ∈
                G.essential (G.source ∪
                  G.terminalFrontier (L.warpAt a)) := hrSource.1
            exact fun hrStrict ↦
              Set.disjoint_left.1
                (G.disjoint_essential_union_strictRoof_left
                  (G.terminalFrontier (L.warpAt a)) G.source)
                (by simpa [Set.union_comm] using hrEssentialSource) hrStrict
          apply G.essentialQuotientFinitePath_support_subset_quotientVertexSet
            (G.terminalFrontier (L.warpAt a)) r hrStartQuotient
          have hrFinish : r.finish = x := by simpa using hrTerminal
          exact hrFinish ▸ r.finish_mem_support
        · simp at hrTerminal
      have hxSuccessorEssential :
          x ∈ G.essential (G.terminalFrontier (L.successorWarp a)) := by
        cases hm : L.marker a with
        | none =>
            apply G.stageEssential_mem_successorEssential_of_terminal_noise
              (G.terminalFrontier (L.warpAt a))
              ((L.stageWeb a).terminalFrontier (L.rung a)) ∅
            · simpa using hL.rung_terminalFrontier_subset_successorFrontier a
            · intro v hv
              rcases hL.successorTerminal_mem_rung_or_marker_or_strictOld
                  hfull hv with hvRung | ⟨y, hy, _⟩ | hvOld
              · exact Or.inl (Or.inl hvRung)
              · rw [hm] at hy
                cases hy
              · exact Or.inr hvOld
            · exact hxQuotient
            · change x ∈ (L.stageWeb a).essential
                ((L.stageWeb a).terminalFrontier (L.rung a) ∪ ∅)
              simpa using hxStageEssential
        | some y =>
            have hyCandidate : y ∈ L.markerCandidates a :=
              (hL.freshMarkers.2 a y hm).1
            have hySuccessor : y ∈
                G.terminalFrontier (L.successorWarp a) := by
              refine ⟨G.trivialPath y, (hL.freshMarkers.2 a y hm).2, ?_⟩
              simp
            have hxStageWithMarker :
                x ∈ (L.stageWeb a).essential
                  ((L.stageWeb a).terminalFrontier (L.rung a) ∪ {y}) := by
              exact essential_terminal_insert_of_roofMaximal
                (L.stageWeb a) (hL.waveRungs a) hfull
                (hL.roofMaximalRungs a) hrRung hrTerminal hrEssential
                hyCandidate.1.1 (fun hyRung ↦ hyCandidate.2 (Or.inr hyRung))
            apply G.stageEssential_mem_successorEssential_of_terminal_noise
              (G.terminalFrontier (L.warpAt a))
              ((L.stageWeb a).terminalFrontier (L.rung a)) {y}
            · exact Set.union_subset
                (hL.rung_terminalFrontier_subset_successorFrontier a)
                (fun v hv ↦ by
                  have hvy : v = y := by simpa using hv
                  simpa [hvy] using hySuccessor)
            · intro v hv
              rcases hL.successorTerminal_mem_rung_or_marker_or_strictOld
                  hfull hv with hvRung | ⟨z, hz, hvz⟩ | hvOld
              · exact Or.inl (Or.inl hvRung)
              · have hzy : z = y := Option.some.inj (hz.symm.trans hm)
                exact Or.inl (Or.inr (by simpa [hzy] using hvz))
              · exact Or.inr hvOld
            · exact hxQuotient
            · exact hxStageWithMarker
      exact hqNext.2 ⟨hqNext.1, x, hpTerminal, hxSuccessorEssential⟩
    · obtain ⟨hnoRung, hpq⟩ := hfixed
      subst q
      have hzx : z = x :=
        Option.some.inj (hqTerminal.symm.trans hpTerminal)
      have hpNotEssential :
          p ∉ G.essentialWarpPart (L.warpAt a) := by
        intro hpEssential
        have hxEssential :
            x ∈ G.essential (G.terminalFrontier (L.warpAt a)) := by
          obtain ⟨_, t, hpt, ht⟩ := hpEssential
          have htx : t = x := Option.some.inj (hpt.symm.trans hpTerminal)
          exact htx ▸ ht
        have hxSource : x ∈ (L.stageWeb a).source := by
          change x ∈ L.frontier a
          rw [L.frontier_eq_essential_terminalFrontier
            hL.roofsSourceAtStages]
          exact hxEssential
        have hxInitial : x ∈
            (L.stageWeb a).initialSet (L.rung a) := by
          rw [hfull]
          exact hxSource
        obtain ⟨r, hr, hri⟩ := hxInitial
        exact hnoRung ⟨r, hr, hri.trans hzx.symm⟩
      exact hqNotCurrent ⟨hqCurrent, hpNotEssential⟩
  · subst p
    have hySource : y ∈ G.source := by simpa using hpSource
    exact hL.marker_not_mem_roof_frontier hyMarker
      (hsourceRoof hySource)

/-- In the actual canonical ladder, a genuinely successor-new selected ray
forces the named rung itself to be a hindrance. -/
theorem canonicalLadder_freshInessentialRecord_ray_mem_phiHindrance
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a : Ladder.Stage kappa} {r : DirectedPath.Ray G.graph}
    (ha : a ∈ (canonicalLadder G kappa preferred).freshInessentialRecordStages)
    (hrChosen : (canonicalLadder G kappa preferred).chosen a =
      some (Sum.inr r : G.DPath)) :
    a ∈ (canonicalLadder G kappa preferred).phiHindrance := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  have hstage : ¬ (L.stageWeb a).IsUnhindered :=
    L.freshInessentialRecord_ray_stageWeb_not_isUnhindered
      hlegal ha hrChosen
  change (L.stageWeb a).IsHindrance (L.rung a)
  change ((G.canonicalLadderCore kappa preferred).stageWeb a).IsHindrance
    ((G.canonicalLadderCore kappa preferred).rung a)
  exact canonicalLadderCore_rung_isHindrance kappa preferred a hstage

/-- Every grounded fresh obstruction in the canonical ladder is a genuine
hindrance rung.  This is the successor-corrected diagonal classification:
the finite case uses maximal-rung terminal stability, and the ray case is
the direct rung-ray obstruction. -/
theorem canonicalLadder_freshInessentialGroundStages_subset_phiHindrance
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (canonicalLadder G kappa preferred).freshInessentialGroundStages ⊆
      (canonicalLadder G kappa preferred).phiHindrance := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  rintro a ⟨haGround, haFresh⟩
  obtain ⟨p, hpChosen, hpSource⟩ := haGround
  have hstage : ¬ (L.stageWeb a).IsUnhindered := by
    rcases p with p | r
    · exact L.freshInessentialRecord_finite_stageWeb_not_isUnhindered
        hlegal haFresh hpChosen hpSource rfl
    · exact L.freshInessentialRecord_ray_stageWeb_not_isUnhindered
        hlegal haFresh hpChosen
  change (L.stageWeb a).IsHindrance (L.rung a)
  change ((G.canonicalLadderCore kappa preferred).stageWeb a).IsHindrance
    ((G.canonicalLadderCore kappa preferred).rung a)
  exact canonicalLadderCore_rung_isHindrance kappa preferred a hstage

/-- Stationarily many grounded fresh records therefore give stationarily
many hindered rungs.  This is the exact local conclusion of the diagonal
argument; grounding those quotient hindrances in the ambient web remains
the global Section 8 step. -/
theorem canonicalLadder_phiHindrance_isStationary_of_freshGround
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hfresh : Stationary.IsStationaryBelow kappa
      (canonicalLadder G kappa preferred).freshInessentialGroundStages) :
    Stationary.IsStationaryBelow kappa
      (canonicalLadder G kappa preferred).phiHindrance :=
  hfresh.mono
    (canonicalLadder_freshInessentialGroundStages_subset_phiHindrance
      preferred hkappa huncountable hNoEnter)

/-- Pathwise maximal-rung defect supplied by a grounded fresh stage: the
canonical rung omits an actual source of its essential quotient stage.  This
is the precise local augmentation endpoint available to the equal-route
construction. -/
theorem canonicalLadder_freshInessentialGroundStage_exists_rungDefect
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a : Ladder.Stage kappa}
    (ha : a ∈
      (canonicalLadder G kappa preferred).freshInessentialGroundStages) :
    ∃ z : V,
      z ∈ ((canonicalLadder G kappa preferred).stageWeb a).source ∧
      z ∉ ((canonicalLadder G kappa preferred).stageWeb a).initialSet
        ((canonicalLadder G kappa preferred).rung a) := by
  let L := canonicalLadder G kappa preferred
  have hrung : (L.stageWeb a).IsHindrance (L.rung a) :=
    canonicalLadder_freshInessentialGroundStages_subset_phiHindrance
      preferred hkappa huncountable hNoEnter ha
  have hnot : ¬ (L.stageWeb a).source ⊆
      (L.stageWeb a).initialSet (L.rung a) := by
    intro hsub
    exact hrung.2 (Set.Subset.antisymm hrung.1.2.1 hsub)
  exact Set.not_subset.mp hnot

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.freshInessentialRecord_ray_stageWeb_not_isUnhindered
#print axioms Erdos599.DWeb.KappaLadder.canonicalLadder_freshInessentialRecord_ray_mem_phiHindrance
#print axioms Erdos599.DWeb.KappaLadder.freshInessentialRecord_finite_stageWeb_not_isUnhindered
#print axioms Erdos599.DWeb.KappaLadder.canonicalLadder_freshInessentialGroundStages_subset_phiHindrance
#print axioms Erdos599.DWeb.KappaLadder.canonicalLadder_phiHindrance_isStationary_of_freshGround
#print axioms Erdos599.DWeb.KappaLadder.canonicalLadder_freshInessentialGroundStage_exists_rungDefect
