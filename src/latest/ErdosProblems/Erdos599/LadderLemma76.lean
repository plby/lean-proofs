/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.EssentialWaveLift
import ErdosProblems.Erdos599.Ladder
import ErdosProblems.Erdos599.Normalization

/-!
# The hindrance-rung obstruction lemma

This file proves source Lemma 7.6 of Aharoni--Berger.  If the wave chosen
on a ladder rung is a hindrance, an omitted source of the essential
quotient stage determines an old essential component.  The successor
arrow leaves that component fixed.  On the other hand, the terminal
frontier of the rung roofs the omitted source, and every rung terminal is
a different successor terminal.  Consequently the fixed old component is
inessential in the successor warp.  It was not recorded earlier (recorded
components persist as inessential components), so it is available for the
stage bookkeeping.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open DirectedPath
open Ladder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- The construction laws actually used by source Lemma 7.6.  Hanging-path
provenance plays no role in this lemma, so keeping this interface separate
lets both legacy and successor-normalized split legality use the result. -/
structure Lemma76Data (L : G.KappaLadder kappa) : Prop where
  waveRungs : L.HasWaveRungs
  exactSuccessorArrows : L.HasExactSuccessorArrows
  roofsSourceAtStages : L.RoofsSourceAtStages
  recordedPathsPersist : L.RecordedPathsPersist

/-- Legacy legality supplies the geometric Lemma 7.6 interface. -/
theorem IsLegal.lemma76Data {L : G.KappaLadder kappa}
    (hL : L.IsLegal) : L.Lemma76Data where
  waveRungs := hL.waveRungs
  exactSuccessorArrows := hL.exactSuccessorArrows
  roofsSourceAtStages := hL.roofsSourceAtStages
  recordedPathsPersist := hL.recordedPathsPersist

/-- Each old component has its unique exact successor-arrow image using
only the successor geometry needed by Lemma 7.6. -/
theorem Lemma76Data.existsUniqueSuccessorArrow
    {L : G.KappaLadder kappa} (hL : L.Lemma76Data)
    (a : Stage kappa) (p : G.DPath) (hp : p ∈ L.warpAt a) :
    ∃! q : G.DPath,
      (q ∈ L.successorWarp a ∧ q ∉ L.markerPathSet a) ∧
        L.IsRungArrowPair a p q := by
  simpa only [arrowPart, Set.mem_sdiff] using
    (hL.exactSuccessorArrows a).1.1 p hp

/-- Normalization of the ambient web passes the no-incoming-edge property
to every essential quotient stage of a ladder. -/
private theorem stageWeb_noEdgeEnters_of_normalized
    (hG : G.IsNormalized) (L : G.KappaLadder kappa)
    (a : Stage kappa) :
    (L.stageWeb a).NoEdgeEnters (L.stageWeb a).source := by
  intro x y hxy hy
  have hxyQuotient :
      (G.quotient (G.terminalFrontier (L.warpAt a))).graph.Adj x y :=
    hxy.1
  have hySourceOrCommitment :
      y ∈ G.source ∪ G.terminalFrontier (L.warpAt a) :=
    hy.1.1
  rcases hySourceOrCommitment with hySource | hyCommitment
  · exact (hG hxyQuotient.1).1 hySource
  · exact hxyQuotient.2.2.2 hyCommitment

/-- A source vertex occurring on a member of a wave in a web with no
incoming source edges is that member's initial vertex. -/
private theorem wave_source_mem_support_eq_initial
    (Q : DWeb V) (hNoEnter : Q.NoEdgeEnters Q.source)
    {W : Set Q.DPath} (hW : Q.IsWave W) {p : Q.DPath}
    (hp : p ∈ W) {x : V} (hxp : x ∈ p.support)
    (hx : x ∈ Q.source) : x = p.initial := by
  rcases p with p | r
  · have hpStart : p.start ∈ Q.source :=
      hW.2.1 ⟨Sum.inl p, hp, rfl⟩
    exact Q.targetPath_meets_noEdgeEnters_only_at_start
      hNoEnter p hpStart hxp hx
  · rcases hxp with ⟨n, rfl⟩
    cases n with
    | zero => rfl
    | succ n =>
        exact (hNoEnter (r.adj_succ n) hx).elim

/-- The terminal of a lifted rung path is unchanged. -/
private theorem terminal_liftStagePath
    (L : G.KappaLadder kappa) (a : Stage kappa)
    (r : (L.stageWeb a).DPath) :
    G.terminal? (L.liftStagePath a r) = (L.stageWeb a).terminal? r := by
  rcases r with r | r <;> rfl

/-- A wave in the essential quotient stage roofs the old essential
commitment frontier in the original web.  The usual quotient lemma assumes
that the old source is disjoint from the commitment set.  Ladder stages
need the more general form below: the accumulated-frontier invariant
`hroof` identifies the quotient source with the essential commitment
frontier even when the two sets overlap. -/
private theorem essential_subset_original_roof_of_quotientEssentialPart_wave
    (Q : DWeb V) {S : Set V}
    (hroof : Q.source ⊆ Q.roof S)
    {U : Set ((Q.quotient S).essentialPart.DPath)}
    (hU : (Q.quotient S).essentialPart.IsWave U) :
    Q.essential S ⊆
      Q.roof ((Q.quotient S).essentialPart.terminalFrontier U) := by
  let W : Set (Q.quotient S).DPath :=
    (Q.quotient S).liftEssentialPartFamily U
  have hW : (Q.quotient S).IsWave W :=
    (Q.quotient S).isWave_liftEssentialPartFamily hU
  intro x hx p hp
  have hmeetS : Q.Meets p S :=
    ⟨p.start, p.start_mem_support, hp.1 ▸ hx.1⟩
  let hm : p.walk.Meets S :=
    ⟨hmeetS.choose, hmeetS.choose_spec.1, hmeetS.choose_spec.2⟩
  let K := p.walk.lastHit S hm
  have hKEssential : K.startpoint ∈ Q.essential S :=
    Q.lastHit_mem_essential S p hp hmeetS
  have hKSource : K.startpoint ∈ (Q.quotient S).source := by
    have hSourceEq :
        (Q.quotient S).source = Q.essential S := by
      simpa only [Q.terminalFrontier_trivialPaths] using
        (Q.quotient_source_eq_essential_terminalFrontier_of_roofsSource
          (W := Q.trivialPath '' S) (by
            simpa only [Q.terminalFrontier_trivialPaths] using hroof))
    rw [hSourceEq]
    exact hKEssential
  obtain ⟨q, hqStart, hqFinish, hqSupport⟩ :=
    Q.exists_quotientPath_from_lastHit S p hp hmeetS
  have hqTarget : (Q.quotient S).IsTargetPathFrom K.startpoint q :=
    ⟨hqStart, hqFinish ▸ hp.2⟩
  obtain ⟨y, hyq, hyW⟩ := hW.2.2 hKSource q hqTarget
  refine ⟨y, K.support_subset ?_, ?_⟩
  · rw [hqSupport] at hyq
    exact hyq
  · rw [(Q.quotient S).terminalFrontier_liftEssentialPartFamily] at hyW
    exact hyW

/-- Every terminal of the rung occurs as a terminal of the successor warp.
This is the pathwise content of the arrow operation used in Lemma 7.6. -/
private theorem rung_terminalFrontier_subset_successor
    {L : G.KappaLadder kappa} (hL : L.Lemma76Data) (a : Stage kappa) :
    (L.stageWeb a).terminalFrontier (L.rung a) ⊆
      G.terminalFrontier (L.successorWarp a) := by
  intro t ht
  obtain ⟨r, hr, hrt⟩ := ht
  have hrInitial : r.initial ∈ (L.stageWeb a).source :=
    (hL.waveRungs a).2.1 ⟨r, hr, rfl⟩
  have hOldRoof :
      G.source ⊆ G.roof (G.terminalFrontier (L.warpAt a)) :=
    hL.roofsSourceAtStages (Stage.toExtended a)
  obtain ⟨p, hpEssential, hpTerminal⟩ :=
    G.exists_essentialWarpPart_terminal_of_mem_quotientEssentialPart_source
      hOldRoof hrInitial
  obtain ⟨q, hq, _hqunique⟩ :=
    hL.existsUniqueSuccessorArrow a p hpEssential.1
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
    rw [hqTerminal, hrr', terminal_liftStagePath, hrt]
  · have hz : z = r.initial := Option.some.inj (hpz.symm.trans hpTerminal)
    exfalso
    apply hfixed.1
    exact ⟨r, hr, hz.symm⟩

/-- Witness-preserving form of source Lemma 7.6.  A hindered rung produces
an unrecorded successor-inessential component which was already present in
the accumulated warp at the current stage.  Retaining the last clause is
useful for bookkeeping schemes which defer the newly inserted marker
component. -/
theorem exists_warpAt_available_of_mem_phiHindrance
    {L : G.KappaLadder kappa}
    (hG : G.IsNormalized) (hL : L.Lemma76Data)
    {a : Stage kappa} (ha : a ∈ L.phiHindrance) :
    ∃ p : G.DPath,
      p ∈ L.warpAt a ∧
        p ∈ G.inessentialPaths (L.successorWarp a) ∧
          p ∉ L.bookkeeping.recordedBefore a := by
  have hRung : (L.stageWeb a).IsHindrance (L.rung a) := ha
  have hRungWave : (L.stageWeb a).IsWave (L.rung a) := hRung.1
  have hNotSubset :
      ¬ (L.stageWeb a).source ⊆ (L.stageWeb a).initialSet (L.rung a) := by
    intro hsubset
    exact hRung.2 (Set.Subset.antisymm hRungWave.2.1 hsubset)
  obtain ⟨x, hxSource, hxNotInitial⟩ := Set.not_subset.mp hNotSubset
  have hOldRoof :
      G.source ⊆ G.roof (G.terminalFrontier (L.warpAt a)) :=
    hL.roofsSourceAtStages (Stage.toExtended a)
  obtain ⟨p, hpEssential, hpTerminal⟩ :=
    G.exists_essentialWarpPart_terminal_of_mem_quotientEssentialPart_source
      hOldRoof hxSource
  have hpSuccessor : p ∈ L.successorWarp a := by
    obtain ⟨q, hq, _hqunique⟩ :=
      hL.existsUniqueSuccessorArrow a p hpEssential.1
    have hqp : q = p := by
      rcases hq.2 with hRay | ⟨z, hpz, hcontinue | hfixed⟩
      · rw [hpTerminal] at hRay
        simp at hRay
      · have hz : z = x := Option.some.inj (hpz.symm.trans hpTerminal)
        obtain ⟨r, hrInitial, hrRung, _⟩ := hcontinue
        exfalso
        apply hxNotInitial
        exact ⟨r, hrRung, hrInitial.trans hz⟩
      · exact hfixed.2
    exact hqp ▸ hq.1.1
  have hxNotRungTerminal :
      x ∉ (L.stageWeb a).terminalFrontier (L.rung a) := by
    rintro ⟨r, hr, hrx⟩
    have hxSupport : x ∈ r.support :=
      (L.stageWeb a).terminal_mem_support hrx
    have hxInitial : x = r.initial :=
      wave_source_mem_support_eq_initial (L.stageWeb a)
        (stageWeb_noEdgeEnters_of_normalized hG L a)
        hRungWave hr hxSupport hxSource
    apply hxNotInitial
    exact ⟨r, hr, hxInitial.symm⟩
  have hxOldEssential :
      x ∈ G.essential (G.terminalFrontier (L.warpAt a)) := by
    rw [← G.terminalFrontier_essentialWarpPart]
    exact ⟨p, hpEssential, hpTerminal⟩
  have hxRoofRungTerminal :
      x ∈ G.roof ((L.stageWeb a).terminalFrontier (L.rung a)) := by
    exact essential_subset_original_roof_of_quotientEssentialPart_wave
      G hOldRoof hRungWave hxOldEssential
  have hRungTerminalSubset :
      (L.stageWeb a).terminalFrontier (L.rung a) ⊆
        G.terminalFrontier (L.successorWarp a) \ {x} := by
    intro t ht
    exact ⟨rung_terminalFrontier_subset_successor hL a ht,
      fun htx ↦ hxNotRungTerminal (htx ▸ ht)⟩
  have hxRoofSuccessorWithoutX :
      x ∈ G.roof (G.terminalFrontier (L.successorWarp a) \ {x}) :=
    G.roof_mono hRungTerminalSubset hxRoofRungTerminal
  have hxNotEssential :
      x ∉ G.essential (G.terminalFrontier (L.successorWarp a)) := by
    intro hxEssential
    exact hxEssential.2 hxRoofSuccessorWithoutX
  have hpInessential : p ∈ G.inessentialPaths (L.successorWarp a) := by
    refine ⟨hpSuccessor, ?_⟩
    rintro ⟨_, t, hpt, htEssential⟩
    have htx : t = x := Option.some.inj (hpt.symm.trans hpTerminal)
    exact hxNotEssential (htx ▸ htEssential)
  have hpNotRecorded : p ∉ L.bookkeeping.recordedBefore a := by
    rintro ⟨b, hba, hchosen⟩
    have hpOldInessential : p ∈ G.inessentialPaths (L.warpAt a) := by
      apply L.recorded_mem_inessential hL.recordedPathsPersist hchosen
        (b := Stage.toExtended a)
      change b.1 + 1 ≤ a.1
      exact (Order.add_one_le_iff).2 hba
    exact hpOldInessential.2 hpEssential
  exact ⟨p, hpEssential.1, hpInessential, hpNotRecorded⟩

/-- Source Lemma 7.6 from its exact geometric construction interface. -/
theorem phiHindrance_subset_phi_of_lemma76Data
    {L : G.KappaLadder kappa}
    (hG : G.IsNormalized) (hL : L.Lemma76Data) :
    L.phiHindrance ⊆ L.phi := by
  intro a ha
  obtain ⟨p, _hpCurrent, hpInessential, hpNotRecorded⟩ :=
    L.exists_warpAt_available_of_mem_phiHindrance hG hL ha
  exact ⟨p, hpInessential, hpNotRecorded⟩

/-- Source Lemma 7.6: a hindrance rung creates an unrecorded inessential
successor component, hence its stage belongs to the obstruction set
`Phi(L)`. -/
theorem phiHindrance_subset_phi
    {L : G.KappaLadder kappa}
    (hG : G.IsNormalized) (hL : L.IsLegal) :
    L.phiHindrance ⊆ L.phi :=
  L.phiHindrance_subset_phi_of_lemma76Data hG hL.lemma76Data

end KappaLadder
end DWeb
end Erdos599
