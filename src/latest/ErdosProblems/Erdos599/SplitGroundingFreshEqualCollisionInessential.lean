/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualPriorCollision
import ErdosProblems.Erdos599.SplitGroundingFreshGroundedMarkerMaximal

/-!
# Fresh equal collisions have inessential owners

The successor-correct form of Assertion 8.19 retains same-stage contacts.
For the canonical ladder, a genuinely fresh grounded source cannot contact
an *essential* hanging component owned at that same stage.  The source
record starts in the strict roof of the arrow-only frontier; target-pure
decoding keeps the contact in its closed roof.  Roof membership propagates
backwards along the limiting component to its marker, contradicting the
pre-marker exclusion.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Ladder Stationary

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- Roof membership in an arrow-only frontier propagates backwards along a
limiting component. -/
private theorem canonicalLadder_limitComponent_initial_mem_roof_arrowPartFrontier
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : Ladder.Stage kappa) {p : G.DPath}
    (hp : p ∈ (canonicalLadder G kappa preferred).limitWarp)
    {v : V} (hvp : v ∈ p.support)
    (hvRoof : v ∈ G.roof (G.terminalFrontier
      ((canonicalLadder G kappa preferred).arrowPart a))) :
    p.initial ∈ G.roof (G.terminalFrontier
      ((canonicalLadder G kappa preferred).arrowPart a)) := by
  let L := canonicalLadder G kappa preferred
  have hback : ∀ {x y : V}, (x, y) ∈ p.edgeSet →
      y ∈ G.roof (G.terminalFrontier (L.arrowPart a)) →
      x ∈ G.roof (G.terminalFrontier (L.arrowPart a)) := by
    intro x y hxy hy
    exact (canonicalLadder_limitFamilyEdge_tail_mem_strictRoof_arrowPartFrontier
      preferred hkappa huncountable hNoEnter a ⟨p, hp, hxy⟩ hy).1
  rcases p with path | ray
  · apply Walk.start_mem_of_meets_of_backwardClosed
      (w := path.walk)
    · intro x y hxy hy
      exact hback hxy hy
    · exact ⟨v, hvp, hvRoof⟩
  · obtain ⟨n, hn⟩ := hvp
    subst v
    change ray 0 ∈ G.roof (G.terminalFrontier (L.arrowPart a))
    induction n with
    | zero => exact hvRoof
    | succ n ih =>
        apply ih
        apply hback
        · exact ⟨n, rfl⟩
        · exact hvRoof

/-- In the canonical ladder, the hanging component of a fresh equal-stage
grounded collision belongs to the inessential part of the limiting warp. -/
theorem canonicalLadder_freshEqualCollision_component_mem_inessentialPaths
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hL : (canonicalLadder G kappa preferred).IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa
      (canonicalLadder G kappa preferred).phiGround)
    (S : Popular.PopularSeparator
      ((canonicalLadder G kappa preferred)
        |>.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      ((canonicalLadder G kappa preferred)
        |>.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    {a : Below kappa}
    (E : (canonicalLadder G kappa preferred)
      |>.SplitGroundedAssertion819EqualMatch hL hground S r a) :
    E.owner.component ∈ G.inessentialPaths
      (canonicalLadder G kappa preferred).limitWarp := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  let I := L.splitGroundedPopularAuxiliaryInput hL.legal
  let U := L.splitGroundedPopularAuxiliaryIndexed hL hground
  let d := E.owner
  let R := PopularSwitching.restrictPaths
    (PopularGroundingBridge.requestFan S r)
    {q | GroundingConcreteControls.hangingLadderCollision I S.cut r q}
  let afresh : L.freshInessentialGroundStages :=
    ⟨a, E.source_mem_freshInessentialGroundStages⟩
  refine ⟨d.component_mem, ?_⟩
  intro hessential
  have hs : d.path.start ∈ I.lambda.source := R.starts_in_source d.path_mem
  have hpure : I.IsTargetPure d.path :=
    I.requestFan_path_isTargetPure S r d.path_mem.1
  have hmeet : d.path.walk.Meets ({d.traceContact} : Set I.LV) :=
    ⟨d.traceContact, d.traceContact_mem_path, Set.mem_singleton _⟩
  let q : FinitePath I.lambda.graph :=
    d.path.firstHit ({d.traceContact} : Set I.LV) hmeet
  have hqStart : q.start = d.path.start := rfl
  have hqFinish : q.finish = d.traceContact :=
    Set.mem_singleton_iff.1
      (d.path.firstHit_finish_mem ({d.traceContact} : Set I.LV) hmeet)
  have hqSource : q.start ∈ I.lambda.source := hqStart ▸ hs
  have hqPure : I.IsTargetPure q :=
    PopularAuxiliary.Input.IsTargetPure.firstHit I hpure
      ({d.traceContact} : Set I.LV) hmeet
  have hcontactRoof : d.contact ∈ G.roof
      (G.terminalFrontier (L.arrowPart a)) := by
    rcases I.start_of_mem_lambda_source d.path hs with
        ⟨x, hxSource, hpx⟩ | ⟨i, hpi⟩
    · let xs : L.groundedFiniteTerminalSet := ⟨x, hxSource⟩
      let xs' : L.finiteTerminalSet :=
        ⟨x, L.groundedFiniteTerminalSet_subset_finiteTerminalSet xs.2⟩
      have hsourceIndex : a = L.finiteTerminalIndex xs := by
        have hsEq :
            (⟨d.path.start, hs⟩ : I.lambda.source) =
              ⟨.old x, (I.mem_lambda_source_old x).2 hxSource⟩ :=
          Subtype.ext hpx
        have hindex : U.f ⟨d.path.start, hs⟩ =
            L.finiteTerminalIndex xs := by
          rw [hsEq]
          rfl
        exact d.index_eq.symm.trans hindex
      obtain ⟨_hphi, sourcePath, hchosen, hterminal⟩ :=
        L.finiteTerminalStage_spec xs'
      have hchosenA : L.chosen a = some sourcePath := by
        rw [hsourceIndex]
        exact hchosen
      have hrecordPath : sourcePath = L.freshGroundRecordPath hlegal afresh :=
        Option.some.inj (hchosenA.symm.trans
          (L.chosen_freshGroundRecordPath hlegal afresh))
      cases hrecord : L.freshGroundRecordPath hlegal afresh with
      | inl f =>
          have hsourcePath : sourcePath = (Sum.inl f : G.DPath) :=
            hrecordPath.trans hrecord
          have hfinish : f.finish = x := by
            rw [hsourcePath] at hterminal
            exact Option.some.inj hterminal
          have hpArrow : L.freshGroundRecordPath hlegal afresh ∈
              L.arrowPart a :=
            L.freshGroundRecordPath_mem_arrowPart hlegal afresh
          have hpNotEssential : L.freshGroundRecordPath hlegal afresh ∉
              G.essentialWarpPart (L.arrowPart a) := by
            intro hpEssential
            exact canonicalLadder_no_freshFinite_of_essential_arrowPart
              preferred hkappa huncountable hNoEnter afresh f hrecord
                hpEssential (by
                  have hm := L.marker_splitHangingComponentStage hL.legal
                    d.component d.component_mem d.component_hanging
                  rw [E.every_owner_stage_eq d] at hm
                  exact hm)
          have hxStrict : x ∈ G.strictRoof
              (G.terminalFrontier (L.arrowPart a)) := by
            apply G.terminal_mem_strictRoof_of_mem_inessentialPaths
              ⟨hpArrow, hpNotEssential⟩
            rw [hrecord]
            exact hfinish ▸ rfl
          have hrun : PopularAuxiliary.Input.RunsFromTo x d.contact
              (I.decodeWalkSteps q.walk) :=
            I.decodeWalkSteps_runs_from_entry q.walk
              (by rw [hqStart, hpx]; rfl)
              (by rw [hqFinish]; exact d.traceContact_exit)
          exact canonicalLadder_targetPure_run_terminal_mem_roof_arrowPartFrontier_of_ladder
            preferred hkappa huncountable hNoEnter I (by rfl) a q
              hqSource hqPure hrun hxStrict
      | inr ray =>
          have hsourcePath : sourcePath = (Sum.inr ray : G.DPath) :=
            hrecordPath.trans hrecord
          rw [hsourcePath] at hterminal
          cases hterminal
    · have hsourceIndex : a = L.groundedInfiniteStage i := by
        have hsEq :
            (⟨d.path.start, hs⟩ : I.lambda.source) =
              ⟨.proxy i, I.mem_lambda_source_proxy i⟩ :=
          Subtype.ext hpi
        have hindex : U.f ⟨d.path.start, hs⟩ =
            L.groundedInfiniteStage i := by
          rw [hsEq]
          rfl
        exact d.index_eq.symm.trans hindex
      have hchosenI : L.chosen a = some i.1 := by
        rw [hsourceIndex]
        exact (L.groundedInfiniteStage_spec i).2
      have hiRecord : i.1 = L.freshGroundRecordPath hlegal afresh :=
        Option.some.inj (hchosenI.symm.trans
          (L.chosen_freshGroundRecordPath hlegal afresh))
      obtain ⟨ray, hir⟩ := I.proxy_isRay i
      have hrecord : L.freshGroundRecordPath hlegal afresh =
          (Sum.inr ray : G.DPath) := by
        have hiRay : (i.1 : G.DPath) = .inr ray := by
          simpa [I, splitGroundedPopularAuxiliaryInput,
            splitGroundedInfinitePath] using hir
        exact hiRecord.symm.trans hiRay
      obtain ⟨z, hzProxy, hrun⟩ :=
        I.decodeWalkSteps_runs_from_eq_proxy q.walk
          (hqStart.trans hpi)
          (by rw [hqFinish]; exact d.traceContact_exit)
      have hzRay : z ∈ ray.support := by
        have hproxy : I.proxyPath i = (Sum.inr ray : G.DPath) := by
          change L.splitGroundedInfinitePath hL.legal i =
            (Sum.inr ray : G.DPath)
          simpa only [splitGroundedInfinitePath] using hiRecord.trans hrecord
        rw [hproxy] at hzProxy
        exact hzProxy
      have hzStrict : z ∈ G.strictRoof
          (G.terminalFrontier (L.arrowPart a)) :=
        canonicalLadder_freshRay_support_subset_strictRoof_arrowPartFrontier
          preferred hkappa huncountable hNoEnter afresh ray hrecord hzRay
      exact canonicalLadder_targetPure_run_terminal_mem_roof_arrowPartFrontier_of_ladder
        preferred hkappa huncountable hNoEnter I (by rfl) a q
          hqSource hqPure hrun hzStrict
  have hinitialRoof : d.component.initial ∈ G.roof
      (G.terminalFrontier (L.arrowPart a)) := by
    exact canonicalLadder_limitComponent_initial_mem_roof_arrowPartFrontier
      preferred hkappa huncountable hNoEnter a d.component_mem
        d.contact_mem_component hcontactRoof
  have hmarker : L.marker a = some d.component.initial := by
    have hm := L.marker_splitHangingComponentStage hL.legal
      d.component d.component_mem d.component_hanging
    rw [E.every_owner_stage_eq d] at hm
    exact hm
  have htarget : d.component.initial ∈
      (L.splitPopularAuxiliaryInput hlegal).targetMarkers :=
    ⟨⟨a, hmarker⟩,
      ⟨d.component, hessential, d.component.initial_mem_support⟩⟩
  exact canonicalLadder_targetMarker_not_mem_roof_arrowPartFrontier
    preferred hkappa huncountable hNoEnter hmarker htarget hinitialRoof

end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.canonicalLadder_freshEqualCollision_component_mem_inessentialPaths
