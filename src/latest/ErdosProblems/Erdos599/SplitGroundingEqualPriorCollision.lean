/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedAssertion819

/-!
# Prior-record elimination for equal-stage grounded collisions

The successor chronology used by the split grounding auxiliary is only weak:
a route whose source has index `a` may contact a hanging limiting component
whose marker was born at `a`.  For a source record which was already
inessential in the current warp at stage `a`, however, the source lies in the
strict roof of the *current* frontier.  Target-pure transport and backward
closure along the contacted component then put its initial marker in the roof
of that same frontier.  Marker freshness rules out equality of the owner and
source stages.

Thus the equal-stage remainder of grounded Assertion 8.19 is supported only
on genuinely successor-new records.  This is the local analogue of
`targetPure_equalSubwarp_initialIndex_not_prior`; it does not assert that the
fresh diagonal is empty.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Ladder Stationary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Under split legality, a finite record already inessential in the current
warp has its terminal in the strict roof of the current frontier. -/
theorem splitPriorInessential_finite_terminal_mem_strictRoof_frontier
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {a : Stage kappa} (ha : a ∈ L.priorInessentialRecordStages)
    {p : Gamma.DPath} {x : V} (hp : L.chosen a = some p)
    (hterminal : Gamma.terminal? p = some x) :
    x ∈ Gamma.strictRoof (L.frontier a) := by
  obtain ⟨q, hq, hqCurrent⟩ := ha
  have hqp : q = p := Option.some.inj (hq.symm.trans hp)
  subst q
  have hx : x ∈ Gamma.strictRoof
      (Gamma.terminalFrontier (L.warpAt a)) :=
    Gamma.terminal_mem_strictRoof_of_mem_inessentialPaths
      hqCurrent hterminal
  rw [L.frontier_eq_essential_terminalFrontier
    hlegal.roofsSourceAtStages a, Gamma.strictRoof_essential]
  exact hx

/-- Under split legality, every vertex of a grounded ray already
inessential in the current warp lies in the strict roof of the current
frontier. -/
theorem splitPriorInessential_grounded_ray_support_subset_strictRoof_frontier
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {a : Stage kappa} (ha : a ∈ L.priorInessentialRecordStages)
    {r : Ray Gamma.graph}
    (hchosen : L.chosen a = some (.inr r : Gamma.DPath))
    (hground : r.initial ∈ Gamma.source) :
    r.support ⊆ Gamma.strictRoof (L.frontier a) := by
  obtain ⟨p, hp, hpCurrent⟩ := ha
  have hpr : p = (.inr r : Gamma.DPath) :=
    Option.some.inj (hp.symm.trans hchosen)
  subst p
  let T := Gamma.terminalFrontier (L.warpAt a)
  have hsupportDisjoint : Disjoint r.support T := by
    apply Set.disjoint_left.2
    intro z hzr hzT
    obtain ⟨q, hqWarp, hqTerminal⟩ := hzT
    have hrq : (.inr r : Gamma.DPath) ≠ q := by
      intro hrq
      have hterm := congrArg Gamma.terminal? hrq
      rw [Gamma.terminal?_ray, hqTerminal] at hterm
      cases hterm
    exact Set.disjoint_left.1
      (hlegal.warpStages (Stage.toExtended a)
        hpCurrent.1 hqWarp hrq)
      hzr (Gamma.terminal_mem_support hqTerminal)
  have hsupportRoofT : r.support ⊆ Gamma.roof T := by
    apply Gamma.pathSupportRoof (.inr r : Gamma.DPath) T
    · exact hlegal.roofsSourceAtStages (Stage.toExtended a) hground
    · intro t ht
      rw [Gamma.terminal?_ray] at ht
      cases ht
    · intro z hz
      exact False.elim
        (Set.disjoint_left.1 hsupportDisjoint hz.1 hz.2)
  intro z hzr
  have hzRoof : z ∈ Gamma.roof (L.frontier a) := by
    rw [L.frontier_eq_essential_terminalFrontier
      hlegal.roofsSourceAtStages a, Gamma.roof_essential]
    exact hsupportRoofT hzr
  refine ⟨hzRoof, ?_⟩
  intro hzEssential
  have hzFrontier : z ∈ L.frontier a := by
    rw [← hlegal.frontiersEssential a]
    exact hzEssential
  have hzT : z ∈ T := by
    rw [L.frontier_eq_essential_terminalFrontier
      hlegal.roofsSourceAtStages a] at hzFrontier
    exact hzFrontier.1
  exact Set.disjoint_left.1 hsupportDisjoint hzr hzT

/-- A target-pure grounded route whose source record was already
inessential at its indexed stage can contact a hanging limiting component
only at a strictly earlier owner stage. -/
theorem splitGroundedTargetPure_hangingComponentStage_lt_of_prior
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (p : FinitePath
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.graph)
    (hs : p.start ∈
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source)
    (hpure :
      (L.splitGroundedPopularAuxiliaryInput hL.legal).IsTargetPure p)
    (hprior :
      (L.splitGroundedPopularAuxiliaryIndexed hL hground).f ⟨p.start, hs⟩ ∈
        L.priorInessentialRecordStages)
    {Y : Gamma.DPath} (hY : Y ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma Y)
    (z : (L.splitGroundedPopularAuxiliaryInput hL.legal).LV)
    (hzp : z ∈ p.support)
    (v : V) (hvY : v ∈ Y.support)
    (hzexit :
      (L.splitGroundedPopularAuxiliaryInput hL.legal).gadgetExit z = some v) :
    L.splitHangingComponentStage hL.legal Y hY hhang <
      (L.splitGroundedPopularAuxiliaryIndexed hL hground).f ⟨p.start, hs⟩ := by
  let I := L.splitGroundedPopularAuxiliaryInput hL.legal
  let U := L.splitGroundedPopularAuxiliaryIndexed hL hground
  let a := U.f ⟨p.start, hs⟩
  have hmeet : p.walk.Meets ({z} : Set I.LV) :=
    ⟨z, hzp, Set.mem_singleton z⟩
  let q : FinitePath I.lambda.graph :=
    p.firstHit ({z} : Set I.LV) hmeet
  have hqStart : q.start = p.start := rfl
  have hqFinish : q.finish = z :=
    Set.mem_singleton_iff.1
      (p.firstHit_finish_mem ({z} : Set I.LV) hmeet)
  have hqSource : q.start ∈ I.lambda.source := hqStart ▸ hs
  have hqPure : I.IsTargetPure q :=
    PopularAuxiliary.Input.IsTargetPure.firstHit I hpure
      ({z} : Set I.LV) hmeet
  have hvRoof : v ∈ Gamma.roof (L.frontier a) := by
    rcases I.start_of_mem_lambda_source p hs with
        ⟨x, hxSource, hpx⟩ | ⟨i, hpi⟩
    · let xs : L.groundedFiniteTerminalSet := ⟨x, hxSource⟩
      let xs' : L.finiteTerminalSet :=
        ⟨x, L.groundedFiniteTerminalSet_subset_finiteTerminalSet xs.2⟩
      have hsourceIndex : a = L.finiteTerminalIndex xs := by
        have hsEq :
            (⟨p.start, hs⟩ : I.lambda.source) =
              ⟨.old x, (I.mem_lambda_source_old x).2 hxSource⟩ :=
          Subtype.ext hpx
        change U.f ⟨p.start, hs⟩ = L.finiteTerminalIndex xs
        rw [hsEq]
        rfl
      have hpriorX : L.finiteTerminalIndex xs ∈
          L.priorInessentialRecordStages := hsourceIndex ▸ hprior
      obtain ⟨_hphi, sourcePath, hchosen, hterminal⟩ :=
        L.finiteTerminalStage_spec xs'
      have hxStrict : x ∈ Gamma.strictRoof
          (L.frontier (L.finiteTerminalIndex xs)) :=
        L.splitPriorInessential_finite_terminal_mem_strictRoof_frontier
          hL.legal hpriorX hchosen hterminal
      have hrun : PopularAuxiliary.Input.RunsFromTo x v
          (I.decodeWalkSteps q.walk) :=
        I.decodeWalkSteps_runs_from_entry q.walk
          (by rw [hqStart, hpx]; rfl)
          (by rw [hqFinish]; exact hzexit)
      rw [hsourceIndex]
      exact hL.legal.splitGroundedTargetPure_run_terminal_mem_roof
        (L.finiteTerminalIndex xs) q hqSource hqPure hrun hxStrict
    · have hsourceIndex : a = L.groundedInfiniteStage i := by
        have hsEq :
            (⟨p.start, hs⟩ : I.lambda.source) =
              ⟨.proxy i, I.mem_lambda_source_proxy i⟩ :=
          Subtype.ext hpi
        change U.f ⟨p.start, hs⟩ = L.groundedInfiniteStage i
        rw [hsEq]
        rfl
      have hpriorI : L.groundedInfiniteStage i ∈
          L.priorInessentialRecordStages := hsourceIndex ▸ hprior
      have hchosen : L.chosen (L.groundedInfiniteStage i) = some i.1 :=
        (L.groundedInfiniteStage_spec i).2
      obtain ⟨r, hr⟩ := I.proxy_isRay i
      have hir : (i.1 : Gamma.DPath) = .inr r := by
        simpa [I, splitGroundedPopularAuxiliaryInput,
          splitGroundedInfinitePath] using hr
      have hsupport : i.1.support ⊆ Gamma.strictRoof
          (L.frontier (L.groundedInfiniteStage i)) := by
        rw [hir]
        apply L.splitPriorInessential_grounded_ray_support_subset_strictRoof_frontier
          hL.legal hpriorI
        · simpa [hir] using hchosen
        · obtain ⟨sourcePath, hsourceChosen, hsourceGround⟩ :=
            (L.groundedInfiniteStage_spec i).1.1
          have heq : sourcePath = i.1 :=
            Option.some.inj (hsourceChosen.symm.trans hchosen)
          rw [heq, hir] at hsourceGround
          exact hsourceGround
      obtain ⟨w, hwProxy, hrun⟩ :=
        I.decodeWalkSteps_runs_from_eq_proxy q.walk
          (hqStart.trans hpi) (by rw [hqFinish]; exact hzexit)
      have hwStrict : w ∈ Gamma.strictRoof
          (L.frontier (L.groundedInfiniteStage i)) := by
        apply hsupport
        simpa [I, splitGroundedPopularAuxiliaryInput,
          splitGroundedInfinitePath] using hwProxy
      rw [hsourceIndex]
      exact hL.legal.splitGroundedTargetPure_run_terminal_mem_roof
        (L.groundedInfiniteStage i) q hqSource hqPure hrun hwStrict
  have hInitialRoof : Y.initial ∈ Gamma.roof (L.frontier a) :=
    hL.legal.limitComponent_initial_mem_roof_of_support_mem
      a hY hvY hvRoof
  have hle := L.splitGroundedTargetPure_hangingComponentStage_le_of_gadgetExit_contact
    hL hground p hs hpure hY hhang z hzp v hvY hzexit
  have hne : L.splitHangingComponentStage hL.legal Y hY hhang ≠ a := by
    intro heq
    have hmarker := L.marker_splitHangingComponentStage
      hL.legal Y hY hhang
    rw [heq] at hmarker
    exact L.splitMarker_not_mem_roof_frontier hL.legal hmarker hInitialRoof
  exact lt_of_le_of_ne hle hne

/-- Every equal-stage collision match in grounded Assertion 8.19 is
supported by a genuinely successor-new source record. -/
theorem SplitGroundedAssertion819EqualMatch.source_mem_freshInessentialRecordStages
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    {a : Below kappa}
    (E : L.SplitGroundedAssertion819EqualMatch hL hground S r a) :
    a ∈ L.freshInessentialRecordStages := by
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hp, _hground⟩ := E.source_grounded
    exact (L.bookkeeping.mem_phi_iff_exists_chosen
      hL.legal.validBookkeeping).2 ⟨p, hp⟩
  · intro hprior
    let d := E.owner
    have hpure :
        (L.splitGroundedPopularAuxiliaryInput hL.legal).IsTargetPure d.path :=
      (L.splitGroundedPopularAuxiliaryInput hL.legal).requestFan_path_isTargetPure
        S r d.path_mem.1
    have hlt := L.splitGroundedTargetPure_hangingComponentStage_lt_of_prior
      hL hground d.path
      ((PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
        |>.starts_in_source d.path_mem)
      hpure (by simpa only [d.index_eq] using hprior)
      d.component_mem d.component_hanging d.traceContact
      d.traceContact_mem_path d.contact d.contact_mem_component
      d.traceContact_exit
    have heq := E.every_owner_stage_eq d
    exact (ne_of_lt hlt) (heq.trans d.index_eq.symm)

/-- Grounded form of the diagonal conclusion. -/
theorem SplitGroundedAssertion819EqualMatch.source_mem_freshInessentialGroundStages
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    {a : Below kappa}
    (E : L.SplitGroundedAssertion819EqualMatch hL hground S r a) :
    a ∈ L.freshInessentialGroundStages :=
  ⟨E.source_grounded, E.source_mem_freshInessentialRecordStages⟩

/-- Indices of literal hanging collisions which have no strictly earlier
owner.  These are precisely the diagonal indices left after Assertion 8.19's
regressive deletion. -/
def splitGroundedAssertion819EqualCollisionIndices
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    Set (Below kappa) :=
  L.splitGroundedAssertion819CollisionIndices hL hground S r \
    L.splitGroundedAssertion819StrictCollisionIndices hL hground S r

/-- Every diagonal collision index is genuinely successor-new. -/
theorem splitGroundedAssertion819EqualCollisionIndices_subset_fresh
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    L.splitGroundedAssertion819EqualCollisionIndices hL hground S r ⊆
      L.freshInessentialRecordStages := by
  rintro a ⟨haCollision, haNotStrict⟩
  rcases L.splitGroundedAssertion819_strict_or_equalMatch
      hL hground S r haCollision with haStrict | hequal
  · exact False.elim (haNotStrict haStrict)
  · exact hequal.some.source_mem_freshInessentialRecordStages

/-- Grounded strengthening of the diagonal-index inclusion. -/
theorem splitGroundedAssertion819EqualCollisionIndices_subset_freshGround
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    L.splitGroundedAssertion819EqualCollisionIndices hL hground S r ⊆
      L.freshInessentialGroundStages := by
  rintro a ⟨haCollision, haNotStrict⟩
  rcases L.splitGroundedAssertion819_strict_or_equalMatch
      hL hground S r haCollision with haStrict | hequal
  · exact False.elim (haNotStrict haStrict)
  · exact hequal.some.source_mem_freshInessentialGroundStages

/-- If the original-hanging collision subfan at one request is stationary,
then its diagonal remainder is stationary and hence the ladder has
stationarily many genuinely successor-new records.  This is the exact
source-faithful conclusion available from the matched-stage case; no
ordinary hindrance is fabricated from a single match. -/
theorem freshInessentialRecordStages_isStationary_of_splitGrounded_collisions
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (hcollisions : IsStationaryBelow kappa
      (L.splitGroundedAssertion819CollisionIndices hL hground S r)) :
    IsStationaryBelow kappa L.freshInessentialRecordStages := by
  have hequal : IsStationaryBelow kappa
      (L.splitGroundedAssertion819EqualCollisionIndices hL hground S r) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      hL.legal.regular hL.legal.uncountable hcollisions
      (L.splitGroundedAssertion819StrictCollisionIndices_nonstationary
        hL hground S r)
  exact hequal.mono
    (L.splitGroundedAssertion819EqualCollisionIndices_subset_fresh
      hL hground S r)

/-- Exact grounded form consumed by the global split grounding trichotomy. -/
theorem freshInessentialGroundStages_isStationary_of_splitGrounded_collisions
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (hcollisions : IsStationaryBelow kappa
      (L.splitGroundedAssertion819CollisionIndices hL hground S r)) :
    IsStationaryBelow kappa L.freshInessentialGroundStages := by
  have hequal : IsStationaryBelow kappa
      (L.splitGroundedAssertion819EqualCollisionIndices hL hground S r) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      hL.legal.regular hL.legal.uncountable hcollisions
      (L.splitGroundedAssertion819StrictCollisionIndices_nonstationary
        hL hground S r)
  exact hequal.mono
    (L.splitGroundedAssertion819EqualCollisionIndices_subset_freshGround
      hL hground S r)

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.SplitGroundedAssertion819EqualMatch.source_mem_freshInessentialRecordStages
