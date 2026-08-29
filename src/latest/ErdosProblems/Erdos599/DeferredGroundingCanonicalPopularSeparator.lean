/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingCanonicalEqualImpossible
import ErdosProblems.Erdos599.DeferredGroundingSuccessorTransport

/-!
# The canonical deferred auxiliary has a popular separator

First-target truncation makes every route target-pure.  Deferred selection
puts a finite source record in the strict roof of its pre-marker arrow; a ray
source has its whole support there.  The decoded route therefore ends in that
closed roof, which implies that the target marker stage does not exceed the
source record stage.  The equal-index subwarp is empty by the maximal-rung
theorem, leaving the popular-separator arm of the standard dichotomy.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath Ladder Stationary

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- A finite path chosen by deferred bookkeeping is already inessential in
the pre-marker arrow.  The only alternative would be that adjoining the
current marker kills an essential arrow component, which contradicts the
maximality of the canonical rung. -/
theorem canonicalDeferredLadder_chosenFinite_terminal_mem_strictRoof_arrowPart
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a : Stage kappa} (f : FinitePath G.graph)
    (hchosen : (canonicalDeferredLadder G kappa preferred).chosen a =
      some (.inl f : G.DPath)) :
    f.finish ∈ G.strictRoof (G.terminalFrontier
      ((canonicalDeferredLadder G kappa preferred).arrowPart a)) := by
  let L := canonicalDeferredLadder G kappa preferred
  have hlegal : IsDeferredLegal L :=
    canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
      hNoEnter
  have hsplit : (canonicalLadder G kappa preferred).IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  have hpArrow : (Sum.inl f : G.DPath) ∈ L.arrowPart a :=
    canonicalDeferredLadder_chosen_mem_arrowPart preferred hkappa huncountable
      hNoEnter hchosen
  have hpSuccessorInessential : (Sum.inl f : G.DPath) ∈
      G.inessentialPaths (L.successorWarp a) :=
    (chosen_spec hlegal.validBookkeeping hchosen).1
  have hpNotEssential : (Sum.inl f : G.DPath) ∉
      G.essentialWarpPart (L.arrowPart a) := by
    intro hpEssential
    cases hm : L.marker a with
    | none =>
        have hsuccessor : L.successorWarp a = L.arrowPart a := by
          calc
            L.successorWarp a = L.arrowPart a ∪ L.markerPathSet a := by
              change (canonicalLadder G kappa preferred).successorWarp a =
                (canonicalLadder G kappa preferred).arrowPart a ∪
                  (canonicalLadder G kappa preferred).markerPathSet a
              exact (hsplit.exactSuccessorArrows a).2
            _ = L.arrowPart a := by simp [markerPathSet, hm]
        rw [hsuccessor] at hpSuccessorInessential
        exact hpSuccessorInessential.2 hpEssential
    | some y =>
        exact canonicalDeferredLadder_no_chosenFinite_of_essential_arrowPart
          preferred hkappa huncountable hNoEnter f hchosen hpEssential hm
  exact G.terminal_mem_strictRoof_of_mem_inessentialPaths
    ⟨hpArrow, hpNotEssential⟩ rfl

/-- The pre-marker arrow roof is contained in the successor frontier roof. -/
private theorem canonicalDeferredLadder_arrowRoof_subset_successorFrontierRoof
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : Stage kappa) :
    G.roof (G.terminalFrontier
      ((canonicalDeferredLadder G kappa preferred).arrowPart a)) ⊆
    G.roof ((canonicalDeferredLadder G kappa preferred).frontier
      (successorStage (canonicalDeferredLadder G kappa preferred)
        (canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
          hNoEnter) a)) := by
  let L := canonicalDeferredLadder G kappa preferred
  let hlegal : IsDeferredLegal L :=
    canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
      hNoEnter
  have hsplit : (canonicalLadder G kappa preferred).IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  have hsubset : G.terminalFrontier (L.arrowPart a) ⊆
      G.terminalFrontier (L.successorWarp a) := by
    rintro z ⟨p, hp, hpz⟩
    refine ⟨p, ?_, hpz⟩
    have hsuccessor : L.successorWarp a =
        L.arrowPart a ∪ L.markerPathSet a := by
      change (canonicalLadder G kappa preferred).successorWarp a =
        (canonicalLadder G kappa preferred).arrowPart a ∪
          (canonicalLadder G kappa preferred).markerPathSet a
      exact (hsplit.exactSuccessorArrows a).2
    rw [hsuccessor]
    exact Or.inl hp
  intro y hy
  rw [L.frontier_eq_essential_terminalFrontier
      hlegal.roofsSourceAtStages,
    G.roof_essential,
    warpAt_successorStage L hlegal]
  exact G.roof_mono hsubset hy

/-- Target-pure paths in the canonical deferred auxiliary have weakly
decreasing marker/record stages. -/
theorem canonicalDeferredLadder_targetPure_auxiliaryNonincreasing
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder G kappa preferred))
    (q : FinitePath
      (popularAuxiliaryInput (canonicalDeferredLadder G kappa preferred)
        hL.legal).lambda.graph)
    (hs : q.start ∈
      (popularAuxiliaryInput (canonicalDeferredLadder G kappa preferred)
        hL.legal).lambda.source)
    (ht : q.finish ∈
      (popularAuxiliaryInput (canonicalDeferredLadder G kappa preferred)
        hL.legal).lambda.target)
    (hpure : (popularAuxiliaryInput
      (canonicalDeferredLadder G kappa preferred) hL.legal).IsTargetPure q) :
    (popularAuxiliaryIndexed (canonicalDeferredLadder G kappa preferred) hL).g
        ⟨q.finish, ht⟩ ≤
      (popularAuxiliaryIndexed (canonicalDeferredLadder G kappa preferred) hL).f
        ⟨q.start, hs⟩ := by
  let L := canonicalDeferredLadder G kappa preferred
  let I := popularAuxiliaryInput L hL.legal
  let U := popularAuxiliaryIndexed L hL
  obtain ⟨y, hyTarget, hqy⟩ := I.finish_of_mem_lambda_target q ht
  let b : Stage kappa := L.markerStage ⟨y, hyTarget.1⟩
  have hmarker : L.marker b = some y := L.markerStage_spec ⟨y, hyTarget.1⟩
  have hyNotRoof : y ∉ G.roof (L.frontier b) :=
    marker_not_mem_roof_frontier L hL.legal hmarker
  rcases I.start_of_mem_lambda_source q hs with
      ⟨x, hxFinite, hqx⟩ | ⟨i, hqi⟩
  · let xs : finiteTerminalSet L := ⟨x, hxFinite⟩
    let a : Stage kappa := finiteTerminalStage L xs
    obtain ⟨_, p, hpChosen, hpTerminal⟩ := finiteTerminalStage_spec L xs
    rcases p with f | r
    · have hfx : f.finish = x := Option.some.inj hpTerminal
      have hxStrict : x ∈ G.strictRoof
          (G.terminalFrontier (L.arrowPart a)) := by
        rw [← hfx]
        exact canonicalDeferredLadder_chosenFinite_terminal_mem_strictRoof_arrowPart
          preferred hkappa huncountable hNoEnter f hpChosen
      have hrun : PopularAuxiliary.Input.RunsFromTo x y
          (I.decodeWalkSteps q.walk) :=
        I.decodeWalkSteps_runs_from_entry q.walk
          (by rw [hqx]; rfl) (by rw [hqy]; rfl)
      have hyArrow : y ∈ G.roof (G.terminalFrontier (L.arrowPart a)) :=
        canonicalLadder_targetPure_run_terminal_mem_roof_arrowPartFrontier_of_ladder
          preferred hkappa huncountable hNoEnter I rfl a q hs hpure
            hrun hxStrict
      have hySucc : y ∈ G.roof
          (L.frontier (successorStage L hL.legal a)) :=
        canonicalDeferredLadder_arrowRoof_subset_successorFrontierRoof
          preferred hkappa huncountable hNoEnter a hyArrow
      have hba : b ≤ a := by
        by_contra hnot
        have hab : a < b := lt_of_not_ge hnot
        have hsuccle : successorStage L hL.legal a ≤ b :=
          (successorStage_le_iff_lt L hL.legal).2 hab
        apply hyNotRoof
        rcases hsuccle.lt_or_eq with hlt | heq
        · exact G.roof_cut (hL.legal.frontierChronology hlt) hySucc
        · rwa [heq] at hySucc
      have htEq : (⟨q.finish, ht⟩ : I.lambda.target) =
          ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ :=
        Subtype.ext hqy
      have hsEq : (⟨q.start, hs⟩ : I.lambda.source) =
          ⟨.old x, (I.mem_lambda_source_old x).2 hxFinite⟩ :=
        Subtype.ext hqx
      rw [htEq, hsEq]
      exact hba
    · simp at hpTerminal
  · let a : Stage kappa := infiniteStage L i
    obtain ⟨r, hir⟩ := infinitePath_isRay L hL.legal i
    have hchosen : L.chosen a = some (.inr r : G.DPath) := by
      rw [← hir]
      exact (infiniteStage_spec L i).2
    obtain ⟨z, hzProxy, hrun⟩ :=
      I.decodeWalkSteps_runs_from_eq_proxy q.walk hqi
        (by rw [hqy]; rfl)
    have hzRay : z ∈ r.support := by
      change z ∈ (infinitePath L hL.legal i).support at hzProxy
      rwa [hir] at hzProxy
    have hzStrict : z ∈ G.strictRoof
        (G.terminalFrontier (L.arrowPart a)) :=
      canonicalDeferredLadder_chosenRay_support_subset_strictRoof_arrowPart
        preferred hkappa huncountable hNoEnter r hchosen hzRay
    have hyArrow : y ∈ G.roof (G.terminalFrontier (L.arrowPart a)) :=
      canonicalLadder_targetPure_run_terminal_mem_roof_arrowPartFrontier_of_ladder
        preferred hkappa huncountable hNoEnter I rfl a q hs hpure
          hrun hzStrict
    have hySucc : y ∈ G.roof
        (L.frontier (successorStage L hL.legal a)) :=
      canonicalDeferredLadder_arrowRoof_subset_successorFrontierRoof
        preferred hkappa huncountable hNoEnter a hyArrow
    have hba : b ≤ a := by
      by_contra hnot
      have hab : a < b := lt_of_not_ge hnot
      have hsuccle : successorStage L hL.legal a ≤ b :=
        (successorStage_le_iff_lt L hL.legal).2 hab
      apply hyNotRoof
      rcases hsuccle.lt_or_eq with hlt | heq
      · exact G.roof_cut (hL.legal.frontierChronology hlt) hySucc
      · rwa [heq] at hySucc
    have htEq : (⟨q.finish, ht⟩ : I.lambda.target) =
        ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ :=
      Subtype.ext hqy
    have hsEq : (⟨q.start, hs⟩ : I.lambda.source) =
        ⟨.proxy i, I.mem_lambda_source_proxy i⟩ := Subtype.ext hqi
    rw [htEq, hsEq]
    exact hba

/-- The target-pure equal arm of the canonical deferred auxiliary is empty,
so the standard strong-target dichotomy returns an actual popular separator. -/
theorem canonicalDeferredLadder_popularAuxiliary_popularSeparator_nonempty
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder G kappa preferred)) :
    Nonempty (Popular.PopularSeparator
      (popularAuxiliaryIndexed (canonicalDeferredLadder G kappa preferred)
        hL)) := by
  let L := canonicalDeferredLadder G kappa preferred
  let I := popularAuxiliaryInput L hL.legal
  let U := popularAuxiliaryIndexed L hL
  have hsource : U.SourceBounded :=
    U.sourceBounded_of_sourceIndexed (popularAuxiliaryIndexed_sourceIndexed L hL)
  rcases Popular.stronglyPopular_target_or_popularSeparator U hsource with
      ⟨P, hP⟩ | hseparator
  · let Q := P.firstTargetWarp
    have hQstat : IsStationaryBelow kappa
        (Popular.initialIndicesOf U Q.paths Q.starts_in_source) :=
      hP.mono (P.initialIndices_subset_firstTargetWarp U)
    have hQpure : ∀ p (hp : p ∈ Q.paths), I.IsTargetPure p := by
      intro p hp
      rcases hp with ⟨q, rfl⟩
      exact I.firstHit_target_isTargetPure q.1
        ⟨q.1.finish, q.1.finish_mem_support, P.ends_in_target q.2⟩
    have hmono : ∀ p (hp : p ∈ Q.paths),
        U.g ⟨p.finish, Q.ends_in_target hp⟩ ≤
          U.f ⟨p.start, Q.starts_in_source hp⟩ := by
      intro p hp
      exact canonicalDeferredLadder_targetPure_auxiliaryNonincreasing
        preferred hkappa huncountable hNoEnter hL p
          (Q.starts_in_source hp) (Q.ends_in_target hp) (hQpure p hp)
    have hequal : IsStationaryBelow kappa
        (Popular.initialIndicesOf U (U.equalSubwarp Q).paths
          (U.equalSubwarp Q).starts_in_source) :=
      U.stationary_equalSubwarp_of_pathwise_nonincreasing Q hQstat hmono
    obtain ⟨_, p, hp, _hpa⟩ := hequal.nonempty
    exact False.elim
      (canonicalDeferredLadder_no_targetPure_equalSubwarp_path
        preferred hkappa huncountable hNoEnter hL Q hp
          (hQpure p (U.equalPaths_subset Q hp)))
  · exact hseparator

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.canonicalDeferredLadder_popularAuxiliary_popularSeparator_nonempty
