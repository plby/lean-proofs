import ErdosProblems.Erdos118.AlignedLastOpening
import ErdosProblems.Erdos118.AlignedPenultimateRun

/-! The aligned third game reaches both critical leaves on an arbitrary
fresh tail, with the final root indices of the two original source words. -/

namespace Erdos118.AlignedThirdRun

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns AlignedLastOpening

theorem right_body_endpoint {H : Set ℕ} {payoff : Completed → Completed → Bool}
    (S : State) (D : BodyDecision) (P : Pending)
    (hs : ConservativeRuns.Step H payoff (S, .body D) (S, .leaf P)) :
    ∀ x ∈ S.decorated, x < P.position.ordinary.getLastD 0 := by
  generalize hV : (S, State.body D) = V at hs
  generalize hW : (S, State.leaf P) = W at hs
  cases hs with
  | left n R hs hR a ha hg =>
    have he := (congrArg Prod.snd hV).trans (congrArg Prod.snd hW).symm
    cases he
  | right n R hs hR a ha hg =>
    intro x hx
    have hS := congrArg Prod.fst hV
    have hP := congrArg Prod.snd hW
    dsimp only at hS hP
    have hbound := pairBound_left _ (hS ▸ hx)
    have he := AlignedRootPreparation.response_endpoint R a
    rw [← hP] at he
    exact hbound.trans_lt he

theorem checkpoint {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      InsideCounts.beforeLast S = InsideCounts.beforeLast T)
    (O : Opening H B) (d : ℕ) :
    ∃ T U : Pending,
      T.roots = [O.oldNext] ∧ T.leaves = [] ∧ U.roots = [O.insertedNext] ∧ U.leaves = [] ∧
      ExactSlots.Exact (.leaf T) ∧ ExactSlots.Exact (.leaf U) ∧
      ConservativeRuns.Run H (GraphPayoff.payoff B .inside)
        (.leaf O.first.target, .leaf O.second.target) (.leaf T, .leaf U) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf T, .leaf U)) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf T, .leaf U) ∧
      ∃ v w : List ℕ, T.position.ordinary = O.oldRight.position.ordinary ++ v ∧
        U.position.ordinary = O.insertedRight.position.ordinary ++ w ∧
        (∀ x ∈ v, x ∈ H ∧ d < x) ∧ (∀ x ∈ w, x ∈ H ∧ d < x) := by
  have hroots : O.second.target.roots ≠ [] := by
    intro he
    have h := congrArg List.length he
    change O.second.rootSetup.stem.rootLabel.tail.length = 0 at h
    rw [List.length_tail, O.second.rootSetup.label_length] at h
    have hp := O.sourcePositive
    omega
  have horder : O.first.target.position.ordinary.getLastD 0 <
      O.second.target.position.ordinary.getLastD 0 := by
    have hne : O.first.target.position.ordinary ≠ [] := by
      simp [Position.ordinary, Stem.ordinary]
    have hm : O.first.target.position.ordinary.getLastD 0 ∈ O.first.target.position.ordinary := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
      exact List.getLast_mem hne
    exact right_body_endpoint (.leaf O.first.target) (ofRoot O.second.rootSetup)
      O.second.target O.second.step _ (O.first.target.position.ordinary_sublist.subset hm)
  obtain ⟨T, U, a, c, hTR, hTL, hUR, hUL, hT, hU, _, hrun, hb, hh, hf⟩ :=
    AlignedPenultimateRun.right hH Set.Subset.rfl B hall O.first.target O.second.target
      O.firstExact O.secondExact hroots horder O.second.blue (fun _ ↦ O.second.handoff) d
  have hext := SkippedCuts.run_extensions hrun
  have hTlabel : T.position.stem.rootLabel = O.first.target.position.stem.rootLabel :=
    Option.some.inj (hext.1.labels.root _ rfl)
  have hUlabel : U.position.stem.rootLabel = O.second.target.position.stem.rootLabel :=
    Option.some.inj (hext.2.labels.root _ rfl)
  have ha : a = O.oldNext := by
    have h := ExactSlots.pending_next_last_root T hT hTR
    rw [hTlabel] at h
    change O.first.body.position.stem.rootLabel.getLastD 0 = a at h
    rw [O.first.body.stem_eq, O.first.rootLast,
      ExactSlots.pending_next_last_root O.oldRight O.oldRightExact O.oldRightRoots] at h
    exact h.symm
  have hc : c = O.insertedNext := by
    have h := ExactSlots.pending_next_last_root U hU hUR
    rw [hUlabel] at h
    change O.second.body.position.stem.rootLabel.getLastD 0 = c at h
    rw [O.second.body.stem_eq, O.second.rootLast,
      ExactSlots.pending_next_last_root O.insertedRight O.insertedRightExact
        O.insertedRightRoots] at h
    exact h.symm
  subst a
  subst c
  obtain ⟨v, w, hv, hw, hvf, hwf⟩ := hf
  have hv' : T.position.ordinary = O.oldRight.position.ordinary ++ v := by
    change T.position.ordinary = O.first.body.position.ordinary ++ v at hv
    rwa [O.first.ordinary] at hv
  have hw' : U.position.ordinary = O.insertedRight.position.ordinary ++ w := by
    change U.position.ordinary = O.second.body.position.ordinary ++ w at hw
    rwa [O.second.ordinary] at hw
  exact ⟨T, U, hTR, hTL, hUR, hUL, hT, hU, hrun, hb, hh, v, w, hv', hw', hvf, hwf⟩

end Erdos118.AlignedThirdRun
