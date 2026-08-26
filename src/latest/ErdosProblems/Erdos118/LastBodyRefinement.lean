import ErdosProblems.Erdos118.IntrinsicAnnotations
import ErdosProblems.Erdos118.InsideRootLeaf

/-!
Refine an initial inside-blue graph to exclude singleton last-body labels
at every true terminal. Exact last-body decisions then have positive body
parameters. The remaining nonsingleton inside case is not excluded here.
-/

namespace Erdos118.LastBodyRefinement

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns

def lastIndex (S : Completed) : ℕ := S.stem.rootLabel.getLastD 0 - 1

def lastLabel (S : Completed) : List ℕ := (S.stem.bodyLabels[lastIndex S]?).getD []

theorem lastIndex_of_extension (P : Pending) (S : Completed)
    (hP : ExactSlots.Exact (.leaf P)) (hroots : P.roots = [])
    (hext : DecisionStates.LabelsExtend (.leaf P) (.complete S)) :
    lastIndex S = P.position.stem.done.length := by
  have hroot : S.stem.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (hext.root _ rfl)
  unfold lastIndex
  rw [hroot, ExactSlots.pending_last_root P hP hroots]
  omega

theorem lastLabel_of_extension (P : Pending) (S : Completed)
    (hP : ExactSlots.Exact (.leaf P)) (hroots : P.roots = [])
    (hext : DecisionStates.LabelsExtend (.leaf P) (.complete S)) :
    lastLabel S = P.position.label := by
  have hp : P.position.bodyLabels <+: S.stem.bodyLabels := hext.bodies
  have hi : P.position.stem.done.length < P.position.bodyLabels.length := by
    simp [Position.bodyLabels, Stem.bodyLabels]
  have hiS := hi.trans_le hp.length_le
  unfold lastLabel
  rw [lastIndex_of_extension P S hP hroots hext, List.getElem?_eq_getElem hiS,
    ← hp.getElem hi]
  simp [Position.bodyLabels, Stem.bodyLabels]

theorem remaining_leaf_not_singleton (P : Pending) (j : ℕ) (hnext : P.leaves = [j]) :
    P.position.label.length ≠ 1 := by
  intro hlen
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
  have hslot := P.leafSlots.bounded j (hnext ▸ List.mem_singleton_self j)
  have hold := P.leafSelected
  rw [hx, List.mem_singleton] at hold
  have hj : j = x := by simpa only [hx, List.mem_singleton] using hslot.2.2
  omega

theorem not_all_singleton {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (lastLabel S).length = 1) : False := by
  obtain ⟨k, b, _, _, P, T, _, j, _, hroots, hleaves, hP, _, _, hblue, _⟩ :=
    InsideRootLeaf.initial_remaining_leaf hH B hB hinit
  obtain ⟨S, U, hrun, hpay⟩ := blue_completion hH (GraphPayoff.payoff B .inside)
    (.leaf P, .leaf T) hblue
  have hlabel := lastLabel_of_extension P S hP hroots (SkippedCuts.run_extensions hrun).1.labels
  exact remaining_leaf_not_singleton P j hleaves (hlabel ▸ hall S U hpay)

theorem exists_refined {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true) :
    ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      RamseyGame.Outcome K (GraphPayoff.game C .inside (.initial, .initial)) true ∧
      ∀ S T : Completed, GraphPayoff.payoff C .inside S T = true →
        (lastLabel S).length ≠ 1 := by
  obtain ⟨K, hKH, hK, C, hCB, hC, hblue, value, htest⟩ :=
    IntrinsicAnnotations.refine_test hH B hB .inside hinit
      (fun S _ ↦ (lastLabel S).length = 1)
  cases value with
  | true =>
    exact (not_all_singleton hK C hC hblue
      (fun S T hp ↦ @of_decide_eq_true _ (Classical.propDecidable _) (htest S T hp))).elim
  | false =>
    exact ⟨K, hKH, hK, C, hCB, hC, hblue,
      fun S T hp ↦ @of_decide_eq_false _ (Classical.propDecidable _) (htest S T hp)⟩

theorem pending_label_not_singleton {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (lastLabel S).length ≠ 1)
    (P : Pending) (W : State) (hP : ExactSlots.Exact (.leaf P)) (hroots : P.roots = [])
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, W)) true) :
    P.position.label.length ≠ 1 := by
  obtain ⟨S, T, hrun, hpay⟩ := blue_completion hH (GraphPayoff.payoff B .inside)
    (.leaf P, W) hblue
  have hlabel := lastLabel_of_extension P S hP hroots (SkippedCuts.run_extensions hrun).1.labels
  exact hlabel ▸ hall S T hpay

theorem positive_last_body {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (lastLabel S).length ≠ 1)
    (D : BodyDecision) (W : State) (hD : ExactSlots.Exact (.body D)) (hroots : D.roots = [])
    (hblue : LeftBlue H (GraphPayoff.payoff B .inside) (.body D, W)) :
    ∃ k b : ℕ, 0 < k ∧ ∀ A : BodyResponses.Setup D.stem k,
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
      (∀ x ∈ BodyResponses.newWord A.position, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf (applyBody D A), W)) true := by
  obtain ⟨k, b, hb⟩ := BlueReservations.left_body_setups
    (GraphPayoff.payoff B .inside) D W hblue
  refine ⟨k, b, ?_, hb⟩
  by_contra hn
  have hk : k = 0 := by omega
  obtain ⟨A, hA⟩ := BodyResponses.setup_above D.stem k D.room hH b
  have hchild := hb A (fun x hx ↦ (hA x hx).1) (fun x hx ↦ (hA x hx).2)
  have he := ExactSlots.step_exact (DecisionStates.Step.body D A) hD
  have hne := pending_label_not_singleton hH B hall (applyBody D A) W he hroots hchild
  apply hne
  change A.position.label.length = 1
  rw [A.label_length, hk]

end Erdos118.LastBodyRefinement
