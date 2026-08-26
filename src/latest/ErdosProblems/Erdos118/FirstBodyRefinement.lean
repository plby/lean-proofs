import ErdosProblems.Erdos118.FirstBody
import ErdosProblems.Erdos118.IntrinsicAnnotations

/-!
Refining the first selected label at terminals makes every actual
first-body certificate positive. Unlike the earlier root-pool reduction,
the resulting terminal restriction is available for any root prefix that
has a blue certificate in this graph.
-/

namespace Erdos118.FirstBodyRefinement

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns

def firstIndex (S : Completed) : ℕ := S.stem.rootLabel.headD 0 - 1

def firstLabel (S : Completed) : List ℕ := (S.stem.bodyLabels[firstIndex S]?).getD []

theorem firstIndex_of_extension (P : Pending) (S : Completed)
    (hfirst : P.position.stem.done.length + 1 = P.position.stem.rootLabel.headD 0)
    (hext : DecisionStates.LabelsExtend (.leaf P) (.complete S)) :
    firstIndex S = P.position.stem.done.length := by
  have hroot : S.stem.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (hext.root _ rfl)
  unfold firstIndex
  rw [hroot, ← hfirst]
  omega

theorem firstLabel_of_extension (P : Pending) (S : Completed)
    (hfirst : P.position.stem.done.length + 1 = P.position.stem.rootLabel.headD 0)
    (hext : DecisionStates.LabelsExtend (.leaf P) (.complete S)) :
    firstLabel S = P.position.label := by
  have hp : P.position.bodyLabels <+: S.stem.bodyLabels := hext.bodies
  have hi : P.position.stem.done.length < P.position.bodyLabels.length := by
    simp [Position.bodyLabels, Stem.bodyLabels]
  have hiS := hi.trans_le hp.length_le
  unfold firstLabel
  rw [firstIndex_of_extension P S hfirst hext, List.getElem?_eq_getElem hiS,
    ← hp.getElem hi]
  simp [Position.bodyLabels, Stem.bodyLabels]

theorem first_body (k m : ℕ) (A : RootResponses.Setup k) (C : BodyResponses.Setup A.stem m) :
    (applyBody (ofRoot A) C).position.stem.done.length + 1 =
      (applyBody (ofRoot A) C).position.stem.rootLabel.headD 0 := by
  change C.position.stem.done.length + 1 = C.position.stem.rootLabel.headD 0
  rw [C.stem_eq]
  exact A.first_body

theorem not_all_singleton {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (firstLabel S).length = 1) : False := by
  obtain ⟨k, b, hk, hroot⟩ := InsideSingleton.initial_root_setups_at_least_two hH B hB hinit
  apply FirstBody.no_uniform_singleton hH hH B hB hinit k b hk
  intro A hA
  have hb := hroot A (fun x hx ↦ (hA x hx).1) (fun x hx ↦ (hA x hx).2)
  obtain ⟨m, hm⟩ := FirstBody.certificate_exists B (ofRoot A) hb
  obtain ⟨b₁, hcert⟩ := hm
  obtain ⟨C, hC⟩ := BodyResponses.setup_above A.stem m (ofRoot A).room hH b₁
  have hc := hcert C (fun x hx ↦ (hC x hx).1) (fun x hx ↦ (hC x hx).2)
  obtain ⟨S, T, hrun, hpay⟩ := blue_completion hH (GraphPayoff.payoff B .inside)
    (.leaf (applyBody (ofRoot A) C), .initial) hc
  have hlabel := firstLabel_of_extension (applyBody (ofRoot A) C) S (first_body k m A C)
    (SkippedCuts.run_extensions hrun).1.labels
  have hlen := hall S T hpay
  rw [hlabel] at hlen
  change C.position.label.length = 1 at hlen
  rw [C.label_length] at hlen
  have hmzero : m = 0 := by omega
  subst m
  exact ⟨b₁, hcert⟩

theorem exists_refined {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true) :
    ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      RamseyGame.Outcome K (GraphPayoff.game C .inside (.initial, .initial)) true ∧
      ∀ S T : Completed, GraphPayoff.payoff C .inside S T = true →
        (firstLabel S).length ≠ 1 := by
  obtain ⟨K, hKH, hK, C, hCB, hC, hblue, value, htest⟩ :=
    IntrinsicAnnotations.refine_test hH B hB .inside hinit
      (fun S _ ↦ (firstLabel S).length = 1)
  cases value with
  | true =>
    exact (not_all_singleton hK C hC hblue
      (fun S T hp ↦ @of_decide_eq_true _ (Classical.propDecidable _) (htest S T hp))).elim
  | false =>
    exact ⟨K, hKH, hK, C, hCB, hC, hblue,
      fun S T hp ↦ @of_decide_eq_false _ (Classical.propDecidable _) (htest S T hp)⟩

theorem certificate_positive {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (firstLabel S).length ≠ 1)
    (k m : ℕ) (A : RootResponses.Setup k) (hcert : FirstBody.Certificate H B (ofRoot A) m) :
    0 < m := by
  by_contra hn
  have hm : m = 0 := by omega
  subst m
  obtain ⟨b, hcert⟩ := hcert
  obtain ⟨C, hC⟩ := BodyResponses.setup_above A.stem 0 (ofRoot A).room hH b
  have hc := hcert C (fun x hx ↦ (hC x hx).1) (fun x hx ↦ (hC x hx).2)
  obtain ⟨S, T, hrun, hpay⟩ := blue_completion hH (GraphPayoff.payoff B .inside)
    (.leaf (applyBody (ofRoot A) C), .initial) hc
  have hlabel := firstLabel_of_extension (applyBody (ofRoot A) C) S (first_body k 0 A C)
    (SkippedCuts.run_extensions hrun).1.labels
  apply hall S T hpay
  rw [hlabel]
  exact C.label_length

theorem positive_certificate {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (firstLabel S).length ≠ 1)
    (k : ℕ) (A : RootResponses.Setup k)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.body (ofRoot A), .initial)) true) :
    ∃ m : ℕ, 0 < m ∧ FirstBody.Certificate H B (ofRoot A) m := by
  obtain ⟨m, hm⟩ := FirstBody.certificate_exists B (ofRoot A) hblue
  exact ⟨m, certificate_positive hH B hall k m A hm, hm⟩

end Erdos118.FirstBodyRefinement
