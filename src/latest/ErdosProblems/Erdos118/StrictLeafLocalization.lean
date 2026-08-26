import ErdosProblems.Erdos118.ResponseRankRefinement
import ErdosProblems.Erdos118.StrictCriticalBounds
import ErdosProblems.Erdos118.CriticalCursor

/-! Fix the strict critical leaf rank after reaching its body, while
keeping the body's actual response parameter and old state unchanged. -/

namespace Erdos118.StrictLeafLocalization

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open BlueRuns InsideCounts LastBodyRefinement CriticalPair

theorem exists_body {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T)
    (P : Pending) (hP : 1 < P.position.stem.rootLabel.length) (D : BodyDecision)
    (hc : RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, .body D))
    (hbody : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      SkippedCuts.StateExtension (.leaf P) (.complete S) →
      SkippedCuts.StateExtension (.body D) (.complete T) →
      (CriticalPair.pair T.stem (lastLabel S).length).1 = D.stem.done.length) :
    ∃ k : ℕ, ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      RightBlue K (GraphPayoff.payoff C .inside) (.leaf P, .body D) ∧
      ∃ value : ℕ, 0 < value ∧ value ≤ k + 1 ∧ ∃ b : ℕ,
        (∀ A : BodyResponses.Setup D.stem k,
          (∀ x ∈ BodyResponses.newWord A.position, x ∈ K) →
          (∀ x ∈ BodyResponses.newWord A.position, b < x) →
          RamseyGame.Outcome K (GraphPayoff.game C .inside
            (.leaf P, .leaf (applyBody D A))) true) ∧
        (∀ S T : Completed, GraphPayoff.payoff C .inside S T = true →
          min (leafRank T.stem (lastLabel S).length) (k + 1) = value) ∧
        (∀ S T : Completed, GraphPayoff.payoff C .inside S T = true →
          1 < S.stem.rootLabel.length →
          (T.stem.bodyLabels.getD (CriticalPair.pair T.stem (lastLabel S).length).1 []).length =
            k + 1 →
          leafRank T.stem (lastLabel S).length = value ∧
            (last T.stem (lastLabel S).length = true ↔ value = k + 1)) := by
  obtain ⟨k, K, hKH, hK, C, hCB, hC, hcC, value, hv, b, hcert, htest⟩ :=
    ResponseRankRefinement.body hH B hB true D (.leaf P) hc
      (fun k S T ↦ min (leafRank T.stem (lastLabel S).length) (k + 1))
      (fun k ↦ k + 1) (fun k S T _ ↦ min_le_right _ _)
  have hstrict : ∀ S T, GraphPayoff.payoff C .inside S T = true → beforeLast S < beforeLast T :=
    fun S T hp ↦ hall S T (LastMarkerRefinement.payoff_true_mono hCB .inside S T hp)
  have exactRank (S T : Completed) (hp : GraphPayoff.payoff C .inside S T = true)
      (hS : 1 < S.stem.rootLabel.length)
      (hcard :
        (T.stem.bodyLabels.getD
          (CriticalPair.pair T.stem (lastLabel S).length).1 []).length = k + 1) :
      0 < value ∧ leafRank T.stem (lastLabel S).length = value ∧
        (last T.stem (lastLabel S).length = true ↔ value = k + 1) := by
    obtain ⟨_, hs, _, _, _, _⟩ := StrictCriticalBounds.terminal C S T hp hS (hstrict S T hp)
    have hpos := leafRank_pos hs
    have hle := leafRank_le T.stem (lastLabel S).length
    rw [hcard] at hle
    have he := htest S T hp
    rw [min_eq_left hle] at he
    have hl := last_iff_leafRank_eq T.stem (lastLabel S).length hs
    rw [hcard, he] at hl
    exact ⟨he ▸ hpos, he, hl⟩
  obtain ⟨A, hA⟩ := BodyResponses.setup_above D.stem k D.room hK b
  have hb := hcert A (fun x hx ↦ (hA x hx).1) (fun x hx ↦ (hA x hx).2)
  obtain ⟨S, T, hrun, hp⟩ := blue_completion hK (GraphPayoff.payoff C .inside)
    (.leaf P, .leaf (applyBody D A)) hb
  obtain ⟨heP, heA⟩ := SkippedCuts.run_extensions hrun
  have heD := (SkippedCuts.stateExtension_of_step (DecisionStates.Step.body D A)).trans heA
  have hindex := hbody S T (LastMarkerRefinement.payoff_true_mono hCB .inside S T hp) heP heD
  have hlabel := CriticalCursor.current_label (applyBody D A) T heA
  change T.stem.bodyLabels.getD A.position.stem.done.length [] = A.position.label at hlabel
  rw [A.stem_eq] at hlabel
  have hcard :
      (T.stem.bodyLabels.getD
        (CriticalPair.pair T.stem (lastLabel S).length).1 []).length = k + 1 := by
    rw [hindex, hlabel, A.label_length]
  have hSroot : S.stem.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (heP.labels.root _ rfl)
  have hvalue := exactRank S T hp (hSroot ▸ hP) hcard
  exact ⟨k, K, hKH, hK, C, hCB, hC, hcC, value, hvalue.1, hv, b, hcert, htest,
    fun S T hp hs hc ↦ (exactRank S T hp hs hc).2⟩

end Erdos118.StrictLeafLocalization
