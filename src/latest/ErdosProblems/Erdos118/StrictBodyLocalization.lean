import ErdosProblems.Erdos118.ResponseRankRefinement
import ErdosProblems.Erdos118.StrictCriticalBounds

/-! The strict critical body rank is fixed before the actual right root
label is sampled. A real response and completion prove that the bounded
terminal test was not truncated. -/

namespace Erdos118.StrictBodyLocalization

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open BlueRuns InsideCounts LastBodyRefinement CriticalPair

theorem exists_root {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T)
    (P : Pending) (hP : 1 < P.position.stem.rootLabel.length)
    (hc : RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, .initial)) :
    ∃ k : ℕ, ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      RightBlue K (GraphPayoff.payoff C .inside) (.leaf P, .initial) ∧
      ∃ value : ℕ, 0 < value ∧ value < k + 1 ∧ ∃ b : ℕ,
        (∀ A : RootResponses.Setup k,
          (∀ x ∈ A.stem.decorated, x ∈ K) → (∀ x ∈ A.stem.decorated, b < x) →
          RamseyGame.Outcome K (GraphPayoff.game C .inside (.leaf P, .body (ofRoot A))) true) ∧
        (∀ S T : Completed, GraphPayoff.payoff C .inside S T = true →
          min (bodyRank T.stem (lastLabel S).length) (k + 1) = value) ∧
        (∀ S T : Completed, GraphPayoff.payoff C .inside S T = true →
          1 < S.stem.rootLabel.length → T.stem.rootLabel.length = k + 1 →
          bodyRank T.stem (lastLabel S).length = value ∧
          (last T.stem (lastLabel S).length = true → value + 1 < k + 1)) := by
  obtain ⟨k, K, hKH, hK, C, hCB, hC, hcC, value, _, b, hcert, htest⟩ :=
    ResponseRankRefinement.right_root hH B hB hinit P hc
      (fun k S T ↦ min (bodyRank T.stem (lastLabel S).length) (k + 1))
      (fun k ↦ k + 1) (fun k S T _ ↦ min_le_right _ _)
  have hstrict : ∀ S T, GraphPayoff.payoff C .inside S T = true → beforeLast S < beforeLast T :=
    fun S T hp ↦ hall S T (LastMarkerRefinement.payoff_true_mono hCB .inside S T hp)
  have exactRank (S T : Completed) (hp : GraphPayoff.payoff C .inside S T = true)
      (hS : 1 < S.stem.rootLabel.length) (hT : T.stem.rootLabel.length = k + 1) :
      0 < value ∧ value < k + 1 ∧ bodyRank T.stem (lastLabel S).length = value ∧
        (last T.stem (lastLabel S).length = true → value + 1 < k + 1) := by
    obtain ⟨_, _, _, hpos, hlt, hlast⟩ := StrictCriticalBounds.terminal C S T hp hS (hstrict S T hp)
    rw [hT] at hlt hlast
    have he := htest S T hp
    rw [min_eq_left hlt.le] at he
    exact ⟨he ▸ hpos, he ▸ hlt, he, fun hl ↦ he ▸ hlast hl⟩
  obtain ⟨A, hA⟩ := RootResponses.setup_above k hK b
  have hb := hcert A (fun x hx ↦ (hA x hx).1) (fun x hx ↦ (hA x hx).2)
  obtain ⟨S, T, hrun, hp⟩ := blue_completion hK (GraphPayoff.payoff C .inside)
    (.leaf P, .body (ofRoot A)) hb
  obtain ⟨heP, heA⟩ := SkippedCuts.run_extensions hrun
  have hSroot : S.stem.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (heP.labels.root _ rfl)
  have hTroot : T.stem.rootLabel = A.stem.rootLabel :=
    Option.some.inj (heA.labels.root _ rfl)
  have hSlen : 1 < S.stem.rootLabel.length := hSroot ▸ hP
  have hTlen : T.stem.rootLabel.length = k + 1 := by rw [hTroot, A.label_length]
  have hvalue := exactRank S T hp hSlen hTlen
  exact ⟨k, K, hKH, hK, C, hCB, hC, hcC, value, hvalue.1, hvalue.2.1, b,
    hcert, htest, fun S T hp hs ht ↦ (exactRank S T hp hs ht).2.2⟩

end Erdos118.StrictBodyLocalization
