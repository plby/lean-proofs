import ErdosProblems.Erdos118.StrictInitialOpening

/-! Localize the next original target's second root on any fresh tail
of the source alphabet, without changing previously read coordinates. -/

namespace Erdos118.StrictUpperRoot

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open BlueRuns InsideCounts LastBodyRefinement CriticalPair

private theorem right_mono {H K : Set ℕ} (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (S : State × State) (hb : RightBlue H payoff S) :
    RightBlue K payoff S := by
  obtain ⟨n, R, hs, hR, b, hc⟩ := hb
  exact ⟨n, R, hs, hR, b, fun a ha hlarge ↦
    (hc a (ha.trans hKH) hlarge).almost_mono (RamseyGame.almostSubset_of_subset hKH)⟩

theorem localize {H : Set ℕ} {B : SimpleGraph G} (O : StrictInitialOpening.Opening H B)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (hstrict : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T)
    (value : Bool) (hcolor : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      last T.stem (lastLabel S).length = value) (d : ℕ) :
    let P := applyBody (ofRoot O.target.rootSetup) O.opening.target
    ∃ k : ℕ, ∃ K ⊆ O.prepared.alphabet, K.Infinite ∧ (∀ x ∈ K, d < x) ∧
      ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
        RightBlue K (GraphPayoff.payoff C .inside) (.leaf P, .initial) ∧
        ∃ v : ℕ, 0 < v ∧ v < k + 1 ∧ (value = true → v + 1 < k + 1) ∧ ∃ b : ℕ,
          (∀ A : RootResponses.Setup k,
            (∀ x ∈ A.stem.decorated, x ∈ K) → (∀ x ∈ A.stem.decorated, b < x) →
            RamseyGame.Outcome K (GraphPayoff.game C .inside (.leaf P, .body (ofRoot A))) true) ∧
          (∀ S T : Completed, GraphPayoff.payoff C .inside S T = true →
            1 < S.stem.rootLabel.length → T.stem.rootLabel.length = k + 1 →
            bodyRank T.stem (lastLabel S).length = v ∧
              (last T.stem (lastLabel S).length = true → v + 1 < k + 1)) := by
  let P := applyBody (ofRoot O.target.rootSetup) O.opening.target
  let J := O.prepared.alphabet \ Set.Iic d
  have hJ : J.Infinite := O.prepared.infinite.sdiff (Set.finite_Iic d)
  have hJP : J ⊆ O.prepared.alphabet := fun _ hx ↦ hx.1
  have hJH : J ⊆ H := hJP.trans (O.prepared.subset.trans O.subset)
  have hPlen : 1 < P.position.stem.rootLabel.length := by
    change 1 < O.opening.target.position.stem.rootLabel.length
    rw [O.opening.target.stem_eq, O.target.rootSetup.label_length]
    have hpos := O.positive
    omega
  have hc : RightBlue J (GraphPayoff.payoff B .inside) (.leaf P, .initial) :=
    right_mono hJH _ _ O.opening.targetHandoff
  have hbJ := hinit.almost_mono (RamseyGame.almostSubset_of_subset hJH)
  obtain ⟨k, K, hKJ, hK, C, hCB, hC, hcC, v, hv, hvk, b, hcert, _, hexact⟩ :=
    StrictBodyLocalization.exists_root hJ B hB hbJ hstrict P hPlen hc
  have hlast : value = true → v + 1 < k + 1 := by
    intro hval
    obtain ⟨A, hA⟩ := RootResponses.setup_above k hK b
    have hb := hcert A (fun x hx ↦ (hA x hx).1) (fun x hx ↦ (hA x hx).2)
    obtain ⟨S, T, hr, hp⟩ := blue_completion hK (GraphPayoff.payoff C .inside)
      (.leaf P, .body (ofRoot A)) hb
    obtain ⟨heP, heA⟩ := SkippedCuts.run_extensions hr
    have hSroot : S.stem.rootLabel = P.position.stem.rootLabel :=
      Option.some.inj (heP.labels.root _ rfl)
    have hTroot : T.stem.rootLabel = A.stem.rootLabel := Option.some.inj (heA.labels.root _ rfl)
    have hTlen : T.stem.rootLabel.length = k + 1 := by rw [hTroot, A.label_length]
    have hlastT :=
      (hcolor S T (LastMarkerRefinement.payoff_true_mono hCB .inside S T hp)).trans hval
    exact (hexact S T hp (hSroot ▸ hPlen) hTlen).2 hlastT
  exact ⟨k, K, hKJ.trans hJP, hK, fun x hx ↦ Nat.lt_of_not_ge (hKJ hx).2,
    C, hCB, hC, hcC, v, hv, hvk, hlast, b, hcert, hexact⟩

end Erdos118.StrictUpperRoot
