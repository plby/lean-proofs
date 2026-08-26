import ErdosProblems.Erdos118.BlueCheckpoints

/-! A last-body checkpoint with ordinary suffixes above an extra fixed bound. -/

namespace Erdos118.FreshBodyCheckpoint

open LabelledExtensions LabelledFrames DecisionStates AdaptiveGame BlueRuns BlueCheckpoints

private theorem safe_step {S T : State} (hS : BeforeLastBody S) (hn : ¬ LastBody S)
    (h : DecisionStates.Step T S) : BeforeLastBody T := by
  cases h <;> simp_all [BeforeLastBody, LastBody, applyBody, LeafResponses.toPending]

private theorem nonterminal (payoff : Completed → Completed → Bool)
    (S : State × State) (hS : BeforeLastBody S.1) : terminalPayoff payoff S = none := by
  obtain ⟨S, T⟩ := S
  cases S <;> cases T <;> simp_all [BeforeLastBody, terminalPayoff]

theorem left_last {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation)
    (S X : State) (hS : BeforeLastBody S) (d : ℕ)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (S, X)) true) :
    ∃ D : BodyDecision, ∃ Y : State, D.roots = [] ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (S, X) (.body D, Y) ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (.body D, Y)) true ∧
      LeftBlue H (GraphPayoff.payoff B o) (.body D, Y) ∧
      FreshCheckpoints.FreshExtension K d (S, X) (.body D, Y) := by
  have hs : ∀ V W : State × State, BeforeLastBody V.1 → ¬ LastBody V.1 →
      PairStep W V → BeforeLastBody W.1 := by
    intro V W hV hn h
    cases h with
    | left U hstep => exact safe_step hV hn hstep
    | right U hstep => exact hV
  obtain ⟨⟨V, Y⟩, hr, hb, _, hlast, _, hf⟩ := FreshCheckpoints.blue_stop_above
    hK hKH (GraphPayoff.payoff B o) (fun V ↦ BeforeLastBody V.1) (fun V ↦ LastBody V.1)
    (fun V hV _ ↦ nonterminal _ V hV) hs d (S, X) hS hblue
  cases V with
  | initial => exact hlast.elim
  | leaf P => exact hlast.elim
  | complete C => exact hlast.elim
  | body D =>
    refine ⟨D, Y, hlast, hr, hb, ?_, hf⟩
    rcases blue_command (GraphPayoff.payoff B o) (.body D, Y) rfl hb with hl | hr
    · exact hl
    · obtain ⟨n, R, ha, _⟩ := hr
      simp [allowedSide] at ha

end Erdos118.FreshBodyCheckpoint
