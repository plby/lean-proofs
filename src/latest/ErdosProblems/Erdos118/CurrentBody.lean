import ErdosProblems.Erdos118.FreshCheckpoints
import ErdosProblems.Erdos118.PreparedRelays

/-!
Stop at the last selected leaf of the current body, without requiring the
remaining root list to be empty. Retain the actual entry handoff and fresh
ordinary suffixes on the unchanged working alphabet.
-/

namespace Erdos118.CurrentBody

open LabelledExtensions LabelledFrames DecisionStates AdaptiveGame BlueRuns PreparedRelays

structure SameBody (P Q : Pending) : Prop where
  roots : Q.roots = P.roots
  stem : Q.position.stem = P.position.stem
  size : Q.position.size = P.position.size
  label : Q.position.label = P.position.label

private def Local (P : Pending) (S : State) : Prop :=
  ∃ Q : Pending, S = .leaf Q ∧ SameBody P Q

private def Last : State → Prop
  | .leaf Q => Q.leaves = []
  | _ => False

private theorem local_step {P : Pending} {S T : State} (hS : Local P S)
    (hn : ¬ Last S) (h : DecisionStates.Step T S) : Local P T := by
  obtain ⟨Q, rfl, hQ⟩ := hS
  cases h with
  | leaf F j rest hF A => exact ⟨_, rfl, ⟨hQ.roots, hQ.stem, hQ.size, hQ.label⟩⟩
  | nextBody F c rest hR hL A => exact (hn hL).elim
  | finish F hR hL A => exact (hn hL).elim

private theorem local_nonterminal_left (payoff : Completed → Completed → Bool)
    (P : Pending) (S : State × State) (hS : Local P S.1) : terminalPayoff payoff S = none := by
  obtain ⟨Q, hQ, _⟩ := hS
  obtain ⟨S, T⟩ := S
  dsimp only at hQ
  subst S
  cases T <;> rfl

private theorem local_nonterminal_right (payoff : Completed → Completed → Bool)
    (P : Pending) (S : State × State) (hS : Local P S.2) : terminalPayoff payoff S = none := by
  obtain ⟨Q, hQ, _⟩ := hS
  obtain ⟨S, T⟩ := S
  dsimp only at hQ
  subst T
  cases S <;> rfl

theorem left_last {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation)
    (P : Pending) (X : State) (d : ℕ)
    (hb : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf P, X)) true)
    (hready : P.leaves = [] → RightBlue H (GraphPayoff.payoff B o) (.leaf P, X)) :
    ∃ Q : Pending, ∃ Y : State, SameBody P Q ∧ Q.leaves = [] ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (.leaf P, X) (.leaf Q, Y) ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (.leaf Q, Y)) true ∧
      RightBlue H (GraphPayoff.payoff B o) (.leaf Q, Y) ∧
      FreshCheckpoints.FreshExtension K d (.leaf P, X) (.leaf Q, Y) := by
  have hs : ∀ V W : State × State, Local P V.1 → ¬ Last V.1 →
      PairStep W V → Local P W.1 := by
    intro V W hV hn h
    cases h with
    | left U hstep => exact local_step hV hn hstep
    | right U hstep => exact hV
  obtain ⟨V, hr, hbV, hsafe, hlast, hentry, hf⟩ := FreshCheckpoints.blue_stop_above
    hK hKH (GraphPayoff.payoff B o) (fun V ↦ Local P V.1) (fun V ↦ Last V.1)
    (fun V hV _ ↦ local_nonterminal_left _ P V hV) hs d (.leaf P, X)
    ⟨P, rfl, ⟨rfl, rfl, rfl, rfl⟩⟩ hb
  have hh : RightBlue H (GraphPayoff.payoff B o) V := by
    rcases hentry with rfl | ⟨W, _, hn, hstep⟩
    · exact hready hlast
    · cases hstep with
      | left n R hs hR a ha hlarge =>
        cases he : R.result a with
        | initial => simp only [he, Last] at hlast
        | body D => simp only [he, Last] at hlast
        | complete C => simp only [he, Last] at hlast
        | leaf Q =>
          rw [he] at hbV
          exact handoff_after_left (hK.mono hKH) B o W R a Q he hbV
      | right n R hs hR a ha hlarge => exact (hn hlast).elim
  obtain ⟨V, Y⟩ := V
  obtain ⟨Q, he, hQ⟩ := hsafe
  dsimp only at he
  subst V
  exact ⟨Q, Y, hQ, hlast, hr, hbV, hh, hf⟩

theorem right_last_entry {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation)
    (P : Pending) (X : State) (d : ℕ)
    (hb : RamseyGame.Outcome H (GraphPayoff.game B o (X, .leaf P)) true)
    (hready : P.leaves = [] → LeftBlue H (GraphPayoff.payoff B o) (X, .leaf P)) :
    ∃ Q : Pending, ∃ Y : State, SameBody P Q ∧ Q.leaves = [] ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (X, .leaf P) (Y, .leaf Q) ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (Y, .leaf Q)) true ∧
      LeftBlue H (GraphPayoff.payoff B o) (Y, .leaf Q) ∧
      FreshCheckpoints.FreshExtension K d (X, .leaf P) (Y, .leaf Q) ∧
      ((Y, State.leaf Q) = (X, State.leaf P) ∨
        (∀ D : BodyDecision, Y ≠ .body D) ∧
          ∀ x ∈ Y.decorated, x < Q.position.ordinary.getLastD 0) := by
  have hs : ∀ V W : State × State, Local P V.2 → ¬ Last V.2 →
      PairStep W V → Local P W.2 := by
    intro V W hV hn h
    cases h with
    | left U hstep => exact hV
    | right U hstep => exact local_step hV hn hstep
  obtain ⟨V, hr, hbV, hsafe, hlast, hentry, hf⟩ := FreshCheckpoints.blue_stop_above
    hK hKH (GraphPayoff.payoff B o) (fun V ↦ Local P V.2) (fun V ↦ Last V.2)
    (fun V hV _ ↦ local_nonterminal_right _ P V hV) hs d (X, .leaf P)
    ⟨P, rfl, ⟨rfl, rfl, rfl, rfl⟩⟩ hb
  have hh : LeftBlue H (GraphPayoff.payoff B o) V := by
    rcases hentry with rfl | ⟨W, _, hn, hstep⟩
    · exact hready hlast
    · cases hstep with
      | left n R hs hR a ha hlarge => exact (hn hlast).elim
      | right n R hs hR a ha hlarge =>
        cases he : R.result a with
        | initial => simp only [he, Last] at hlast
        | body D => simp only [he, Last] at hlast
        | complete C => simp only [he, Last] at hlast
        | leaf Q =>
          rw [he] at hbV
          exact handoff_after_right (hK.mono hKH) B o W R a Q he hbV
  have hentryData : V = (X, .leaf P) ∨
      (∀ D : BodyDecision, V.1 ≠ .body D) ∧
        ∀ x ∈ V.1.decorated, x < V.2.ordinary.getLastD 0 := by
    rcases hentry with rfl | ⟨W, _, hn, hs⟩
    · exact Or.inl rfl
    · cases hs with
      | left n R hs hR a ha hg => exact (hn hlast).elim
      | right n R hs hR a ha hg =>
        refine Or.inr ⟨?_, ?_⟩
        · intro D he
          change W.1 = .body D at he
          simp [allowedSide, he] at hs
        · intro x hx
          obtain ⟨v, hv, hvne, hvlarge⟩ := SkippedCuts.response_ordinary_suffix R a
          have hlastv : (R.result a).ordinary.getLastD 0 ∈ v := by
            rw [hv, List.getLastD_eq_getLast?, List.getLast?_append_of_ne_nil _ hvne,
              List.getLast?_eq_some_getLast hvne]
            exact List.getLast_mem hvne
          exact (pairBound_left W hx).trans_lt (hvlarge _ hlastv)
  obtain ⟨Y, V⟩ := V
  obtain ⟨Q, he, hQ⟩ := hsafe
  dsimp only at he
  subst V
  exact ⟨Q, Y, hQ, hlast, hr, hbV, hh, hf, hentryData⟩

theorem right_last {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation)
    (P : Pending) (X : State) (d : ℕ)
    (hb : RamseyGame.Outcome H (GraphPayoff.game B o (X, .leaf P)) true)
    (hready : P.leaves = [] → LeftBlue H (GraphPayoff.payoff B o) (X, .leaf P)) :
    ∃ Q : Pending, ∃ Y : State, SameBody P Q ∧ Q.leaves = [] ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (X, .leaf P) (Y, .leaf Q) ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (Y, .leaf Q)) true ∧
      LeftBlue H (GraphPayoff.payoff B o) (Y, .leaf Q) ∧
      FreshCheckpoints.FreshExtension K d (X, .leaf P) (Y, .leaf Q) := by
  obtain ⟨Q, Y, hsame, hlast, hr, hbQ, hh, hf, _⟩ :=
    right_last_entry hK hKH B o P X d hb hready
  exact ⟨Q, Y, hsame, hlast, hr, hbQ, hh, hf⟩

theorem last_on {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation) (right : Bool)
    (P : Pending) (X : State) (d : ℕ) (hb : Blue H B o right (.leaf P) X)
    (hready : P.leaves = [] → OtherBlue H B o right (.leaf P) X) :
    ∃ Q : Pending, ∃ Y : State, SameBody P Q ∧ Q.leaves = [] ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o)
        (pair right (.leaf P) X) (pair right (.leaf Q) Y) ∧
      Blue H B o right (.leaf Q) Y ∧ OtherBlue H B o right (.leaf Q) Y ∧
      ∃ v w : List ℕ, Q.position.ordinary = P.position.ordinary ++ v ∧
        Y.ordinary = X.ordinary ++ w ∧
        (∀ x ∈ v, x ∈ K ∧ d < x) ∧ (∀ x ∈ w, x ∈ K ∧ d < x) := by
  cases right with
  | false => exact left_last hK hKH B o P X d hb hready
  | true =>
    obtain ⟨Q, Y, hQ, hL, hr, hbQ, hh, w, v, hw, hv, hwf, hvf⟩ :=
      right_last hK hKH B o P X d hb hready
    exact ⟨Q, Y, hQ, hL, hr, hbQ, hh, v, w, hv, hw, hvf, hwf⟩

end Erdos118.CurrentBody
