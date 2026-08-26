import ErdosProblems.Erdos118.FreshCheckpoints

/-!
Blue continuations stopped at actual last-body or last-leaf states. New
coordinates may be restricted to any infinite subalphabet, while the blue
certificate remains on the original alphabet. No intermediate certificate
is inferred merely from a completed run's terminal color.
-/

namespace Erdos118.BlueCheckpoints

open LabelledExtensions LabelledFrames DecisionStates AdaptiveGame BlueRuns

theorem blue_stop_with_entry {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (Safe Check : State × State → Prop)
    (hnonterminal : ∀ S, Safe S → ¬ Check S → terminalPayoff payoff S = none)
    (hstep : ∀ S T, Safe S → ¬ Check S → PairStep T S → Safe T)
    (S : State × State) (hS : Safe S)
    (hblue : RamseyGame.Outcome H (AdaptiveGame.game payoff S) true) :
    ∃ T : State × State, ConservativeRuns.Run K payoff S T ∧
      RamseyGame.Outcome H (AdaptiveGame.game payoff T) true ∧ Check T ∧
      (T = S ∨ ∃ U, ConservativeRuns.Run K payoff S U ∧ ¬ Check U ∧
        ConservativeRuns.Step K payoff U T) := by
  obtain ⟨T, hrun, hb, _, hc, hentry, _⟩ := FreshCheckpoints.blue_stop_above
    hK hKH payoff Safe Check hnonterminal hstep 0 S hS hblue
  exact ⟨T, hrun, hb, hc, hentry⟩

theorem blue_stop {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (Safe Check : State × State → Prop)
    (hnonterminal : ∀ S, Safe S → ¬ Check S → terminalPayoff payoff S = none)
    (hstep : ∀ S T, Safe S → ¬ Check S → PairStep T S → Safe T)
    (S : State × State) (hS : Safe S)
    (hblue : RamseyGame.Outcome H (AdaptiveGame.game payoff S) true) :
    ∃ T : State × State, ConservativeRuns.Run K payoff S T ∧
      RamseyGame.Outcome H (AdaptiveGame.game payoff T) true ∧ Check T := by
  obtain ⟨T, hrun, hb, hc, _⟩ :=
    blue_stop_with_entry hK hKH payoff Safe Check hnonterminal hstep S hS hblue
  exact ⟨T, hrun, hb, hc⟩

def Working : State → Prop
  | .body _ | .leaf _ => True
  | _ => False

def LastLeaf : State → Prop
  | .leaf P => P.roots = [] ∧ P.leaves = []
  | _ => False

def BeforeLastBody : State → Prop
  | .body _ => True
  | .leaf P => P.roots ≠ []
  | _ => False

def LastBody : State → Prop
  | .body D => D.roots = []
  | _ => False

private theorem working_step {S T : State} (hS : Working S) (hnot : ¬ LastLeaf S)
    (h : DecisionStates.Step T S) : Working T := by
  cases h <;> simp_all [Working, LastLeaf]

private theorem beforeLastBody_step {S T : State} (hS : BeforeLastBody S)
    (hnot : ¬ LastBody S) (h : DecisionStates.Step T S) : BeforeLastBody T := by
  cases h <;> simp_all [BeforeLastBody, LastBody, applyBody, LeafResponses.toPending]

private theorem working_nonterminal_left (payoff : Completed → Completed → Bool)
    (S : State × State) (hS : Working S.1) : terminalPayoff payoff S = none := by
  obtain ⟨S, T⟩ := S
  cases S <;> cases T <;> simp_all [Working, terminalPayoff]

private theorem working_nonterminal_right (payoff : Completed → Completed → Bool)
    (S : State × State) (hS : Working S.2) : terminalPayoff payoff S = none := by
  obtain ⟨S, T⟩ := S
  cases S <;> cases T <;> simp_all [Working, terminalPayoff]

private theorem beforeLastBody_working {S : State} (hS : BeforeLastBody S) : Working S := by
  cases S <;> simp_all [BeforeLastBody, Working]

theorem left_last_leaf {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (S T : State) (hS : Working S)
    (hblue : RamseyGame.Outcome H (AdaptiveGame.game payoff (S, T)) true) :
    ∃ P : Pending, ∃ U : State, P.roots = [] ∧ P.leaves = [] ∧
      ConservativeRuns.Run K payoff (S, T) (.leaf P, U) ∧
      RamseyGame.Outcome H (AdaptiveGame.game payoff (.leaf P, U)) true := by
  have hstep : ∀ V W : State × State, Working V.1 → ¬ LastLeaf V.1 →
      PairStep W V → Working W.1 := by
    intro V W hV hn h
    cases h with
    | left U hs => exact working_step hV hn hs
    | right U hs => exact hV
  obtain ⟨⟨V, U⟩, hrun, hb, hlast⟩ := blue_stop hK hKH payoff
    (fun V ↦ Working V.1) (fun V ↦ LastLeaf V.1)
    (fun V hV _ ↦ working_nonterminal_left payoff V hV) hstep (S, T) hS hblue
  cases V with
  | initial => exact hlast.elim
  | body D => exact hlast.elim
  | complete C => exact hlast.elim
  | leaf P => exact ⟨P, U, hlast.1, hlast.2, hrun, hb⟩

theorem right_last_leaf {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (S T : State) (hT : Working T)
    (hblue : RamseyGame.Outcome H (AdaptiveGame.game payoff (S, T)) true) :
    ∃ P : Pending, ∃ U : State, P.roots = [] ∧ P.leaves = [] ∧
      ConservativeRuns.Run K payoff (S, T) (U, .leaf P) ∧
      RamseyGame.Outcome H (AdaptiveGame.game payoff (U, .leaf P)) true := by
  have hstep : ∀ V W : State × State, Working V.2 → ¬ LastLeaf V.2 →
      PairStep W V → Working W.2 := by
    intro V W hV hn h
    cases h with
    | left U hs => exact hV
    | right U hs => exact working_step hV hn hs
  obtain ⟨⟨U, V⟩, hrun, hb, hlast⟩ := blue_stop hK hKH payoff
    (fun V ↦ Working V.2) (fun V ↦ LastLeaf V.2)
    (fun V hV _ ↦ working_nonterminal_right payoff V hV) hstep (S, T) hT hblue
  cases V with
  | initial => exact hlast.elim
  | body D => exact hlast.elim
  | complete C => exact hlast.elim
  | leaf P => exact ⟨P, U, hlast.1, hlast.2, hrun, hb⟩

theorem left_last_body {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (D : BodyDecision) (T : State)
    (hblue : RamseyGame.Outcome H (AdaptiveGame.game payoff (.body D, T)) true) :
    ∃ E : BodyDecision, ∃ U : State, E.roots = [] ∧
      ConservativeRuns.Run K payoff (.body D, T) (.body E, U) ∧
      RamseyGame.Outcome H (AdaptiveGame.game payoff (.body E, U)) true := by
  have hstep : ∀ V W : State × State, BeforeLastBody V.1 → ¬ LastBody V.1 →
      PairStep W V → BeforeLastBody W.1 := by
    intro V W hV hn h
    cases h with
    | left U hs => exact beforeLastBody_step hV hn hs
    | right U hs => exact hV
  obtain ⟨⟨V, U⟩, hrun, hb, hlast⟩ := blue_stop hK hKH payoff
    (fun V ↦ BeforeLastBody V.1) (fun V ↦ LastBody V.1)
    (fun V hV _ ↦ working_nonterminal_left payoff V (beforeLastBody_working hV))
    hstep (.body D, T) trivial hblue
  cases V with
  | initial => exact hlast.elim
  | leaf P => exact hlast.elim
  | complete C => exact hlast.elim
  | body E => exact ⟨E, U, hlast, hrun, hb⟩

theorem right_last_body {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (S : State) (D : BodyDecision)
    (hblue : RamseyGame.Outcome H (AdaptiveGame.game payoff (S, .body D)) true) :
    ∃ E : BodyDecision, ∃ U : State, E.roots = [] ∧
      ConservativeRuns.Run K payoff (S, .body D) (U, .body E) ∧
      RamseyGame.Outcome H (AdaptiveGame.game payoff (U, .body E)) true := by
  have hstep : ∀ V W : State × State, BeforeLastBody V.2 → ¬ LastBody V.2 →
      PairStep W V → BeforeLastBody W.2 := by
    intro V W hV hn h
    cases h with
    | left U hs => exact hV
    | right U hs => exact beforeLastBody_step hV hn hs
  obtain ⟨⟨U, V⟩, hrun, hb, hlast⟩ := blue_stop hK hKH payoff
    (fun V ↦ BeforeLastBody V.2) (fun V ↦ LastBody V.2)
    (fun V hV _ ↦ working_nonterminal_right payoff V (beforeLastBody_working hV))
    hstep (S, .body D) trivial hblue
  cases V with
  | initial => exact hlast.elim
  | leaf P => exact hlast.elim
  | complete C => exact hlast.elim
  | body E => exact ⟨E, U, hlast, hrun, hb⟩

theorem left_last_leaf_handoff {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation)
    (S T : State) (hS : Working S)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (S, T)) true)
    (hready : LastLeaf S → RightBlue H (GraphPayoff.payoff B o) (S, T)) :
    ∃ P : Pending, ∃ U : State, P.roots = [] ∧ P.leaves = [] ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (S, T) (.leaf P, U) ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (.leaf P, U)) true ∧
      RightBlue H (GraphPayoff.payoff B o) (.leaf P, U) := by
  have hH : H.Infinite := hK.mono hKH
  have hstep : ∀ V W : State × State, Working V.1 → ¬ LastLeaf V.1 →
      PairStep W V → Working W.1 := by
    intro V W hV hn h
    cases h with
    | left U hs => exact working_step hV hn hs
    | right U hs => exact hV
  obtain ⟨V, hrun, hb, hlast, hentry⟩ := blue_stop_with_entry hK hKH
    (GraphPayoff.payoff B o) (fun V ↦ Working V.1) (fun V ↦ LastLeaf V.1)
    (fun V hV _ ↦ working_nonterminal_left _ V hV) hstep (S, T) hS hblue
  have hhand : RightBlue H (GraphPayoff.payoff B o) V := by
    rcases hentry with rfl | ⟨W, _, hn, hs⟩
    · exact hready hlast
    · cases hs with
      | left n R hs hR a haK hlarge =>
        cases he : R.result a with
        | initial => simp only [he, LastLeaf] at hlast
        | body D => simp only [he, LastLeaf] at hlast
        | complete C => simp only [he, LastLeaf] at hlast
        | leaf P =>
          rw [he] at hb
          exact handoff_after_left hH B o W R a P he hb
      | right n R hs hR a haK hlarge => exact (hn hlast).elim
  obtain ⟨V, U⟩ := V
  cases V with
  | initial => exact hlast.elim
  | body D => exact hlast.elim
  | complete C => exact hlast.elim
  | leaf P => exact ⟨P, U, hlast.1, hlast.2, hrun, hb, hhand⟩

theorem right_last_leaf_handoff_entry {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation)
    (S T : State) (hT : Working T)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (S, T)) true)
    (hready : LastLeaf T → LeftBlue H (GraphPayoff.payoff B o) (S, T)) :
    ∃ P : Pending, ∃ U : State, P.roots = [] ∧ P.leaves = [] ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (S, T) (U, .leaf P) ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (U, .leaf P)) true ∧
      LeftBlue H (GraphPayoff.payoff B o) (U, .leaf P) ∧
      (U = S ∨ ∀ D : BodyDecision, U ≠ .body D) := by
  have hH : H.Infinite := hK.mono hKH
  have hstep : ∀ V W : State × State, Working V.2 → ¬ LastLeaf V.2 →
      PairStep W V → Working W.2 := by
    intro V W hV hn h
    cases h with
    | left U hs => exact hV
    | right U hs => exact working_step hV hn hs
  obtain ⟨V, hrun, hb, hlast, hentry⟩ := blue_stop_with_entry hK hKH
    (GraphPayoff.payoff B o) (fun V ↦ Working V.2) (fun V ↦ LastLeaf V.2)
    (fun V hV _ ↦ working_nonterminal_right _ V hV) hstep (S, T) hT hblue
  have hbody : V.1 = S ∨ ∀ D : BodyDecision, V.1 ≠ .body D := by
    rcases hentry with rfl | ⟨W, _, hn, hs⟩
    · exact Or.inl rfl
    · cases hs with
      | left n R hs hR a haK hlarge => exact (hn hlast).elim
      | right n R hs hR a haK hlarge =>
        right
        intro D hD
        change W.1 = .body D at hD
        simp [allowedSide, hD] at hs
  have hhand : LeftBlue H (GraphPayoff.payoff B o) V := by
    rcases hentry with rfl | ⟨W, _, hn, hs⟩
    · exact hready hlast
    · cases hs with
      | left n R hs hR a haK hlarge => exact (hn hlast).elim
      | right n R hs hR a haK hlarge =>
        cases he : R.result a with
        | initial => simp only [he, LastLeaf] at hlast
        | body D => simp only [he, LastLeaf] at hlast
        | complete C => simp only [he, LastLeaf] at hlast
        | leaf P =>
          rw [he] at hb
          exact handoff_after_right hH B o W R a P he hb
  obtain ⟨U, V⟩ := V
  cases V with
  | initial => exact hlast.elim
  | body D => exact hlast.elim
  | complete C => exact hlast.elim
  | leaf P => exact ⟨P, U, hlast.1, hlast.2, hrun, hb, hhand, hbody⟩

theorem right_last_leaf_handoff {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation)
    (S T : State) (hT : Working T)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (S, T)) true)
    (hready : LastLeaf T → LeftBlue H (GraphPayoff.payoff B o) (S, T)) :
    ∃ P : Pending, ∃ U : State, P.roots = [] ∧ P.leaves = [] ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (S, T) (U, .leaf P) ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (U, .leaf P)) true ∧
      LeftBlue H (GraphPayoff.payoff B o) (U, .leaf P) := by
  obtain ⟨P, U, hPR, hPL, hrun, hb, hh, _⟩ :=
    right_last_leaf_handoff_entry hK hKH B o S T hT hblue hready
  exact ⟨P, U, hPR, hPL, hrun, hb, hh⟩

end Erdos118.BlueCheckpoints
