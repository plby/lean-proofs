import ErdosProblems.Erdos118.CurrentBody

/-! Stop at any specified selected leaf of the current body, retaining
future roots, exact slots, actual entry information, and fresh suffixes. -/

namespace Erdos118.SelectedLeafCheckpoint

open LabelledExtensions LabelledFrames DecisionStates AdaptiveGame BlueRuns PreparedRelays

private def Local (P : Pending) (j : ℕ) (S : State) : Prop :=
  ∃ Q : Pending, S = .leaf Q ∧ CurrentBody.SameBody P Q ∧
    ExactSlots.Exact (.leaf Q) ∧ j ∈ Q.position.label ∧ Q.position.entries.length ≤ j

private def At (j : ℕ) : State → Prop
  | .leaf Q => Q.position.entries.length = j
  | _ => False

private theorem local_step {P : Pending} {j : ℕ} {S T : State}
    (hS : Local P j S) (hn : ¬ At j S) (h : DecisionStates.Step T S) : Local P j T := by
  obtain ⟨Q, rfl, hQ, hX, hj, hle⟩ := hS
  have hlt : Q.position.entries.length < j := lt_of_le_of_ne hle hn
  have hmem : j ∈ Q.leaves := by
    rw [hX.2]
    exact List.mem_filter.mpr ⟨hj, decide_eq_true hlt⟩
  cases h with
  | leaf F i rest hF A =>
    have hinc : (i :: rest).Pairwise (· < ·) :=
      (hX.2.symm.trans hF) ▸ Q.position.label_pairwise.sublist List.filter_sublist
    have hij : i ≤ j := by
      rw [hF] at hmem
      rcases List.mem_cons.mp hmem with he | hm
      · exact he.symm.le
      · exact ((List.pairwise_cons.mp hinc).1 j hm).le
    refine ⟨_, rfl, ⟨hQ.roots, hQ.stem, hQ.size, hQ.label⟩,
      ExactSlots.step_exact (DecisionStates.Step.leaf Q i rest hF A) hX, hj, ?_⟩
    have hi := Q.leafSlots.bounded i (hF ▸ List.mem_cons_self ..)
    change (Q.position.entries ++ A.newWord).length ≤ j
    rw [List.length_append, A.length_eq, Nat.add_sub_of_le hi.1.le]
    exact hij
  | nextBody F c rest hR hL A => exact (List.not_mem_nil (hL ▸ hmem)).elim
  | finish F hR hL A => exact (List.not_mem_nil (hL ▸ hmem)).elim

theorem right_entry {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation)
    (P : Pending) (hP : ExactSlots.Exact (.leaf P)) (X : State) (j d : ℕ)
    (hj : j ∈ P.position.label) (hle : P.position.entries.length ≤ j)
    (hb : RamseyGame.Outcome H (GraphPayoff.game B o (X, .leaf P)) true)
    (hready : P.position.entries.length = j →
      LeftBlue H (GraphPayoff.payoff B o) (X, .leaf P)) :
    ∃ Q : Pending, ∃ Y : State, CurrentBody.SameBody P Q ∧
      ExactSlots.Exact (.leaf Q) ∧ Q.position.entries.length = j ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (X, .leaf P) (Y, .leaf Q) ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (Y, .leaf Q)) true ∧
      LeftBlue H (GraphPayoff.payoff B o) (Y, .leaf Q) ∧
      FreshCheckpoints.FreshExtension K d (X, .leaf P) (Y, .leaf Q) ∧
      ((Y, State.leaf Q) = (X, State.leaf P) ∨
        (∀ D : BodyDecision, Y ≠ .body D) ∧
          ∀ x ∈ Y.decorated, x < Q.position.ordinary.getLastD 0) := by
  have hs : ∀ V W : State × State, Local P j V.2 → ¬ At j V.2 →
      PairStep W V → Local P j W.2 := by
    intro V W hV hn h
    cases h with
    | left U hstep => exact hV
    | right U hstep => exact local_step hV hn hstep
  have hterm : ∀ V : State × State, Local P j V.2 → ¬ At j V.2 →
      terminalPayoff (GraphPayoff.payoff B o) V = none := by
    rintro ⟨Y, V⟩ ⟨Q, rfl, _⟩ _
    cases Y <;> rfl
  obtain ⟨V, hr, hbV, hsafe, hat, hentry, hf⟩ := FreshCheckpoints.blue_stop_above
    hK hKH (GraphPayoff.payoff B o) (fun V ↦ Local P j V.2) (fun V ↦ At j V.2)
    hterm hs d (X, .leaf P) ⟨P, rfl, ⟨rfl, rfl, rfl, rfl⟩, hP, hj, hle⟩ hb
  have hh : LeftBlue H (GraphPayoff.payoff B o) V := by
    rcases hentry with rfl | ⟨W, _, hn, hstep⟩
    · exact hready hat
    · cases hstep with
      | left n R hs hR a ha hlarge => exact (hn hat).elim
      | right n R hs hR a ha hlarge =>
        cases he : R.result a with
        | initial => simp only [he, At] at hat
        | body D => simp only [he, At] at hat
        | complete C => simp only [he, At] at hat
        | leaf Q =>
          rw [he] at hbV
          exact handoff_after_right (hK.mono hKH) B o W R a Q he hbV
  have hentryData : V = (X, .leaf P) ∨
      (∀ D : BodyDecision, V.1 ≠ .body D) ∧
        ∀ x ∈ V.1.decorated, x < V.2.ordinary.getLastD 0 := by
    rcases hentry with rfl | ⟨W, _, hn, hs⟩
    · exact Or.inl rfl
    · cases hs with
      | left n R hs hR a ha hg => exact (hn hat).elim
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
  obtain ⟨Q, he, hQ, hX, _⟩ := hsafe
  dsimp only at he
  subst V
  exact ⟨Q, Y, hQ, hX, hat, hr, hbV, hh, hf, hentryData⟩

end Erdos118.SelectedLeafCheckpoint
