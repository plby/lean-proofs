import ErdosProblems.Erdos118.ManagedCritical
import ErdosProblems.Erdos118.ReplaySources

/-! A critical left checkpoint with both fresh ordinary suffixes,
without a deferred replay invariant or a change of the blue graph. -/

namespace Erdos118.FreshCriticalCheckpoint

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays ManagedCritical

theorem stop_handoff {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (S T : State) (hS : Early S)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (S, T)) true)
    (hready : Critical S → RightBlue H (GraphPayoff.payoff B .inside) (S, T)) (d : ℕ) :
    ∃ P : Pending, ∃ U : State, ∃ c : ℕ,
      P.roots = [c] ∧ P.leaves = [] ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B .inside) (S, T) (.leaf P, U) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, U)) true ∧
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, U) ∧
      FreshCheckpoints.FreshExtension K d (S, T) (.leaf P, U) := by
  let Safe : State × State → Prop := fun V ↦ Early V.1
  let Check : State × State → Prop := fun V ↦ Critical V.1
  have hstep : ∀ V W : State × State, Safe V → ¬ Check V → PairStep W V → Safe W := by
    intro V W hV hn hs
    cases hs with
    | left U hs => exact early_step hV hn hs
    | right U hs => exact hV
  obtain ⟨V, hrun, hb, _, hcrit, hentry, hf⟩ := FreshCheckpoints.blue_stop_above hK hKH
    (GraphPayoff.payoff B .inside) Safe Check
    (fun V hV _ ↦ early_nonterminal _ V hV) hstep d (S, T) hS hblue
  have hh : RightBlue H (GraphPayoff.payoff B .inside) V := by
    rcases hentry with rfl | ⟨W, _, hn, hs⟩
    · exact hready hcrit
    · cases hs with
      | left n R hs hR a ha hg =>
        cases he : R.result a with
        | initial => simp only [Check, he, Critical] at hcrit
        | body D => simp only [Check, he, Critical] at hcrit
        | complete C => simp only [Check, he, Critical] at hcrit
        | leaf P =>
          rw [he] at hb
          exact handoff_after_left (hK.mono hKH) B .inside W R a P he hb
      | right n R hs hR a ha hg => exact (hn hcrit).elim
  obtain ⟨V, U⟩ := V
  cases V with
  | initial => exact hcrit.elim
  | body D => exact hcrit.elim
  | complete C => exact hcrit.elim
  | leaf P =>
    obtain ⟨c, hR, hL⟩ := hcrit
    exact ⟨P, U, c, hR, hL, hrun, hb, hh, hf⟩

private theorem response_endpoint {T : State} {b : ℕ}
    (R : Response T b) (a : R.family.members) : b < (R.result a).ordinary.getLastD 0 := by
  obtain ⟨v, hv, hvne, hvlarge⟩ := SkippedCuts.response_ordinary_suffix R a
  have hlastv : (R.result a).ordinary.getLastD 0 ∈ v := by
    rw [hv, List.getLastD_eq_getLast?, List.getLast?_append_of_ne_nil _ hvne,
      List.getLast?_eq_some_getLast hvne]
    exact List.getLast_mem hvne
  exact hvlarge _ hlastv

theorem right_handoff {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (P : Pending) (T : State) (hP : P.roots ≠ [])
    (hblue : RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, T)) (d : ℕ) :
    ∃ Q : Pending,
      ConservativeRuns.Run K (GraphPayoff.payoff B .inside) (.leaf P, T) (.leaf P, .leaf Q) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q) ∧
      FreshCheckpoints.FreshExtension K d (.leaf P, T) (.leaf P, .leaf Q) ∧
      ∀ x ∈ P.position.decorated, x < Q.position.ordinary.getLastD 0 := by
  have hH := hK.mono hKH
  obtain ⟨R, a, hs, hb, ha⟩ := respond_on hK hKH B .inside true T (.leaf P) hblue d
  obtain ⟨v, hv, hvf⟩ := FreshCheckpoints.response_suffix R a
    (fun x hx ↦ (ha x hx).1) (fun x hx ↦ (ha x hx).2)
  have hf : FreshCheckpoints.FreshExtension K d (.leaf P, T) (.leaf P, R.result a) :=
    ⟨[], v, by simp, hv, by simp, hvf⟩
  change ConservativeRuns.Step K (GraphPayoff.payoff B .inside)
    (.leaf P, T) (.leaf P, R.result a) at hs
  change RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, R.result a)) true at hb
  cases he : R.result a with
  | initial =>
    have hmove := R.step a
    rw [he] at hmove
    cases hmove
  | complete C =>
    rw [he] at hb
    exact (hP (EndpointOrder.leaf_complete_slots_empty hH B .inside P C hb).1).elim
  | leaf Q =>
    rw [he] at hs hb hf
    refine ⟨Q, Relation.ReflTransGen.single hs, hb,
      handoff_after_right hH B .inside (.leaf P, T) R a Q he hb, hf, ?_⟩
    intro x hx
    have hlast := response_endpoint R a
    rw [he] at hlast
    exact (pairBound_left (.leaf P, T) hx).trans_lt hlast
  | body D =>
    rw [he] at hs hb hf
    have hc := ReplaySources.body_command B .inside true D P hb
    obtain ⟨k, A, hs', hb', hh', hA⟩ := respond_body_on hK hKH B .inside true D (.leaf P) hc d
    have hf' : FreshCheckpoints.FreshExtension K d
        (.leaf P, .body D) (.leaf P, .leaf (applyBody D A)) := by
      refine ⟨[], A.position.size :: A.position.entries, by simp, ?_, by simp, ?_⟩
      · exact BodyResponses.setup_ordinary A
      · intro x hx
        exact hA x (List.mem_append_right _ hx)
    have hsB : ConservativeRuns.Step K (GraphPayoff.payoff B .inside)
        (.leaf P, .body D) (.leaf P, .leaf (applyBody D A)) := hs'
    have hbefore : ∀ x ∈ P.position.decorated,
        x < (applyBody D A).position.ordinary.getLastD 0 := by
      intro x hx
      generalize hV : (State.leaf P, State.body D) = V at hsB
      generalize hW : (State.leaf P, State.leaf (applyBody D A)) = W at hsB
      cases hsB with
      | left n R hs hR a ha hg =>
        have heq := (congrArg Prod.snd hV).trans (congrArg Prod.snd hW).symm
        cases heq
      | right n R hs hR a ha hg =>
        have hleft := congrArg Prod.fst hV
        have hright := congrArg Prod.snd hW
        dsimp only at hleft hright
        have hlast := response_endpoint R a
        rw [← hright] at hlast
        exact (pairBound_left _ (hleft ▸ hx)).trans_lt hlast
    exact ⟨applyBody D A, Relation.ReflTransGen.tail (Relation.ReflTransGen.single hs) hs',
      hb', hh', FreshCheckpoints.fresh_trans hf hf', hbefore⟩

theorem critical_pair {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (S T : State) (hS : Early S)
    (hXS : ExactSlots.Exact S) (hXT : ExactSlots.Exact T)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (S, T)) true)
    (hready : Critical S → RightBlue H (GraphPayoff.payoff B .inside) (S, T)) (d : ℕ) :
    ∃ P Q : Pending, (∃ c : ℕ, P.roots = [c] ∧ P.leaves = []) ∧
      ExactSlots.Exact (.leaf P) ∧ ExactSlots.Exact (.leaf Q) ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B .inside) (S, T) (.leaf P, .leaf Q) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q) ∧
      FreshCheckpoints.FreshExtension K d (S, T) (.leaf P, .leaf Q) ∧
      (∀ x ∈ P.position.decorated, x < Q.position.ordinary.getLastD 0) ∧
      P.position.ordinary.getLastD 0 < Q.position.ordinary.getLastD 0 := by
  obtain ⟨P, U, c, hR, hL, hr, hb, hh, hf⟩ := stop_handoff hK hKH B S T hS hblue hready d
  have hP : P.roots ≠ [] := by rw [hR]; simp
  obtain ⟨Q, hr', hb', hh', hf', hbefore⟩ := right_handoff hK hKH B P U hP hh d
  have hrun := hr.trans hr'
  refine ⟨P, Q, ⟨c, hR, hL⟩, ExactSlots.run_exact_left hrun hXS,
    ExactSlots.run_exact_right hrun hXT, hrun, hb', hh',
    FreshCheckpoints.fresh_trans hf hf', hbefore, ?_⟩
  apply hbefore
  apply P.position.ordinary_sublist.subset
  have hne : P.position.ordinary ≠ [] := by simp [Position.ordinary, Stem.ordinary]
  simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne,
    Option.getD_some] using List.getLast_mem hne

end Erdos118.FreshCriticalCheckpoint
