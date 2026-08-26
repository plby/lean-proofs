import ErdosProblems.Erdos118.AlignedEndpoint
import ErdosProblems.Erdos118.ManagedCritical

/-! An actual fresh run to both penultimate-body last leaves, allowing
the right word to pass through earlier bodies before stopping. -/

namespace Erdos118.AlignedPenultimateRun

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns
open ManagedCritical (Early Critical early_step)

theorem right {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H) (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      InsideCounts.beforeLast S = InsideCounts.beforeLast T)
    (P Q : Pending) (hP : ExactSlots.Exact (.leaf P)) (hQ : ExactSlots.Exact (.leaf Q))
    (hroots : Q.roots ≠ [])
    (horder : P.position.ordinary.getLastD 0 < Q.position.ordinary.getLastD 0)
    (hb : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true)
    (hready : Critical (.leaf Q) →
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q)) (d : ℕ) :
    ∃ P' Q' : Pending, ∃ a c : ℕ,
      P'.roots = [a] ∧ P'.leaves = [] ∧ Q'.roots = [c] ∧ Q'.leaves = [] ∧
      ExactSlots.Exact (.leaf P') ∧ ExactSlots.Exact (.leaf Q') ∧
      P'.position.ordinary.getLastD 0 < Q'.position.ordinary.getLastD 0 ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B .inside)
        (.leaf P, .leaf Q) (.leaf P', .leaf Q') ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P', .leaf Q')) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P', .leaf Q') ∧
      FreshCheckpoints.FreshExtension K d (.leaf P, .leaf Q) (.leaf P', .leaf Q') := by
  have hH : H.Infinite := hK.mono hKH
  have hstep : ∀ V W : State × State, Early V.2 → ¬ Critical V.2 → PairStep W V → Early W.2 := by
    intro V W hV hn hs
    cases hs with
    | left U hstep => exact hV
    | right U hstep => exact early_step hV hn hstep
  have hterm : ∀ V : State × State, Early V.2 → ¬ Critical V.2 →
      terminalPayoff (GraphPayoff.payoff B .inside) V = none := by
    rintro ⟨X, Y⟩ hY _
    cases Y <;> cases X <;> simp_all [Early, terminalPayoff]
  obtain ⟨V, hr, hbV, _, hcrit, hentry, hf⟩ := FreshCheckpoints.blue_stop_above hK hKH
    (GraphPayoff.payoff B .inside) (fun V ↦ Early V.2) (fun V ↦ Critical V.2)
    hterm hstep d (.leaf P, .leaf Q) hroots hb
  have hh : LeftBlue H (GraphPayoff.payoff B .inside) V := by
    rcases hentry with rfl | ⟨W, _, hn, hs⟩
    · exact hready hcrit
    · cases hs with
      | left n R hs hR a ha hg => exact (hn hcrit).elim
      | right n R hs hR a ha hg =>
        cases he : R.result a with
        | initial => simp only [he, Critical] at hcrit
        | body D => simp only [he, Critical] at hcrit
        | complete C => simp only [he, Critical] at hcrit
        | leaf Q' =>
          rw [he] at hbV
          exact handoff_after_right hH B .inside W R a Q' he hbV
  have hentryData : V = (.leaf P, .leaf Q) ∨
      (∀ D : BodyDecision, V.1 ≠ .body D) ∧
        ∀ x ∈ V.1.decorated, x < V.2.ordinary.getLastD 0 := by
    rcases hentry with rfl | ⟨W, _, hn, hs⟩
    · exact Or.inl rfl
    · cases hs with
      | left n R hs hR a ha hg => exact (hn hcrit).elim
      | right n R hs hR a ha hg =>
        refine Or.inr ⟨?_, ?_⟩
        · intro D he
          change W.1 = .body D at he
          simp [allowedSide, he] at hs
        · intro x hx
          obtain ⟨v, hv, hvne, hvlarge⟩ := SkippedCuts.response_ordinary_suffix R a
          have hm : (R.result a).ordinary.getLastD 0 ∈ v := by
            rw [hv, List.getLastD_eq_getLast?, List.getLast?_append_of_ne_nil _ hvne,
              List.getLast?_eq_some_getLast hvne]
            exact List.getLast_mem hvne
          exact (pairBound_left W hx).trans_lt (hvlarge _ hm)
  obtain ⟨Y, X⟩ := V
  cases X with
  | initial => exact hcrit.elim
  | body D => exact hcrit.elim
  | complete C => exact hcrit.elim
  | leaf Q' =>
    obtain ⟨c, hQR, hQL⟩ := hcrit
    have hnotbody : ∀ D : BodyDecision, Y ≠ .body D := by
      rcases hentryData with he | ⟨hn, _⟩
      · have hY : Y = .leaf P := congrArg Prod.fst he
        intro D he'
        rw [hY] at he'
        cases he'
      · exact hn
    have hnotinitial : Y ≠ .initial := by
      have hm : P.position.stem.root ∈ Y.ordinary :=
        (SkippedCuts.run_extensions hr).1.ordinary.subset
          (by simp [State.ordinary, Position.ordinary, Stem.ordinary])
      intro he
      simp [he, State.ordinary] at hm
    cases Y with
    | initial => exact (hnotinitial rfl).elim
    | body D => exact (hnotbody D rfl).elim
    | complete C =>
      have he := (EndpointOrder.complete_leaf_slots_empty hH B .inside C Q' hbV).1
      rw [hQR] at he
      cases he
    | leaf P' =>
      have horder' : P'.position.ordinary.getLastD 0 < Q'.position.ordinary.getLastD 0 := by
        rcases hentryData with he | ⟨_, hlt⟩
        · have hPP : P' = P := State.leaf.inj (congrArg Prod.fst he)
          have hQQ : Q' = Q := State.leaf.inj (congrArg Prod.snd he)
          simpa only [hPP, hQQ] using horder
        · have hne : P'.position.ordinary ≠ [] := by simp [Position.ordinary, Stem.ordinary]
          have hm : P'.position.ordinary.getLastD 0 ∈ P'.position.ordinary := by
            rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
            exact List.getLast_mem hne
          exact hlt _ (P'.position.ordinary_sublist.subset hm)
      have hP' := ExactSlots.run_exact_left hr hP
      have hQ' := ExactSlots.run_exact_right hr hQ
      obtain ⟨a, ha, hl⟩ :=
        (AlignedEndpoint.critical_iff hH B hall P' Q' hP' hQ' horder' hbV).mpr ⟨c, hQR, hQL⟩
      exact ⟨P', Q', a, c, ha, hl, hQR, hQL, hP', hQ', horder', hr, hbV, hh, hf⟩

end Erdos118.AlignedPenultimateRun
