import ErdosProblems.Erdos118.AlignedEndpoint
import ErdosProblems.Erdos118.CurrentBody

/-! Reach both critical penultimate-body last leaves by an actual right
current-body run, proving the coordinate order from its actual entry. -/

namespace Erdos118.AlignedCurrentCheckpoint

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open BlueRuns

theorem right_critical {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      InsideCounts.beforeLast S = InsideCounts.beforeLast T)
    (P Q : Pending) (hP : ExactSlots.Exact (.leaf P)) (hQ : ExactSlots.Exact (.leaf Q))
    (c : ℕ) (hroots : Q.roots = [c])
    (horder : P.position.ordinary.getLastD 0 < Q.position.ordinary.getLastD 0)
    (hb : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true)
    (hready : Q.leaves = [] →
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q)) (d : ℕ) :
    ∃ P' Q' : Pending, ∃ a : ℕ, CurrentBody.SameBody Q Q' ∧
      P'.roots = [a] ∧ P'.leaves = [] ∧ Q'.roots = [c] ∧ Q'.leaves = [] ∧
      ExactSlots.Exact (.leaf P') ∧ ExactSlots.Exact (.leaf Q') ∧
      P'.position.ordinary.getLastD 0 < Q'.position.ordinary.getLastD 0 ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B .inside)
        (.leaf P, .leaf Q) (.leaf P', .leaf Q') ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P', .leaf Q')) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P', .leaf Q') ∧
      FreshCheckpoints.FreshExtension K d (.leaf P, .leaf Q) (.leaf P', .leaf Q') := by
  have hH : H.Infinite := hK.mono hKH
  obtain ⟨Q', Y, hsame, hlast, hr, hb', hh, hf, hentry⟩ :=
    CurrentBody.right_last_entry hK hKH B .inside Q (.leaf P) d hb hready
  have hQR : Q'.roots = [c] := hsame.roots.trans hroots
  have hnotbody : ∀ D : BodyDecision, Y ≠ .body D := by
    rcases hentry with he | ⟨hn, _⟩
    · have hY : Y = .leaf P := congrArg Prod.fst he
      intro D he'
      rw [hY] at he'
      cases he'
    · exact hn
  have hnotinitial : Y ≠ .initial := by
    have hmem : P.position.stem.root ∈ Y.ordinary :=
      (SkippedCuts.run_extensions hr).1.ordinary.subset
        (by simp [State.ordinary, Position.ordinary, Stem.ordinary])
    intro he
    simp [he, State.ordinary] at hmem
  cases Y with
  | initial => exact (hnotinitial rfl).elim
  | body D => exact (hnotbody D rfl).elim
  | complete C =>
    have he := (EndpointOrder.complete_leaf_slots_empty hH B .inside C Q' hb').1
    rw [hQR] at he
    cases he
  | leaf P' =>
    have horder' : P'.position.ordinary.getLastD 0 < Q'.position.ordinary.getLastD 0 := by
      rcases hentry with he | ⟨_, hlt⟩
      · have hPP : P' = P := State.leaf.inj (congrArg Prod.fst he)
        have hQQ : Q' = Q := State.leaf.inj (congrArg Prod.snd he)
        simpa only [hPP, hQQ] using horder
      · have hne : P'.position.ordinary ≠ [] := by
          simp [Position.ordinary, Stem.ordinary]
        have hmem : P'.position.ordinary.getLastD 0 ∈ P'.position.ordinary := by
          rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
          exact List.getLast_mem hne
        exact hlt _ (P'.position.ordinary_sublist.subset hmem)
    have hP' := ExactSlots.run_exact_left hr hP
    have hQ' := ExactSlots.run_exact_right hr hQ
    obtain ⟨a, ha, hl⟩ :=
      (AlignedEndpoint.critical_iff hH B hall P' Q' hP' hQ' horder' hb').mpr ⟨c, hQR, hlast⟩
    exact ⟨P', Q', a, hsame, ha, hl, hQR, hlast, hP', hQ', horder', hr, hb', hh, hf⟩

end Erdos118.AlignedCurrentCheckpoint
