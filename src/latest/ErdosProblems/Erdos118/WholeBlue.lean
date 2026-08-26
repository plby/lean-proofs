import ErdosProblems.Erdos118.BlueRuns

/-!
The initial whole-completion blue branch gives the concrete two-completion
game and hence a triangle. For a triangle-free graph the remaining initial
blue command must choose a positive root-label size.
-/

namespace Erdos118.WholeBlue

open Negative Negative.Exact LabelledExtensions DecisionStates AdaptiveGame BlueRuns

def wholeMember (b : ℕ) (s : WordResponses.family) (h : ∀ x ∈ s.1, b < x) :
    (wholeResponse b).family.members := ⟨s.1, s.2, h⟩

theorem wholeMember_result (b : ℕ) (s : WordResponses.family) (h : ∀ x ∈ s.1, b < x) :
    (wholeResponse b).result (wholeMember b s h) =
      .complete (ofGood (WordResponses.supportEquiv.symm s)) := rfl

theorem plain_vertex (s : G) : GraphPayoff.vertex (ofGood s) = s := by
  apply Subtype.ext
  simp [GraphPayoff.vertex, ofGood, Stem.toGood, List.map_map,
    Function.comp_def, LabelledExtensions.plain]

def WholeFirstBlue (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation) : Prop :=
  ∃ b : ℕ, ∀ a : (wholeResponse 0).family.members,
    (↑a.1 : Set ℕ) ⊆ H → (∀ x ∈ a.1, b < x) →
    RamseyGame.Outcome H (GraphPayoff.game B o ((wholeResponse 0).result a, .initial)) true

theorem whole_first_pairGame {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (hfirst : WholeFirstBlue H B o) :
    RamseyGame.Outcome H (RamseyGame.pairGame WordResponses.responseFamily
      (B.comap WordResponses.supportEquiv.symm)) true := by
  classical
  obtain ⟨b₀, hb₀⟩ := hfirst
  unfold RamseyGame.pairGame
  apply RamseyGame.Outcome.response _ _ b₀ true
  intro s hsH hslarge
  have hs0 : ∀ x ∈ s.1, 0 < x := fun x hx ↦ (Nat.zero_le b₀).trans_lt (hslarge x hx)
  have hfirstS := hb₀ (wholeMember 0 s hs0) hsH hslarge
  rw [wholeMember_result 0 s hs0] at hfirstS
  let S := ofGood (WordResponses.supportEquiv.symm s)
  obtain ⟨bS, hbS⟩ := complete_initial_whole_blue hH B o S hfirstS
  let c := pairBound (.complete S, .initial)
  apply RamseyGame.Outcome.response _ _ (max bS c) true
  intro t htH htlarge
  have htc : ∀ x ∈ t.1, c < x := fun x hx ↦ (le_max_right _ _).trans_lt (htlarge x hx)
  have htb : ∀ x ∈ t.1, bS < x := fun x hx ↦ (le_max_left _ _).trans_lt (htlarge x hx)
  have hsecond := hbS (wholeMember c t htc) htH htb
  rw [wholeMember_result c t htc, GraphPayoff.game, AdaptiveGame.game_complete] at hsecond
  have hpay := RamseyGame.outcome_leaf_iff.mp hsecond
  have hedge := ((GraphPayoff.payoff_true_iff B o S
    (ofGood (WordResponses.supportEquiv.symm t))).mp hpay).2.2.2
  have hedge' : (B.comap WordResponses.supportEquiv.symm).Adj s t := by
    change B.Adj (WordResponses.supportEquiv.symm s) (WordResponses.supportEquiv.symm t)
    simpa only [S, plain_vertex] using hedge
  exact RamseyGame.outcome_leaf_iff.mpr (decide_eq_true hedge')

theorem whole_first_triangle {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (hfirst : WholeFirstBlue H B o) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  obtain ⟨s, t, u, hst, hsu, htu⟩ := RamseyGame.pairGame_triangle
    WordResponses.responseFamily (B.comap WordResponses.supportEquiv.symm) hH
    (whole_first_pairGame hH B o hfirst)
  exact ⟨WordResponses.supportEquiv.symm s, WordResponses.supportEquiv.symm t,
    WordResponses.supportEquiv.symm u, hst, hsu, htu⟩

theorem initial_root_blue {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph G) (hB : B.CliqueFree 3) (o : GraphPayoff.Orientation)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.initial, .initial)) true) :
    ∃ k b : ℕ, ∀ a : (rootResponse k 0).family.members,
      (↑a.1 : Set ℕ) ⊆ H → (∀ x ∈ a.1, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B o ((rootResponse k 0).result a, .initial)) true := by
  rcases blue_command (GraphPayoff.payoff B o) (.initial, .initial) rfl hblue with hl | hr
  · obtain ⟨n, R, _, hR, b, hb⟩ := hl
    cases n with
    | zero =>
      have he : R = wholeResponse 0 := Option.some.inj hR.symm
      subst R
      obtain ⟨s, t, u, hst, hsu, htu⟩ := whole_first_triangle hH B o ⟨b, hb⟩
      exact (hB {s, t, u} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hst, hsu, htu⟩)).elim
    | succ k =>
      have he : R = rootResponse k 0 := Option.some.inj hR.symm
      subst R
      exact ⟨k, b, hb⟩
  · obtain ⟨n, R, hs, _⟩ := hr
    simp [allowedSide] at hs

end Erdos118.WholeBlue
