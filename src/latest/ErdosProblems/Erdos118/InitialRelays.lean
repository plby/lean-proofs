import ErdosProblems.Erdos118.BlueRelays
import ErdosProblems.Erdos118.RightRelays

/-!
A right word's last selected leaf becomes a first left pending word in
a fresh game. The initial root certificate is fixed in advance and all
original responses use the same working alphabet.
-/

namespace Erdos118.InitialRelays

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses BoundaryRelays

theorem root_to_last_first_nonbody {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H) (b : ℕ)
    (hKb : ∀ x ∈ K, b < x) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    {k l : ℕ}
    (hrootBlue : ∀ A : RootResponses.Setup l,
      (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B o (.body (ofRoot A), .initial)) true)
    (A : RootResponses.Setup k) (hA : ∀ x ∈ A.stem.decorated, x ∈ H ∧ b < x)
    (C : Reserve A.stem.rootLabel A.stem.root l) (hC : ∀ x ∈ C.label, x ∈ H ∧ b < x)
    (S : State) (hS : ExactSlots.Exact S)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (S, .body (ofRoot A))) true) :
    ∃ P : Pending, ∃ U : State, ∃ Q : Pending,
      P.roots = [] ∧ P.leaves = [] ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (S, .body (ofRoot A)) (U, .leaf P) ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (U, .leaf P)) true ∧
      LeftBlue H (GraphPayoff.payoff B o) (U, .leaf P) ∧
      Q.position.ordinary = P.position.ordinary ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (.leaf Q, .initial)) true ∧
      RightBlue H (GraphPayoff.payoff B o) (.leaf Q, .initial) ∧
      (∀ D : BodyDecision, U ≠ .body D) := by
  obtain ⟨D, V, hR, hrun, hb⟩ := BlueCheckpoints.right_last_body hK hKH
    (GraphPayoff.payoff B o) S (ofRoot A) hblue
  obtain ⟨V', hready, _, hc⟩ := RightRelays.right_body_ready hK hKH B o V D hb
  have hV' : ∀ E : BodyDecision, V' ≠ .body E := by
    intro E he
    have hs := PreparedRelays.command_allowed B o true D V' hc
    simp [PreparedRelays.pair, allowedSide, he] at hs
  have hwhole := hrun.trans hready
  obtain ⟨hD, C', _, hsecond⟩ := BlueRelays.right_root_relay hKH b hKb B o
    hrootBlue A hA C hC S hS D V' hwhole hR
  let E := ofRoot (rootAtLastBody D hD hR C')
  have hleft : LeftBlue H (GraphPayoff.payoff B o) (.body E, .initial) := by
    rcases blue_command (GraphPayoff.payoff B o) (.body E, .initial) rfl hsecond with hl | hr
    · exact hl
    · obtain ⟨n, R, hs, _⟩ := hr
      simp [allowedSide] at hs
  obtain ⟨k', A', Z, hs, hb', hh, _⟩ := PreparedRelays.prepare hK hKH B o true false
    D E V' .initial hD hR C'.label C'.increasing C'.below rfl hc hleft 0
  let P₀ := applyBody D A'
  obtain ⟨P, U, hPR, hPL, hlast, hbP, hhP, hnonbody⟩ :=
    BlueCheckpoints.right_last_leaf_handoff_entry
    hK hKH B o V' (.leaf P₀) trivial hb' (fun _ ↦ hh)
  obtain ⟨W, _⟩ := PreparedRelays.carry_right_of_run Z P V' U hKH (GraphPayoff.payoff B o) hlast
  have hfire := PreparedRelays.fire (hK.mono hKH) W hPL
  refine ⟨P, U, applyBody E (W.setup hPL), hPR, hPL,
    hwhole.trans (Relation.ReflTransGen.head hs hlast), hbP, hhP,
    hfire.1, hfire.2.1, hfire.2.2, ?_⟩
  rcases hnonbody with rfl | h
  · exact hV'
  · exact h

theorem root_to_last_first {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H) (b : ℕ)
    (hKb : ∀ x ∈ K, b < x) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    {k l : ℕ}
    (hrootBlue : ∀ A : RootResponses.Setup l,
      (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B o (.body (ofRoot A), .initial)) true)
    (A : RootResponses.Setup k) (hA : ∀ x ∈ A.stem.decorated, x ∈ H ∧ b < x)
    (C : Reserve A.stem.rootLabel A.stem.root l) (hC : ∀ x ∈ C.label, x ∈ H ∧ b < x)
    (S : State) (hS : ExactSlots.Exact S)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (S, .body (ofRoot A))) true) :
    ∃ P : Pending, ∃ U : State, ∃ Q : Pending,
      P.roots = [] ∧ P.leaves = [] ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (S, .body (ofRoot A)) (U, .leaf P) ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (U, .leaf P)) true ∧
      LeftBlue H (GraphPayoff.payoff B o) (U, .leaf P) ∧
      Q.position.ordinary = P.position.ordinary ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (.leaf Q, .initial)) true ∧
      RightBlue H (GraphPayoff.payoff B o) (.leaf Q, .initial) := by
  obtain ⟨P, U, Q, hPR, hPL, hrun, hb, hh, hQord, hQb, hQh, _⟩ :=
    root_to_last_first_nonbody hK hKH b hKb B o hrootBlue A hA C hC S hS hblue
  exact ⟨P, U, Q, hPR, hPL, hrun, hb, hh, hQord, hQb, hQh⟩

end Erdos118.InitialRelays
