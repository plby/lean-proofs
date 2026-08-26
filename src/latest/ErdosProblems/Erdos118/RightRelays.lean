import ErdosProblems.Erdos118.PreparedRelays
import ErdosProblems.Erdos118.BlueCheckpoints

/-!
The shared word lies on the right of both games. Its second-game root
command is fixed before the original root is chosen. The original game
then reaches its last right leaf with a first right leaf in the new game.
-/

namespace Erdos118.RightRelays

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses BoundaryRelays

private theorem right_body_command {H : Set ℕ} (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (S : State) (D : BodyDecision)
    (hS : ¬ ∃ E : BodyDecision, S = .body E)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (S, .body D)) true) :
    RightBlue H (GraphPayoff.payoff B o) (S, .body D) := by
  have hn : terminalPayoff (GraphPayoff.payoff B o) (S, .body D) = none := by
    cases S <;> rfl
  rcases blue_command (GraphPayoff.payoff B o) (S, .body D) hn hblue with hl | hr
  · obtain ⟨n, R, hs, _⟩ := hl
    cases S <;> simp_all [allowedSide]
  · exact hr

theorem right_body_ready {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (S : State) (D : BodyDecision)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (S, .body D)) true) :
    ∃ U : State, ConservativeRuns.Run K (GraphPayoff.payoff B o) (S, .body D) (U, .body D) ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (U, .body D)) true ∧
      RightBlue H (GraphPayoff.payoff B o) (U, .body D) := by
  by_cases hS : ∃ E : BodyDecision, S = .body E
  · obtain ⟨E, rfl⟩ := hS
    have hl : LeftBlue H (GraphPayoff.payoff B o) (.body E, .body D) := by
      rcases blue_command (GraphPayoff.payoff B o) (.body E, .body D) rfl hblue with hl | hr
      · exact hl
      · obtain ⟨n, R, hs, _⟩ := hr
        simp [allowedSide] at hs
    obtain ⟨k, A, hs, hb, _, _⟩ :=
      PreparedRelays.respond_body_on hK hKH B o false E (.body D) hl 0
    exact ⟨.leaf (applyBody E A), Relation.ReflTransGen.single hs, hb,
      right_body_command B o _ D (by simp) hb⟩
  · exact ⟨S, Relation.ReflTransGen.refl, hblue, right_body_command B o S D hS hblue⟩

theorem root_relay {H K : Set ℕ} (hKH : K ⊆ H) (b : ℕ)
    (hKb : ∀ x ∈ K, b < x) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (T : Pending) {k l : ℕ}
    (hrootBlue : ∀ A : RootResponses.Setup l,
      (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B o (.leaf T, .body (ofRoot A))) true)
    (A : RootResponses.Setup k) (hA : ∀ x ∈ A.stem.decorated, x ∈ H ∧ b < x)
    (C : Reserve A.stem.rootLabel A.stem.root l) (hC : ∀ x ∈ C.label, x ∈ H ∧ b < x)
    (S U : State) (D : BodyDecision)
    (hrun : ConservativeRuns.Run K (GraphPayoff.payoff B o)
      (S, .body (ofRoot A)) (U, .body D)) (hR : D.roots = []) :
    ∃ hD : ExactSlots.Exact (.body D), ∃ C' : Reserve D.stem.rootLabel D.stem.root l,
      C'.label = C.label ∧ RamseyGame.Outcome H (GraphPayoff.game B o
        (.leaf T, .body (ofRoot (rootAtLastBody D hD hR C')))) true := by
  have hD := ExactSlots.run_exact_right hrun
    (ExactSlots.step_exact (DecisionStates.Step.root A) trivial)
  have hext := (SkippedCuts.run_extensions hrun).2
  have hlabel : D.stem.rootLabel = A.stem.rootLabel :=
    Option.some.inj (hext.labels.root A.stem.rootLabel rfl)
  have hmarker : A.stem.root = D.stem.root := (List.cons_prefix_cons.mp hext.ordinary).1
  let C' : Reserve D.stem.rootLabel D.stem.root l :=
    { label := C.label, card := C.card, increasing := C.increasing
      first := by rw [hlabel]; exact C.first
      below := by intro x hx; rw [← hmarker]; exact C.below x hx
      shared := by intro x; rw [hlabel]; exact C.shared x }
  obtain ⟨w, v, _, hv, _, hvK⟩ := CompletionReplay.run_supported_suffixes hrun
  have hstem : ∀ x ∈ D.stem.ordinary, x ∈ H ∧ b < x := by
    change D.stem.ordinary = A.stem.ordinary ++ v at hv
    intro x hx
    rw [hv] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hA x (A.stem.ordinary_sublist.subset hx)
    · exact ⟨hKH (hvK x hx), hKb x (hvK x hx)⟩
  have hfresh := rootAtLastBody_supported D hD hR C' hC hstem
  exact ⟨hD, C', rfl, hrootBlue (rootAtLastBody D hD hR C')
    (fun x hx ↦ (hfresh x hx).1) (fun x hx ↦ (hfresh x hx).2)⟩

theorem last_body_relay {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (S : State) (T : Pending)
    (D : BodyDecision) (hD : ExactSlots.Exact (.body D)) (hR : D.roots = [])
    {l : ℕ} (C : Reserve D.stem.rootLabel D.stem.root l)
    (hfirst : RightBlue H (GraphPayoff.payoff B o) (S, .body D))
    (hsecond : RamseyGame.Outcome H (GraphPayoff.game B o
      (.leaf T, .body (ofRoot (rootAtLastBody D hD hR C)))) true) :
    ∃ P : Pending, ∃ U : State, ∃ Q : Pending,
      P.roots = [] ∧ P.leaves = [] ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (S, .body D) (U, .leaf P) ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (U, .leaf P)) true ∧
      LeftBlue H (GraphPayoff.payoff B o) (U, .leaf P) ∧
      Q.position.ordinary = P.position.ordinary ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (.leaf T, .leaf Q)) true := by
  let E := ofRoot (rootAtLastBody D hD hR C)
  have hsecondCommand := right_body_command B o (.leaf T) E (by simp) hsecond
  obtain ⟨k, A, Z, hs, hb, hh, _⟩ := PreparedRelays.prepare hK hKH B o true true
    D E S (.leaf T) hD hR C.label C.increasing C.below rfl hfirst hsecondCommand 0
  let P₀ := applyBody D A
  obtain ⟨P, U, hPR, hPL, hrun, hbP, hhP⟩ := BlueCheckpoints.right_last_leaf_handoff
    hK hKH B o S (.leaf P₀) trivial hb (fun _ ↦ hh)
  obtain ⟨W, _⟩ := PreparedRelays.carry_right_of_run Z P S U hKH (GraphPayoff.payoff B o) hrun
  have hfire := PreparedRelays.fire (hK.mono hKH) W hPL
  exact ⟨P, U, applyBody E (W.setup hPL), hPR, hPL,
    Relation.ReflTransGen.head hs hrun, hbP, hhP, hfire.1, hfire.2.1⟩

theorem root_to_last {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H) (b : ℕ)
    (hKb : ∀ x ∈ K, b < x) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (S T : Pending) {k l : ℕ}
    (hrootBlue : ∀ A : RootResponses.Setup l,
      (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B o (.leaf T, .body (ofRoot A))) true)
    (A : RootResponses.Setup k) (hA : ∀ x ∈ A.stem.decorated, x ∈ H ∧ b < x)
    (C : Reserve A.stem.rootLabel A.stem.root l) (hC : ∀ x ∈ C.label, x ∈ H ∧ b < x)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf S, .body (ofRoot A))) true) :
    ∃ P : Pending, ∃ U : State, ∃ Q : Pending,
      P.roots = [] ∧ P.leaves = [] ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (.leaf S, .body (ofRoot A)) (U, .leaf P) ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (U, .leaf P)) true ∧
      LeftBlue H (GraphPayoff.payoff B o) (U, .leaf P) ∧
      Q.position.ordinary = P.position.ordinary ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (.leaf T, .leaf Q)) true := by
  obtain ⟨D, V, hR, hrun, hb⟩ := BlueCheckpoints.right_last_body hK hKH
    (GraphPayoff.payoff B o) (.leaf S) (ofRoot A) hblue
  obtain ⟨V', hready, hb', hc⟩ := right_body_ready hK hKH B o V D hb
  have hwhole := hrun.trans hready
  obtain ⟨hD, C', _, hsecond⟩ :=
    root_relay hKH b hKb B o T hrootBlue A hA C hC (.leaf S) V' D hwhole hR
  obtain ⟨P, U, Q, hPR, hPL, hlast, hbP, hhP, hord, hblueQ⟩ :=
    last_body_relay hK hKH B o V' T D hD hR C' hc hsecond
  exact ⟨P, U, Q, hPR, hPL, hwhole.trans hlast, hbP, hhP, hord, hblueQ⟩

end Erdos118.RightRelays
