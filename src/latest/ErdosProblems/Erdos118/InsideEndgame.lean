import ErdosProblems.Erdos118.PreparedRelays

/-!
The inside game must complete its right word first. At a last left leaf,
the only possible blue command finishes a right word that is also last.
This does not assert the inside triangle theorem.
-/

namespace Erdos118.InsideEndgame

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns

theorem complete_incomplete_not_blue {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph G) (S : Completed) (T : State)
    (hT : ¬ ∃ U : Completed, T = .complete U) :
    ¬ RamseyGame.Outcome H (GraphPayoff.game B .inside (.complete S, T)) true := by
  intro hblue
  have hn : terminalPayoff (GraphPayoff.payoff B .inside) (.complete S, T) = none := by
    cases T <;> simp_all [terminalPayoff]
  rcases blue_command (GraphPayoff.payoff B .inside) (.complete S, T) hn hblue with hl | hr
  · exact not_leftBlue_complete H (GraphPayoff.payoff B .inside) S T hl
  · obtain ⟨n, R, _, _, b, hb⟩ := hr
    obtain ⟨a, haH, hab⟩ := R.family.conservative_exists hH b
    obtain ⟨U, V, hrun, hpay⟩ := blue_completion hH (GraphPayoff.payoff B .inside) _
      (hb a haH hab)
    obtain ⟨v, hv, hvne, hvlarge⟩ := SkippedCuts.response_ordinary_suffix R a
    obtain ⟨x, xs, hxv⟩ := List.exists_cons_of_ne_nil hvne
    have hxmem : x ∈ v := hxv ▸ List.mem_cons_self ..
    have heS : GraphPayoff.endpoint S.stem ∈ State.decorated (.complete S) :=
      S.stem.ordinary_sublist.subset (GraphPayoff.endpoint_mem S.stem)
    have hSx : GraphPayoff.endpoint S.stem < x :=
      (pairBound_left (.complete S, T) heS).trans_lt (hvlarge x hxmem)
    have hxnew : x ∈ (R.result a).ordinary := hv ▸ List.mem_append_right _ hxmem
    have hxV : x ∈ V.stem.ordinary := (SkippedCuts.run_extensions hrun).2.ordinary.subset hxnew
    have hends := EndpointOrder.completed_endpoint_eq_of_prefix S U
      (SkippedCuts.run_extensions hrun).1.ordinary
    have horient := ((GraphPayoff.payoff_true_iff B .inside U V).mp hpay).2.2.1
    change GraphPayoff.endpoint V.stem < GraphPayoff.endpoint U.stem at horient
    have hxend := EndpointOrder.ordinary_le_endpoint V.stem hxV
    omega

theorem last_left_not_leftBlue {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (P : Pending) (T : State) (hR : P.roots = []) (hL : P.leaves = [])
    (hT : ¬ ∃ C : Completed, T = .complete C) :
    ¬ LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, T) := by
  intro hblue
  obtain ⟨n, R, _, hresp, b, hb⟩ := hblue
  let c := pairBound (.leaf P, T)
  have he : R = finishResponse P hR hL c :=
    Option.some.inj (hresp.symm.trans (SecondWhole.finish_selector P hR hL c n))
  subst R
  obtain ⟨a, haH, hab⟩ := (finishResponse P hR hL c).family.conservative_exists hH b
  exact complete_incomplete_not_blue hH B _ T hT (hb a haH hab)

theorem last_body_not_blue {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (P : Pending) (D : BodyDecision) (hR : P.roots = []) (hL : P.leaves = []) :
    ¬ RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .body D)) true := by
  intro hblue
  rcases blue_command (GraphPayoff.payoff B .inside) (.leaf P, .body D) rfl hblue with hl | hr
  · exact last_left_not_leftBlue hH B P (.body D) hR hL (by simp) hl
  · obtain ⟨k, A, _, _, hh, _⟩ :=
      PreparedRelays.respond_body hH B .inside true D (.leaf P) hr 0
    exact last_left_not_leftBlue hH B P (.leaf (applyBody D A)) hR hL (by simp) hh

theorem last_left_right_command {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (P : Pending) (T : State) (hR : P.roots = []) (hL : P.leaves = [])
    (hT : T ≠ .initial)
    (hblue : RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, T)) :
    ∃ Q : Pending, T = .leaf Q ∧ Q.roots = [] ∧ Q.leaves = [] := by
  cases T with
  | initial => exact (hT rfl).elim
  | complete C => exact (not_rightBlue_complete H (GraphPayoff.payoff B .inside)
      (.leaf P) C hblue).elim
  | body D =>
    obtain ⟨k, A, _, _, hh, _⟩ :=
      PreparedRelays.respond_body hH B .inside true D (.leaf P) hblue 0
    exact (last_left_not_leftBlue hH B P (.leaf (applyBody D A)) hR hL (by simp) hh).elim
  | leaf Q =>
    obtain ⟨n, R, _, _, b, hb⟩ := hblue
    obtain ⟨a, haH, hab⟩ := R.family.conservative_exists hH b
    have hnext := hb a haH hab
    rcases EndpointOrder.leaf_step_cases Q (R.result a) (R.step a) with
      ⟨U, hU⟩ | ⟨D, hD⟩ | hlast
    · rw [hU] at hnext
      have hh := handoff_after_right hH B .inside (.leaf P, .leaf Q) R a U hU hnext
      exact (last_left_not_leftBlue hH B P (.leaf U) hR hL (by simp) hh).elim
    · rw [hD] at hnext
      exact (last_body_not_blue hH B P D hR hL hnext).elim
    · exact ⟨Q, rfl, hlast⟩

theorem last_left_rightBlue {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (P Q : Pending) (hR : P.roots = []) (hL : P.leaves = [])
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true) :
    RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q) := by
  rcases blue_command (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q) rfl hblue with hl | hr
  · exact (last_left_not_leftBlue hH B P (.leaf Q) hR hL (by simp) hl).elim
  · exact hr

theorem last_right_command_left_last {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (P T : Pending) (hTR : T.roots = []) (hTL : T.leaves = [])
    (hblue : RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf T)) :
    P.roots = [] ∧ P.leaves = [] := by
  obtain ⟨n, R, _, hresp, b, hb⟩ := hblue
  let c := pairBound (.leaf P, .leaf T)
  have he : R = finishResponse T hTR hTL c :=
    Option.some.inj (hresp.symm.trans (SecondWhole.finish_selector T hTR hTL c n))
  subst R
  obtain ⟨a, haH, hab⟩ := (finishResponse T hTR hTL c).family.conservative_exists hH b
  exact EndpointOrder.leaf_complete_slots_empty hH B .inside P _ (hb a haH hab)

theorem advance_last_left {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (P T : Pending) (hPR : P.roots = [])
    (hTR : T.roots = []) (hTL : T.leaves = [])
    (hblue : LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf T)) :
    ∃ Q : Pending, Q.roots = [] ∧ Q.leaves = [] ∧
      ConservativeRuns.Step K (GraphPayoff.payoff B .inside) (.leaf P, .leaf T) (.leaf Q, .leaf T) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf Q, .leaf T)) true ∧
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf Q, .leaf T) := by
  have hH := hK.mono hKH
  obtain ⟨R, a, hs, hb, _⟩ :=
    PreparedRelays.respond_on hK hKH B .inside false (.leaf P) (.leaf T) hblue 0
  rcases BoundaryRelays.run_last_body_left_cases P (.leaf T) (R.result a) (.leaf T) hPR
      (Relation.ReflTransGen.single hs) with ⟨Q, hQ, _⟩ | ⟨C, hC⟩
  · change RamseyGame.Outcome H (GraphPayoff.game B .inside (R.result a, .leaf T)) true at hb
    rw [hQ] at hb
    have hh := handoff_after_left hH B .inside (.leaf P, .leaf T) R a Q hQ hb
    have hlast := last_right_command_left_last hH B Q T hTR hTL hh
    refine ⟨Q, hlast.1, hlast.2, ?_, hb, hh⟩
    change ConservativeRuns.Step K (GraphPayoff.payoff B .inside)
      (.leaf P, .leaf T) (R.result a, .leaf T) at hs
    rwa [hQ] at hs
  · change RamseyGame.Outcome H (GraphPayoff.game B .inside (R.result a, .leaf T)) true at hb
    rw [hC] at hb
    exact (complete_incomplete_not_blue hH B C (.leaf T) (by simp) hb).elim

theorem penultimate_left {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (P T : Pending) (hPR : P.roots = []) (hTR : T.roots = []) (hTL : T.leaves = [])
    (hblue : LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf T)) :
    ∃ j : ℕ, P.leaves = [j] := by
  obtain ⟨Q, hQR, hQL, hs, _, _⟩ := advance_last_left hH (Set.Subset.rfl) B P T hPR hTR hTL hblue
  have hpair := hs.pairStep
  cases hpair with
  | left U hmove =>
    cases hmove with
    | leaf F j rest hF A =>
      change rest = [] at hQL
      exact ⟨j, hF.trans (congrArg (List.cons j) hQL)⟩
  | right U hmove =>
    exact (last_left_not_leftBlue hH B P (.leaf T) hPR hQL (by simp) hblue).elim

theorem last_right_body_setups {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (D : BodyDecision) (T : Pending) (hTR : T.roots = []) (hTL : T.leaves = [])
    (hblue : LeftBlue H (GraphPayoff.payoff B .inside) (.body D, .leaf T)) :
    D.roots = [] ∧ ∃ b : ℕ, ∀ A : BodyResponses.Setup D.stem 0,
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
      (∀ x ∈ BodyResponses.newWord A.position, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf (applyBody D A), .leaf T)) true := by
  obtain ⟨k, b, hb⟩ := BlueReservations.left_body_setups
    (GraphPayoff.payoff B .inside) D (.leaf T) hblue
  let c := pairBound (.body D, .leaf T)
  obtain ⟨A, hA⟩ := BodyResponses.setup_above D.stem k D.room hH (max b c)
  have hAc : ∀ x ∈ BodyResponses.newWord A.position, c < x :=
    fun x hx ↦ (le_max_right _ _).trans_lt (hA x hx).2
  have hnext := hb A (fun x hx ↦ (hA x hx).1)
    (fun x hx ↦ (le_max_left _ _).trans_lt (hA x hx).2)
  have hh := handoff_after_left hH B .inside (.body D, .leaf T) (bodyResponse D k c)
    (ReservedResponses.bodyMember D c A hAc) (applyBody D A)
    (ReservedResponses.bodyMember_result D c A hAc) hnext
  have hlast := last_right_command_left_last hH B (applyBody D A) T hTR hTL hh
  have hk : k = 0 := by
    have hlen := congrArg List.length hlast.2
    change A.position.label.tail.length = 0 at hlen
    rw [List.length_tail, A.label_length] at hlen
    omega
  subst k
  exact ⟨hlast.1, b, hb⟩

theorem last_right_body_roots {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (D : BodyDecision) (T : Pending) (hTR : T.roots = []) (hTL : T.leaves = [])
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.body D, .leaf T)) true) :
    D.roots = [] := by
  rcases blue_command (GraphPayoff.payoff B .inside) (.body D, .leaf T) rfl hblue with hl | hr
  · exact (last_right_body_setups hH B D T hTR hTL hl).1
  · obtain ⟨n, R, hs, _⟩ := hr
    simp [allowedSide] at hs

theorem last_right_pending_cases {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (P T : Pending) (hTR : T.roots = []) (hTL : T.leaves = [])
    (hblue : LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf T)) :
    (P.roots = [] ∧ ∃ j : ℕ, P.leaves = [j]) ∨
      (P.leaves = [] ∧ ∃ c : ℕ, P.roots = [c]) := by
  obtain ⟨R, a, _, hb, _⟩ :=
    PreparedRelays.respond_on hH Set.Subset.rfl B .inside false (.leaf P) (.leaf T) hblue 0
  change RamseyGame.Outcome H (GraphPayoff.game B .inside (R.result a, .leaf T)) true at hb
  have hmove := R.step a
  generalize he : R.result a = S at hmove hb
  cases hmove with
  | leaf F j rest hF A =>
    have hh := handoff_after_left hH B .inside (.leaf P, .leaf T) R a
      (LeafResponses.toPending P j rest hF A) he hb
    have hlast := last_right_command_left_last hH B
      (LeafResponses.toPending P j rest hF A) T hTR hTL hh
    exact Or.inl ⟨hlast.1, j, hF.trans (congrArg (List.cons j) hlast.2)⟩
  | nextBody F c rest hR hL A =>
    have hlast := last_right_body_roots hH B (ofStem P c rest hR A) T hTR hTL hb
    exact Or.inr ⟨hL, c, hR.trans (congrArg (List.cons c) hlast)⟩
  | finish F hR hL A =>
    exact (complete_incomplete_not_blue hH B (ofCompletion P A) (.leaf T) (by simp) hb).elim

end Erdos118.InsideEndgame
