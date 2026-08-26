import ErdosProblems.Erdos118.BlueRuns

/-!
Alphabet support and completed endpoints along concrete runs. Outside blue
plays cannot complete the second word first, and blue pending states against
a completed word have no unused slots. No triangle synchronization is assumed.
-/

namespace Erdos118.EndpointOrder

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame BlueRuns

theorem run_supported {H : Set ℕ} {payoff : Completed → Completed → Bool}
    {S T : State × State} (h : ConservativeRuns.Run H payoff S T)
    (hS : (∀ x ∈ S.1.decorated, x ∈ H) ∧ (∀ x ∈ S.2.decorated, x ∈ H)) :
    (∀ x ∈ T.1.decorated, x ∈ H) ∧ (∀ x ∈ T.2.decorated, x ∈ H) := by
  induction h with
  | refl => exact hS
  | tail hprev hstep ih =>
    cases hstep with
    | left n R hs hR a haH hlarge =>
      obtain ⟨d, hd, hsupport⟩ := R.suffix a
      refine ⟨?_, ih.2⟩
      intro x hx
      rw [hd] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ih.1 x hx
      · exact haH (hsupport ▸ List.mem_toFinset.mpr hx)
    | right n R hs hR a haH hlarge =>
      obtain ⟨d, hd, hsupport⟩ := R.suffix a
      refine ⟨ih.1, ?_⟩
      intro x hx
      rw [hd] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ih.2 x hx
      · exact haH (hsupport ▸ List.mem_toFinset.mpr hx)

theorem completed_ordinary_eq_of_prefix (S T : Completed)
    (h : S.stem.ordinary <+: T.stem.ordinary) : S.stem.ordinary = T.stem.ordinary := by
  have hp : word (S.stem.toGood S.full).1 <+: word (T.stem.toGood T.full).1 := by
    rw [Stem.toGood_word, Stem.toGood_word]
    exact h
  have he := WordResponses.word_prefix_rigid hp
  exact (S.stem.toGood_word S.full).symm.trans ((congrArg word he).trans
    (T.stem.toGood_word T.full))

theorem completed_endpoint_eq_of_prefix (S T : Completed)
    (h : S.stem.ordinary <+: T.stem.ordinary) :
    GraphPayoff.endpoint S.stem = GraphPayoff.endpoint T.stem := by
  have he := completed_ordinary_eq_of_prefix S T h
  simp only [GraphPayoff.endpoint, he]

theorem ordinary_le_endpoint (S : Stem) {x : ℕ} (hx : x ∈ S.ordinary) :
    x ≤ GraphPayoff.endpoint S :=
  ((S.increasing.sublist S.ordinary_sublist).imp Nat.le_of_lt).rel_getLast hx

theorem outside_incomplete_complete_not_blue {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph G) (S : State) (T : Completed)
    (hS : ¬ ∃ U : Completed, S = .complete U) :
    ¬ RamseyGame.Outcome H (GraphPayoff.game B .outside (S, .complete T)) true := by
  intro hblue
  have hnone : terminalPayoff (GraphPayoff.payoff B .outside) (S, .complete T) = none := by
    cases S <;> simp_all [terminalPayoff]
  rcases blue_command (GraphPayoff.payoff B .outside) (S, .complete T) hnone hblue with hl | hr
  · obtain ⟨n, R, _, _, b, hb⟩ := hl
    obtain ⟨a, haH, hab⟩ := R.family.conservative_exists hH b
    obtain ⟨U, V, hrun, hpay⟩ := blue_completion hH (GraphPayoff.payoff B .outside) _ (hb a haH hab)
    obtain ⟨v, hv, hvne, hvlarge⟩ := SkippedCuts.response_ordinary_suffix R a
    obtain ⟨x, xs, hxv⟩ := List.exists_cons_of_ne_nil hvne
    have hxmem : x ∈ v := hxv ▸ List.mem_cons_self ..
    have heT : GraphPayoff.endpoint T.stem ∈ State.decorated (.complete T) :=
      T.stem.ordinary_sublist.subset (GraphPayoff.endpoint_mem T.stem)
    have hTx : GraphPayoff.endpoint T.stem < x :=
      (pairBound_right (S, .complete T) heT).trans_lt (hvlarge x hxmem)
    have hxnew : x ∈ (R.result a).ordinary := hv ▸ List.mem_append_right _ hxmem
    have hxU : x ∈ U.stem.ordinary := (SkippedCuts.run_extensions hrun).1.ordinary.subset hxnew
    have hends := completed_endpoint_eq_of_prefix T V (SkippedCuts.run_extensions hrun).2.ordinary
    have horient := ((GraphPayoff.payoff_true_iff B .outside U V).mp hpay).2.2.1
    change GraphPayoff.endpoint U.stem < GraphPayoff.endpoint V.stem at horient
    have hxend := ordinary_le_endpoint U.stem hxU
    omega
  · exact not_rightBlue_complete H (GraphPayoff.payoff B .outside) S T hr

theorem outside_right_root_blue {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph G) (S : State) (hS : ¬ ∃ U : Completed, S = .complete U)
    (hblue : RightBlue H (GraphPayoff.payoff B .outside) (S, .initial)) :
    ∃ k b : ℕ, ∀ a : (rootResponse k (pairBound (S, .initial))).family.members,
      (↑a.1 : Set ℕ) ⊆ H → (∀ x ∈ a.1, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B .outside
        (S, (rootResponse k (pairBound (S, .initial))).result a)) true := by
  obtain ⟨n, R, _, hR, b, hb⟩ := hblue
  cases n with
  | zero =>
    have he : R = wholeResponse (pairBound (S, .initial)) := Option.some.inj hR.symm
    subst R
    obtain ⟨a, haH, hab⟩ :=
      (wholeResponse (pairBound (S, .initial))).family.conservative_exists hH b
    exact (outside_incomplete_complete_not_blue hH B S _ hS (hb a haH hab)).elim
  | succ k =>
    have he : R = rootResponse k (pairBound (S, .initial)) := Option.some.inj hR.symm
    subst R
    exact ⟨k, b, hb⟩

theorem leaf_step_cases (P : Pending) (S : State) (h : DecisionStates.Step S (.leaf P)) :
    (∃ Q : Pending, S = .leaf Q) ∨ (∃ D : BodyDecision, S = .body D) ∨
      (P.roots = [] ∧ P.leaves = []) := by
  cases h with
  | leaf F j rest hF A => exact Or.inl ⟨_, rfl⟩
  | nextBody F c rest hR hL A => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | finish F hR hL A => exact Or.inr (Or.inr ⟨hR, hL⟩)

theorem leaf_complete_slots_empty {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (P : Pending) (T : Completed)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf P, .complete T)) true) :
    P.roots = [] ∧ P.leaves = [] := by
  rcases blue_command (GraphPayoff.payoff B o) (.leaf P, .complete T) rfl hblue with hl | hr
  · obtain ⟨n, R, _, _, b, hb⟩ := hl
    obtain ⟨a, haH, hab⟩ := R.family.conservative_exists hH b
    have hnext := hb a haH hab
    rcases leaf_step_cases P (R.result a) (R.step a) with ⟨Q, hQ⟩ | ⟨D, hD⟩ | hlast
    · rw [hQ] at hnext
      exact (not_rightBlue_complete H (GraphPayoff.payoff B o) (.leaf Q) T
        (handoff_after_left hH B o (.leaf P, .complete T) R a Q hQ hnext)).elim
    · rw [hD] at hnext
      exact (body_complete_not_blue hH B o D T hnext).elim
    · exact hlast
  · exact (not_rightBlue_complete H (GraphPayoff.payoff B o) (.leaf P) T hr).elim

theorem complete_leaf_slots_empty {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (T : Completed) (P : Pending)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.complete T, .leaf P)) true) :
    P.roots = [] ∧ P.leaves = [] := by
  rcases blue_command (GraphPayoff.payoff B o) (.complete T, .leaf P) rfl hblue with hl | hr
  · exact (not_leftBlue_complete H (GraphPayoff.payoff B o) T (.leaf P) hl).elim
  · obtain ⟨n, R, _, _, b, hb⟩ := hr
    obtain ⟨a, haH, hab⟩ := R.family.conservative_exists hH b
    have hnext := hb a haH hab
    rcases leaf_step_cases P (R.result a) (R.step a) with ⟨Q, hQ⟩ | ⟨D, hD⟩ | hlast
    · rw [hQ] at hnext
      exact (not_leftBlue_complete H (GraphPayoff.payoff B o) T (.leaf Q)
        (handoff_after_right hH B o (.complete T, .leaf P) R a Q hQ hnext)).elim
    · rw [hD] at hnext
      exact (complete_body_not_blue hH B o T D hnext).elim
    · exact hlast

end Erdos118.EndpointOrder
