import ErdosProblems.Erdos118.DeferredManaged

/-!
An actual blue run to the last leaf before the last selected body. The
opposite word retains its deferred initial replay and the left ordinary
word stays supported above the initial certificate's bound.
-/

namespace Erdos118.ManagedCritical

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays DeferredManaged
open ManagedRelays (Initial)

def Early : State → Prop
  | .body D => D.roots ≠ []
  | .leaf P => P.roots ≠ []
  | _ => False

def Critical : State → Prop
  | .leaf P => ∃ c : ℕ, P.roots = [c] ∧ P.leaves = []
  | _ => False

theorem early_before {S : State} (hS : Early S) : BlueCheckpoints.BeforeLastBody S := by
  cases S <;> simp_all [Early, BlueCheckpoints.BeforeLastBody]

theorem early_step {S T : State} (hS : Early S) (hn : ¬ Critical S)
    (hs : DecisionStates.Step T S) : Early T := by
  cases hs with
  | root A => exact hS.elim
  | whole s => exact hS.elim
  | body D A => exact hS
  | leaf P j rest hL A => exact hS
  | nextBody P c rest hR hL A =>
    change rest ≠ []
    intro he
    subst rest
    exact hn ⟨c, hR, hL⟩
  | finish P hR hL A => exact (hS hR).elim

theorem early_nonterminal (payoff : Completed → Completed → Bool)
    (S : State × State) (hS : Early S.1) : terminalPayoff payoff S = none := by
  obtain ⟨S, T⟩ := S
  cases S <;> cases T <;> simp_all [Early, terminalPayoff]

theorem stop_with_entry {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    (I : Initial H B .inside)
    (hfirst : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (FirstBodyRefinement.firstLabel S).length ≠ 1)
    (S : State × State) (hS : Early S.1) (M : Managed I S.2)
    (hf : ∀ x ∈ S.1.ordinary, x ∈ H ∧ I.bound < x)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside S) true) :
    ∃ T : State × State, ConservativeRuns.Run H (GraphPayoff.payoff B .inside) S T ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside T) true ∧
      Critical T.1 ∧ Nonempty (Managed I T.2) ∧
      (∀ x ∈ T.1.ordinary, x ∈ H ∧ I.bound < x) ∧
      (T = S ∨ ∃ U, ConservativeRuns.Run H (GraphPayoff.payoff B .inside) S U ∧
        ¬ Critical U.1 ∧ ConservativeRuns.Step H (GraphPayoff.payoff B .inside) U T) := by
  induction S using pairStep_wellFounded.induction with
  | h S ih =>
    by_cases hc : Critical S.1
    · exact ⟨S, Relation.ReflTransGen.refl, hblue, hc, ⟨M⟩, hf, Or.inl rfl⟩
    · rcases blue_command (GraphPayoff.payoff B .inside) S
        (early_nonterminal _ S hS) hblue with hl | hr
      · obtain ⟨R, a, hs, hb, ha⟩ :=
          PreparedRelays.respond hH B .inside false S.1 S.2 hl I.bound
        obtain ⟨T, hrun, hbT, hcrit, hM, hfT, hentry⟩ := ih (R.result a, S.2) hs.pairStep
          (early_step hS hc (R.step a)) M (response_ordinary_fresh R a hf ha) hb
        refine ⟨T, Relation.ReflTransGen.head hs hrun, hbT, hcrit, hM, hfT, ?_⟩
        rcases hentry with rfl | ⟨U, hrU, hnU, hsU⟩
        · exact Or.inr ⟨S, Relation.ReflTransGen.refl, hc, hs⟩
        · exact Or.inr ⟨U, Relation.ReflTransGen.head hs hrU, hnU, hsU⟩
      · obtain ⟨U, ⟨MU⟩, hs, hb⟩ :=
          DeferredManaged.respond_right hH I hfirst S.1 S.2 M (early_before hS) hr
        obtain ⟨T, hrun, hbT, hcrit, hM, hfT, hentry⟩ :=
          ih (S.1, U) hs.pairStep hS MU hf hb
        refine ⟨T, Relation.ReflTransGen.head hs hrun, hbT, hcrit, hM, hfT, ?_⟩
        rcases hentry with rfl | ⟨V, hrV, hnV, hsV⟩
        · exact Or.inr ⟨S, Relation.ReflTransGen.refl, hc, hs⟩
        · exact Or.inr ⟨V, Relation.ReflTransGen.head hs hrV, hnV, hsV⟩

theorem stop_handoff {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    (I : Initial H B .inside)
    (hfirst : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (FirstBodyRefinement.firstLabel S).length ≠ 1)
    (S T : State) (hS : Early S) (M : Managed I T)
    (hf : ∀ x ∈ S.ordinary, x ∈ H ∧ I.bound < x)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (S, T)) true)
    (hready : Critical S → RightBlue H (GraphPayoff.payoff B .inside) (S, T)) :
    ∃ P : Pending, ∃ U : State, ∃ c : ℕ,
      P.roots = [c] ∧ P.leaves = [] ∧ Nonempty (Managed I U) ∧
      ConservativeRuns.Run H (GraphPayoff.payoff B .inside) (S, T) (.leaf P, U) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, U)) true ∧
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, U) ∧
      (∀ x ∈ P.position.ordinary, x ∈ H ∧ I.bound < x) := by
  obtain ⟨V, hrun, hb, hcrit, hM, hfV, hentry⟩ :=
    stop_with_entry hH I hfirst (S, T) hS M hf hblue
  have hh : RightBlue H (GraphPayoff.payoff B .inside) V := by
    rcases hentry with rfl | ⟨W, _, hn, hs⟩
    · exact hready hcrit
    · cases hs with
      | left n R hs hR a haH hlarge =>
        cases he : R.result a with
        | initial => simp only [he, Critical] at hcrit
        | body D => simp only [he, Critical] at hcrit
        | complete C => simp only [he, Critical] at hcrit
        | leaf P =>
          rw [he] at hb
          exact handoff_after_left hH B .inside W R a P he hb
      | right n R hs hR a haH hlarge => exact (hn hcrit).elim
  obtain ⟨V, U⟩ := V
  cases V with
  | initial => exact hcrit.elim
  | body D => exact hcrit.elim
  | complete C => exact hcrit.elim
  | leaf P =>
    obtain ⟨c, hR, hL⟩ := hcrit
    exact ⟨P, U, c, hR, hL, hM, hrun, hb, hh, hfV⟩

theorem right_leaf_handoff {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    (I : Initial H B .inside)
    (hfirst : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (FirstBodyRefinement.firstLabel S).length ≠ 1)
    (P Q : Pending) (hP : P.roots ≠ []) (M : Managed I (.leaf Q))
    (hblue : RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q)) :
    ∃ U : Pending, Nonempty (Managed I (.leaf U)) ∧
      ConservativeRuns.Run H (GraphPayoff.payoff B .inside)
        (.leaf P, .leaf Q) (.leaf P, .leaf U) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf U)) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf U) := by
  obtain ⟨U, ⟨MU⟩, hs, hb, hh⟩ :=
    respond_right_leaf_with_handoff hH I Q (.leaf P) M hP hblue
  cases MU with
  | body D root hD =>
    have hc : RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, .body D) := by
      rcases blue_command (GraphPayoff.payoff B .inside) (.leaf P, .body D) rfl hb with hl | hr
      · obtain ⟨n, R, ha, _⟩ := hl
        simp [allowedSide] at ha
      · exact hr
    obtain ⟨k, A, M', hs', hb', hh'⟩ :=
      DeferredManaged.respond_body hH I hfirst true D (.leaf P) root hD hc
    exact ⟨applyBody D A, ⟨M'⟩,
      Relation.ReflTransGen.tail (Relation.ReflTransGen.single hs) hs', hb', hh'⟩
  | waiting U hn root hf hU =>
    exact ⟨U, ⟨Managed.waiting U hn root hf hU⟩,
      Relation.ReflTransGen.single hs, hb, hh U rfl⟩
  | prepared U A Z =>
    exact ⟨U, ⟨Managed.prepared U A Z⟩, Relation.ReflTransGen.single hs, hb, hh U rfl⟩

theorem right_handoff {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    (I : Initial H B .inside)
    (hfirst : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (FirstBodyRefinement.firstLabel S).length ≠ 1)
    (P : Pending) (T : State) (hP : P.roots ≠ []) (M : Managed I T)
    (hblue : RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, T)) :
    ∃ Q : Pending, Nonempty (Managed I (.leaf Q)) ∧
      ConservativeRuns.Run H (GraphPayoff.payoff B .inside) (.leaf P, T) (.leaf P, .leaf Q) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q) := by
  cases M with
  | body D root hD =>
    obtain ⟨k, A, M, hs, hb, hh⟩ :=
      DeferredManaged.respond_body hH I hfirst true D (.leaf P) root hD hblue
    exact ⟨applyBody D A, ⟨M⟩, Relation.ReflTransGen.single hs, hb, hh⟩
  | waiting Q hn root hf hQ =>
    exact right_leaf_handoff hH I hfirst P Q hP (Managed.waiting Q hn root hf hQ) hblue
  | prepared Q A Z =>
    exact right_leaf_handoff hH I hfirst P Q hP (Managed.prepared Q A Z) hblue

structure InitialReplay {H : Set ℕ} {B : SimpleGraph G}
    (I : Initial H B .inside) (P : Pending) where
  target : Pending
  ordinary : target.position.ordinary = P.position.ordinary
  entries : target.position.entries.length = P.position.entries.length
  marker : target.position.size = P.position.size
  labelLength : 1 < target.position.label.length
  last_mem : P.position.label.getLastD 0 ∈ target.position.label
  next_le : ∀ j ∈ target.position.label, P.position.entries.length < j →
    P.position.label.getLastD 0 ≤ j
  firstBody : target.position.stem.done.length + 1 = target.position.stem.rootLabel.headD 0
  rootLength : target.position.stem.rootLabel.length = I.size + 1
  exactSlots : ExactSlots.Exact (.leaf target)
  blue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf target, .initial)) true
  handoff : RightBlue H (GraphPayoff.payoff B .inside) (.leaf target, .initial)

theorem initialReplay {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    {I : Initial H B .inside} {P : Pending} (M : Managed I (.leaf P))
    (hR : P.roots = []) (hL : P.leaves ≠ []) : Nonempty (InitialReplay I P) := by
  obtain ⟨Q, hord, he, hs, hl, hm, hn, hf, hr, hQ, hb, hh⟩ := M.fire hH hR hL
  exact ⟨⟨Q, hord, he, hs, hl, hm, hn, hf, hr, hQ, hb, hh⟩⟩

theorem critical_replay {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    (I : Initial H B .inside)
    (hfirst : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (FirstBodyRefinement.firstLabel S).length ≠ 1)
    (hlate : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      LastMarkerRefinement.lastMarker T < LastMarkerRefinement.lastMarker S)
    (hlast : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (LastBodyRefinement.lastLabel S).length ≠ 1)
    (S T : State) (hS : Early S) (hX : ExactSlots.Exact S) (M : Managed I T)
    (hf : ∀ x ∈ S.ordinary, x ∈ H ∧ I.bound < x)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (S, T)) true)
    (hready : Critical S → RightBlue H (GraphPayoff.payoff B .inside) (S, T)) :
    ∃ P Q : Pending, ∃ c : ℕ, P.roots = [c] ∧ P.leaves = [] ∧
      Q.roots = [] ∧ Q.leaves ≠ [] ∧
      ExactSlots.Exact (.leaf P) ∧ ExactSlots.Exact (.leaf Q) ∧
      ConservativeRuns.Run H (GraphPayoff.payoff B .inside) (S, T) (.leaf P, .leaf Q) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q) ∧
      (∀ x ∈ P.position.ordinary, x ∈ H ∧ I.bound < x) ∧
      Nonempty (Managed I (.leaf Q)) ∧ Nonempty (InitialReplay I Q) := by
  obtain ⟨P, U, c, hR, hL, ⟨MU⟩, hrun, hb, hh, hfP⟩ :=
    stop_handoff hH I hfirst S T hS M hf hblue hready
  have hne : P.roots ≠ [] := by rw [hR]; simp
  obtain ⟨Q, ⟨MQ⟩, hrun', hb', hh'⟩ := right_handoff hH I hfirst P U hne MU hh
  have hP := ExactSlots.run_exact_left hrun hX
  obtain ⟨hQR, hQL, _⟩ :=
    LateMarkerCritical.before_last_body_right_nonlast hH B hlate hlast P Q c hP hR hL hh'
  exact ⟨P, Q, c, hR, hL, hQR, hQL, hP, MQ.exact,
    hrun.trans hrun', hb', hh', hfP, ⟨MQ⟩, initialReplay hH MQ hQR hQL⟩

end Erdos118.ManagedCritical
