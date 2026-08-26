import ErdosProblems.Erdos118.CurrentBodyReplay

/-! An actual stopped run to a specified selected body, retaining exact
slots, both ordinary suffix bounds, and the body's command priority. -/

namespace Erdos118.RootBodyCheckpoint

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays

def Before (r : ℕ) : State → Prop
  | .body D => r ∈ D.stem.rootLabel ∧ D.stem.done.length + 1 ≤ r
  | .leaf P => r ∈ P.position.stem.rootLabel ∧ P.position.stem.done.length + 1 < r
  | _ => False

def At (r : ℕ) : State → Prop
  | .body D => D.stem.done.length + 1 = r
  | _ => False

theorem before_step {r : ℕ} {S T : State} (hS : Before r S)
    (hX : ExactSlots.Exact S) (hn : ¬ At r S) (hs : DecisionStates.Step T S) :
    Before r T := by
  cases hs with
  | root A => exact hS.elim
  | whole s => exact hS.elim
  | body D A =>
    change r ∈ A.position.stem.rootLabel ∧ A.position.stem.done.length + 1 < r
    rw [A.stem_eq]
    exact ⟨hS.1, lt_of_le_of_ne hS.2 hn⟩
  | leaf P j rest hL A => exact hS
  | nextBody P j rest hR hL A =>
    have hm : r ∈ P.roots := by
      rw [hX.1]
      exact List.mem_filter.mpr ⟨hS.1, decide_eq_true hS.2⟩
    have hinc : (j :: rest).Pairwise (· < ·) :=
      (hX.1.symm.trans hR) ▸ P.position.stem.label_pairwise.sublist List.filter_sublist
    have hjr : j ≤ r := by
      rw [hR] at hm
      rcases List.mem_cons.mp hm with h | h
      · exact h.symm.le
      · exact ((List.pairwise_cons.mp hinc).1 r h).le
    have hjpos := (P.rootSlots.bounded j (hR ▸ List.mem_cons_self ..)).1
    change r ∈ A.stem.rootLabel ∧ A.stem.done.length + 1 ≤ r
    rw [A.rootLabel_eq, A.count]
    exact ⟨hS.1, by omega⟩
  | finish P hR hL A =>
    have hm : r ∈ P.roots := by
      rw [hX.1]
      exact List.mem_filter.mpr ⟨hS.1, decide_eq_true hS.2⟩
    rw [hR] at hm
    exact (List.not_mem_nil hm).elim

theorem root_before {k : ℕ} (A : RootResponses.Setup k) {r : ℕ}
    (hr : r ∈ A.stem.rootLabel) : Before r (.body (ofRoot A)) := by
  refine ⟨hr, ?_⟩
  change A.stem.done.length + 1 ≤ r
  rw [A.first_body]
  have h := (A.stem.label_pairwise.imp Nat.le_of_lt).rel_head hr
  cases he : A.stem.rootLabel with
  | nil => simp [he] at hr
  | cons a rest => simpa only [he, List.head_cons, List.headD_cons] using h

theorem right {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (r d : ℕ)
    (S X : State) (hS : Before r S) (hX : ExactSlots.Exact S)
    (hnotbody : ∀ D : BodyDecision, X ≠ .body D)
    (hb : RamseyGame.Outcome H (GraphPayoff.game B o (X, S)) true) :
    ∃ D : BodyDecision, ∃ Y : State, D.stem.done.length + 1 = r ∧
      ExactSlots.Exact (.body D) ∧ (∀ E : BodyDecision, Y ≠ .body E) ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (X, S) (Y, .body D) ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (Y, .body D)) true ∧
      RightBlue H (GraphPayoff.payoff B o) (Y, .body D) ∧
      FreshCheckpoints.FreshExtension K d (X, S) (Y, .body D) := by
  let Safe : State × State → Prop := fun V ↦ Before r V.2 ∧ ExactSlots.Exact V.2
  have hstep : ∀ V W : State × State, Safe V → ¬ At r V.2 → PairStep W V → Safe W := by
    intro V W hV hn hs
    cases hs with
    | left U hstep => exact hV
    | right U hstep => exact ⟨before_step hV.1 hV.2 hn hstep,
        ExactSlots.step_exact hstep hV.2⟩
  have hterm : ∀ V : State × State, Safe V → ¬ At r V.2 →
      terminalPayoff (GraphPayoff.payoff B o) V = none := by
    rintro ⟨Y, V⟩ ⟨hV, _⟩ _
    cases V <;> cases Y <;> simp_all [Before, terminalPayoff]
  obtain ⟨V, hrun, hbV, hsafe, hat, hentry, hf⟩ := FreshCheckpoints.blue_stop_above
    hK hKH (GraphPayoff.payoff B o) Safe (fun V ↦ At r V.2) hterm hstep d
    (X, S) ⟨hS, hX⟩ hb
  have hother : ∀ E : BodyDecision, V.1 ≠ .body E := by
    rcases hentry with rfl | ⟨W, _, hn, hs⟩
    · exact hnotbody
    · cases hs with
      | left n R hs hR a ha hg => exact (hn hat).elim
      | right n R hs hR a ha hg =>
        intro E he
        change W.1 = .body E at he
        simp [allowedSide, he] at hs
  obtain ⟨Y, V⟩ := V
  cases V with
  | initial => exact hat.elim
  | leaf P => exact hat.elim
  | complete C => exact hat.elim
  | body D =>
    have hh : RightBlue H (GraphPayoff.payoff B o) (Y, .body D) := by
      rcases blue_command (GraphPayoff.payoff B o) (Y, .body D)
        (by cases Y <;> rfl) hbV with hl | hr
      · obtain ⟨n, R, ha, _⟩ := hl
        cases Y with
        | initial => simp [allowedSide] at ha
        | body E => exact (hother E rfl).elim
        | leaf P => simp [allowedSide] at ha
        | complete C => simp [allowedSide] at ha
      · exact hr
    exact ⟨D, Y, hat, hsafe.2, hother, hrun, hbV, hh, hf⟩

end Erdos118.RootBodyCheckpoint
