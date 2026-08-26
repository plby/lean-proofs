import ErdosProblems.Erdos118.Reused591.RootPlan

namespace Erdos118.Reused591

/-!
# Transporting a reserved root and preparing its last body

Before its last selected body a root plan survives every actual winning
move. At that body's marker, replay its upper root request, obtain both
positive body sizes, and install a prepared body with one lower reply.
-/

namespace Erdos591.Positive.Game.Relay.RootPlan

open Erdos591.Negative.Exact
open Payoff

variable {N H : Set ℕ} {blue : SimpleGraph G} {b : Concrete.Hist N → ℕ}
  {σ : (exactGame N blue).ArchitectStrategy}

theorem follow {p q : Concrete.Hist N} (s : Bool)
    (R : RootPlan N H blue b σ (p.position.board.get s))
    (hHN : H ⊆ N) (hH : H.Infinite)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hstep : (exactGame N blue).FollowStep σ H b p q)
    (haway : p.position.board.get s ≠ q.position.board.get s →
      ¬ ((p.position.board.get s).markerEvent = true ∧
        (p.position.board.get s).bodyLabels.length + 1 = R.labels.pivot)) :
    ∃ Q : RootPlan N H blue b σ (q.position.board.get s),
      Q.target = R.target ∧ Q.side = R.side ∧ HEq Q.labels R.labels := by
  by_cases heq : p.position.board.get s = q.position.board.get s
  · rw [← heq]
    exact ⟨R, rfl, rfl, HEq.rfl⟩
  have hnext := History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hstep)
  have hbefore : (q.position.board.get s).bodyLabels.length < R.labels.pivot := by
    cases hp : p.position.pending with
    | none => exact (heq (by rw [hnext.board_eq_of_no_pending hp])).elim
    | some r =>
        obtain ⟨u, hr⟩ := hnext.reply_of_pending hp
        have hside : s = r.side := by
          by_contra hn
          have hs : s = !r.side := Bool.eq_not_of_ne hn
          exact heq (by simpa [hs] using hr.other_eq.symm)
        cases r with
        | mk t command =>
            have hst : s = t := hside
            subst t
            cases command with
            | finish =>
                exact ((winning_pending_finish_not_pending hHN hH blue hwin hp rfl) R.pending).elim
            | advance d =>
                exact (hr.advance_before_body_or_marker R.before_body R.not_start).resolve_right
                  (haway heq) |>.2
  obtain ⟨as, has, hpool⟩ := follow_step_word_inputs_fresh hstep s
  have hfresh : ∀ a ∈ as, a.2 ∈ H ∧ R.budget < a.2 := by
    intro a ha
    exact ⟨(hpool a ha).1, R.budget_lt_bound.trans
      ((le_max_left _ _).trans_lt (hpool a ha).2)⟩
  exact ⟨R.move has hfresh hbefore, rfl, rfl, HEq.rfl⟩

theorem prepare_last {p : Concrete.Hist N} (s : Bool)
    (R : RootPlan N H blue b σ (p.position.board.get s))
    (hHN : H ⊆ N) (hH : H.Infinite)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {r : Request} (hp : p.position.pending = some r)
    (hm : (p.position.board.get s).markerEvent = true)
    (hindex : (p.position.board.get s).bodyLabels.length + 1 = R.labels.pivot) :
    ∃ q, (exactGame N blue).FollowStep σ H b p q ∧ q.position.pending = none ∧
      (q.position.board.get s).relaxed = true ∧
      q.position.board.get (!s) = p.position.board.get (!s) ∧
      ∃ P : PreparedBody N H blue b σ (q.position.board.get s),
        P.side = R.side ∧
        P.target.position.board.get (!P.side) = R.target.position.board.get (!R.side) ∧
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) R.target P.target ∧
        (P.target.position.board.get P.side).NoRootPassed := by
  obtain ⟨a, ha, hr⟩ := winning_pending_marker hHN hH blue hwin hp s hm
  subst r
  obtain ⟨upper, c, hpath, hupper, hc, hsame, hmu, hother, hfirst⟩ :=
    R.fire_first hHN hH hm hindex ((Position.history_dataInvariant p).2.1 s).2
  let B := max (max p.position.bound (b p)) (max upper.position.bound (b upper))
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH B a c ha hc
  have hroot : ∀ i ∈ (p.position.board.get s).rootLabel,
      i ≤ (p.position.board.get s).bodyLabels.length + 1 := by
    intro i hi
    rw [hindex]
    exact R.labels.lower_le i (R.rootLabel ▸ hi)
  have hwinu := R.targetWinning.of_reachable (exactGame N blue) hpath
  obtain ⟨q, hstep, hnone, hrel, hother', P, htarget, hside, _⟩ :=
    prepare_body hHN hH blue hwinu s R.side L hp hupper hm hmu hsame
      (le_max_left _ _) (le_max_right _ _) hroot
  exact ⟨q, hstep, hnone, hrel, hother', P, hside,
    by simpa [htarget, hside] using hother, by simpa [htarget] using hpath,
    by simpa [htarget, hside] using hfirst⟩

#print axioms follow
#print axioms prepare_last

end Erdos591.Positive.Game.Relay.RootPlan

end Erdos118.Reused591
