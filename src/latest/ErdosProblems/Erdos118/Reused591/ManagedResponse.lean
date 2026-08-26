import ErdosProblems.Erdos118.Reused591.ManagedWord

namespace Erdos118.Reused591

/-!
# One conservative response preserves a managed word

At the last selected body, choose the response that installs its delayed
upper reply. Elsewhere an arbitrary conservative response suffices.
A prepared word cannot finish before the two-word checkpoint: in a
winning history its completion would force the other word to have no
unread selected index either.
-/

namespace Erdos591.Positive.Game

open Erdos591.Negative.Exact
open Payoff

namespace Relay.Managed

theorem respond_from {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) {r : Request}
    (hp : p.position.pending = some r) (hnot : ¬ BothLast p.position.board)
    {t mode : Bool} {other : LabeledWord}
    (M : Managed N H blue b σ t mode other (p.position.board.get r.side))
    (origin : Concrete.Hist N)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target) :
    ∃ q, (exactGame N blue).FollowStep σ H b p q ∧ q.position.pending = none ∧
      q.position.board.get (!r.side) = p.position.board.get (!r.side) ∧
      ∃ Q : Managed N H blue b σ t mode other (q.position.board.get r.side),
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin Q.target := by
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨r, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
  let q := Concrete.response p u
  have hstep : (exactGame N blue).FollowStep σ H b p q :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
  have hreply := (Concrete.response_spec hu).reply_spec hp
  have hnone : q.position.pending = none :=
    (History.Next.position_next (FiniteResponseGame.FollowStep.next
      (exactGame N blue) hstep)).no_pending_after_reply hp
  have hother : q.position.board.get (!r.side) = p.position.board.get (!r.side) := hreply.other_eq
  cases M with
  | root R hside hanchor hmode =>
      by_cases hm : (p.position.board.get r.side).markerEvent = true ∧
          (p.position.board.get r.side).bodyLabels.length + 1 = R.labels.pivot
      · obtain ⟨q', hs, hn, _hrel, ho, P, ht, ha, htargetPath, hfirst⟩ :=
          R.prepare_last r.side hHN hH hwin hp hm.1 hm.2
        exact ⟨q', hs, hn, ho, Managed.prepared P (ht.trans hside) (ha.trans hanchor)
          (follow_mode_some htargetPath hmode) hfirst, hfrom.trans htargetPath⟩
      · obtain ⟨Q, ht, hs, _⟩ := R.follow r.side hHN hH hwin hstep (fun _ => hm)
        refine ⟨q, hstep, hnone, hother,
          Managed.root Q (hs.trans hside) (by simpa [ht, hs] using hanchor)
            (by simpa [ht] using hmode), ?_⟩
        change Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin Q.target
        rw [ht]
        exact hfrom
  | prepared P hside hanchor hmode hfirst =>
      have hlt : (p.position.board.get r.side).leafIndex < P.labels.pivot := by
        apply lt_of_le_of_ne P.upto.before
        intro heq
        have hn := P.not_pending heq
        obtain ⟨a, k, hparse⟩ := P.upto.parser_leaves
          ((Position.history_dataInvariant p).2.1 r.side).1
        have hstart : (p.position.board.get r.side).parser ≠ .start := by simp [hparse]
        have hlegal := (Position.history_controlInvariant p).2 r hp
        have hf := (Reply.not_pending_iff_finish p.position.board r u q.position.board
          hlegal hstart hn).mp hreply
        have hterm := hf.finish_terminal
        have hwinq := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hstep)
        have hotherNo := winning_not_pending_of_other_complete hHN hH blue hwinq (!r.side)
          (by simpa using hterm)
        rw [hother] at hotherNo
        apply hnot
        intro s
        by_cases hs : s = r.side
        · simpa [hs] using hn
        · have hs' : s = !r.side := Bool.eq_not_of_ne hs
          simpa [hs'] using hotherNo
      obtain ⟨Q, ht, hs, _⟩ := P.follow r.side hHN hH hwin hstep (fun _ => hlt)
      refine ⟨q, hstep, hnone, hother,
        Managed.prepared Q (hs.trans hside) (by simpa [ht, hs] using hanchor)
          (by simpa [ht] using hmode) (by simpa [ht, hs] using hfirst), ?_⟩
      change Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin Q.target
      rw [ht]
      exact hfrom

theorem respond {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) {r : Request}
    (hp : p.position.pending = some r) (hnot : ¬ BothLast p.position.board)
    {t mode : Bool} {other : LabeledWord}
    (M : Managed N H blue b σ t mode other (p.position.board.get r.side)) :
    ∃ q, (exactGame N blue).FollowStep σ H b p q ∧ q.position.pending = none ∧
      q.position.board.get (!r.side) = p.position.board.get (!r.side) ∧
      Nonempty (Managed N H blue b σ t mode other (q.position.board.get r.side)) := by
  obtain ⟨q, hs, hn, ho, Q, _hfrom⟩ :=
    M.respond_from hHN hH blue hwin hp hnot M.target Relation.ReflTransGen.refl
  exact ⟨q, hs, hn, ho, ⟨Q⟩⟩

#print axioms respond
#print axioms respond_from

end Relay.Managed

end Erdos591.Positive.Game

end Erdos118.Reused591
