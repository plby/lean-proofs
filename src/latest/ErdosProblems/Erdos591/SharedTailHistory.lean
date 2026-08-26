import ErdosProblems.Erdos591.FollowInputs

/-!
# Shared completion tails as actual strategy-history moves

The structural shared-tail result is lifted to conservative legal
histories. An extra finite bound can be fixed before completing a later
play, and its selected word then supplies the pending complete response
of an earlier play. Neither history nor its stored labels is modified.
-/

namespace Erdos591.Positive.Game

namespace Concrete

theorem follow_reply_with_used {N H : Set ℕ} (hHN : H ⊆ N) (payoff : Bool → Board → Bool)
    {b : Hist N → ℕ} (σ : (game N payoff).ArchitectStrategy)
    (p : Hist N) {r : Request} {u : Finset ℕ} {board : Board}
    (hp : p.position.pending = some r) (hr : Reply p.position.board r u board)
    (hpool : (↑u : Set ℕ) ⊆ H)
    (hfresh : ∀ x ∈ u, p.position.bound < x ∧ b p < x) :
    ∃ q, (game N payoff).FollowStep σ H b p q ∧
      q.position.board = board ∧ q.position.pending = none ∧
      ReplayBudget.used q = ReplayBudget.used p ∪ u := by
  let hn : Position.Next N (p.position.reply u board) p.position :=
    .reply p.position r u board hp hr (hpool.trans hHN) (fun x hx => (hfresh x hx).1)
  let q := p.append (p.position.reply u board) hn
  have hreply : Replies p u q := .mk r board hp hr (hpool.trans hHN)
    (fun x hx => (hfresh x hx).1)
  exact ⟨q, hreply.follow payoff σ hpool (fun x hx => (hfresh x hx).2),
    by simp [q, Position.reply], by simp [q, Position.reply],
    by simp [q, Position.reply, Position.inputs]⟩

theorem follow_reply {N H : Set ℕ} (hHN : H ⊆ N) (payoff : Bool → Board → Bool)
    {b : Hist N → ℕ} (σ : (game N payoff).ArchitectStrategy)
    (p : Hist N) {r : Request} {u : Finset ℕ} {board : Board}
    (hp : p.position.pending = some r) (hr : Reply p.position.board r u board)
    (hpool : (↑u : Set ℕ) ⊆ H)
    (hfresh : ∀ x ∈ u, p.position.bound < x ∧ b p < x) :
    ∃ q, (game N payoff).FollowStep σ H b p q ∧
      q.position.board = board ∧ q.position.pending = none := by
  obtain ⟨q, hs, hb, hn, _⟩ := follow_reply_with_used hHN payoff σ p hp hr hpool hfresh
  exact ⟨q, hs, hb, hn⟩

theorem follow_shared_tail {N H : Set ℕ} (hHN : H ⊆ N) (payoff : Bool → Board → Bool)
    {b : Hist N → ℕ} (σ : (game N payoff).ArchitectStrategy)
    (p : Hist N) {r : Request} {f v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (hp : p.position.pending = some r)
    (hstart : (p.position.board.get r.side).parser ≠ .start)
    (hnopending : ¬ Macro.Pending (p.position.board.get r.side))
    (hsame : LabeledWord.SameStructure (p.position.board.get r.side) f)
    (hr : f.runAtoms xs = some v) (hv : v.terminal = true)
    (hinc : (xs.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ a ∈ xs, a.2 ∈ H ∧ p.position.bound < a.2 ∧ b p < a.2) :
    ∃ q, (game N payoff).FollowStep σ H b p q ∧ q.position.pending = none ∧
      LabeledWord.SameStructure (q.position.board.get r.side) v ∧
      q.position.board.get (!r.side) = p.position.board.get (!r.side) := by
  have hlegal := (Position.history_controlInvariant p).2 r hp
  obtain ⟨z, hz, hlast⟩ := Reply.not_pending_shared_tail p.position.board r hlegal hstart
    hnopending hsame hr hv hinc
  have hvalues : ∀ x ∈ (xs.map Prod.snd).toFinset,
      x ∈ H ∧ p.position.bound < x ∧ b p < x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact hpool a ha
  obtain ⟨q, hfollow, hboard, hnone⟩ := follow_reply hHN payoff σ p hp hz
    (fun x hx => (hvalues x hx).1) (fun x hx => (hvalues x hx).2)
  exact ⟨q, hfollow, hnone, by simpa [hboard] using hlast,
    by simpa [hboard] using hz.other_eq⟩

end Concrete

namespace Payoff

open Erdos591.Negative.Exact

theorem winning_shared_completion {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p old : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool) {r : Request}
    (hp : old.position.pending = some r)
    (hstart : (old.position.board.get r.side).parser ≠ .start)
    (hnopending : ¬ Macro.Pending (old.position.board.get r.side))
    (hsame : LabeledWord.SameStructure (old.position.board.get r.side)
      (p.position.board.get side)) :
    ∃ q old', Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      Concrete.done q.position.board = true ∧
      Winning blue (q.position.mode.getD false) q.position.board ∧
      (exactGame N blue).FollowStep σ H b old old' ∧ old'.position.pending = none ∧
      LabeledWord.SameStructure (old'.position.board.get r.side) (q.position.board.get side) ∧
      old'.position.board.get (!r.side) = old.position.board.get (!r.side) := by
  let B := max old.position.bound (b old)
  obtain ⟨q, hpath, _, hdone, hwinning, hwords⟩ := winning_continuation_above hHN hH blue hwin B
  obtain ⟨as, has, hinputs⟩ := hwords side
  have hcoords := LabeledWord.runAtoms_coordinates has.run
  have hinc : (as.map Prod.snd).Pairwise (· < ·) := by
    have hi := ((Position.history_dataInvariant q).2.1 side).2
    rw [hcoords] at hi
    exact (List.pairwise_append.mp hi).2.1
  obtain ⟨old', hstep, hnone, hsame', hother⟩ := Concrete.follow_shared_tail hHN (payoff blue) σ
    old hp hstart hnopending hsame has.run (q.position.board.terminal_of_done hdone side) hinc
    (fun a ha => ⟨(hinputs a ha).1, (le_max_left _ _).trans_lt (hinputs a ha).2,
      (le_max_right _ _).trans_lt (hinputs a ha).2⟩)
  exact ⟨q, old', hpath, hdone, hwinning, hstep, hnone, hsame', hother⟩

/-- One later play can simultaneously supply any finite family of
already pending complete responses, with a common bound fixed first. -/
theorem winning_shared_completions {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (m : ℕ)
    (old : Fin m → Concrete.Hist N) (r : Fin m → Request) (side : Fin m → Bool)
    (hp : ∀ k, (old k).position.pending = some (r k))
    (hstart : ∀ k, ((old k).position.board.get (r k).side).parser ≠ .start)
    (hnopending : ∀ k, ¬ Macro.Pending ((old k).position.board.get (r k).side))
    (hsame : ∀ k, LabeledWord.SameStructure ((old k).position.board.get (r k).side)
      (p.position.board.get (side k))) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      Concrete.done q.position.board = true ∧
      Winning blue (q.position.mode.getD false) q.position.board ∧
      ∀ k, ∃ old', (exactGame N blue).FollowStep σ H b (old k) old' ∧
        old'.position.pending = none ∧
        LabeledWord.SameStructure (old'.position.board.get (r k).side)
          (q.position.board.get (side k)) ∧
        old'.position.board.get (!(r k).side) = (old k).position.board.get (!(r k).side) := by
  let B := Finset.univ.sup (fun k : Fin m => max (old k).position.bound (b (old k)))
  obtain ⟨q, hpath, _, hdone, hwinning, hwords⟩ := winning_continuation_above hHN hH blue hwin B
  refine ⟨q, hpath, hdone, hwinning, ?_⟩
  intro k
  have hB : max (old k).position.bound (b (old k)) ≤ B :=
    Finset.le_sup (f := fun k : Fin m => max (old k).position.bound (b (old k)))
      (Finset.mem_univ k)
  obtain ⟨as, has, hinputs⟩ := hwords (side k)
  have hcoords := LabeledWord.runAtoms_coordinates has.run
  have hinc : (as.map Prod.snd).Pairwise (· < ·) := by
    have hi := ((Position.history_dataInvariant q).2.1 (side k)).2
    rw [hcoords] at hi
    exact (List.pairwise_append.mp hi).2.1
  exact Concrete.follow_shared_tail hHN (payoff blue) σ (old k) (hp k) (hstart k)
    (hnopending k) (hsame k) has.run (q.position.board.terminal_of_done hdone (side k)) hinc
    (fun a ha => ⟨(hinputs a ha).1,
      ((le_max_left _ _).trans hB).trans_lt (hinputs a ha).2,
      ((le_max_right _ _).trans hB).trans_lt (hinputs a ha).2⟩)

#print axioms winning_shared_completion
#print axioms winning_shared_completions

end Payoff

end Erdos591.Positive.Game
