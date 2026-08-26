import ErdosProblems.Erdos118.Reused591.SeparatedOpening
import ErdosProblems.Erdos118.Reused591.CompleteResponse

namespace Erdos118.Reused591

/-!
# A blue tail after a complete first word

At a winning history with the first word complete and the second still
initial, every sufficiently high complete response gives a blue edge.
The bound is the finite maximum of the actual next request's freshness
and conservativity bounds. The response is submitted unchanged.
-/

namespace Erdos591.Positive.Game

theorem Request.Legal.selected_live {r : Request} {board : Board} (h : r.Legal board) :
    (board.get r.side).terminal = false := by
  cases hc : r.command with
  | finish => simpa [Request.Legal, hc] using h
  | advance d =>
      exact (show (board.get r.side).AllowedSize d by simpa [Request.Legal, hc] using h).1

namespace CompleteResponse

open Erdos591.Negative.Exact Payoff

theorem blue_tail {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (s : CompleteResponse)
    (hleft : p.position.board.left = s.cursor)
    (hright : p.position.board.right = LabeledWord.initial)
    (hturn : p.position.pending = none) :
    ∃ B : ℕ, ∀ t : CompleteResponse, (↑t.input : Set ℕ) ⊆ H →
      (∀ x ∈ t.input, B < x) → blue.Adj s.vertex t.vertex := by
  have hk : (exactGame N blue).kind p = .architect := by
    apply (Concrete.kind_architect_iff (payoff blue) p).mpr
    exact ⟨hturn, by simp [Concrete.done, hright, LabeledWord.initial, LabeledWord.terminal]⟩
  obtain ⟨mode, r, hreq, hchoice⟩ := Concrete.architect_choice (payoff blue) σ p hk
  let q := p.append (p.position.request mode r) hreq
  have hfollow : (exactGame N blue).FollowStep σ H b p q := by
    dsimp only [q]
    rw [← hchoice]
    exact FiniteResponseGame.FollowStep.architect (exactGame N blue) σ p hk
  have hqwin := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hfollow)
  have hqboard : q.position.board = p.position.board := by simp [q, Position.request]
  have hqpend : q.position.pending = some r := by simp [q, Position.request]
  have hlegal := (Position.history_controlInvariant q).2 r hqpend
  have hside : r.side = true := by
    have hnot : r.side ≠ false := by
      intro hs
      have hlive := hlegal.selected_live
      simp only [hqboard, hs, Board.get, hleft, s.terminal] at hlive
      contradiction
    exact Bool.eq_true_of_not_eq_false hnot
  have hinit : q.position.board.get r.side = LabeledWord.initial := by
    simp [hqboard, hside, Board.get, hright]
  have hterm : (q.position.board.get (!r.side)).terminal = true := by
    simp [hqboard, hside, Board.get, hleft, s.terminal]
  have hsize := winning_pending_after_complete_size_zero hHN hH blue hqwin hqpend hinit hterm
  refine ⟨max q.position.bound (b q), ?_⟩
  intro t htH htB
  let last := q.position.board.update r.side t.cursor
  have hreply : Reply q.position.board r t.input last := t.reply _ r hinit hsize
  have hN : (↑t.input : Set ℕ) ⊆ N := htH.trans hHN
  have hfresh : ∀ x ∈ t.input, q.position.bound < x :=
    fun x hx => (le_max_left _ _).trans_lt (htB x hx)
  let k := q.append (q.position.reply t.input last)
    (.reply q.position r t.input last hqpend hreply hN hfresh)
  have hrep : Concrete.Replies q t.input k :=
    .mk r last hqpend hreply hN hfresh
  have hf := hrep.follow (payoff blue) σ htH
    (fun x hx => (le_max_right _ _).trans_lt (htB x hx))
  have hdone : Concrete.done k.position.board = true := by
    simp [k, Position.reply, last, hside, Board.update, Concrete.done,
      hqboard, hleft, s.terminal, t.terminal]
  have hkind : (exactGame N blue).kind k =
      .terminal (payoff blue (k.position.mode.getD false) k.position.board) := by
    apply (Concrete.kind_terminal_iff (payoff blue) k _).mpr
    exact ⟨by simp [k, Position.reply], hdone, rfl⟩
  have hpay := hqwin k _ (Relation.ReflTransGen.single hf) hkind
  have hwinning := (payoff_true_iff blue _ _).mp hpay
  have hsword : word s.vertex.val = k.position.board.left.coordinates := by
    simpa [k, Position.reply, last, hside, Board.update, hqboard, hleft] using s.vertex_word
  have htword : word t.vertex.val = k.position.board.right.coordinates := by
    simpa [k, Position.reply, last, hside, Board.update] using t.vertex_word
  exact ((winning_iff blue _ _ s.vertex t.vertex hsword htword).mp hwinning).2.1

#print axioms blue_tail

end CompleteResponse

end Erdos591.Positive.Game

end Erdos118.Reused591
