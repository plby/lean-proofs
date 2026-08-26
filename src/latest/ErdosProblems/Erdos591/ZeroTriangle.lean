import ErdosProblems.Erdos591.ZeroBlueTail

/-!
# A zero-label opening forces a blue triangle

Every complete word above the opening bound can serve as the first
response and has a blue tail of complete second responses. Choose the
second word above both its first-response bound and the first word's
blue-tail bound; choose the third above the two blue-tail bounds.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem pending_initial_zero_triangle {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {r : Request} (hp : p.position.pending = some r)
    (hboard : p.position.board = Board.initial) (hside : r.side = false)
    (hsize : r.size = 0) : ¬ blue.CliqueFree 3 := by
  classical
  let B₀ := max p.position.bound (b p)
  have htail (s : CompleteResponse) (hsH : (↑s.input : Set ℕ) ⊆ H)
      (hsB : ∀ x ∈ s.input, B₀ < x) :
      ∃ B, ∀ t : CompleteResponse, (↑t.input : Set ℕ) ⊆ H →
        (∀ x ∈ t.input, B < x) → blue.Adj s.vertex t.vertex := by
    let last := p.position.board.update r.side s.cursor
    have hinit : p.position.board.get r.side = LabeledWord.initial := by
      simp [hboard, hside, Board.initial, Board.get]
    have hreply : Reply p.position.board r s.input last := s.reply _ r hinit hsize
    have hN : (↑s.input : Set ℕ) ⊆ N := hsH.trans hHN
    have hfresh : ∀ x ∈ s.input, p.position.bound < x :=
      fun x hx => (le_max_left _ _).trans_lt (hsB x hx)
    let q := p.append (p.position.reply s.input last)
      (.reply p.position r s.input last hp hreply hN hfresh)
    have hrep : Concrete.Replies p s.input q := .mk r last hp hreply hN hfresh
    have hf := hrep.follow (payoff blue) σ hsH
      (fun x hx => (le_max_right _ _).trans_lt (hsB x hx))
    have hqwin := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hf)
    apply s.blue_tail hHN hH blue hqwin
    · simp [q, Position.reply, last, hside, Board.update]
    · simp [q, Position.reply, last, hside, Board.update, hboard, Board.initial]
    · simp [q, Position.reply]
  obtain ⟨s, hsH, hsB⟩ := CompleteResponse.exists_above hH B₀
  obtain ⟨Bs, hBs⟩ := htail s hsH hsB
  obtain ⟨t, htH, htB⟩ := CompleteResponse.exists_above hH (max B₀ Bs)
  have htB₀ : ∀ x ∈ t.input, B₀ < x := fun x hx => (le_max_left _ _).trans_lt (htB x hx)
  obtain ⟨Bt, hBt⟩ := htail t htH htB₀
  obtain ⟨u, huH, huB⟩ := CompleteResponse.exists_above hH (max Bs Bt)
  have hst := hBs t htH (fun x hx => (le_max_right _ _).trans_lt (htB x hx))
  have hsu := hBs u huH (fun x hx => (le_max_left _ _).trans_lt (huB x hx))
  have htu := hBt u huH (fun x hx => (le_max_right _ _).trans_lt (huB x hx))
  intro hfree
  exact hfree {s.vertex, t.vertex, u.vertex}
    (SimpleGraph.is3Clique_triple_iff.mpr ⟨hst, hsu, htu⟩)

#print axioms pending_initial_zero_triangle

end Erdos591.Positive.Game.Payoff
