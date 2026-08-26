import ErdosProblems.Erdos591.PrescribedLastBody

/-!
# Last--first root gluing in two actual strategy histories

The shared root is chosen after both root-label sizes are known. The
lower play reaches its last selected-body request. Its coordinate prefix
is the upper play's first selected-body response, whose next positive
body request is obtained before either body label or marker is chosen.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_request_at_marker {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool)
    (hp : p.position.pending = none) (hm : (p.position.board.get side).markerEvent = true) :
    ∃ q d, (exactGame N blue).FollowStep σ H b p q ∧ q.position.board = p.position.board ∧
      q.position.pending = some ⟨side, .advance d⟩ ∧ 0 < d := by
  have hk : (exactGame N blue).kind p = .architect :=
    (Concrete.kind_architect_iff (payoff blue) p).mpr
      ⟨hp, Board.not_done_of_live (LabeledWord.marker_not_terminal hm)⟩
  obtain ⟨mode, r, hn, heq⟩ := Concrete.architect_choice (payoff blue) σ p hk
  let q := p.append (p.position.request mode r) hn
  have hstep : (exactGame N blue).FollowStep σ H b p q := by
    simpa only [heq] using FiniteResponseGame.FollowStep.architect (exactGame N blue) σ p hk
  have hboard : q.position.board = p.position.board := by simp [q, Position.request]
  have hpend : q.position.pending = some r := by simp [q, Position.request]
  have hwinq := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hstep)
  obtain ⟨d, hd, hr⟩ := winning_pending_marker hHN hH blue hwinq hpend side
    (by simpa only [hboard] using hm)
  exact ⟨q, d, hstep, hboard, hr ▸ hpend, hd⟩

theorem winning_root_gluing {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {lower upper : Concrete.Hist N}
    (hwinl : (exactGame N blue).ArchitectWins H b σ lower)
    (hwinu : (exactGame N blue).ArchitectWins H b σ upper) (s t : Bool)
    {B a c : ℕ} (L : LastFirstLabels H B a c)
    (hlower : lower.position.pending = some ⟨s, .advance a⟩)
    (hupper : upper.position.pending = some ⟨t, .advance c⟩)
    (hil : lower.position.board.get s = LabeledWord.initial)
    (hiu : upper.position.board.get t = LabeledWord.initial)
    (hBl : max lower.position.bound (b lower) ≤ B)
    (hBu : max upper.position.bound (b upper) ≤ B) :
    ∃ q v d e, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) lower q ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upper v ∧
      q.position.pending = some ⟨s, .advance d⟩ ∧
      v.position.pending = some ⟨t, .advance e⟩ ∧ 0 < d ∧ 0 < e ∧
      LabeledWord.SameStructure (q.position.board.get s) (v.position.board.get t) ∧
      (q.position.board.get s).markerEvent = true ∧ (v.position.board.get t).markerEvent = true ∧
      (q.position.board.get s).bodyLabels.length + 1 = L.pivot ∧
      (q.position.board.get s).rootLabel = L.lower ∧
      (v.position.board.get t).rootLabel = L.upper ∧
      v.position.board.get (!t) = upper.position.board.get (!t) := by
  obtain ⟨q, d, as, hpath, hpend, hd, hm, hindex, hraw, hinc, hpool, hroot⟩ :=
    winning_prescribed_last_body hHN hH blue hwinl s L hlower hil hBl
  obtain ⟨u, hreply, _hsort, huH, huB⟩ := L.root_reply upper.position.board t hiu hraw hm hindex
    hinc (fun x hx => (hpool x (List.mem_cons_of_mem _ hx)).1)
  obtain ⟨v₀, hstep, hboard, hnone⟩ := Concrete.follow_reply hHN (payoff blue) σ upper
    hupper hreply huH (fun x hx => ⟨((le_max_left _ _).trans hBu).trans_lt (huB x hx),
      ((le_max_right _ _).trans hBu).trans_lt (huB x hx)⟩)
  have hword₀ : v₀.position.board.get t = LabeledWord.rootRelabel L.upper
      (q.position.board.get s) := by simp [hboard]
  have hmarker : (v₀.position.board.get t).markerEvent = true := by
    obtain ⟨k, hparse⟩ := LabeledWord.marker_blocks hm
    simp [hword₀, LabeledWord.rootRelabel, LabeledWord.markerEvent, hparse, hindex, L.pivot_upper]
  have hwin₀ := hwinu.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hstep)
  obtain ⟨v, e, hstep', hboard', hpend', he⟩ := winning_request_at_marker hHN hH blue hwin₀
    t hnone hmarker
  have hword : v.position.board.get t = LabeledWord.rootRelabel L.upper
      (q.position.board.get s) := by simpa only [hboard'] using hword₀
  have hshape : LabeledWord.SameStructure (q.position.board.get s) (v.position.board.get t) := by
    rw [hword]
    exact (LabeledWord.rootRelabel_sameStructure L.upper _).symm
  exact ⟨q, v, d, e, hpath, (Relation.ReflTransGen.single hstep).tail hstep',
    hpend, hpend', hd, he, hshape, hm, by simpa only [hboard'] using hmarker,
    hindex, hroot, by simp [hword, LabeledWord.rootRelabel],
    by simpa [hboard', hboard] using hreply.other_eq⟩

#print axioms winning_request_at_marker
#print axioms winning_root_gluing

end Erdos591.Positive.Game.Payoff
