import ErdosProblems.Erdos118.Reused591.CompletedOther

namespace Erdos118.Reused591

/-!
# The word with the larger final endpoint cannot finish first

The mode fixes which endpoint is larger. If that word were already
complete, completing the other word would introduce a fresh coordinate
above its endpoint, contradicting the final order. In particular, an
initial request on the larger-endpoint side cannot have size zero while
the other word is unfinished.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem follow_mode_some {N H : Set ℕ} {blue : SimpleGraph G}
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p q : Concrete.Hist N} {mode : Bool}
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q)
    (hp : p.position.mode = some mode) : q.position.mode = some mode := by
  induction hpath with
  | refl => exact hp
  | tail _ hs ih =>
      exact (History.Next.position_next
        (FiniteResponseGame.FollowStep.next (exactGame N blue) hs)).mode_some ih

theorem MaxOrder.side {board : Board} {mode : Bool} (h : MaxOrder mode board) :
    (board.get mode).coordinates.getLastD 0 < (board.get (!mode)).coordinates.getLastD 0 := by
  cases mode <;> simpa [MaxOrder, Board.get] using h

theorem winning_complete_larger {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N} {mode : Bool}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some mode)
    (hcomplete : (p.position.board.get (!mode)).terminal = true) :
    (p.position.board.get mode).terminal = true := by
  cases hlive : (p.position.board.get mode).terminal with
  | true => rfl
  | false =>
      obtain ⟨q, hpath, _hn, hdone, s, t, _hc, _hb, hmax⟩ :=
        winning_continuation hHN hH blue hwin
      have hmodeq := follow_mode_some hpath hmode
      have horder : MaxOrder mode q.position.board := by simpa [hmodeq] using hmax
      obtain ⟨as, has, hfresh⟩ :=
        (History.reachable_word_extension (follow_history_path hpath)).2 mode
      obtain ⟨bs, hbs, _⟩ :=
        (History.reachable_word_extension (follow_history_path hpath)).2 (!mode)
      have hother := hbs.terminal_eq hcomplete
      have hnon : as ≠ [] := by
        intro heq
        subst as
        have hw := (LabeledWord.legalRun_nil_iff _ _).mp has
        have ht := q.position.board.terminal_of_done hdone mode
        rw [← hw, hlive] at ht
        cases ht
      obtain ⟨a, tail, rfl⟩ := List.exists_cons_of_ne_nil hnon
      have ha : a.2 ∈ (q.position.board.get mode).coordinates := by
        rw [LabeledWord.runAtoms_coordinates has.run]
        simp
      have hinc := ((Position.history_dataInvariant q).2.1 mode).2
      have hlast : a.2 ≤ (q.position.board.get mode).coordinates.getLastD 0 := by
        simpa only [List.getLastD_eq_getLast?,
          List.getLast?_eq_some_getLast (List.ne_nil_of_mem ha), Option.getD_some] using
          (hinc.imp Nat.le_of_lt).rel_getLast ha
      have hlarge : (p.position.board.get (!mode)).coordinates.getLastD 0 < a.2 :=
        (Position.history_last_bound p (!mode)).trans_lt (hfresh a (by simp))
      have hord := horder.side
      rw [hother] at hord
      exact (Nat.lt_irrefl _ (hord.trans (hlarge.trans_le hlast))).elim

theorem winning_initial_larger_request_positive {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} {mode : Bool}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some mode) {r : Request}
    (hp : p.position.pending = some r) (hside : r.side = !mode)
    (hinit : p.position.board.get r.side = LabeledWord.initial)
    (hlive : (p.position.board.get mode).terminal = false) :
    ∃ d, 0 < d ∧ r = ⟨!mode, .advance d⟩ := by
  have hpos : 0 < r.size := by
    by_contra hn
    have hz : r.size = 0 := by omega
    have hk : (exactGame N blue).kind p = .builder :=
      (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨r, hp⟩
    obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
    have hs : (exactGame N blue).FollowStep σ H b p (Concrete.response p u) :=
      FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
    have hpath := Relation.ReflTransGen.single hs
    have hr := (Concrete.response_spec hu).reply_spec hp
    have ht := hr.size_zero_terminal (by simp [hinit, LabeledWord.initial]) hz
    have hwinq := hwin.of_reachable (exactGame N blue) hpath
    have hsmall := winning_complete_larger hHN hH blue hwinq
      (follow_mode_some hpath hmode) (by simpa [hside] using ht)
    have hother := hr.other_eq
    simp only [hside, Bool.not_not] at hother
    rw [hother, hlive] at hsmall
    cases hsmall
  cases r with
  | mk side command =>
      cases command with
      | finish => simp [Request.size] at hpos
      | advance d =>
          exact ⟨d, hpos, by simpa using congrArg (fun s => Request.mk s (.advance d)) hside⟩

#print axioms winning_complete_larger
#print axioms winning_initial_larger_request_positive

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
