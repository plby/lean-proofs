import ErdosProblems.Erdos591.EndpointOrder

/-!
# Exhausted selections at the larger-endpoint boundary

Once the larger-endpoint word has no unread selection, a winning play
cannot still have an unread selection in the smaller-endpoint word.
Reaching such a selection would force a switch to the larger word,
whose only legal response completes it too early.
-/

namespace Erdos591.Positive.Game

open Erdos591.Negative.Exact
open Payoff

theorem LabeledWord.LegalRun.not_pending {w v : LabeledWord} {as : List (Finset ℕ × ℕ)}
    (h : LabeledWord.LegalRun w as v) (hstart : w.parser ≠ .start)
    (hn : ¬ Macro.Pending w) : ¬ Macro.Pending v := by
  revert hstart hn
  induction h with
  | nil => exact fun _ hn => hn
  | cons w D n u as v _ hr _ ih =>
      intro hstart hn
      exact ih (LabeledWord.read_parser_ne_start hr)
        (fun hu => hn (Macro.pending_before_read hstart hr (Or.inl hu)))

namespace Payoff

theorem winning_pending_larger_no_selection {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} {mode : Bool}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some mode) {r : Request}
    (hp : p.position.pending = some r) (hside : r.side = !mode)
    (hstart : (p.position.board.get r.side).parser ≠ .start)
    (hn : ¬ Macro.Pending (p.position.board.get r.side)) :
    (p.position.board.get mode).terminal = true := by
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨r, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
  have hs : (exactGame N blue).FollowStep σ H b p (Concrete.response p u) :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
  have hpath := Relation.ReflTransGen.single hs
  have hr := (Concrete.response_spec hu).reply_spec hp
  have hf := (Reply.not_pending_iff_finish p.position.board r u _
    ((Position.history_controlInvariant p).2 r hp) hstart hn).mp hr
  have hsmall := winning_complete_larger hHN hH blue
    (hwin.of_reachable (exactGame N blue) hpath) (follow_mode_some hpath hmode)
    (by simpa [hside] using hf.finish_terminal)
  have hother := hr.other_eq
  simp only [hside, Bool.not_not] at hother
  simpa only [hother] using hsmall

theorem winning_fresh_smaller_has_pending_larger {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} {mode : Bool}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some mode) (hp : p.position.pending = none)
    (hr : (p.position.board.get mode).relaxed = true)
    (hsep : ∀ y ∈ (p.position.board.get (!mode)).coordinates,
      y ≤ (p.position.board.get mode).coordinates.getLastD 0)
    (hstart : (p.position.board.get (!mode)).parser ≠ .start) :
    Macro.Pending (p.position.board.get (!mode)) := by
  by_contra hn
  have hw := ((Position.history_dataInvariant p).2.1 mode).1
  have hlive := LabeledWord.relaxed_not_terminal hw.2.1 hw.2.2 hr
  have hk : (exactGame N blue).kind p = .architect :=
    (Concrete.kind_architect_iff (payoff blue) p).mpr
      ⟨hp, Board.not_done_of_live hlive⟩
  obtain ⟨flag, r, hnext, heq⟩ := Concrete.architect_choice (payoff blue) σ p hk
  let q := p.append (p.position.request flag r) hnext
  have hs : (exactGame N blue).FollowStep σ H b p q := by
    simpa only [heq] using FiniteResponseGame.FollowStep.architect (exactGame N blue) σ p hk
  have hboard : q.position.board = p.position.board := by simp [q, Position.request]
  have hpend : q.position.pending = some r := by simp [q, Position.request]
  have hpath := Relation.ReflTransGen.single hs
  have hwinq := hwin.of_reachable (exactGame N blue) hpath
  have hside := winning_pending_switch hHN hH blue hwinq hpend mode
    (by simpa [hboard] using hr) (by simpa [hboard] using hsep)
  have ht := winning_pending_larger_no_selection hHN hH blue hwinq
    (follow_mode_some hpath hmode) hpend hside
    (by simpa [hboard, hside] using hstart) (by simpa [hboard, hside] using hn)
  rw [hboard, hlive] at ht
  cases ht

theorem winning_no_pending_smaller {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N} {mode : Bool}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some mode)
    (hsmall : (p.position.board.get mode).parser ≠ .start)
    (hlarge : (p.position.board.get (!mode)).parser ≠ .start)
    (hn : ¬ Macro.Pending (p.position.board.get (!mode))) :
    ¬ Macro.Pending (p.position.board.get mode) := by
  have impossible (q : Concrete.Hist N)
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q)
      (hp : q.position.pending = none) (hr : (q.position.board.get mode).relaxed = true)
      (hsep : ∀ y ∈ (q.position.board.get (!mode)).coordinates,
        y ≤ (q.position.board.get mode).coordinates.getLastD 0) : False := by
    obtain ⟨as, has, _⟩ :=
      (History.reachable_word_extension (follow_history_path hpath)).2 (!mode)
    exact has.not_pending hlarge hn (winning_fresh_smaller_has_pending_larger hHN hH blue
      (hwin.of_reachable (exactGame N blue) hpath) (follow_mode_some hpath hmode)
      hp hr hsep (has.parser_ne_start hlarge))
  rintro (⟨i, hi, hlt⟩ | ⟨hsel, j, hj, hlt⟩)
  · obtain ⟨q, d, hpath, hp, hd, hm, _hi⟩ :=
      winning_reach_body_marker hHN hH blue hwin mode i hsmall ⟨hi, hlt⟩
    have hk : (exactGame N blue).kind q = .builder :=
      (Concrete.kind_builder_iff (payoff blue) q).mpr ⟨_, hp⟩
    obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH q hk (b q)
    have hs : (exactGame N blue).FollowStep σ H b q (Concrete.response q u) :=
      FiniteResponseGame.FollowStep.builder (exactGame N blue) σ q u hk hu huH hub
    have hnext := FiniteResponseGame.FollowStep.next (exactGame N blue) hs
    have hr := (Concrete.response_spec hu).reply_spec hp
    have hrel := hr.advance_selected_leaf ((Position.history_dataInvariant q).2.1 mode).1
      hm hd (fun x hx => (Nat.zero_le (b q)).trans_lt (hub x hx))
    exact impossible _ (hpath.tail hs)
      (History.Next.position_next hnext |>.no_pending_after_reply hp) hrel
      (hnext.reply_separation hp)
  · obtain ⟨q, hpath, hp, hr, _hi, _hb, _hm, hsep⟩ :=
      winning_reach_selected_leaf_fresh hHN hH blue hwin mode j ⟨hsel, hj, hlt.le⟩ hlt
    exact impossible q hpath hp hr hsep

#print axioms winning_pending_larger_no_selection
#print axioms winning_no_pending_smaller

end Payoff

end Erdos591.Positive.Game
