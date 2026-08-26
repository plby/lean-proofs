import ErdosProblems.Erdos591.RootGluingHistory

/-!
# No unread selected position opposite a completed word

After one word completes, every new coordinate of the other word lies
above it. A later selected-leaf event would require a cut witnessed by
that completed word and is impossible in a winning continuation. Reaching
each unread selected body or leaf turns this into the pending-index rule
needed to stop the coupled construction before either word completes.
-/

namespace Erdos591.Positive.Game

theorem Reply.advance_selected_leaf {board last : Board} {side : Bool} {d : ℕ}
    {u : Finset ℕ} (h : Reply board ⟨side, .advance d⟩ u last)
    (hw : (board.get side).CursorInvariant) (hm : (board.get side).markerEvent = true)
    (hd : 0 < d) (hpos : ∀ x ∈ u, 0 < x) : (last.get side).relaxed = true := by
  cases h with
  | advance side d u w hlegal hrun =>
      simpa using (Advance.selected_positive_first_leaf ⟨board.get side, hlegal.1⟩ hw hm d hd
        (u.sort (· ≤ ·)) w (Finset.sortedLT_sort u).pairwise
        (fun x hx => hpos x ((Finset.mem_sort (· ≤ ·)).mp hx)) hrun).1

namespace Payoff

open Erdos591.Negative.Exact

theorem winning_relaxed_extension_other_unfinished {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p q : Concrete.Hist N}
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q)
    (hwinq : (exactGame N blue).ArchitectWins H b σ q) (side : Bool)
    (hne : p.position.board.get side ≠ q.position.board.get side)
    (hr : (q.position.board.get side).relaxed = true) :
    (p.position.board.get (!side)).terminal = false := by
  cases ht : (p.position.board.get (!side)).terminal with
  | false => rfl
  | true =>
      have hext := History.reachable_word_extension (follow_history_path hpath)
      obtain ⟨as, has, hnew⟩ := hext.2 side
      obtain ⟨bs, hbs, _⟩ := hext.2 (!side)
      have hother := hbs.terminal_eq ht
      have hnon : as ≠ [] := by
        intro heq
        subst as
        exact hne ((LabeledWord.legalRun_nil_iff _ _).mp has)
      obtain ⟨a, tail, rfl⟩ := List.exists_cons_of_ne_nil hnon
      have ha : a.2 ∈ (q.position.board.get side).coordinates := by
        rw [LabeledWord.runAtoms_coordinates has.run]
        simp
      have hinc := ((Position.history_dataInvariant q).2.1 side).2
      have hlast : a.2 ≤ (q.position.board.get side).coordinates.getLastD 0 :=
        by simpa only [List.getLastD_eq_getLast?,
          List.getLast?_eq_some_getLast (List.ne_nil_of_mem ha), Option.getD_some] using
          (hinc.imp Nat.le_of_lt).rel_getLast ha
      have hsep : ∀ y ∈ (q.position.board.get (!side)).coordinates,
          y ≤ (q.position.board.get side).coordinates.getLastD 0 := by
        intro y hy
        rw [hother] at hy
        have hyb := ((Position.history_dataInvariant p).1 y
          (p.position.board.get_support_subset (!side) (LabeledWord.coordinate_mem_support hy))).2.2
        exact (hyb.trans_lt (hnew a (by simp))).le.trans hlast
      have hf := winning_relaxed_other_unfinished hHN hH blue hwinq side hr hsep
      rw [hother, ht] at hf
      cases hf

theorem winning_pending_marker_other_unfinished {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {r : Request} (hp : p.position.pending = some r) (side : Bool)
    (hm : (p.position.board.get side).markerEvent = true) :
    (p.position.board.get (!side)).terminal = false := by
  obtain ⟨d, hd, heq⟩ := winning_pending_marker hHN hH blue hwin hp side hm
  subst r
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨_, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
  have hstep := FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
  have hpath := Relation.ReflTransGen.single hstep
  have hqwin := hwin.of_reachable (exactGame N blue) hpath
  have hs := Concrete.response_spec hu
  have hr := hs.reply_spec hp
  have hrel := hr.advance_selected_leaf ((Position.history_dataInvariant p).2.1 side).1 hm hd
    (fun x hx => (Nat.zero_le (b p)).trans_lt (hub x hx))
  have hne : p.position.board.get side ≠ (Concrete.response p u).position.board.get side := by
    intro heq
    obtain ⟨n, xs, hc⟩ := hr.coordinates_extend
    rw [← heq] at hc
    have hh := congrArg List.length hc
    simp only [List.length_append, List.length_cons] at hh
    omega
  exact winning_relaxed_extension_other_unfinished hHN hH blue hpath hqwin side hne hrel

theorem winning_not_pending_of_other_complete {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool)
    (hcomplete : (p.position.board.get (!side)).terminal = true) :
    ¬ Macro.Pending (p.position.board.get side) := by
  rintro (⟨i, hi, hlt⟩ | ⟨hselected, j, hj, hlt⟩)
  · have hstart : (p.position.board.get side).parser ≠ .start := by
      obtain ⟨as, has⟩ := History.word_run p side
      cases as with
      | nil =>
          have heq := (LabeledWord.legalRun_nil_iff _ _).mp has
          simp [← heq, LabeledWord.initial] at hi
      | cons a as =>
          cases has with
          | cons _ _ _ v _ _ _ hr ht =>
              exact ht.parser_ne_start (LabeledWord.read_parser_ne_start hr)
    obtain ⟨q, d, hpath, hp, _hd, hm, _hindex⟩ :=
      winning_reach_body_marker hHN hH blue hwin side i hstart ⟨hi, hlt⟩
    obtain ⟨as, has, _⟩ :=
      (History.reachable_word_extension (follow_history_path hpath)).2 (!side)
    have hother := has.terminal_eq hcomplete
    have hf := winning_pending_marker_other_unfinished hHN hH blue
      (hwin.of_reachable (exactGame N blue) hpath) hp side hm
    rw [hother, hcomplete] at hf
    cases hf
  · have htarget : LabeledWord.UpToLeaf j (p.position.board.get side) :=
      ⟨hselected, hj, hlt.le⟩
    obtain ⟨q, hpath, _hn, hrel, hleaf, _hlabels, _hmarker⟩ :=
      winning_reach_selected_leaf hHN hH blue hwin side j htarget hlt
    have hne : p.position.board.get side ≠ q.position.board.get side := by
      intro heq
      rw [heq, hleaf] at hlt
      exact Nat.lt_irrefl _ hlt
    have hf := winning_relaxed_extension_other_unfinished hHN hH blue hpath
      (hwin.of_reachable (exactGame N blue) hpath) side hne hrel
    rw [hcomplete] at hf
    cases hf

#print axioms winning_not_pending_of_other_complete

end Payoff

end Erdos591.Positive.Game
