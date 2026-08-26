import ErdosProblems.Erdos118.Reused591.ArchitectPersistence

namespace Erdos118.Reused591

/-!
# Forced architect requests

At a selected body marker, a winning request that continues this word
must have positive label size. Consequently it is an advance request,
not a finish request. The proof uses a genuine conservative response
and its winning continuation, with persistent original label slots.
-/

namespace Erdos591.Positive.Game

namespace Concrete

theorem Replies.follow {N H : Set ℕ} (payoff : Bool → Board → Bool)
    {b : Hist N → ℕ} (σ : (game N payoff).ArchitectStrategy)
    {p q : Hist N} {u : Finset ℕ} (h : Replies p u q)
    (huH : (↑u : Set ℕ) ⊆ H) (hub : ∀ x ∈ u, b p < x) :
    (game N payoff).FollowStep σ H b p q := by
  have hk : (game N payoff).kind p = .builder := by
    apply (kind_builder_iff payoff p).mpr
    cases h with
    | mk r _ hp _ _ _ => exact ⟨r, hp⟩
  have hf := FiniteResponseGame.FollowStep.builder (game N payoff) σ p u hk h.mem_family huH hub
  simpa only [game, response_eq h] using hf

theorem Replies.reply_spec {N : Set ℕ} {p q : Hist N} {u : Finset ℕ}
    (h : Replies p u q) {r : Request} (hp : p.position.pending = some r) :
    Reply p.position.board r u q.position.board := by
  cases h with
  | mk s board hpend hr _ _ =>
      have heq : s = r := Option.some.inj (hpend.symm.trans hp)
      subst s
      simpa [Position.reply] using hr

theorem Replies.fresh {N : Set ℕ} {p q : Hist N} {u : Finset ℕ}
    (h : Replies p u q) : ∀ x ∈ u, p.position.bound < x := by
  cases h with
  | mk _ _ _ _ _ hfresh => exact hfresh

end Concrete

namespace Payoff

open Erdos591.Negative.Exact

theorem winning_reply_selected_size_pos {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {q : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ q)
    {board : Board} {r : Request} {u : Finset ℕ}
    (hreply : Reply board r u q.position.board)
    (hmarker : (board.get r.side).markerEvent = true) : 0 < r.size := by
  obtain ⟨D, n, v, as, hcard, hread, htail⟩ := hreply.first_read
  obtain ⟨z, hqz, _, _, hz⟩ := winning_continuation hHN hH blue hwin
  obtain ⟨s, t, hc, _⟩ := hz.side_clear r.side
  obtain ⟨bs, hbs, _⟩ :=
    (History.reachable_word_extension (follow_history_path hqz)).2 r.side
  have hnon : D.Nonempty := by
    cases hp : (board.get r.side).parser with
    | start => simp [LabeledWord.markerEvent, hp] at hmarker
    | leaves r k => simp [LabeledWord.markerEvent, hp] at hmarker
    | blocks k =>
        cases k with
        | zero => simp [LabeledWord.markerEvent, hp] at hmarker
        | succ k =>
            have hsel : (board.get r.side).bodyLabels.length + 1 ∈
                (board.get r.side).rootLabel := by
              simpa [LabeledWord.markerEvent, hp] using hmarker
            exact hc.selected_body_label_nonempty hread (htail.append hbs) hp hsel
  rw [← hcard]
  exact Finset.card_pos.mpr hnon

theorem winning_pending_marker_size_pos {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {r : Request} (hp : p.position.pending = some r)
    (hmarker : (p.position.board.get r.side).markerEvent = true) : 0 < r.size := by
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨r, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
  have hf := FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
  have hqwin := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hf)
  have hr := (Concrete.response_spec hu).reply_spec hp
  exact winning_reply_selected_size_pos hHN hH blue hqwin hr hmarker

theorem winning_pending_marker_advance {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {r : Request} (hp : p.position.pending = some r)
    (hmarker : (p.position.board.get r.side).markerEvent = true) :
    ∃ d, 0 < d ∧ r.command = .advance d := by
  have hpos := winning_pending_marker_size_pos hHN hH blue hwin hp hmarker
  cases hc : r.command with
  | finish => simp [Request.size, hc] at hpos
  | advance d => exact ⟨d, by simpa [Request.size, hc] using hpos, rfl⟩

theorem winning_reply_cannot_continue_relaxed {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p q : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ q)
    (hpq : Relation.ReflTransGen (fun p q => History.Next q p) p q)
    {r : Request} {u : Finset ℕ} (hreply : Reply p.position.board r u q.position.board)
    (hr : (p.position.board.get r.side).relaxed = true)
    (hsep : ∀ y ∈ (p.position.board.get (!r.side)).coordinates,
      y ≤ (p.position.board.get r.side).coordinates.getLastD 0) : False := by
  obtain ⟨as, has⟩ := History.word_run p r.side
  have hpos := has.relaxed_coordinates_pos hr
  obtain ⟨n, xs, hcoords⟩ := hreply.coordinates_extend
  have hk : (p.position.board.get r.side).coordinates.length - 1 + 1 <
      (q.position.board.get r.side).coordinates.length := by
    rw [hcoords, List.length_append, List.length_cons]
    omega
  have hcut := (winning_prefix_cut_iff_relaxed hHN hH blue hwin hpq r.side
    (k := (p.position.board.get r.side).coordinates.length - 1) (by omega) hk).mpr hr
  obtain ⟨_, y, hy, hlo, _⟩ := hcut
  rw [hreply.other_eq] at hy
  have hyold := hsep y hy
  rw [hcoords, List.getD_append _ _ _ _ (by omega)] at hlo
  have hlast : (p.position.board.get r.side).coordinates.getLastD 0 =
      (p.position.board.get r.side).coordinates.getD
        ((p.position.board.get r.side).coordinates.length - 1) 0 := by
    simp only [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
      List.getD_eq_getElem?_getD]
  rw [hlast] at hyold
  exact not_lt_of_ge hyold hlo

theorem winning_pending_switch {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {r : Request} (hp : p.position.pending = some r) (side : Bool)
    (hr : (p.position.board.get side).relaxed = true)
    (hsep : ∀ y ∈ (p.position.board.get (!side)).coordinates,
      y ≤ (p.position.board.get side).coordinates.getLastD 0) : r.side = !side := by
  have hne : r.side ≠ side := by
    intro heq
    have hk : (exactGame N blue).kind p = .builder :=
      (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨r, hp⟩
    obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
    have hf := FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
    have hqwin := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hf)
    have hreply := (Concrete.response_spec hu).reply_spec hp
    exact winning_reply_cannot_continue_relaxed hHN hH blue hqwin
      (follow_history_path (Relation.ReflTransGen.single hf)) hreply
      (by simpa [heq] using hr) (by simpa [heq] using hsep)
  exact Bool.eq_not_of_ne hne

theorem winning_reply_marker_same {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p q : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ q) {u : Finset ℕ}
    (hreplies : Concrete.Replies p u q) {r : Request} (hp : p.position.pending = some r)
    (side : Bool) (hm : (p.position.board.get side).markerEvent = true) : r.side = side := by
  by_contra hne
  have hs : r.side = !side := Bool.eq_not_of_ne hne
  have hreply := hreplies.reply_spec hp
  have heq : q.position.board.get side = p.position.board.get side := by
    simpa only [hs, Bool.not_not] using hreply.other_eq
  obtain ⟨n, hn, xs, hcoords⟩ := hreply.coordinates_extend_input
    (fun x hx => (Nat.zero_le p.position.bound).trans_lt (hreplies.fresh x hx))
  have hnmem : n ∈ (q.position.board.get (!side)).coordinates := by
    rw [hs] at hcoords
    simp [hcoords]
  have habove : (q.position.board.get side).coordinates.getLastD 0 < n := by
    rw [heq]
    exact (Position.history_last_bound p side).trans_lt (hreplies.fresh n hn)
  obtain ⟨as, has⟩ := History.word_run p side
  have hpos : 0 < (q.position.board.get side).coordinates.length := by
    rw [heq]
    exact has.marker_coordinates_pos hm
  have hlive : (q.position.board.get side).terminal = false := by
    rw [heq]
    exact LabeledWord.marker_not_terminal hm
  have hrel := winning_overtaken_relaxed hHN hH blue hwin side hlive hpos hnmem habove
  rw [heq] at hrel
  have hw := (Position.history_dataInvariant p).2.1 side
  have hnot := LabeledWord.relaxed_not_marker hw.1.2.1 hw.1.2.2 hrel
  simp [hm] at hnot

theorem winning_pending_marker_same {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {r : Request} (hp : p.position.pending = some r) (side : Bool)
    (hm : (p.position.board.get side).markerEvent = true) : r.side = side := by
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨r, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
  have hf := FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
  have hqwin := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hf)
  exact winning_reply_marker_same hHN hH blue hqwin (Concrete.response_spec hu) hp side hm

theorem winning_pending_marker {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {r : Request} (hp : p.position.pending = some r) (side : Bool)
    (hm : (p.position.board.get side).markerEvent = true) :
    ∃ d, 0 < d ∧ r = ⟨side, .advance d⟩ := by
  have hs := winning_pending_marker_same hHN hH blue hwin hp side hm
  obtain ⟨d, hd, hc⟩ := winning_pending_marker_advance hHN hH blue hwin hp (by simpa [hs] using hm)
  refine ⟨d, hd, ?_⟩
  have heq : r = ⟨r.side, r.command⟩ := rfl
  simpa only [hs, hc] using heq

#print axioms winning_pending_marker_advance
#print axioms winning_pending_switch
#print axioms winning_pending_marker

end Payoff

end Erdos591.Positive.Game

end Erdos118.Reused591
