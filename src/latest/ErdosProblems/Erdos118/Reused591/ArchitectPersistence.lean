import ErdosProblems.Erdos118.Reused591.ArchitectContinuation
import ErdosProblems.Erdos118.Reused591.CutPersistence

namespace Erdos118.Reused591

/-!
# Prefix obligations of a winning architect

The final clarity condition already constrains every reached history:
stored selected-body labels are nonempty, and any interval whose two
endpoints have been read has its permanent cut status. These statements
use an actual conservative winning continuation of the given strategy.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem follow_history_path {N H : Set ℕ} {blue : SimpleGraph G}
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p q : Concrete.Hist N}
    (h : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q) :
    Relation.ReflTransGen (fun p q => History.Next q p) p q :=
  Relation.ReflTransGen.mono
    (fun _ _ hs => FiniteResponseGame.FollowStep.next (exactGame N blue) hs) _ _ h

theorem Winning.side_clear {blue : SimpleGraph G} {mode : Bool} {b : Board}
    (h : Winning blue mode b) (side : Bool) :
    ∃ s t : G, ClearSide (b.get side) s t ∧ word t.val = (b.get (!side)).coordinates := by
  obtain ⟨s, t, hc, _, _⟩ := h
  cases side with
  | false => exact ⟨s, t, hc.1, hc.2.1.coordinates⟩
  | true => exact ⟨t, s, hc.2.1, hc.1.coordinates⟩

theorem winning_body_nonempty {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool) (i : ℕ)
    (hstart : (p.position.board.get side).parser ≠ .start)
    (hi : i < (p.position.board.get side).bodyLabels.length)
    (hsel : i + 1 ∈ (p.position.board.get side).rootLabel) :
    ((p.position.board.get side).bodyLabels.getD i ∅).Nonempty := by
  obtain ⟨q, hpath, _, _, hq⟩ := winning_continuation hHN hH blue hwin
  obtain ⟨s, t, hc, _⟩ := hq.side_clear side
  obtain ⟨as, has, _⟩ :=
    (History.reachable_word_extension (follow_history_path hpath)).2 side
  have hil : i < s.val.length := by
    rw [← hc.labels_length]
    exact hi.trans_le (has.bodyLabels_prefix hstart).length_le
  have hroot : i + 1 ∈ (q.position.board.get side).rootLabel := by
    rw [has.rootLabel_eq hstart]
    exact hsel
  have hn := (hc.root_mem_iff_body_nonempty hil).mp hroot
  simpa only [has.body_getD_eq hstart hi] using hn

theorem winning_prefix_cut_iff_relaxed {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p q : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ q)
    (hpq : Relation.ReflTransGen (fun p q => History.Next q p) p q)
    (side : Bool) {k : ℕ} (hlen : (p.position.board.get side).coordinates.length = k + 1)
    (hk : k + 1 < (q.position.board.get side).coordinates.length) :
    Cut (q.position.board.get side).coordinates (q.position.board.get (!side)).coordinates k ↔
      (p.position.board.get side).relaxed = true := by
  obtain ⟨r, hqr, _, _, hr⟩ := winning_continuation hHN hH blue hwin
  have hqr' := follow_history_path hqr
  obtain ⟨s, t, hc, hother⟩ := hr.side_clear side
  obtain ⟨as, has⟩ := History.word_run p side
  obtain ⟨bs, hbs, _⟩ := (History.reachable_word_extension (hpq.trans hqr')).2 side
  have hiff := history_cut_iff hqr' side hk
  rw [← hc.coordinates, ← hother] at hiff
  constructor
  · intro hcut
    exact hc.relaxed_of_cut_prefix has hbs hlen (hiff.mpr hcut)
  · intro hrel
    exact hiff.mp (hc.cut_of_relaxed_prefix has hbs hlen hrel)

theorem winning_relaxed_other_unfinished {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool)
    (hr : (p.position.board.get side).relaxed = true)
    (hsep : ∀ y ∈ (p.position.board.get (!side)).coordinates,
      y ≤ (p.position.board.get side).coordinates.getLastD 0) :
    (p.position.board.get (!side)).terminal = false := by
  cases ht : (p.position.board.get (!side)).terminal with
  | false => rfl
  | true =>
      obtain ⟨q, hpath, _, _, hq⟩ := winning_continuation hHN hH blue hwin
      obtain ⟨s, t, hc, hother⟩ := hq.side_clear side
      obtain ⟨as, has⟩ := History.word_run p side
      have hpos := has.relaxed_coordinates_pos hr
      obtain ⟨bs, hbs, _⟩ :=
        (History.reachable_word_extension (follow_history_path hpath)).2 side
      obtain ⟨cs, hcs, _⟩ :=
        (History.reachable_word_extension (follow_history_path hpath)).2 (!side)
      have hsame := hcs.terminal_eq ht
      have hcut := hc.cut_of_relaxed_prefix has hbs
        (k := (p.position.board.get side).coordinates.length - 1) (by omega) hr
      obtain ⟨_, y, hy, hlo, _⟩ := hcut
      rw [hother, hsame] at hy
      have hyold := hsep y hy
      rw [hc.coordinates, LabeledWord.runAtoms_coordinates hbs.run,
        List.getD_append _ _ _ _ (by omega)] at hlo
      have hlast : (p.position.board.get side).coordinates.getLastD 0 =
          (p.position.board.get side).coordinates.getD
            ((p.position.board.get side).coordinates.length - 1) 0 := by
        simp only [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
          List.getD_eq_getElem?_getD]
      rw [hlast] at hyold
      exact (not_lt_of_ge hyold hlo).elim

theorem winning_overtaken_relaxed {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool)
    (hlive : (p.position.board.get side).terminal = false)
    (hpos : 0 < (p.position.board.get side).coordinates.length)
    {y : ℕ} (hy : y ∈ (p.position.board.get (!side)).coordinates)
    (habove : (p.position.board.get side).coordinates.getLastD 0 < y) :
    (p.position.board.get side).relaxed = true := by
  obtain ⟨q, hpath, _, hdone, hq⟩ := winning_continuation hHN hH blue hwin
  obtain ⟨s, t, hc, hother⟩ := hq.side_clear side
  obtain ⟨as, has⟩ := History.word_run p side
  obtain ⟨bs, hbs, hbf⟩ :=
    (History.reachable_word_extension (follow_history_path hpath)).2 side
  obtain ⟨cs, hcs, _⟩ :=
    (History.reachable_word_extension (follow_history_path hpath)).2 (!side)
  apply hc.relaxed_of_cut_prefix has hbs
    (k := (p.position.board.get side).coordinates.length - 1) (by omega)
  cases bs with
  | nil =>
      have heq := (LabeledWord.legalRun_nil_iff _ _).mp hbs
      have ht := q.position.board.terminal_of_done hdone side
      rw [← heq, hlive] at ht
      contradiction
  | cons a bs =>
      have hcoords := LabeledWord.runAtoms_coordinates hbs.run
      have hindex : (p.position.board.get side).coordinates.length - 1 + 1 =
          (p.position.board.get side).coordinates.length := by omega
      have hlast : (p.position.board.get side).coordinates.getLastD 0 =
          (p.position.board.get side).coordinates.getD
            ((p.position.board.get side).coordinates.length - 1) 0 := by
        simp only [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
          List.getD_eq_getElem?_getD]
      have hybound : y ≤ p.position.bound :=
        ((Position.history_dataInvariant p).1 y
          (p.position.board.get_support_subset (!side)
            (LabeledWord.coordinate_mem_support hy))).2.2
      refine ⟨?_, y, ?_, ?_, ?_⟩
      · rw [hc.coordinates, hcoords, List.length_append, List.length_map, List.length_cons]
        omega
      · rw [hother]
        exact hcs.coordinates_prefix.sublist.subset hy
      · rw [hc.coordinates, hcoords, List.getD_append _ _ _ _ (by omega)]
        exact hlast ▸ habove
      · rw [hc.coordinates, hcoords, hindex,
          List.getD_append_right _ _ _ _ le_rfl]
        simpa using hybound.trans_lt (hbf a (by simp))

#print axioms winning_body_nonempty
#print axioms winning_prefix_cut_iff_relaxed
#print axioms winning_relaxed_other_unfinished
#print axioms winning_overtaken_relaxed

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
