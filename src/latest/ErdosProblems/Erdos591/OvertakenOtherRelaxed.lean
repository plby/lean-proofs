import ErdosProblems.Erdos591.ArchitectPersistence
import ErdosProblems.Erdos591.ReplySeparation

/-! # Recover the opposite relaxed cursor from a fresh selected endpoint -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_overtaken_other_relaxed {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) (hr : (p.position.board.get side).relaxed = true)
    (hpos : 0 < (p.position.board.get (!side)).coordinates.length)
    (hsep : ∀ x ∈ (p.position.board.get (!side)).coordinates,
      x ≤ (p.position.board.get side).coordinates.getLastD 0) :
    (p.position.board.get (!side)).relaxed = true ∧
      (p.position.board.get (!side)).coordinates.getLastD 0 <
        (p.position.board.get side).coordinates.getLastD 0 := by
  have last_mem (xs : List ℕ) (hn : 0 < xs.length) : xs.getLastD 0 ∈ xs := by
    have hne : xs ≠ [] := by intro he; simp [he] at hn
    simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne,
      Option.getD_some] using List.getLast_mem hne
  obtain ⟨as, has⟩ := History.word_run p side
  have hm := last_mem _ (has.relaxed_coordinates_pos hr)
  have ho := last_mem _ hpos
  have hdisj : Disjoint (p.position.board.get (!side)).support
      (p.position.board.get side).support := by
    cases side
    · simpa only [Board.get, Bool.not_false] using (Position.history_dataInvariant p).2.2.symm
    · simpa only [Board.get, Bool.not_true, Board.DisjointWords] using
        (Position.history_dataInvariant p).2.2
  have hne : (p.position.board.get (!side)).coordinates.getLastD 0 ≠
      (p.position.board.get side).coordinates.getLastD 0 := by
    intro heq
    exact Finset.disjoint_left.mp hdisj (LabeledWord.coordinate_mem_support ho)
      (heq ▸ LabeledWord.coordinate_mem_support hm)
  have hlt := lt_of_le_of_ne (hsep _ ho) hne
  have hlive := winning_relaxed_other_unfinished hHN hH blue hwin side hr hsep
  exact ⟨winning_overtaken_relaxed hHN hH blue hwin (!side) hlive hpos
    (by simpa only [Bool.not_not] using hm) hlt, hlt⟩

#print axioms winning_overtaken_other_relaxed

end Erdos591.Positive.Game.Payoff
