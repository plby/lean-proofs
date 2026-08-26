import ErdosProblems.Erdos591.OutsideForks
import ErdosProblems.Erdos591.OutsideBoundary
import ErdosProblems.Erdos591.LastFirstHistory

/-!
# Gluing the third word on the right of the two outside plays

Both initial right requests are obtained before either right root is
chosen. Two-level last--first gluing then gives the last lower and first
upper selected leaf. The lower play is at its final smaller-word
completion boundary, while the upper left word is unchanged.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem outside_third_word {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (su tu : Concrete.Hist N)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    (hmodeSU : su.position.mode = some false) (hmodeTU : tu.position.mode = some false)
    (hpSU : su.position.pending = none) (hpTU : tu.position.pending = none)
    (hiSU : su.position.board.right = LabeledWord.initial)
    (hiTU : tu.position.board.right = LabeledWord.initial)
    (hrSU : su.position.board.left.relaxed = true)
    (hrTU : tu.position.board.left.relaxed = true) :
    ∃ q v, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) su q ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) tu v ∧
      q.position.pending = none ∧ v.position.pending = none ∧
      LabeledWord.SameStructure q.position.board.right v.position.board.right ∧
      v.position.board.left = tu.position.board.left ∧
      q.position.board.right.relaxed = true ∧ v.position.board.right.relaxed = true ∧
      q.position.board.left.terminal = false ∧ q.position.board.left.parser ≠ .start ∧
      ¬ Macro.Pending q.position.board.left ∧ ¬ Macro.Pending q.position.board.right := by
  have hwSU := ((Position.history_dataInvariant su).2.1 false).1
  have hwTU := ((Position.history_dataInvariant tu).2.1 false).1
  have hstartSU := LabeledWord.relaxed_ne_start hwSU hrSU
  obtain ⟨pSU, a, hsSU, hbSU, hrqSU, ha⟩ := outside_initial_right_request hHN hH blue hwinSU
    hmodeSU hpSU hiSU hrSU (LabeledWord.relaxed_not_terminal hwSU.2.1 hwSU.2.2 hrSU)
  obtain ⟨pTU, c, hsTU, hbTU, hrqTU, hc⟩ := outside_initial_right_request hHN hH blue hwinTU
    hmodeTU hpTU hiTU hrTU (LabeledWord.relaxed_not_terminal hwTU.2.1 hwTU.2.2 hrTU)
  obtain ⟨q, v, hpathQ, hpathV, hnQ, hnV, hshape, hrQ, hrV, hlastQ, hother, hsep⟩ :=
    winning_last_first_gluing_fresh hHN hH blue
      (hwinSU.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hsSU))
      (hwinTU.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hsTU))
      true true ha hc hrqSU hrqTU (by simpa [hbSU, Board.get] using hiSU)
      (by simpa [hbTU, Board.get] using hiTU)
  have hfullQ := hpathQ.head hsSU
  have hfullV := hpathV.head hsTU
  have hwinQ := hwinSU.of_reachable (exactGame N blue) hfullQ
  have hmodeQ := follow_mode_some hfullQ hmodeSU
  have hleftLive := winning_relaxed_other_unfinished hHN hH blue hwinQ true hrQ hsep
  obtain ⟨as, has, _⟩ :=
    (History.reachable_word_extension (follow_history_path hfullQ)).2 false
  have hleftStart := has.parser_ne_start hstartSU
  have hrightStart := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant q).2.1 true).1 hrQ
  have hleftLast := winning_no_pending_smaller hHN hH blue hwinQ hmodeQ
    hleftStart hrightStart hlastQ
  exact ⟨q, v, hfullQ, hfullV, hnQ, hnV, hshape,
    by simpa [hbTU, Board.get] using hother, hrQ, hrV, hleftLive,
    hleftStart, hleftLast, hlastQ⟩

#print axioms outside_third_word

end Erdos591.Positive.Game.Payoff
