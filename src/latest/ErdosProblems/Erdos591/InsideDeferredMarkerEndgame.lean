import ErdosProblems.Erdos591.DeferredNextMarker
import ErdosProblems.Erdos591.InsideLastFirstEndgame

/-!
# Inside endgame with the upper opposite next-body response still pending

Both lower selected parts have finished. Fix their actual completion
bounds before extending the upper singleton-prefix response. Its newly
created tail then supplies the prefix-aware two-tail/common-head endgame.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_deferred_marker_endgame {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (st su tu : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    (hmodeST : st.position.mode = some true) (hmodeSU : su.position.mode = some true)
    (hlastST : Relay.BothLast st.position.board) (hlastSU : Relay.BothLast su.position.board)
    (hrelST : ∀ side, (st.position.board.get side).relaxed = true)
    (hrelSU : ∀ side, (su.position.board.get side).relaxed = true)
    (hS : LabeledWord.SameStructure st.position.board.left su.position.board.left)
    (hT : LabeledWord.SameStructure st.position.board.right tu.position.board.left)
    (hpTU : tu.position.pending = some ⟨true, .advance 0⟩)
    (hrelTU : tu.position.board.right.relaxed = true)
    (hnoTU : tu.position.board.right.NoLeafPending) {i : ℕ}
    (hiTU : LabeledWord.BeforeBody i tu.position.board.right)
    (hnextTU : ∀ k ∈ tu.position.board.right.rootLabel,
      tu.position.board.right.bodyLabels.length < k → i ≤ k)
    {f : LabeledWord} {frontU : List (Finset ℕ × ℕ)}
    (hU : LabeledWord.SameStructure tu.position.board.right f)
    (hfrontU : LabeledWord.LegalRun f frontU su.position.board.right)
    (hcountU : su.position.board.right.bodyLabels.length = f.bodyLabels.length)
    (hstrictU : f.leafIndex < su.position.board.right.leafIndex)
    (hpoolU : ∀ a ∈ frontU, a.2 ∈ H ∧ max tu.position.bound (b tu) < a.2) :
    ¬ blue.CliqueFree 3 := by
  have hstartST (s : Bool) : (st.position.board.get s).parser ≠ .start :=
    LabeledWord.relaxed_ne_start ((Position.history_dataInvariant st).2.1 s).1 (hrelST s)
  have hstartSU (s : Bool) : (su.position.board.get s).parser ≠ .start :=
    LabeledWord.relaxed_ne_start ((Position.history_dataInvariant su).2.1 s).1 (hrelSU s)
  have hliveST (s : Bool) : (st.position.board.get s).terminal = false :=
    LabeledWord.relaxed_not_terminal ((Position.history_dataInvariant st).2.1 s).1.2.1
      ((Position.history_dataInvariant st).2.1 s).1.2.2 (hrelST s)
  have hliveSU (s : Bool) : (su.position.board.get s).terminal = false :=
    LabeledWord.relaxed_not_terminal ((Position.history_dataInvariant su).2.1 s).1.2.1
      ((Position.history_dataInvariant su).2.1 s).1.2.2 (hrelSU s)
  obtain ⟨pST, rST, hstPath, hbST, hpST, hsST⟩ := request_smaller_at_boundary hHN hH blue
    hwinST hmodeST (hliveST true) (hstartST false) (hlastST false)
  obtain ⟨pSU, rSU, hsuPath, hbSU, hpSU, hsSU⟩ := request_smaller_at_boundary hHN hH blue
    hwinSU hmodeSU (hliveSU true) (hstartSU false) (hlastSU false)
  let C := max (max pST.position.bound (b pST)) (max pSU.position.bound (b pSU))
  obtain ⟨qTU, htuStep, _hqNone, _hqMarker, _hqIndex, hqOther,
      anchor, hUanchor, tailU, htailU, hfreshU⟩ :=
    deferred_next_marker_from_prefix hHN hH blue σ tu true hpTU hrelTU hnoTU hiTU hnextTU
      hU hfrontU hcountU hstrictU ((Position.history_dataInvariant su).2.1 true).2 hpoolU C
  have hTprefix : ∃ anchor, LabeledWord.SameStructure pST.position.board.right anchor ∧
      ∃ as, LabeledWord.LegalRun anchor as qTU.position.board.left ∧
        ∀ a ∈ as, a.2 ∈ H ∧ max pST.position.bound (b pST) < a.2 := by
    refine ⟨qTU.position.board.left, ?_, [], .nil _, by simp⟩
    simpa [hbST, show qTU.position.board.left = tu.position.board.left from hqOther] using hT
  have hUprefix : ∃ anchor, LabeledWord.SameStructure pSU.position.board.right anchor ∧
      ∃ as, LabeledWord.LegalRun anchor as qTU.position.board.right ∧
        ∀ a ∈ as, a.2 ∈ H ∧ max pSU.position.bound (b pSU) < a.2 := by
    exact ⟨anchor, by simpa [hbSU] using hUanchor, tailU, htailU,
      fun a ha => ⟨(hfreshU a ha).1, (le_max_right _ _).trans_lt (hfreshU a ha).2⟩⟩
  exact triangle_of_pending_tails_then_common_head_from_prefixes hHN hH blue pST pSU qTU
    (hwinST.of_reachable (exactGame N blue) hstPath)
    (hwinSU.of_reachable (exactGame N blue) hsuPath)
    (hwinTU.of_reachable (exactGame N blue) (.single htuStep)) hpST hpSU hsST hsSU
    (by simpa [hbST, Board.get] using hstartST true)
    (by simpa [hbSU, Board.get] using hstartSU true)
    (by simpa [hbST, Board.get] using hlastST true)
    (by simpa [hbSU, Board.get] using hlastSU true)
    (by simpa [hbSU, Board.get] using hstartSU false)
    (by simpa [hbSU, Board.get] using hlastSU false)
    (by simpa [hbSU, Board.get] using hliveSU false)
    (by simpa [hbST, hbSU] using hS) hTprefix hUprefix

#print axioms inside_deferred_marker_endgame

end Erdos591.Positive.Game.Payoff
