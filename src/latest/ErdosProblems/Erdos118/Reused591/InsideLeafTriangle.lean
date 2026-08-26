import ErdosProblems.Erdos118.Reused591.NextLeafReplayHistory
import ErdosProblems.Erdos118.Reused591.SharedHeadTriangle
import ErdosProblems.Erdos118.Reused591.ManagedWord

namespace Erdos118.Reused591

/-!
# The last/next selected-leaf inside triangle

The lower TU play has exhausted its selections, while its last T and U
prefixes are the first target prefixes in ST and SU. Continue SU to its
last selected S leaf and replay it as the next selected ST leaf. Complete
U in both plays, then obtain both remaining heads from one winning ST run.
-/

namespace Erdos591.Positive.Game

open Erdos591.Negative.Exact
open Payoff

theorem History.sameStructure_of_coordinates {N : Set ℕ} (p q : Concrete.Hist N)
    (s t : Bool) (h : (p.position.board.get s).coordinates =
      (q.position.board.get t).coordinates) :
    LabeledWord.SameStructure (p.position.board.get s) (q.position.board.get t) := by
  obtain ⟨as, has⟩ := History.word_run p s
  obtain ⟨bs, hbs⟩ := History.word_run q t
  exact LabeledWord.sameStructure_of_initial_runs has.run hbs.run h

namespace Payoff

theorem inside_triangle_of_leaf_forks {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (st su tu : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    (hmSU : su.position.mode = some true) (hmTU : tu.position.mode = some true)
    (hlast : Relay.BothLast tu.position.board)
    (hrT : tu.position.board.left.relaxed = true) (hrU : tu.position.board.right.relaxed = true)
    (hrST : st.position.board.right.relaxed = true)
    (hsepST : ∀ y ∈ st.position.board.left.coordinates,
      y ≤ st.position.board.right.coordinates.getLastD 0)
    (hrSU : su.position.board.right.relaxed = true)
    (hS : LabeledWord.SameStructure st.position.board.left su.position.board.left)
    (hT : tu.position.board.left.coordinates = st.position.board.right.coordinates)
    (hU : tu.position.board.right.coordinates = su.position.board.right.coordinates)
    {j : ℕ} (hcoarse : LabeledWord.UpToLeaf j st.position.board.left)
    (hstrict : st.position.board.left.leafIndex < j)
    (hnext : ∀ k ∈ st.position.board.left.currentLabel,
      st.position.board.left.leafIndex < k → j ≤ k)
    (hfine : LabeledWord.UpToLeaf j su.position.board.left)
    (hrootLast : ∀ i ∈ su.position.board.left.rootLabel,
      i ≤ su.position.board.left.bodyLabels.length)
    (hleafLast : ∀ k ∈ su.position.board.left.currentLabel, k ≤ j) :
    ¬ blue.CliqueFree 3 := by
  have hwT := ((Position.history_dataInvariant tu).2.1 false).1
  have hwU := ((Position.history_dataInvariant tu).2.1 true).1
  have hstartT := LabeledWord.relaxed_ne_start hwT hrT
  have hstartU := LabeledWord.relaxed_ne_start hwU hrU
  have hliveT := LabeledWord.relaxed_not_terminal hwT.2.1 hwT.2.2 hrT
  have hliveU := LabeledWord.relaxed_not_terminal hwU.2.1 hwU.2.2 hrU
  obtain ⟨oldTU, rTU, hpathTU, hbTU, hpTU, hsTU⟩ :=
    request_smaller_at_boundary hHN hH blue hwinTU hmTU hliveU hstartT (hlast false)
  have hwST := ((Position.history_dataInvariant st).2.1 true).1
  have hliveST := LabeledWord.relaxed_not_terminal hwST.2.1 hwST.2.2 hrST
  obtain ⟨oldST, rST, hpathST, hbST, hpST⟩ :=
    request_on_live_board σ st (Board.not_done_of_live hliveST)
  have hwinOldST := hwinST.of_reachable (exactGame N blue) hpathST
  have hsST : rST.side = false := winning_pending_switch hHN hH blue hwinOldST hpST true
    (by simpa [hbST, Board.get] using hrST) (by simpa [hbST, Board.get] using hsepST)
  have hrSTeq := winning_pending_leaf_advance_zero hHN hH blue hwinOldST hpST false hsST
    (by simpa [hbST, Board.get] using hcoarse) (by simpa [hbST, Board.get] using hstrict)
  have hpSTzero : oldST.position.pending = some ⟨false, .advance 0⟩ := by
    simpa [hrSTeq] using hpST
  let B := max (max oldST.position.bound (b oldST)) (max oldTU.position.bound (b oldTU))
  obtain ⟨curSU, curST, hpathSU, hstepST, _hnSU, _hnST, hshapeS, hrCurS, _hrCurST,
      hidx, hotherST, hruns, hlabels, _hmarker, hsepSU⟩ :=
    winning_next_leaf_replay_fresh hHN hH blue su oldST hwinSU false false hpSTzero
      (by simpa [hbST, Board.get] using hS) (by simpa [hbST, Board.get] using hcoarse)
      (by simpa [hbST, Board.get] using hstrict) (by simpa [hbST, Board.get] using hnext)
      hfine B (le_max_left _ _)
  have hwinCurSU := hwinSU.of_reachable (exactGame N blue) hpathSU
  have hwinCurST := hwinOldST.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hstepST)
  have hwCurS := ((Position.history_dataInvariant curSU).2.1 false).1
  have hstartCurS := LabeledWord.relaxed_ne_start hwCurS hrCurS
  have hliveCurS := LabeledWord.relaxed_not_terminal hwCurS.2.1 hwCurS.2.2 hrCurS
  have hliveCurU := winning_relaxed_other_unfinished hHN hH blue hwinCurSU false hrCurS hsepSU
  obtain ⟨as, has, _hasPool⟩ := hruns false
  obtain ⟨r, k, hparse⟩ := hfine.parser_leaves ((Position.history_dataInvariant su).2.1 false).1
  have hroots := has.rootLabel_eq (by simp [Board.get, hparse])
  have hlastCurS : ¬ Macro.Pending curSU.position.board.left := by
    have hlen := congrArg List.length hlabels
    have hcurrent : curSU.position.board.left.currentLabel = su.position.board.left.currentLabel :=
      congrArg (fun ls => ls.getLastD ∅) hlabels
    intro hpending
    rcases hpending with ⟨i, himem, hilt⟩ | ⟨_, k, hkmem, hklt⟩
    · have hi := hrootLast i (hroots ▸ himem)
      change curSU.position.board.left.bodyLabels.length = su.position.board.left.bodyLabels.length
        at hlen
      omega
    · have hk := hleafLast k (hcurrent ▸ hkmem)
      change curSU.position.board.left.leafIndex = j at hidx
      omega
  obtain ⟨us, hus, husPool⟩ := hruns true
  have hstartFineU := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant su).2.1 true).1 hrSU
  have hstartCurU := hus.parser_ne_start hstartFineU
  have hmCurSU := follow_mode_some hpathSU hmSU
  have hlastCurU := winning_no_pending_smaller hHN hH blue hwinCurSU hmCurSU
    hstartCurU hstartCurS hlastCurS
  obtain ⟨pendingSU, rSU, hrequestSU, hbSU, hpSU, hsSU⟩ :=
    request_smaller_at_boundary hHN hH blue hwinCurSU hmCurSU hliveCurU hstartCurS hlastCurS
  have hbefore : LabeledWord.LegalRun su.position.board.right us
      (pendingSU.position.board.get rSU.side) := by simpa [hsSU, hbSU, Board.get] using hus
  have hpool : ∀ a ∈ us, a.2 ∈ H ∧ oldTU.position.bound < a.2 ∧ b oldTU < a.2 := by
    intro a ha
    have hbig : max oldTU.position.bound (b oldTU) < a.2 :=
      (le_max_right _ _).trans_lt (husPool a ha).2
    exact ⟨(husPool a ha).1, (le_max_left _ _).trans_lt hbig,
      (le_max_right _ _).trans_lt hbig⟩
  have hsameU := History.sameStructure_of_coordinates oldTU su rTU.side true
    (by simpa [hsTU, hbTU, Board.get] using hU)
  obtain ⟨doneTU, doneSU, hstepTU, hstepSU, _hnDoneTU, _hnDoneSU, htermSU, hshapeU,
      hotherTU, hotherSU⟩ := complete_shared_extension hHN hH blue oldTU pendingSU hpTU hpSU
    (by simpa [hsTU, hbTU, Board.get] using hstartU)
    (by simpa [hsTU, hbTU, Board.get] using hlast true)
    (by simpa [hsSU, hbSU, Board.get] using hstartCurU)
    (by simpa [hsSU, hbSU, Board.get] using hlastCurU) hsameU hbefore hpool
  have hshapeU' : LabeledWord.SameStructure doneTU.position.board.right
      doneSU.position.board.right := by simpa [hsTU, hsSU, Board.get] using hshapeU
  have htermU : doneSU.position.board.right.terminal = true := by
    simpa [hsSU, Board.get] using htermSU
  have htermU' : doneTU.position.board.right.terminal = true := by
    change decide (doneTU.position.board.right.parser = .blocks 0) = true
    rw [hshapeU'.parser_eq]
    exact htermU
  have hremainT : doneTU.position.board.left = tu.position.board.left := by
    simpa [hsTU, hbTU, Board.get] using hotherTU
  have hremainS : doneSU.position.board.left = curSU.position.board.left := by
    simpa [hsSU, hbSU, Board.get] using hotherSU
  have hremainST : curST.position.board.right = st.position.board.right := by
    simpa [hbST, Board.get] using hotherST
  have hsharedS : LabeledWord.SameStructure doneSU.position.board.left
      curST.position.board.left := by rw [hremainS]; exact hshapeS.symm
  have hsharedT : LabeledWord.SameStructure doneTU.position.board.left
      curST.position.board.right := by
    rw [hremainT, hremainST]
    exact History.sameStructure_of_coordinates tu st false true hT
  exact triangle_after_shared_last hHN hH blue curST doneSU doneTU hwinCurST
    ((hwinCurSU.of_reachable (exactGame N blue) hrequestSU).of_reachable
      (exactGame N blue) (Relation.ReflTransGen.single hstepSU))
    ((hwinTU.of_reachable (exactGame N blue) hpathTU).of_reachable
      (exactGame N blue) (Relation.ReflTransGen.single hstepTU))
    (by simpa [hremainS, Board.get] using hstartCurS)
    (by simpa [hremainT, Board.get] using hstartT)
    (by simpa [hremainS] using hlastCurS) (by simpa [hremainT, Board.get] using hlast false)
    htermU htermU' (by simpa [hremainS, Board.get] using hliveCurS)
    (by simpa [hremainT, Board.get] using hliveT)
    hshapeU'.coordinates_eq.symm hsharedS hsharedT

#print axioms inside_triangle_of_leaf_forks

end Payoff

end Erdos591.Positive.Game

end Erdos118.Reused591
