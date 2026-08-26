import ErdosProblems.Erdos591.NextMarkerReplayHistory
import ErdosProblems.Erdos591.InsideCompletionTriangle
import ErdosProblems.Erdos591.InsideLeafTriangle

/-!
# The last/next selected-body inside triangle

The first selected coarse body is exhausted. Continue the fine SU word
to its last selected body, replaying this as the next ST marker. The
two now-known body requests receive last/first overlapping leaf labels.
This yields the same completion configuration as the leaf-level case.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_triangle_of_root_forks {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
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
    (hrS : st.position.board.left.relaxed = true)
    (hnS : st.position.board.left.NoLeafPending)
    {i : ℕ} (hcoarse : LabeledWord.BeforeBody i st.position.board.left)
    (hnext : ∀ k ∈ st.position.board.left.rootLabel,
      st.position.board.left.bodyLabels.length < k → i ≤ k)
    (hfine : LabeledWord.BeforeBody i su.position.board.left)
    (hrootLast : ∀ k ∈ su.position.board.left.rootLabel, k ≤ i) :
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
  have hrSTeq := winning_pending_root_advance_zero hHN hH blue hwinOldST hpST false hsST
    (by simpa [hbST, Board.get] using hrS) (by simpa [hbST, Board.get] using hcoarse)
  have hpSTzero : oldST.position.pending = some ⟨false, .advance 0⟩ := by
    simpa [hrSTeq] using hpST
  let C := max oldTU.position.bound (b oldTU)
  let K := H \ Set.Iic C
  have hK : K.Infinite := hH.sdiff (Set.finite_Iic C)
  have hKH : K ⊆ H := fun _ hx => hx.1
  have hKN : K ⊆ N := hKH.trans hHN
  have hwinSUK := hwinSU.mono (exactGame N blue) hKH (fun _ => le_rfl)
  have hwinSTK := hwinOldST.mono (exactGame N blue) hKH (fun _ => le_rfl)
  obtain ⟨markerSU, markerST, d, hpathSU, hstepST, hpMarkerSU, hd, hnMarkerST,
      hshapeMarker, hmMarkerSU, hmMarkerST, hidxMarker, hotherST, _hinputs⟩ :=
    winning_next_marker_replay hKN hK blue su oldST hwinSUK false false hpSTzero
      (by simpa [hbST, Board.get] using hS) (by simpa [hbST, Board.get] using hrS)
      (by simpa [hbST, Board.get] using hnS) (by simpa [hbST, Board.get] using hcoarse)
      (by simpa [hbST, Board.get] using hnext) hfine
      (max oldST.position.bound (b oldST)) le_rfl
  have hwinMarkerSU := hwinSUK.of_reachable (exactGame N blue) hpathSU
  have hwinMarkerST := hwinSTK.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hstepST)
  obtain ⟨pendingST, e, hrequestST, hbPendingST, hpPendingST, he⟩ :=
    winning_request_at_marker hKN hK blue hwinMarkerST false hnMarkerST hmMarkerST
  let B := max (max markerSU.position.bound (b markerSU))
    (max pendingST.position.bound (b pendingST))
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hK B d e hd he
  obtain ⟨curSU, curST, hbodySU, hbodyST, _hnCurSU, _hnCurST, hshapeS, hrCurS, _hrCurST,
      hidxCur, hlabelsCur, _hlabelsST, hotherCurST, hsepCurSU⟩ :=
    winning_body_gluing_fresh hKN hK blue hwinMarkerSU false false L hpMarkerSU hpPendingST
      hmMarkerSU (by simpa [hbPendingST] using hmMarkerST)
      (by rw [hbPendingST]; exact hshapeMarker.symm) (le_max_left _ _) (le_max_right _ _)
  have hfullSU := hpathSU.trans hbodySU
  have hwinCurSU := hwinSUK.of_reachable (exactGame N blue) hfullSU
  have hwinCurST := hwinSTK.of_reachable (exactGame N blue)
    ((Relation.ReflTransGen.single hstepST).tail hrequestST |>.tail hbodyST)
  obtain ⟨as, has, _hasPool⟩ := follow_word_inputs hfullSU 0 (fun _ => Nat.zero_le _) false
  have hstartS : su.position.board.left.parser ≠ .start :=
    fun he => (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant st).2.1 false).1 hrS) (hS.parser_eq.trans he)
  have hroots := has.rootLabel_eq hstartS
  have hlength : curSU.position.board.left.bodyLabels.length = i := by
    have hl := congrArg List.length hlabelsCur
    simp only [List.length_append, List.length_singleton, Board.get] at hl hidxMarker
    omega
  have hlastCurS : ¬ Macro.Pending curSU.position.board.left :=
    last_selected_leaf_not_pending L
      (fun k hk => hlength ▸ hrootLast k (hroots ▸ hk))
      (by simp [LabeledWord.currentLabel, show curSU.position.board.left.bodyLabels =
        markerSU.position.board.left.bodyLabels ++ [L.lower] from hlabelsCur]) hidxCur
  obtain ⟨us, hus, husPool⟩ := follow_word_inputs hfullSU 0 (fun _ => Nat.zero_le _) true
  have hstartCurU := hus.parser_ne_start (LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant su).2.1 true).1 hrSU)
  have hpool : ∀ a ∈ us, a.2 ∈ K ∧ oldTU.position.bound < a.2 ∧ b oldTU < a.2 := by
    intro a ha
    have hm := (husPool a ha).1
    have hbig : C < a.2 := lt_of_not_ge hm.2
    exact ⟨hm, (le_max_left _ _).trans_lt hbig, (le_max_right _ _).trans_lt hbig⟩
  have hremainST : curST.position.board.right = st.position.board.right := by
    have hotherST' : markerST.position.board.right = st.position.board.right := by
      simpa [Board.get, hbST] using hotherST
    simpa [Board.get, hbPendingST, hotherST'] using hotherCurST
  have hsharedT : LabeledWord.SameStructure oldTU.position.board.left curST.position.board.right := by
    rw [hremainST, hbTU]
    exact History.sameStructure_of_coordinates tu st false true hT
  exact inside_completion_triangle hKN hK blue curST curSU oldTU hwinCurST hwinCurSU
    ((hwinTU.of_reachable (exactGame N blue) hpathTU).mono (exactGame N blue) hKH
      (fun _ => le_rfl)) (follow_mode_some hfullSU hmSU) hpTU hsTU
    (by simpa [hbTU, Board.get] using hstartT) (by simpa [hbTU, Board.get] using hliveT)
    (by simpa [hbTU, Board.get] using hlast false)
    (by simpa [hbTU, Board.get] using hstartU) (by simpa [hbTU, Board.get] using hlast true)
    hrCurS hsepCurSU hlastCurS hstartCurU
    (History.sameStructure_of_coordinates oldTU su true true (by simpa [hbTU, Board.get] using hU))
    hus hpool hshapeS hsharedT

#print axioms inside_triangle_of_root_forks

end Erdos591.Positive.Game.Payoff
