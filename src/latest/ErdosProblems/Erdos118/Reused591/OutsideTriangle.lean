import ErdosProblems.Erdos118.Reused591.OutsideThirdWord
import ErdosProblems.Erdos118.Reused591.SharedTailTriangle

namespace Erdos118.Reused591

/-!
# The outside architect construction gives a blue triangle

Start with the coupled last-leaf checkpoint and its two delayed plays.
Fix the old first-word completion request, restrict all new inputs above
its bound, glue the third word, and replay the first-word completion.
The final two shared tails then give the three blue edges.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem outside_triangle_of_forks {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (st su tu : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    (hmST : st.position.mode = some false) (hmSU : su.position.mode = some false)
    (hmTU : tu.position.mode = some false)
    (hlast : Relay.BothLast st.position.board)
    (hrS : st.position.board.left.relaxed = true) (hrT : st.position.board.right.relaxed = true)
    (hnSU : su.position.pending = none) (hnTU : tu.position.pending = none)
    (hiSU : su.position.board.right = LabeledWord.initial)
    (hiTU : tu.position.board.right = LabeledWord.initial)
    (hrSU : su.position.board.left.relaxed = true) (hrTU : tu.position.board.left.relaxed = true)
    (hS : su.position.board.left.coordinates = st.position.board.left.coordinates)
    (hT : tu.position.board.left.coordinates = st.position.board.right.coordinates) :
    ¬ blue.CliqueFree 3 := by
  have hwS := ((Position.history_dataInvariant st).2.1 false).1
  have hwT := ((Position.history_dataInvariant st).2.1 true).1
  have hstartS := LabeledWord.relaxed_ne_start hwS hrS
  have hstartT := LabeledWord.relaxed_ne_start hwT hrT
  have hliveS := LabeledWord.relaxed_not_terminal hwS.2.1 hwS.2.2 hrS
  have hliveT := LabeledWord.relaxed_not_terminal hwT.2.1 hwT.2.2 hrT
  obtain ⟨old, oldRequest, hpathOld, hbOld, hpOld, hsOld⟩ :=
    request_smaller_at_boundary hHN hH blue hwinST hmST hliveS hstartT (hlast true)
  let B := max old.position.bound (b old)
  let K := H \ Set.Iic B
  have hK : K.Infinite := hH.sdiff (Set.finite_Iic B)
  have hKH : K ⊆ H := fun _ hx => hx.1
  have hKN : K ⊆ N := hKH.trans hHN
  have hwinOld : (exactGame N blue).ArchitectWins K b σ old :=
    (hwinST.of_reachable (exactGame N blue) hpathOld).mono
      (exactGame N blue) hKH (fun _ => le_rfl)
  have hwinSUK := hwinSU.mono (exactGame N blue) hKH (fun _ => le_rfl)
  have hwinTUK := hwinTU.mono (exactGame N blue) hKH (fun _ => le_rfl)
  obtain ⟨curSU, curTU, hpathSU, hpathTU, _hnCurSU, _hnCurTU, hU, hTOther,
      hrU, _hrU', hliveCurS, hstartCurS, hlastCurS, hlastCurU⟩ :=
    outside_third_word hKN hK blue su tu hwinSUK hwinTUK hmSU hmTU hnSU hnTU
      hiSU hiTU hrSU hrTU
  have hwinCurSU := hwinSUK.of_reachable (exactGame N blue) hpathSU
  have hwinCurTU := hwinTUK.of_reachable (exactGame N blue) hpathTU
  have hwU := ((Position.history_dataInvariant curSU).2.1 true).1
  have hstartU := LabeledWord.relaxed_ne_start hwU hrU
  have hliveU := LabeledWord.relaxed_not_terminal hwU.2.1 hwU.2.2 hrU
  obtain ⟨pendingSU, rSU, hrequestSU, hbSU, hpSU, hsSU⟩ := request_smaller_at_boundary hKN hK blue
    hwinCurSU (follow_mode_some hpathSU hmSU) hliveCurS hstartU hlastCurU
  have hfullSU := hpathSU.trans hrequestSU
  obtain ⟨xs, hxs, hxsPool⟩ := follow_word_inputs hfullSU 0 (fun _ => Nat.zero_le _) false
  have hbefore : LabeledWord.LegalRun su.position.board.left xs
      (pendingSU.position.board.get rSU.side) := by simpa [hsSU, Board.get] using hxs
  have hfresh : ∀ a ∈ xs, a.2 ∈ K ∧ old.position.bound < a.2 ∧ b old < a.2 := by
    intro a ha
    have hmem := (hxsPool a ha).1
    have hB : B < a.2 := lt_of_not_ge hmem.2
    exact ⟨hmem, (le_max_left _ _).trans_lt hB, (le_max_right _ _).trans_lt hB⟩
  obtain ⟨oldAtoms, hOldAtoms⟩ := History.word_run old oldRequest.side
  obtain ⟨suAtoms, hSUAtoms⟩ := History.word_run su false
  have hsameS : LabeledWord.SameStructure (old.position.board.get oldRequest.side)
      su.position.board.left := LabeledWord.sameStructure_of_initial_runs hOldAtoms.run hSUAtoms.run
        (by simpa [hbOld, hsOld, Board.get] using hS.symm)
  obtain ⟨doneST, doneSU, hstepST, hstepSU, _hnDoneST, _hnDoneSU, htermSU, hshapeS,
      hotherST, hotherSU⟩ := complete_shared_extension hKN hK blue old pendingSU hpOld hpSU
    (by simpa [hbOld, hsOld, Board.get] using hstartS)
    (by simpa [hbOld, hsOld, Board.get] using hlast false)
    (by simpa [hbSU, hsSU, Board.get] using hstartCurS)
    (by simpa [hbSU, hsSU, Board.get] using hlastCurS) hsameS hbefore hfresh
  have hshapeS' : LabeledWord.SameStructure doneST.position.board.left
      doneSU.position.board.left := by simpa [hsOld, hsSU, Board.get] using hshapeS
  have htermS : doneSU.position.board.left.terminal = true := by
    simpa [hsSU, Board.get] using htermSU
  have htermS' : doneST.position.board.left.terminal = true := by
    change decide (doneST.position.board.left.parser = .blocks 0) = true
    rw [hshapeS'.parser_eq]
    exact htermS
  have hremainT : doneST.position.board.right = st.position.board.right := by
    simpa [hsOld, hbOld, Board.get] using hotherST
  have hremainU : doneSU.position.board.right = curSU.position.board.right := by
    simpa [hsSU, hbSU, Board.get] using hotherSU
  obtain ⟨stAtoms, hSTAtoms⟩ := History.word_run st true
  obtain ⟨tuAtoms, hTUAtoms⟩ := History.word_run tu false
  have hsameT : LabeledWord.SameStructure st.position.board.right tu.position.board.left :=
    LabeledWord.sameStructure_of_initial_runs hSTAtoms.run hTUAtoms.run hT.symm
  have hsharedT : LabeledWord.SameStructure doneST.position.board.right
      curTU.position.board.left := by rw [hremainT, hTOther]; exact hsameT
  have hsharedU : LabeledWord.SameStructure doneSU.position.board.right
      curTU.position.board.right := by rw [hremainU]; exact hU
  exact triangle_after_shared_first hKN hK blue doneST doneSU curTU
    (hwinOld.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hstepST))
    ((hwinCurSU.of_reachable (exactGame N blue) hrequestSU).of_reachable
      (exactGame N blue) (Relation.ReflTransGen.single hstepSU)) hwinCurTU
    (by simpa [hremainT, Board.get] using hstartT)
    (by simpa [hremainU, Board.get] using hstartU)
    (by simpa [hremainT, Board.get] using hlast true) (by simpa [hremainU] using hlastCurU)
    htermS' htermS (by simpa [hremainT, Board.get] using hliveT)
    (by simpa [hremainU, Board.get] using hliveU)
    hshapeS'.coordinates_eq hsharedT hsharedU

theorem outside_positive_opening_triangle {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) {a : ℕ} (ha : 0 < a)
    (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hboard : p.position.board = Board.initial) (hmode : p.position.mode = some false) :
    ¬ blue.CliqueFree 3 := by
  obtain ⟨st, _hpath, hwinST, hmST, hlast, hf⟩ := Relay.outside_forks hHN hH blue hwin ha hp
    hboard hmode
  obtain ⟨hrS, su, hwinSU, hnSU, hmSU, hS, hrSU, hiSU⟩ := hf false
  obtain ⟨hrT, tu, hwinTU, hnTU, hmTU, hT, hrTU, hiTU⟩ := hf true
  exact outside_triangle_of_forks hHN hH blue st su tu hwinST hwinSU hwinTU hmST hmSU hmTU
    hlast hrS hrT hnSU hnTU hiSU hiTU hrSU hrTU hS hT

#print axioms outside_triangle_of_forks
#print axioms outside_positive_opening_triangle

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
