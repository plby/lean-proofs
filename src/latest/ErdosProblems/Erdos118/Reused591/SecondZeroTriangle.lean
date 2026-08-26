import ErdosProblems.Erdos118.Reused591.CompletePairResponses
import ErdosProblems.Erdos118.Reused591.SharedTailTriangle

namespace Erdos118.Reused591

/-!
# A zero second-word request forces a blue triangle

One high winning initial play supplies a complete blue pair. Either
word of this pair is an actual zero-size response after the fixed first
selected leaf. The first-word prefix is then completed identically in
the two resulting winning histories. This argument is independent of
the orientation and discharges all such zero-request subcases.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem pending_second_zero_triangle {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {r : Request} (hp : p.position.pending = some r) (hside : r.side = true)
    (hsize : r.size = 0) (hinit : p.position.board.right = LabeledWord.initial)
    (hrel : p.position.board.left.relaxed = true) : ¬ blue.CliqueFree 3 := by
  let B := max p.position.bound (b p)
  obtain ⟨tu, hwinTU, t, u, hT, hU, htH, huH, htB, huB⟩ :=
    winning_complete_pair_responses_above hHN hH blue hroot B
  have hinit' : p.position.board.get r.side = LabeledWord.initial := by
    simpa [hside, Board.get] using hinit
  obtain ⟨pt, hstepT, hboardT, hnT⟩ := Concrete.follow_reply hHN (payoff blue) σ p hp
    (t.reply p.position.board r hinit' hsize) htH
    (fun x hx => ⟨(le_max_left _ _).trans_lt (htB x hx),
      (le_max_right _ _).trans_lt (htB x hx)⟩)
  obtain ⟨pu, hstepU, hboardU, hnU⟩ := Concrete.follow_reply hHN (payoff blue) σ p hp
    (u.reply p.position.board r hinit' hsize) huH
    (fun x hx => ⟨(le_max_left _ _).trans_lt (huB x hx),
      (le_max_right _ _).trans_lt (huB x hx)⟩)
  have htLeft : pt.position.board.left = p.position.board.left := by
    simp [hboardT, hside, Board.update]
  have huLeft : pu.position.board.left = p.position.board.left := by
    simp [hboardU, hside, Board.update]
  have htRight : pt.position.board.right = t.cursor := by simp [hboardT, hside, Board.update]
  have huRight : pu.position.board.right = u.cursor := by simp [hboardU, hside, Board.update]
  have hwinT := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hstepT)
  have hwinU := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hstepU)
  have hw := ((Position.history_dataInvariant p).2.1 false).1
  have hstart := LabeledWord.relaxed_ne_start hw hrel
  have hlive := LabeledWord.relaxed_not_terminal hw.2.1 hw.2.2 hrel
  have htermT : pt.position.board.right.terminal = true := by rw [htRight]; exact t.terminal
  have htermU : pu.position.board.right.terminal = true := by rw [huRight]; exact u.terminal
  have hlastT := winning_not_pending_of_other_complete hHN hH blue hwinT false htermT
  have hlastU := winning_not_pending_of_other_complete hHN hH blue hwinU false htermU
  obtain ⟨pst, rST, hpathST, hbST, hpST, hsST⟩ := request_opposite_complete σ pt true htermT
    (by simpa [htLeft, Board.get] using hlive)
  obtain ⟨psu, rSU, hpathSU, hbSU, hpSU, hsSU⟩ := request_opposite_complete σ pu true htermU
    (by simpa [huLeft, Board.get] using hlive)
  have hsame : LabeledWord.SameStructure (pst.position.board.get rST.side)
      (psu.position.board.get rSU.side) := by
    simpa [hbST, hbSU, hsST, hsSU, Board.get, htLeft, huLeft] using
      LabeledWord.SameStructure.refl p.position.board.left
  obtain ⟨st, su, hsOld, hsNew, hnST, hnSU, hterm, hshape, hotherST, hotherSU⟩ :=
    complete_shared_extension hHN hH blue pst psu hpST hpSU
      (by simpa [hbST, hsST, Board.get, htLeft] using hstart)
      (by simpa [hbST, hsST, Board.get] using hlastT)
      (by simpa [hbSU, hsSU, Board.get, huLeft] using hstart)
      (by simpa [hbSU, hsSU, Board.get] using hlastU) hsame
      (LabeledWord.LegalRun.nil _) (by simp)
  have hshapeS : LabeledWord.SameStructure st.position.board.left su.position.board.left := by
    simpa [hsST, hsSU, Board.get] using hshape
  have htermS : su.position.board.left.terminal = true := by
    simpa [hsSU, Board.get] using hterm
  have htermS' : st.position.board.left.terminal = true := by
    change decide (st.position.board.left.parser = .blocks 0) = true
    rw [hshapeS.parser_eq]
    exact htermS
  have hrightST : st.position.board.right = t.cursor := by
    simpa [hsST, hbST, Board.get, htRight] using hotherST
  have hrightSU : su.position.board.right = u.cursor := by
    simpa [hsSU, hbSU, Board.get, huRight] using hotherSU
  have hdoneST : Concrete.done st.position.board = true := by
    simp [Concrete.done, htermS', hrightST, t.terminal]
  have hdoneSU : Concrete.done su.position.board = true := by
    simp [Concrete.done, htermS, hrightSU, u.terminal]
  exact triangle_of_shared_coordinates
    (winning_of_done ((hwinT.of_reachable (exactGame N blue) hpathST).of_reachable
      (exactGame N blue) (Relation.ReflTransGen.single hsOld)) hnST hdoneST)
    (winning_of_done ((hwinU.of_reachable (exactGame N blue) hpathSU).of_reachable
      (exactGame N blue) (Relation.ReflTransGen.single hsNew)) hnSU hdoneSU)
    hwinTU hshapeS.coordinates_eq (by simpa [hrightST] using hT) (by simpa [hrightSU] using hU)

theorem winning_second_request_positive {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {r : Request} (hp : p.position.pending = some r) (hside : r.side = true)
    (hinit : p.position.board.right = LabeledWord.initial)
    (hrel : p.position.board.left.relaxed = true) : 0 < r.size := by
  by_contra hn
  have hz : r.size = 0 := by omega
  exact pending_second_zero_triangle hHN hH blue hroot hwin hp hside hz hinit hrel htri

#print axioms pending_second_zero_triangle
#print axioms winning_second_request_positive

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
