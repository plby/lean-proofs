import ErdosProblems.Erdos118.Reused591.SharedTailTriangle

namespace Erdos118.Reused591

/-!
# Two shared heads after completion of the common last word

The inside endgame has the common right word already complete in SU
and TU. A late winning completion of ST supplies the two pending left
responses. This is the reversed completion order of the outside endgame.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem triangle_of_two_pending_heads {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (st su tu : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    {rSU rTU : Request} (hpSU : su.position.pending = some rSU)
    (hpTU : tu.position.pending = some rTU) (hsSU : rSU.side = false) (hsTU : rTU.side = false)
    (hstartSU : su.position.board.left.parser ≠ .start)
    (hstartTU : tu.position.board.left.parser ≠ .start)
    (hlastSU : ¬ Macro.Pending su.position.board.left)
    (hlastTU : ¬ Macro.Pending tu.position.board.left)
    (hcompleteSU : su.position.board.right.terminal = true)
    (hcompleteTU : tu.position.board.right.terminal = true)
    (hU : su.position.board.right.coordinates = tu.position.board.right.coordinates)
    (hS : LabeledWord.SameStructure su.position.board.left st.position.board.left)
    (hT : LabeledWord.SameStructure tu.position.board.left st.position.board.right) :
    ¬ blue.CliqueFree 3 := by
  let old : Fin 2 → Concrete.Hist N := fun k => if k = 0 then su else tu
  let requests : Fin 2 → Request := fun k => if k = 0 then rSU else rTU
  let sides : Fin 2 → Bool := fun k => if k = 0 then false else true
  have hp : ∀ k, (old k).position.pending = some (requests k) := by
    intro k
    by_cases hk : k = 0 <;> simp [old, requests, hk, hpSU, hpTU]
  have hstart : ∀ k, ((old k).position.board.get (requests k).side).parser ≠ .start := by
    intro k
    by_cases hk : k = 0
    · simpa [old, requests, hk, hsSU, Board.get] using hstartSU
    · simpa [old, requests, hk, hsTU, Board.get] using hstartTU
  have hlast : ∀ k, ¬ Macro.Pending ((old k).position.board.get (requests k).side) := by
    intro k
    by_cases hk : k = 0
    · simpa [old, requests, hk, hsSU, Board.get] using hlastSU
    · simpa [old, requests, hk, hsTU, Board.get] using hlastTU
  have hsame : ∀ k, LabeledWord.SameStructure ((old k).position.board.get (requests k).side)
      (st.position.board.get (sides k)) := by
    intro k
    by_cases hk : k = 0
    · simpa [old, requests, sides, hk, hsSU, Board.get] using hS
    · simpa [old, requests, sides, hk, hsTU, Board.get] using hT
  obtain ⟨last, _hpath, hdone, hwinning, hfinish⟩ :=
    winning_shared_completions hHN hH blue hwinST 2 old requests sides hp hstart hlast hsame
  obtain ⟨su', hsu, hsuNone, hsuShape, hsuOther⟩ := hfinish 0
  obtain ⟨tu', htu, htuNone, htuShape, htuOther⟩ := hfinish 1
  have hsuShape' : LabeledWord.SameStructure su'.position.board.left last.position.board.left := by
    simpa [old, requests, sides, hsSU, Board.get] using hsuShape
  have htuShape' : LabeledWord.SameStructure tu'.position.board.left last.position.board.right := by
    simpa [old, requests, sides, hsTU, Board.get] using htuShape
  have hsuOther' : su'.position.board.right = su.position.board.right := by
    simpa [old, requests, hsSU, Board.get] using hsuOther
  have htuOther' : tu'.position.board.right = tu.position.board.right := by
    simpa [old, requests, hsTU, Board.get] using htuOther
  have hsTerm : su'.position.board.left.terminal = true := by
    change decide (su'.position.board.left.parser = .blocks 0) = true
    rw [hsuShape'.parser_eq]
    exact last.position.board.terminal_of_done hdone false
  have htTerm : tu'.position.board.left.terminal = true := by
    change decide (tu'.position.board.left.parser = .blocks 0) = true
    rw [htuShape'.parser_eq]
    exact last.position.board.terminal_of_done hdone true
  have hsuDone : Concrete.done su'.position.board = true := by
    simp [Concrete.done, hsuOther', hcompleteSU, hsTerm]
  have htuDone : Concrete.done tu'.position.board = true := by
    simp [Concrete.done, htuOther', hcompleteTU, htTerm]
  exact triangle_of_shared_coordinates hwinning
    (winning_of_done (hwinSU.of_reachable (exactGame N blue)
      (Relation.ReflTransGen.single hsu)) hsuNone hsuDone)
    (winning_of_done (hwinTU.of_reachable (exactGame N blue)
      (Relation.ReflTransGen.single htu)) htuNone htuDone)
    hsuShape'.coordinates_eq.symm htuShape'.coordinates_eq.symm
    (by simpa [hsuOther', htuOther'] using hU)

theorem triangle_after_shared_last {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (st su tu : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    (hstartSU : su.position.board.left.parser ≠ .start)
    (hstartTU : tu.position.board.left.parser ≠ .start)
    (hlastSU : ¬ Macro.Pending su.position.board.left)
    (hlastTU : ¬ Macro.Pending tu.position.board.left)
    (hcompleteSU : su.position.board.right.terminal = true)
    (hcompleteTU : tu.position.board.right.terminal = true)
    (hliveSU : su.position.board.left.terminal = false)
    (hliveTU : tu.position.board.left.terminal = false)
    (hU : su.position.board.right.coordinates = tu.position.board.right.coordinates)
    (hS : LabeledWord.SameStructure su.position.board.left st.position.board.left)
    (hT : LabeledWord.SameStructure tu.position.board.left st.position.board.right) :
    ¬ blue.CliqueFree 3 := by
  obtain ⟨pSU, rSU, hpathSU, hbSU, hpSU, hsSU⟩ :=
    request_opposite_complete σ su true hcompleteSU hliveSU
  obtain ⟨pTU, rTU, hpathTU, hbTU, hpTU, hsTU⟩ :=
    request_opposite_complete σ tu true hcompleteTU hliveTU
  exact triangle_of_two_pending_heads hHN hH blue st pSU pTU hwinST
    (hwinSU.of_reachable (exactGame N blue) hpathSU)
    (hwinTU.of_reachable (exactGame N blue) hpathTU) hpSU hpTU hsSU hsTU
    (by simpa [hbSU] using hstartSU) (by simpa [hbTU] using hstartTU)
    (by simpa [hbSU] using hlastSU) (by simpa [hbTU] using hlastTU)
    (by simpa [hbSU] using hcompleteSU) (by simpa [hbTU] using hcompleteTU)
    (by simpa [hbSU, hbTU] using hU) (by simpa [hbSU] using hS) (by simpa [hbTU] using hT)

#print axioms triangle_of_two_pending_heads
#print axioms triangle_after_shared_last

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
