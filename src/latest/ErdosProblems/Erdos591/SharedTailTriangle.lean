import ErdosProblems.Erdos591.TriangleEndgame
import ErdosProblems.Erdos591.SharedExtensionCompletion

/-!
# The final two shared tails produce all three blue edges

The first word has already been completed identically in two plays.
Their right words have pending complete responses and share structural
prefixes with the two words of a third winning play. One sufficiently
late completion of that third play supplies both old responses.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem triangle_of_two_pending_tails {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (st su tu : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    {rST rSU : Request} (hpST : st.position.pending = some rST)
    (hpSU : su.position.pending = some rSU) (hsST : rST.side = true) (hsSU : rSU.side = true)
    (hstartST : st.position.board.right.parser ≠ .start)
    (hstartSU : su.position.board.right.parser ≠ .start)
    (hlastST : ¬ Macro.Pending st.position.board.right)
    (hlastSU : ¬ Macro.Pending su.position.board.right)
    (hcompleteST : st.position.board.left.terminal = true)
    (hcompleteSU : su.position.board.left.terminal = true)
    (hS : st.position.board.left.coordinates = su.position.board.left.coordinates)
    (hT : LabeledWord.SameStructure st.position.board.right tu.position.board.left)
    (hU : LabeledWord.SameStructure su.position.board.right tu.position.board.right) :
    ¬ blue.CliqueFree 3 := by
  let old : Fin 2 → Concrete.Hist N := fun k => if k = 0 then st else su
  let requests : Fin 2 → Request := fun k => if k = 0 then rST else rSU
  let sides : Fin 2 → Bool := fun k => if k = 0 then false else true
  have hp : ∀ k, (old k).position.pending = some (requests k) := by
    intro k
    by_cases hk : k = 0 <;> simp [old, requests, hk, hpST, hpSU]
  have hstart : ∀ k, ((old k).position.board.get (requests k).side).parser ≠ .start := by
    intro k
    by_cases hk : k = 0
    · simpa [old, requests, hk, hsST, Board.get] using hstartST
    · simpa [old, requests, hk, hsSU, Board.get] using hstartSU
  have hlast : ∀ k, ¬ Macro.Pending ((old k).position.board.get (requests k).side) := by
    intro k
    by_cases hk : k = 0
    · simpa [old, requests, hk, hsST, Board.get] using hlastST
    · simpa [old, requests, hk, hsSU, Board.get] using hlastSU
  have hsame : ∀ k, LabeledWord.SameStructure ((old k).position.board.get (requests k).side)
      (tu.position.board.get (sides k)) := by
    intro k
    by_cases hk : k = 0
    · simpa [old, requests, sides, hk, hsST, Board.get] using hT
    · simpa [old, requests, sides, hk, hsSU, Board.get] using hU
  obtain ⟨last, _hpath, hdone, hwinning, hfinish⟩ :=
    winning_shared_completions hHN hH blue hwinTU 2 old requests sides hp hstart hlast hsame
  obtain ⟨st', hst, hstNone, hstShape, hstOther⟩ := hfinish 0
  obtain ⟨su', hsu, hsuNone, hsuShape, hsuOther⟩ := hfinish 1
  have hstShape' : LabeledWord.SameStructure st'.position.board.right last.position.board.left := by
    simpa [old, requests, sides, hsST, Board.get] using hstShape
  have hsuShape' : LabeledWord.SameStructure su'.position.board.right last.position.board.right := by
    simpa [old, requests, sides, hsSU, Board.get] using hsuShape
  have hstOther' : st'.position.board.left = st.position.board.left := by
    simpa [old, requests, hsST, Board.get] using hstOther
  have hsuOther' : su'.position.board.left = su.position.board.left := by
    simpa [old, requests, hsSU, Board.get] using hsuOther
  have htTerm : st'.position.board.right.terminal = true := by
    change decide (st'.position.board.right.parser = .blocks 0) = true
    rw [hstShape'.parser_eq]
    exact last.position.board.terminal_of_done hdone false
  have huTerm : su'.position.board.right.terminal = true := by
    change decide (su'.position.board.right.parser = .blocks 0) = true
    rw [hsuShape'.parser_eq]
    exact last.position.board.terminal_of_done hdone true
  have hstDone : Concrete.done st'.position.board = true := by
    simp [Concrete.done, hstOther', hcompleteST, htTerm]
  have hsuDone : Concrete.done su'.position.board = true := by
    simp [Concrete.done, hsuOther', hcompleteSU, huTerm]
  exact triangle_of_shared_coordinates
    (winning_of_done (hwinST.of_reachable (exactGame N blue)
      (Relation.ReflTransGen.single hst)) hstNone hstDone)
    (winning_of_done (hwinSU.of_reachable (exactGame N blue)
      (Relation.ReflTransGen.single hsu)) hsuNone hsuDone) hwinning
    (by simpa [hstOther', hsuOther'] using hS) hstShape'.coordinates_eq hsuShape'.coordinates_eq

#print axioms triangle_of_two_pending_tails

theorem triangle_after_shared_first {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (st su tu : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    (hstartST : st.position.board.right.parser ≠ .start)
    (hstartSU : su.position.board.right.parser ≠ .start)
    (hlastST : ¬ Macro.Pending st.position.board.right)
    (hlastSU : ¬ Macro.Pending su.position.board.right)
    (hcompleteST : st.position.board.left.terminal = true)
    (hcompleteSU : su.position.board.left.terminal = true)
    (hliveST : st.position.board.right.terminal = false)
    (hliveSU : su.position.board.right.terminal = false)
    (hS : st.position.board.left.coordinates = su.position.board.left.coordinates)
    (hT : LabeledWord.SameStructure st.position.board.right tu.position.board.left)
    (hU : LabeledWord.SameStructure su.position.board.right tu.position.board.right) :
    ¬ blue.CliqueFree 3 := by
  obtain ⟨pST, rST, hpathST, hbST, hpST, hsST⟩ :=
    request_opposite_complete σ st false hcompleteST hliveST
  obtain ⟨pSU, rSU, hpathSU, hbSU, hpSU, hsSU⟩ :=
    request_opposite_complete σ su false hcompleteSU hliveSU
  exact triangle_of_two_pending_tails hHN hH blue pST pSU tu
    (hwinST.of_reachable (exactGame N blue) hpathST)
    (hwinSU.of_reachable (exactGame N blue) hpathSU) hwinTU hpST hpSU hsST hsSU
    (by simpa [hbST] using hstartST) (by simpa [hbSU] using hstartSU)
    (by simpa [hbST] using hlastST) (by simpa [hbSU] using hlastSU)
    (by simpa [hbST] using hcompleteST) (by simpa [hbSU] using hcompleteSU)
    (by simpa [hbST, hbSU] using hS) (by simpa [hbST] using hT) (by simpa [hbSU] using hU)

#print axioms triangle_after_shared_first

end Erdos591.Positive.Game.Payoff
