import ErdosProblems.Erdos591.SharedHeadTriangle
import ErdosProblems.Erdos591.SharedTailPrefixes

/-!
# Final two heads with recorded fresh prefixes

Both copies of U are complete. Each pending S or T head may already
have a fresh continuation inside ST. One winning completion of ST,
above the two old bounds, completes both heads and yields the triangle.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem triangle_of_two_pending_heads_from_prefixes {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
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
    (hS : ∃ anchor, LabeledWord.SameStructure su.position.board.left anchor ∧
      ∃ as, LabeledWord.LegalRun anchor as st.position.board.left ∧
        ∀ a ∈ as, a.2 ∈ H ∧ max su.position.bound (b su) < a.2)
    (hT : ∃ anchor, LabeledWord.SameStructure tu.position.board.left anchor ∧
      ∃ as, LabeledWord.LegalRun anchor as st.position.board.right ∧
        ∀ a ∈ as, a.2 ∈ H ∧ max tu.position.bound (b tu) < a.2) :
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
  have hprefix : ∀ k, ∃ anchor,
      LabeledWord.SameStructure ((old k).position.board.get (requests k).side) anchor ∧
      ∃ as, LabeledWord.LegalRun anchor as (st.position.board.get (sides k)) ∧
        ∀ a ∈ as, a.2 ∈ H ∧ max (old k).position.bound (b (old k)) < a.2 := by
    intro k
    by_cases hk : k = 0
    · simpa [old, requests, sides, hk, hsSU, Board.get] using hS
    · simpa [old, requests, sides, hk, hsTU, Board.get] using hT
  obtain ⟨last, _hpath, hdone, hwinning, hfinish⟩ :=
    winning_shared_completions_from_prefixes hHN hH blue hwinST 2 old requests sides
      hp hstart hlast hprefix
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


#print axioms triangle_of_two_pending_heads_from_prefixes

end Erdos591.Positive.Game.Payoff
