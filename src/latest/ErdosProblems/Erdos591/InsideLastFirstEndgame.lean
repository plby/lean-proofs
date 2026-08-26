import ErdosProblems.Erdos591.SharedHeadTriangle
import ErdosProblems.Erdos591.ManagedWord
import ErdosProblems.Erdos591.SharedTailPrefixes

/-!
# Complete two delayed tails, then their common first word

The lower T and U selections are exhausted and their complete responses
are pending. One late completion of TU supplies both tails. A subsequent
completion of ST supplies the common final S response in SU as well.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem triangle_of_pending_tails_then_common_head_from_prefixes {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (st su tu : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    {rST rSU : Request} (hpST : st.position.pending = some rST)
    (hpSU : su.position.pending = some rSU) (hsST : rST.side = true) (hsSU : rSU.side = true)
    (hstartST : st.position.board.right.parser ≠ .start)
    (hstartSU : su.position.board.right.parser ≠ .start)
    (hlastST : ¬ Macro.Pending st.position.board.right)
    (hlastSU : ¬ Macro.Pending su.position.board.right)
    (hstartS : su.position.board.left.parser ≠ .start)
    (hlastS : ¬ Macro.Pending su.position.board.left)
    (hliveS : su.position.board.left.terminal = false)
    (hS : LabeledWord.SameStructure st.position.board.left su.position.board.left)
    (hTprefix : ∃ anchor, LabeledWord.SameStructure st.position.board.right anchor ∧
      ∃ as, LabeledWord.LegalRun anchor as tu.position.board.left ∧
        ∀ a ∈ as, a.2 ∈ H ∧ max st.position.bound (b st) < a.2)
    (hUprefix : ∃ anchor, LabeledWord.SameStructure su.position.board.right anchor ∧
      ∃ as, LabeledWord.LegalRun anchor as tu.position.board.right ∧
        ∀ a ∈ as, a.2 ∈ H ∧ max su.position.bound (b su) < a.2) :
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
  have hprefix : ∀ k, ∃ anchor,
      LabeledWord.SameStructure ((old k).position.board.get (requests k).side) anchor ∧
      ∃ as, LabeledWord.LegalRun anchor as (tu.position.board.get (sides k)) ∧
        ∀ a ∈ as, a.2 ∈ H ∧ max (old k).position.bound (b (old k)) < a.2 := by
    intro k
    by_cases hk : k = 0
    · simpa [old, requests, sides, hk, hsST, Board.get] using hTprefix
    · simpa [old, requests, sides, hk, hsSU, Board.get] using hUprefix
  obtain ⟨lastTU, _hpathTU, hdoneTU, hwinningTU, hfinish⟩ :=
    winning_shared_completions_from_prefixes hHN hH blue hwinTU 2 old requests sides
      hp hstart hlast hprefix
  obtain ⟨st', hst, hstNone, hstShape, hstOther⟩ := hfinish 0
  obtain ⟨su', hsu, hsuNone, hsuShape, hsuOther⟩ := hfinish 1
  have hstStep : (exactGame N blue).FollowStep σ H b st st' := by simpa [old] using hst
  have hsuStep : (exactGame N blue).FollowStep σ H b su su' := by simpa [old] using hsu
  have hstShape' : LabeledWord.SameStructure st'.position.board.right
      lastTU.position.board.left := by
    simpa [old, requests, sides, hsST, Board.get] using hstShape
  have hsuShape' : LabeledWord.SameStructure su'.position.board.right
      lastTU.position.board.right := by
    simpa [old, requests, sides, hsSU, Board.get] using hsuShape
  have hstOther' : st'.position.board.left = st.position.board.left := by
    simpa [old, requests, hsST, Board.get] using hstOther
  have hsuOther' : su'.position.board.left = su.position.board.left := by
    simpa [old, requests, hsSU, Board.get] using hsuOther
  have htTerm : st'.position.board.right.terminal = true := by
    change decide (st'.position.board.right.parser = .blocks 0) = true
    rw [hstShape'.parser_eq]
    exact lastTU.position.board.terminal_of_done hdoneTU false
  have huTerm : su'.position.board.right.terminal = true := by
    change decide (su'.position.board.right.parser = .blocks 0) = true
    rw [hsuShape'.parser_eq]
    exact lastTU.position.board.terminal_of_done hdoneTU true
  have hwinST' := hwinST.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hstStep)
  have hwinSU' := hwinSU.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hsuStep)
  obtain ⟨pSU, rS, hsuPath, hboard, hpS, hsS⟩ := request_opposite_complete σ su' true huTerm
    (by simpa [Board.get, hsuOther'] using hliveS)
  have hpSUwin := hwinSU'.of_reachable (exactGame N blue) hsuPath
  have hsS' : rS.side = false := hsS
  have hshapeS : LabeledWord.SameStructure (pSU.position.board.get rS.side)
      (st'.position.board.get false) := by
    simpa [hboard, hsS', Board.get, hstOther', hsuOther'] using hS.symm
  obtain ⟨lastST, lastSU, hstPath, hdoneST, hwinningST, hsuLast, hsuLastNone,
      hsuLastShape, hsuLastOther⟩ :=
    winning_shared_completion hHN hH blue hwinST' false hpS
      (by simpa [hboard, hsS', Board.get, hsuOther'] using hstartS)
      (by simpa [hboard, hsS', Board.get, hsuOther'] using hlastS) hshapeS
  have hshapeS' : LabeledWord.SameStructure lastSU.position.board.left
      lastST.position.board.left := by simpa [hsS', Board.get] using hsuLastShape
  have hotherSU : lastSU.position.board.right = su'.position.board.right := by
    simpa [hsS', Board.get, hboard] using hsuLastOther
  obtain ⟨as, has, _⟩ :=
    (History.reachable_word_extension (follow_history_path hstPath)).2 true
  have hotherST : lastST.position.board.right = st'.position.board.right :=
    has.terminal_eq htTerm
  have hsTerm : lastSU.position.board.left.terminal = true := by
    change decide (lastSU.position.board.left.parser = .blocks 0) = true
    rw [hshapeS'.parser_eq]
    exact lastST.position.board.terminal_of_done hdoneST false
  have hdoneSU : Concrete.done lastSU.position.board = true := by
    simp [Concrete.done, hsTerm, hotherSU, huTerm]
  exact triangle_of_shared_coordinates hwinningST
    (winning_of_done (hpSUwin.of_reachable (exactGame N blue)
      (Relation.ReflTransGen.single hsuLast)) hsuLastNone hdoneSU) hwinningTU
    hshapeS'.coordinates_eq.symm (by simpa [hotherST] using hstShape'.coordinates_eq)
    (by simpa [hotherSU] using hsuShape'.coordinates_eq)

theorem triangle_of_pending_tails_then_common_head {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (st su tu : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    {rST rSU : Request} (hpST : st.position.pending = some rST)
    (hpSU : su.position.pending = some rSU) (hsST : rST.side = true) (hsSU : rSU.side = true)
    (hstartST : st.position.board.right.parser ≠ .start)
    (hstartSU : su.position.board.right.parser ≠ .start)
    (hlastST : ¬ Macro.Pending st.position.board.right)
    (hlastSU : ¬ Macro.Pending su.position.board.right)
    (hstartS : su.position.board.left.parser ≠ .start)
    (hlastS : ¬ Macro.Pending su.position.board.left)
    (hliveS : su.position.board.left.terminal = false)
    (hS : LabeledWord.SameStructure st.position.board.left su.position.board.left)
    (hT : LabeledWord.SameStructure st.position.board.right tu.position.board.left)
    (hU : LabeledWord.SameStructure su.position.board.right tu.position.board.right) :
    ¬ blue.CliqueFree 3 :=
  triangle_of_pending_tails_then_common_head_from_prefixes hHN hH blue st su tu
    hwinST hwinSU hwinTU hpST hpSU hsST hsSU hstartST hstartSU hlastST hlastSU
    hstartS hlastS hliveS hS
    ⟨_, hT, [], .nil _, by simp⟩ ⟨_, hU, [], .nil _, by simp⟩

#print axioms triangle_of_pending_tails_then_common_head_from_prefixes
#print axioms triangle_of_pending_tails_then_common_head

theorem inside_triangle_of_last_first_forks {N H : Set ℕ}
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
    (hU : LabeledWord.SameStructure su.position.board.right tu.position.board.right) :
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
  obtain ⟨pST, rST, hpSTpath, hbST, hpST, hsST⟩ :=
    request_smaller_at_boundary hHN hH blue hwinST hmodeST (hliveST true)
      (hstartST false) (hlastST false)
  obtain ⟨pSU, rSU, hpSUpath, hbSU, hpSU, hsSU⟩ :=
    request_smaller_at_boundary hHN hH blue hwinSU hmodeSU (hliveSU true)
      (hstartSU false) (hlastSU false)
  exact triangle_of_pending_tails_then_common_head hHN hH blue pST pSU tu
    (hwinST.of_reachable (exactGame N blue) hpSTpath)
    (hwinSU.of_reachable (exactGame N blue) hpSUpath) hwinTU hpST hpSU hsST hsSU
    (by simpa [hbST, Board.get] using hstartST true)
    (by simpa [hbSU, Board.get] using hstartSU true)
    (by simpa [hbST, Board.get] using hlastST true)
    (by simpa [hbSU, Board.get] using hlastSU true)
    (by simpa [hbSU, Board.get] using hstartSU false)
    (by simpa [hbSU, Board.get] using hlastSU false)
    (by simpa [hbSU, Board.get] using hliveSU false)
    (by simpa [hbST, hbSU] using hS)
    (by simpa [hbST] using hT) (by simpa [hbSU] using hU)

#print axioms inside_triangle_of_last_first_forks

end Erdos591.Positive.Game.Payoff
