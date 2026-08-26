import ErdosProblems.Erdos118.Reused591.SharedHeadTriangle
import ErdosProblems.Erdos118.Reused591.ArchitectPersistence

namespace Erdos118.Reused591

/-!
# Completing the common last word after an inside overlap

An old TU history is waiting to complete U. A newer SU history has
reached its last S selection, and its recorded U continuation is fresh
for that old request. Complete U in both histories and use one winning
ST continuation for their remaining heads.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_completion_triangle {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (st su oldTU : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ oldTU)
    (hmSU : su.position.mode = some true)
    {rTU : Request} (hpTU : oldTU.position.pending = some rTU) (hsTU : rTU.side = true)
    (hstartT : oldTU.position.board.left.parser ≠ .start)
    (hliveT : oldTU.position.board.left.terminal = false)
    (hlastT : ¬ Macro.Pending oldTU.position.board.left)
    (hstartOldU : oldTU.position.board.right.parser ≠ .start)
    (hlastOldU : ¬ Macro.Pending oldTU.position.board.right)
    (hrS : su.position.board.left.relaxed = true)
    (hsepS : ∀ y ∈ su.position.board.right.coordinates,
      y ≤ su.position.board.left.coordinates.getLastD 0)
    (hlastS : ¬ Macro.Pending su.position.board.left)
    (hstartU : su.position.board.right.parser ≠ .start)
    {before : LabeledWord} {as : List (Finset ℕ × ℕ)}
    (hbefore : LabeledWord.SameStructure oldTU.position.board.right before)
    (hrun : LabeledWord.LegalRun before as su.position.board.right)
    (hpool : ∀ a ∈ as, a.2 ∈ H ∧ oldTU.position.bound < a.2 ∧ b oldTU < a.2)
    (hS : LabeledWord.SameStructure su.position.board.left st.position.board.left)
    (hT : LabeledWord.SameStructure oldTU.position.board.left st.position.board.right) :
    ¬ blue.CliqueFree 3 := by
  have hwS := ((Position.history_dataInvariant su).2.1 false).1
  have hstartS := LabeledWord.relaxed_ne_start hwS hrS
  have hliveS := LabeledWord.relaxed_not_terminal hwS.2.1 hwS.2.2 hrS
  have hliveU := winning_relaxed_other_unfinished hHN hH blue hwinSU false hrS hsepS
  have hlastU := winning_no_pending_smaller hHN hH blue hwinSU hmSU hstartU hstartS hlastS
  obtain ⟨pendingSU, rSU, hpathSU, hbSU, hpSU, hsSU⟩ :=
    request_smaller_at_boundary hHN hH blue hwinSU hmSU hliveU hstartS hlastS
  have hsame : LabeledWord.SameStructure (oldTU.position.board.get rTU.side) before := by
    simpa [hsTU, Board.get] using hbefore
  have hrun' : LabeledWord.LegalRun before as (pendingSU.position.board.get rSU.side) := by
    simpa [hsSU, hbSU, Board.get] using hrun
  obtain ⟨doneTU, doneSU, hstepTU, hstepSU, _hnTU, _hnSU, htermSU, hshapeU, hotherTU, hotherSU⟩ :=
    complete_shared_extension hHN hH blue oldTU pendingSU hpTU hpSU
      (by simpa [hsTU, Board.get] using hstartOldU)
      (by simpa [hsTU, Board.get] using hlastOldU)
      (by simpa [hsSU, hbSU, Board.get] using hstartU)
      (by simpa [hsSU, hbSU, Board.get] using hlastU) hsame hrun' hpool
  have hshapeU' : LabeledWord.SameStructure doneTU.position.board.right
      doneSU.position.board.right := by simpa [hsTU, hsSU, Board.get] using hshapeU
  have htermU : doneSU.position.board.right.terminal = true := by
    simpa [hsSU, Board.get] using htermSU
  have htermU' : doneTU.position.board.right.terminal = true := by
    change decide (doneTU.position.board.right.parser = .blocks 0) = true
    rw [hshapeU'.parser_eq]
    exact htermU
  have hremainT : doneTU.position.board.left = oldTU.position.board.left := by
    simpa [hsTU, Board.get] using hotherTU
  have hremainS : doneSU.position.board.left = su.position.board.left := by
    simpa [hsSU, hbSU, Board.get] using hotherSU
  exact triangle_after_shared_last hHN hH blue st doneSU doneTU hwinST
    ((hwinSU.of_reachable (exactGame N blue) hpathSU).of_reachable
      (exactGame N blue) (Relation.ReflTransGen.single hstepSU))
    (hwinTU.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hstepTU))
    (by simpa [hremainS, Board.get] using hstartS) (by simpa [hremainT] using hstartT)
    (by simpa [hremainS] using hlastS) (by simpa [hremainT] using hlastT)
    htermU htermU' (by simpa [hremainS, Board.get] using hliveS)
    (by simpa [hremainT] using hliveT) hshapeU'.coordinates_eq.symm
    (by rw [hremainS]; exact hS) (by rw [hremainT]; exact hT)

#print axioms inside_completion_triangle

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
