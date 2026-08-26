import ErdosProblems.Erdos118.Reused591.SharedNextLeaf
import ErdosProblems.Erdos118.Reused591.InsideLastFirstEndgame

namespace Erdos118.Reused591

/-!
# Close the inside triangle after the two opposite upper replays

The first words wait at their respective penultimate leaves, with the
fresh second-middle prefix retained. Share their final selected leaf,
then use the checked two-tail/common-head endgame. This branch applies
once both upper opposite prefixes have reached their lower last leaves.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem selected_last_leaf_exhausted {N H : Set ℕ} {blue : SimpleGraph G}
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p q : Concrete.Hist N} {j : ℕ}
    (hstep : (exactGame N blue).FollowStep σ H b p q)
    (hup : LabeledWord.UpToLeaf j p.position.board.left)
    (hroot : ∀ i ∈ p.position.board.left.rootLabel, i ≤ p.position.board.left.bodyLabels.length)
    (hlast : ∀ i ∈ p.position.board.left.currentLabel, i ≤ j)
    (hlabels : q.position.board.left.bodyLabels = p.position.board.left.bodyLabels)
    (hidx : q.position.board.left.leafIndex = j) : ¬ Macro.Pending q.position.board.left := by
  obtain ⟨as, has, _⟩ := follow_step_word_inputs hstep false
  obtain ⟨r, k, hparse⟩ := hup.parser_leaves ((Position.history_dataInvariant p).2.1 false).1
  have hrootEq := has.rootLabel_eq (by simp [Board.get, hparse])
  have hcurrent : q.position.board.left.currentLabel = p.position.board.left.currentLabel := by
    simp [LabeledWord.currentLabel, hlabels]
  rintro (⟨i, hi, hlt⟩ | ⟨_, i, hi, hlt⟩)
  · have hle := hroot i (hrootEq ▸ hi)
    rw [hlabels] at hlt
    exact (not_lt_of_ge hle hlt).elim
  · have hle := hlast i (hcurrent ▸ hi)
    rw [hidx] at hlt
    exact (not_lt_of_ge hle hlt).elim

theorem inside_shared_leaf_triangle {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (old fine upper : Concrete.Hist N)
    (hwinOld : (exactGame N blue).ArchitectWins H b σ old)
    (hwinFine : (exactGame N blue).ArchitectWins H b σ fine)
    (hwinUpper : (exactGame N blue).ArchitectWins H b σ upper)
    (hmodeOld : old.position.mode = some true) (hmodeFine : fine.position.mode = some true)
    (hpOld : old.position.pending = some ⟨false, .advance 0⟩)
    (hpFine : fine.position.pending = some ⟨false, .advance 0⟩) {j : ℕ}
    (hupOld : LabeledWord.UpToLeaf j old.position.board.left)
    (hstrictOld : old.position.board.left.leafIndex < j)
    (hnextOld : ∀ i ∈ old.position.board.left.currentLabel,
      old.position.board.left.leafIndex < i → j ≤ i)
    (hupFine : LabeledWord.UpToLeaf j fine.position.board.left)
    (hstrictFine : fine.position.board.left.leafIndex < j)
    (hnextFine : ∀ i ∈ fine.position.board.left.currentLabel,
      fine.position.board.left.leafIndex < i → j ≤ i)
    (hrootOld : ∀ i ∈ old.position.board.left.rootLabel,
      i ≤ old.position.board.left.bodyLabels.length)
    (hrootFine : ∀ i ∈ fine.position.board.left.rootLabel,
      i ≤ fine.position.board.left.bodyLabels.length)
    (hlastOld : ∀ i ∈ old.position.board.left.currentLabel, i ≤ j)
    (hlastFine : ∀ i ∈ fine.position.board.left.currentLabel, i ≤ j)
    {anchor : LabeledWord} {frontAtoms : List (Finset ℕ × ℕ)}
    (hsame : LabeledWord.SameStructure old.position.board.left anchor)
    (hfront : LabeledWord.LegalRun anchor frontAtoms fine.position.board.left)
    (hfrontPool : ∀ a ∈ frontAtoms, a.2 ∈ H ∧ max old.position.bound (b old) < a.2)
    (hcount : fine.position.board.left.bodyLabels.length = anchor.bodyLabels.length)
    (hmarker : fine.position.board.left.bodyMarker = anchor.bodyMarker)
    (hrelT : old.position.board.right.relaxed = true)
    (hrelU : fine.position.board.right.relaxed = true)
    (hlastT : ¬ Macro.Pending old.position.board.right)
    (hlastU : ¬ Macro.Pending fine.position.board.right)
    (hT : LabeledWord.SameStructure old.position.board.right upper.position.board.left)
    (hU : LabeledWord.SameStructure fine.position.board.right upper.position.board.right) :
    ¬ blue.CliqueFree 3 := by
  obtain ⟨st, su, hstepST, hstepSU, _hnST, _hnSU, hS, hrST, hrSU, hiST, hiSU,
      hlST, hlSU, hoST, hoSU⟩ := shared_next_leaf_from_prefix hHN hH blue σ old fine false false
    hpOld hpFine hupOld hstrictOld hnextOld hupFine hstrictFine hnextFine
    hsame hfront hfrontPool hcount hmarker
  have hSlastST := selected_last_leaf_exhausted hstepST hupOld hrootOld hlastOld hlST hiST
  have hSlastSU := selected_last_leaf_exhausted hstepSU hupFine hrootFine hlastFine hlSU hiSU
  have hlastST : Relay.BothLast st.position.board := by
    intro side
    cases side
    · exact hSlastST
    · simpa [Board.get, show st.position.board.right = old.position.board.right from hoST]
        using hlastT
  have hlastSU : Relay.BothLast su.position.board := by
    intro side
    cases side
    · exact hSlastSU
    · simpa [Board.get, show su.position.board.right = fine.position.board.right from hoSU]
        using hlastU
  have hrelST : ∀ side, (st.position.board.get side).relaxed = true := by
    intro side
    cases side
    · exact hrST
    · simpa [Board.get, show st.position.board.right = old.position.board.right from hoST]
        using hrelT
  have hrelSU : ∀ side, (su.position.board.get side).relaxed = true := by
    intro side
    cases side
    · exact hrSU
    · simpa [Board.get, show su.position.board.right = fine.position.board.right from hoSU]
        using hrelU
  exact inside_triangle_of_last_first_forks hHN hH blue st su upper
    (hwinOld.of_reachable (exactGame N blue) (.single hstepST))
    (hwinFine.of_reachable (exactGame N blue) (.single hstepSU)) hwinUpper
    (follow_mode_some (.single hstepST) hmodeOld) (follow_mode_some (.single hstepSU) hmodeFine)
    hlastST hlastSU hrelST hrelSU hS
    (by simpa [show st.position.board.right = old.position.board.right from hoST] using hT)
    (by simpa [show su.position.board.right = fine.position.board.right from hoSU] using hU)

#print axioms inside_shared_leaf_triangle
#print axioms selected_last_leaf_exhausted

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
