import ErdosProblems.Erdos118.Reused591.FirstLastInterior
import ErdosProblems.Erdos118.Reused591.InsideSharedLeafEndgame

namespace Erdos118.Reused591

/-!
# The two-element first/last ending with exhausted opposite lower words

There are no intermediate first-word selections. Their common next
selection is their last. Share it once, then apply the existing inside
completion theorem to the three genuine winning histories.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_first_last_singleton_triangle {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (st su tu : Concrete.Hist N) {B p q : ℕ} (S : FirstLastLabels H B p q)
    (hp : p = 2) (hq : q = 2)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    (hmodeST : st.position.mode = some true) (hmodeSU : su.position.mode = some true)
    (hpST : st.position.pending = some ⟨false, .advance 0⟩)
    (hpSU : su.position.pending = some ⟨false, .advance 0⟩)
    (hS : LabeledWord.SameStructure st.position.board.left su.position.board.left)
    (hrST : st.position.board.left.relaxed = true) (hrSU : su.position.board.left.relaxed = true)
    (hlabelST : st.position.board.left.currentLabel = S.lower)
    (hlabelSU : su.position.board.left.currentLabel = S.upper)
    (hindexST : st.position.board.left.leafIndex = S.first)
    (hindexSU : su.position.board.left.leafIndex = S.first)
    (hrootST : ∀ i ∈ st.position.board.left.rootLabel, i ≤ st.position.board.left.bodyLabels.length)
    (hrootSU : ∀ i ∈ su.position.board.left.rootLabel, i ≤ su.position.board.left.bodyLabels.length)
    (hrT : st.position.board.right.relaxed = true) (hrU : su.position.board.right.relaxed = true)
    (hlastT : ¬ Macro.Pending st.position.board.right)
    (hlastU : ¬ Macro.Pending su.position.board.right)
    (hT : LabeledWord.SameStructure st.position.board.right tu.position.board.left)
    (hU : LabeledWord.SameStructure su.position.board.right tu.position.board.right) :
    ¬ blue.CliqueFree 3 := by
  have hupST : LabeledWord.UpToLeaf S.last st.position.board.left :=
    ⟨(of_decide_eq_true hrST).2.1, hlabelST ▸ S.last_lower,
      by rw [hindexST]; exact S.first_lt_last.le⟩
  have hupSU : LabeledWord.UpToLeaf S.last su.position.board.left :=
    ⟨(of_decide_eq_true hrSU).2.1, hlabelSU ▸ S.last_upper,
      by rw [hindexSU]; exact S.first_lt_last.le⟩
  have hnextST : ∀ i ∈ st.position.board.left.currentLabel,
      st.position.board.left.leafIndex < i → S.last ≤ i := by
    intro i hi hlt
    rw [hlabelST, S.lower_eq_pair hp] at hi
    rw [hindexST] at hlt
    rcases Finset.mem_insert.mp hi with heq | hi
    · exact (not_lt_of_ge heq.le hlt).elim
    · exact (Finset.mem_singleton.mp hi).ge
  have hnextSU : ∀ i ∈ su.position.board.left.currentLabel,
      su.position.board.left.leafIndex < i → S.last ≤ i := by
    intro i hi hlt
    rw [hlabelSU, S.upper_eq_pair hq] at hi
    rw [hindexSU] at hlt
    rcases Finset.mem_insert.mp hi with heq | hi
    · exact (not_lt_of_ge heq.le hlt).elim
    · exact (Finset.mem_singleton.mp hi).ge
  exact inside_shared_leaf_triangle hHN hH blue st su tu hwinST hwinSU hwinTU hmodeST hmodeSU
    hpST hpSU hupST (by rw [hindexST]; exact S.first_lt_last) hnextST
    hupSU (by rw [hindexSU]; exact S.first_lt_last) hnextSU hrootST hrootSU
    (fun i hi => (S.lower_bounds i (hlabelST ▸ hi)).2)
    (fun i hi => (S.upper_bounds i (hlabelSU ▸ hi)).2)
    hS (LabeledWord.LegalRun.nil _) (by simp) rfl rfl hrT hrU hlastT hlastU hT hU

#print axioms inside_first_last_singleton_triangle

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
