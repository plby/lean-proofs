import ErdosProblems.Erdos118.Reused591.ReachBodyLastLeaf
import ErdosProblems.Erdos118.Reused591.SelectedBodyCard

namespace Erdos118.Reused591

/-! # Reach the penultimate selected body's last leaf without changing earlier labels -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_reach_penultimate_body {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) (hn : p.position.pending = none)
    (hr : (p.position.board.get side).relaxed = true)
    (hbefore : (p.position.board.get side).bodyLabels.length <
      (p.position.board.get side).lastSelectedBody)
    (hsep : ∀ y ∈ (p.position.board.get (!side)).coordinates,
      y ≤ (p.position.board.get side).coordinates.getLastD 0) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).NoLeafPending ∧
      (q.position.board.get side).rootLabel = (p.position.board.get side).rootLabel ∧
      (q.position.board.get side).bodyLabels.length <
        (q.position.board.get side).lastSelectedBody ∧
      (∀ k ∈ (q.position.board.get side).rootLabel,
        k < (q.position.board.get side).lastSelectedBody →
          k ≤ (q.position.board.get side).bodyLabels.length) ∧
      ∀ y ∈ (q.position.board.get (!side)).coordinates,
        y ≤ (q.position.board.get side).coordinates.getLastD 0 := by
  classical
  let w := p.position.board.get side
  let C := w.rootLabel.erase w.lastSelectedBody
  have hcurrent : w.bodyLabels.length ∈ C :=
    Finset.mem_erase.mpr ⟨hbefore.ne, (of_decide_eq_true hr).2.1⟩
  let i := C.sup id
  have hiC : i ∈ C := by
    simpa [i] using Finset.sup_mem_of_nonempty (f := id) ⟨_, hcurrent⟩
  have hi : i ∈ w.rootLabel := Finset.mem_of_mem_erase hiC
  have hile : w.bodyLabels.length ≤ i := Finset.le_sup (f := id) hcurrent
  have hilt : i < w.lastSelectedBody :=
    lt_of_le_of_ne (Finset.le_sup (f := id) hi) (Finset.ne_of_mem_erase hiC)
  obtain ⟨q, hpq, hqn, hqr, hqno, hqi, hqroot, hqsep⟩ :=
    winning_reach_body_last_leaf hHN hH blue hwin side hn hr hsep hi hile
  have hqlast : (q.position.board.get side).lastSelectedBody = w.lastSelectedBody := by
    simp only [LabeledWord.lastSelectedBody, hqroot, w]
  refine ⟨q, hpq, hqn, hqr, hqno, hqroot, ?_, ?_, hqsep⟩
  · simpa only [hqi, hqlast] using hilt
  · intro k hk hlt
    rw [hqi]
    apply Finset.le_sup (f := id)
    exact Finset.mem_erase.mpr ⟨by simpa only [hqlast] using hlt.ne, hqroot ▸ hk⟩

#print axioms winning_reach_penultimate_body

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
