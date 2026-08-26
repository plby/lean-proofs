import ErdosProblems.Erdos118.Reused591.PreparedNextLeafHandoff
import ErdosProblems.Erdos118.Reused591.FiniteRank

namespace Erdos118.Reused591

/-! # Submit the U first-leaf reply, take the next upper T leaf, and submit T's saved reply -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem strict_anchor_handoff {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N}
    (PT : PreparedSelection N H blue b σ p.position.board.left)
    (PU : PreparedSelection N H blue b σ p.position.board.right)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hUrel : p.position.board.right.relaxed = true)
    (hUat : p.position.board.right.leafIndex = PU.labels.pivot)
    (hsep : ∀ x ∈ p.position.board.left.coordinates,
      x ≤ p.position.board.right.coordinates.getLastD 0)
    (hnextRank : (p.position.board.left.currentLabel.filter
        (fun x => x ≤ PT.labels.pivot)).card =
      (p.position.board.left.currentLabel.filter
        (fun x => x ≤ p.position.board.left.leafIndex)).card + 1) :
    ∃ tu st su, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p tu ∧
      (exactGame N blue).FollowStep σ H b PT.target st ∧
      (exactGame N blue).FollowStep σ H b PU.target su ∧
      tu.position.pending = none ∧ st.position.pending = none ∧ su.position.pending = none ∧
      tu.position.board.left.relaxed = true ∧ tu.position.board.right = p.position.board.right ∧
      tu.position.board.left.currentLabel = PT.lowerLabel ∧
      tu.position.board.left.leafIndex = PT.labels.pivot ∧
      (∀ x ∈ tu.position.board.right.coordinates,
        x ≤ tu.position.board.left.coordinates.getLastD 0) ∧
      LabeledWord.SameStructure tu.position.board.left (st.position.board.get PT.side) ∧
      LabeledWord.SameStructure tu.position.board.right (su.position.board.get PU.side) ∧
      (st.position.board.get PT.side).relaxed = true ∧
      (su.position.board.get PU.side).relaxed = true ∧
      (st.position.board.get PT.side).currentLabel = PT.labels.upper ∧
      (su.position.board.get PU.side).currentLabel = PU.labels.upper ∧
      (st.position.board.get PT.side).leafIndex = PT.labels.pivot ∧
      (su.position.board.get PU.side).leafIndex = PU.labels.pivot ∧
      (st.position.board.get PT.side).rootLabel = (PT.target.position.board.get PT.side).rootLabel ∧
      (su.position.board.get PU.side).rootLabel = (PU.target.position.board.get PU.side).rootLabel ∧
      st.position.board.get (!PT.side) = PT.target.position.board.get (!PT.side) ∧
      su.position.board.get (!PU.side) = PU.target.position.board.get (!PU.side) := by
  have hnext := finite_rank_successor p.position.board.left.currentLabel PT.upto.mem hnextRank
  obtain ⟨su, hSUstep, hSUnone, hSUcoords, hSUrel, hSUother, hSUroot, hSUbody, hSUleaf⟩ :=
    PU.fire_full hHN ((Position.history_dataInvariant p).2.1 true).2 hUat
  obtain ⟨tu, st, hpTU, hSTstep, hTUnone, hSTnone, hTUrel, hTUleaf, hTUlabel,
      hTUother, hTUsep, hTshape, hSTrel, hSTroot, hSTlabel, hSTleaf, hSTother⟩ :=
    PT.fire_at_next_leaf hHN hH blue false hwin hnext.1 hnext.2 hUrel hsep
  have hright : tu.position.board.right = p.position.board.right := hTUother
  have hUshape : LabeledWord.SameStructure tu.position.board.right
      (su.position.board.get PU.side) := by
    rw [hright]
    obtain ⟨as, has⟩ := History.word_run p true
    obtain ⟨bs, hbs⟩ := History.word_run su PU.side
    exact LabeledWord.sameStructure_of_initial_runs has.run hbs.run hSUcoords.symm
  have hSUlabel : (su.position.board.get PU.side).currentLabel = PU.labels.upper := by
    simp [LabeledWord.currentLabel, hSUbody]
  exact ⟨tu, st, su, hpTU, hSTstep, hSUstep, hTUnone, hSTnone, hSUnone,
    hTUrel, hright, hTUlabel, hTUleaf, hTUsep, hTshape, hUshape, hSTrel, hSUrel,
    hSTlabel, hSUlabel, hSTleaf, hSUleaf, hSTroot, hSUroot, hSTother, hSUother⟩

#print axioms strict_anchor_handoff

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
