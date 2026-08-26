import ErdosProblems.Erdos118.Reused591.ReachSelectedLeaf
import ErdosProblems.Erdos118.Reused591.FirstLeafGluingHistory
import ErdosProblems.Erdos118.Reused591.FollowInputs
import ErdosProblems.Erdos118.Reused591.NextMarkerAcceptance

namespace Erdos118.Reused591

/-! # Stop at the last selected leaf of a current or future selected body -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_reach_current_body_last_leaf {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) (hn : p.position.pending = none)
    (hr : (p.position.board.get side).relaxed = true)
    (hsep : ∀ y ∈ (p.position.board.get (!side)).coordinates,
      y ≤ (p.position.board.get side).coordinates.getLastD 0) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).NoLeafPending ∧
      (q.position.board.get side).bodyLabels = (p.position.board.get side).bodyLabels ∧
      ∀ y ∈ (q.position.board.get (!side)).coordinates,
        y ≤ (q.position.board.get side).coordinates.getLastD 0 := by
  have hdata := of_decide_eq_true hr
  let j := (p.position.board.get side).currentLabel.sup id
  have hj : j ∈ (p.position.board.get side).currentLabel := by
    simpa [j] using Finset.sup_mem_of_nonempty (f := id) ⟨_, hdata.2.2⟩
  have hup : LabeledWord.UpToLeaf j (p.position.board.get side) :=
    ⟨hdata.2.1, hj, Finset.le_sup (f := id) hdata.2.2⟩
  obtain ⟨q, hpq, hqn, hqr, hqi, hqb, _hqm, hqsep⟩ :=
    winning_reach_selected_leaf_le_fresh hHN hH blue hwin side j hn hup hsep
  refine ⟨q, hpq, hqn, hqr, ?_, hqb, hqsep⟩
  intro k hk
  rw [hqi]
  exact Finset.le_sup (f := id) (by simpa only [LabeledWord.currentLabel, hqb] using hk)

theorem winning_reach_body_last_leaf {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) (hn : p.position.pending = none)
    (hr : (p.position.board.get side).relaxed = true)
    (hsep : ∀ y ∈ (p.position.board.get (!side)).coordinates,
      y ≤ (p.position.board.get side).coordinates.getLastD 0) {i : ℕ}
    (hi : i ∈ (p.position.board.get side).rootLabel)
    (hbefore : (p.position.board.get side).bodyLabels.length ≤ i) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).NoLeafPending ∧
      (q.position.board.get side).bodyLabels.length = i ∧
      (q.position.board.get side).rootLabel = (p.position.board.get side).rootLabel ∧
      ∀ y ∈ (q.position.board.get (!side)).coordinates,
        y ≤ (q.position.board.get side).coordinates.getLastD 0 := by
  have hstart := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant p).2.1 side).1 hr
  have root_eq {q : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q) :
      (q.position.board.get side).rootLabel = (p.position.board.get side).rootLabel := by
    obtain ⟨as, has, _⟩ := follow_word_inputs hpath 0 (fun _ => Nat.zero_le _) side
    exact has.rootLabel_eq hstart
  rcases lt_or_eq_of_le hbefore with hlt | heq
  · obtain ⟨v, d, hpv, hpV, hd, hmV, hiV⟩ :=
      winning_reach_body_marker hHN hH blue hwin side i hstart ⟨hi, hlt⟩
    let B := max v.position.bound (b v)
    obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH B 1 d (by omega) hd
    obtain ⟨w, _w', hvw, _hvw', hwn, _hwn', _hshape, hwr, _hwr', _hwi, _hwi',
        hwb, _hwb', _hwo, _hwo'⟩ := first_leaf_gluing hHN hH blue σ v v side side
      L L rfl rfl hpV hpV hmV hmV (LabeledWord.SameStructure.refl _) le_rfl le_rfl
    have hpw := hpv.tail hvw
    have hwsep := (FiniteResponseGame.FollowStep.next (exactGame N blue) hvw).reply_separation hpV
    obtain ⟨q, hwq, hqn, hqr, hqno, hqb, hqsep⟩ :=
      winning_reach_current_body_last_leaf hHN hH blue
        (hwin.of_reachable (exactGame N blue) hpw) side hwn hwr hwsep
    refine ⟨q, hpw.trans hwq, hqn, hqr, hqno, ?_, root_eq (hpw.trans hwq), hqsep⟩
    rw [hqb, hwb, List.length_append, List.length_singleton]
    exact hiV
  · obtain ⟨q, hpq, hqn, hqr, hqno, hqb, hqsep⟩ :=
      winning_reach_current_body_last_leaf hHN hH blue hwin side hn hr hsep
    exact ⟨q, hpq, hqn, hqr, hqno, (congrArg List.length hqb).trans heq, root_eq hpq, hqsep⟩

#print axioms winning_reach_current_body_last_leaf
#print axioms winning_reach_body_last_leaf

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
