import ErdosProblems.Erdos591.ReachPenultimateBody
import ErdosProblems.Erdos591.FreshOppositeLeaf

/-!
# The penultimate-body endpoint when the other word may be freshest

Reaching a strictly future body or leaf supplies fresh separation itself.
If the desired endpoint has already been reached, preserve the current
history without asking for separation in the wrong direction.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_reach_later_body_last_leaf {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) (hr : (p.position.board.get side).relaxed = true) {i : ℕ}
    (hi : i ∈ (p.position.board.get side).rootLabel)
    (hbefore : (p.position.board.get side).bodyLabels.length < i) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).NoLeafPending ∧
      (q.position.board.get side).bodyLabels.length = i ∧
      (q.position.board.get side).rootLabel = (p.position.board.get side).rootLabel ∧
      ∀ x ∈ (q.position.board.get (!side)).coordinates,
        x ≤ (q.position.board.get side).coordinates.getLastD 0 := by
  have hstart := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant p).2.1 side).1 hr
  obtain ⟨v, d, hpv, hpV, hd, hmV, hiV⟩ :=
    winning_reach_body_marker hHN hH blue hwin side i hstart ⟨hi, hbefore⟩
  let B := max v.position.bound (b v)
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH B 1 d (by omega) hd
  obtain ⟨w, _other, hvw, _ho, hwn, _hon, _hs, hwr, _hor, _hi, _hoi,
      hwb, _hob, _hwo, _hoo⟩ := first_leaf_gluing hHN hH blue σ v v side side
        L L rfl rfl hpV hpV hmV hmV (LabeledWord.SameStructure.refl _) le_rfl le_rfl
  have hpw := hpv.tail hvw
  have hwsep := (FiniteResponseGame.FollowStep.next (exactGame N blue) hvw).reply_separation hpV
  obtain ⟨q, hwq, hqn, hqr, hqno, hqb, hqsep⟩ :=
    winning_reach_current_body_last_leaf hHN hH blue
      (hwin.of_reachable (exactGame N blue) hpw) side hwn hwr hwsep
  obtain ⟨as, has, _⟩ := follow_word_inputs (hpw.trans hwq) 0 (fun _ => Nat.zero_le _) side
  refine ⟨q, hpw.trans hwq, hqn, hqr, hqno, ?_, has.rootLabel_eq hstart, hqsep⟩
  rw [hqb, hwb, List.length_append, List.length_singleton]
  exact hiV

theorem winning_reach_penultimate_body_or_current {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) (hn : p.position.pending = none)
    (hr : (p.position.board.get side).relaxed = true)
    (hbefore : (p.position.board.get side).bodyLabels.length <
      (p.position.board.get side).lastSelectedBody) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).NoLeafPending ∧
      (q.position.board.get side).rootLabel = (p.position.board.get side).rootLabel ∧
      (q.position.board.get side).bodyLabels.length <
        (q.position.board.get side).lastSelectedBody ∧
      (∀ k ∈ (q.position.board.get side).rootLabel,
        k < (q.position.board.get side).lastSelectedBody →
          k ≤ (q.position.board.get side).bodyLabels.length) ∧
      (q = p ∨ ∀ x ∈ (q.position.board.get (!side)).coordinates,
        x ≤ (q.position.board.get side).coordinates.getLastD 0) := by
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
  have hpen : ∀ k ∈ w.rootLabel, k < w.lastSelectedBody → k ≤ i := by
    intro k hk hlt
    exact Finset.le_sup (f := id) (Finset.mem_erase.mpr ⟨hlt.ne, hk⟩)
  have finish {q : Concrete.Hist N}
      (hqi : (q.position.board.get side).bodyLabels.length = i)
      (hroot : (q.position.board.get side).rootLabel = w.rootLabel) :
      (q.position.board.get side).bodyLabels.length <
          (q.position.board.get side).lastSelectedBody ∧
        ∀ k ∈ (q.position.board.get side).rootLabel,
          k < (q.position.board.get side).lastSelectedBody →
            k ≤ (q.position.board.get side).bodyLabels.length := by
    have hlast : (q.position.board.get side).lastSelectedBody = w.lastSelectedBody := by
      simp only [LabeledWord.lastSelectedBody, hroot]
    simpa only [hqi, hroot, hlast] using And.intro hilt hpen
  rcases lt_or_eq_of_le hile with hlt | heq
  · obtain ⟨q, hpq, hqn, hqr, hqno, hqi, hroot, hsep⟩ :=
      winning_reach_later_body_last_leaf hHN hH blue hwin side hr hi hlt
    exact ⟨q, hpq, hqn, hqr, hqno, hroot, (finish hqi hroot).1,
      (finish hqi hroot).2, Or.inr hsep⟩
  · by_cases hno : w.NoLeafPending
    · exact ⟨p, .refl, hn, hr, hno, rfl, hbefore,
        (fun k hk hlt => by
          change k ≤ w.bodyLabels.length
          rw [heq]
          exact hpen k hk hlt), Or.inl rfl⟩
    · let j := w.currentLabel.sup id
      have hj : j ∈ w.currentLabel := by
        simpa [j] using Finset.sup_mem_of_nonempty (f := id)
          ⟨_, (of_decide_eq_true hr).2.2⟩
      have hleaf : w.leafIndex < j := by
        by_contra hle
        apply hno
        intro k hk
        exact (Finset.le_sup (f := id) hk).trans (Nat.le_of_not_gt hle)
      obtain ⟨q, hpq, hqn, hqr, hqj, hqb, _hqm, hsep⟩ :=
        winning_reach_selected_leaf_fresh hHN hH blue hwin side j
          ⟨(of_decide_eq_true hr).2.1, hj, hleaf.le⟩ hleaf
      have hqno : (q.position.board.get side).NoLeafPending := by
        intro k hk
        rw [hqj]
        exact Finset.le_sup (f := id) (by simpa only [LabeledWord.currentLabel, hqb] using hk)
      obtain ⟨as, has, _⟩ := follow_word_inputs hpq 0 (fun _ => Nat.zero_le _) side
      have hroot := has.rootLabel_eq (LabeledWord.relaxed_ne_start
        ((Position.history_dataInvariant p).2.1 side).1 hr)
      have hqi := (congrArg List.length hqb).trans heq
      exact ⟨q, hpq, hqn, hqr, hqno, hroot, (finish hqi hroot).1,
        (finish hqi hroot).2, Or.inr hsep⟩

#print axioms winning_reach_later_body_last_leaf
#print axioms winning_reach_penultimate_body_or_current

end Erdos591.Positive.Game.Payoff
