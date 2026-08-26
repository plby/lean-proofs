import ErdosProblems.Erdos591.NextLeafEndpoint
import ErdosProblems.Erdos591.NextLeafReplay

/-!
# Share the next selected leaf after a retained same-body prefix

Choose one actual fine response sufficiently late for both histories,
append it to the recorded virtual prefix, and replay the whole run as
the old next-leaf response. Both opposite words and both previously
chosen body-label lists stay unchanged.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem shared_next_leaf_from_prefix {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    (σ : (exactGame N blue).ArchitectStrategy) (old fine : Concrete.Hist N)
    (s t : Bool) {j : ℕ}
    (hpOld : old.position.pending = some ⟨s, .advance 0⟩)
    (hpFine : fine.position.pending = some ⟨t, .advance 0⟩)
    (hupOld : LabeledWord.UpToLeaf j (old.position.board.get s))
    (hstrictOld : (old.position.board.get s).leafIndex < j)
    (hnextOld : ∀ i ∈ (old.position.board.get s).currentLabel,
      (old.position.board.get s).leafIndex < i → j ≤ i)
    (hupFine : LabeledWord.UpToLeaf j (fine.position.board.get t))
    (hstrictFine : (fine.position.board.get t).leafIndex < j)
    (hnextFine : ∀ i ∈ (fine.position.board.get t).currentLabel,
      (fine.position.board.get t).leafIndex < i → j ≤ i)
    {anchor : LabeledWord} {frontAtoms : List (Finset ℕ × ℕ)}
    (hsame : LabeledWord.SameStructure (old.position.board.get s) anchor)
    (hfront : LabeledWord.LegalRun anchor frontAtoms (fine.position.board.get t))
    (hfrontPool : ∀ a ∈ frontAtoms, a.2 ∈ H ∧ max old.position.bound (b old) < a.2)
    (hcount : (fine.position.board.get t).bodyLabels.length = anchor.bodyLabels.length)
    (hmarker : (fine.position.board.get t).bodyMarker = anchor.bodyMarker) :
    ∃ q v, (exactGame N blue).FollowStep σ H b old q ∧
      (exactGame N blue).FollowStep σ H b fine v ∧
      q.position.pending = none ∧ v.position.pending = none ∧
      LabeledWord.SameStructure (q.position.board.get s) (v.position.board.get t) ∧
      (q.position.board.get s).relaxed = true ∧ (v.position.board.get t).relaxed = true ∧
      (q.position.board.get s).leafIndex = j ∧ (v.position.board.get t).leafIndex = j ∧
      (q.position.board.get s).bodyLabels = (old.position.board.get s).bodyLabels ∧
      (v.position.board.get t).bodyLabels = (fine.position.board.get t).bodyLabels ∧
      q.position.board.get (!s) = old.position.board.get (!s) ∧
      v.position.board.get (!t) = fine.position.board.get (!t) := by
  let C := max (b fine) (max old.position.bound (b old))
  have hk : (exactGame N blue).kind fine = .builder :=
    (Concrete.kind_builder_iff (payoff blue) fine).mpr ⟨_, hpFine⟩
  obtain ⟨u, hu, huH, huC⟩ := (exactGame N blue).response_exists_above hHN hH fine hk C
  let v := Concrete.response fine u
  have hsFine : (exactGame N blue).FollowStep σ H b fine v :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ fine u hk hu huH
      (fun x hx => (le_max_left _ _).trans_lt (huC x hx))
  have hr := (Concrete.response_spec hu).reply_spec hpFine
  have hpos : ∀ x ∈ u, 0 < x := fun x hx => (Nat.zero_le C).trans_lt (huC x hx)
  obtain ⟨hvrel, hvidx, hvlabels, hvmarker⟩ := hr.next_leaf_endpoint
    ((Position.history_dataInvariant fine).2.1 t).1 ((Position.history_dataInvariant v).2.1 t).1
    hpos hupFine hstrictFine hnextFine
  obtain ⟨newAtoms, hnew, hnewMem⟩ := hr.legal_run hpos t
  have hwhole := hfront.append hnew
  have hinc : ((frontAtoms ++ newAtoms).map Prod.snd).Pairwise (· < ·) := by
    have hi := ((Position.history_dataInvariant v).2.1 t).2
    rw [LabeledWord.runAtoms_coordinates hwhole.run] at hi
    exact (List.pairwise_append.mp hi).2.1
  have hpool : ∀ a ∈ frontAtoms ++ newAtoms,
      a.2 ∈ H ∧ old.position.bound < a.2 ∧ b old < a.2 := by
    intro a ha
    have hf : a.2 ∈ H ∧ max old.position.bound (b old) < a.2 := by
      rcases List.mem_append.mp ha with ha | ha
      · exact hfrontPool a ha
      · exact ⟨huH (hnewMem a ha), (le_max_right _ _).trans_lt (huC a.2 (hnewMem a ha))⟩
    exact ⟨hf.1, (le_max_left _ _).trans_lt hf.2, (le_max_right _ _).trans_lt hf.2⟩
  obtain ⟨q, hsOld, hqn, hshape, hqr, hqlabels, hother⟩ :=
    Concrete.follow_next_leaf hHN (payoff blue) σ old s hpOld hsame hupOld hstrictOld hnextOld
      hwhole.run hvidx ((congrArg List.length hvlabels).trans hcount)
      (hvmarker.trans hmarker) hinc hpool
  have hvn := (History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hsFine)).no_pending_after_reply hpFine
  exact ⟨q, v, hsOld, hsFine, hqn, hvn, hshape, hqr, hvrel,
    hshape.leaf_eq.trans hvidx, hvidx, hqlabels, hvlabels, hother, hr.other_eq⟩

#print axioms shared_next_leaf_from_prefix

end Erdos591.Positive.Game.Payoff
