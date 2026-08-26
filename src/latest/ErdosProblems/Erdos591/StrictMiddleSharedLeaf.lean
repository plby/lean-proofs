import ErdosProblems.Erdos591.LastBodyFinalRequest
import ErdosProblems.Erdos591.InsideSharedLeafEndgame
import ErdosProblems.Erdos591.LastBodyEndpoint

/-!
# The strict lower middle phase and the shared second/last leaf

The old ST reply waits for its next selected S leaf. Run SU through
all its intervening selected S leaves, stopping before its last one.
The opposite U selections are then exhausted. Read that final S leaf
and replay its complete coordinate prefix as the old ST reply.
Only SU is required to finish its S selection at the shared leaf.
Every new input of either SU word exceeds the prescribed bound.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem strict_middle_shared_leaf {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (old fine : Concrete.Hist N)
    (hwin : (exactGame N blue).ArchitectWins H b σ fine)
    (hmode : fine.position.mode = some true)
    (hpOld : old.position.pending = some ⟨false, .advance 0⟩)
    (hl : fine.position.board.left.relaxed = true)
    (hr : fine.position.board.right.relaxed = true)
    (hsep : ∀ x ∈ fine.position.board.left.coordinates,
      x ≤ fine.position.board.right.coordinates.getLastD 0)
    (hsame : LabeledWord.SameStructure old.position.board.left fine.position.board.left)
    {gamma : ℕ} (hupOld : LabeledWord.UpToLeaf gamma old.position.board.left)
    (hstrictOld : old.position.board.left.leafIndex < gamma)
    (hnextOld : ∀ i ∈ old.position.board.left.currentLabel,
      old.position.board.left.leafIndex < i → gamma ≤ i)
    (hroot : ∀ i ∈ fine.position.board.left.rootLabel,
      i ≤ fine.position.board.left.bodyLabels.length)
    (hgamma : gamma ∈ fine.position.board.left.currentLabel)
    (hlast : ∀ i ∈ fine.position.board.left.currentLabel, i ≤ gamma)
    (B : ℕ) (hB : max old.position.bound (b old) ≤ B) :
    ∃ st su, (exactGame N blue).FollowStep σ H b old st ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) fine su ∧
      st.position.pending = none ∧ su.position.pending = none ∧
      LabeledWord.SameStructure st.position.board.left su.position.board.left ∧
      st.position.board.left.relaxed = true ∧ su.position.board.left.relaxed = true ∧
      su.position.board.right.relaxed = true ∧
      st.position.board.left.leafIndex = gamma ∧ su.position.board.left.leafIndex = gamma ∧
      st.position.board.left.bodyLabels = old.position.board.left.bodyLabels ∧
      su.position.board.left.bodyLabels = fine.position.board.left.bodyLabels ∧
      st.position.board.right = old.position.board.right ∧
      Relay.BothLast su.position.board ∧
      (∀ x ∈ st.position.board.right.coordinates,
        x ≤ st.position.board.left.coordinates.getLastD 0) ∧
      (∀ x ∈ su.position.board.right.coordinates,
        x ≤ su.position.board.left.coordinates.getLastD 0) ∧
      ∀ side, ∃ as, LabeledWord.LegalRun (fine.position.board.get side) as
        (su.position.board.get side) ∧ ∀ a ∈ as, a.2 ∈ H ∧ B < a.2 := by
  let c : Concrete.Hist N → ℕ := fun r => max (b r) B
  have hbc : ∀ r, b r ≤ c r := fun r => le_max_left (b r) B
  have hBc : ∀ r, B ≤ c r := fun r => le_max_right (b r) B
  have hwinC := hwin.mono (exactGame N blue) (Set.Subset.refl H) hbc
  have hbefore : fine.position.board.left.leafIndex < gamma := hsame.leaf_eq ▸ hstrictOld
  obtain ⟨q, hfq, hpq, hql, hqr, hqb, hqroot, hqbefore, hqnext, _hqsep, hqno⟩ :=
    last_body_final_request hHN hH blue hwinC hmode hl hr hsep hroot hgamma hbefore hlast
  obtain ⟨front, hfront, hfrontPool⟩ := follow_word_inputs hfq B hBc false
  have hcount := congrArg List.length hqb
  have hstart := LabeledWord.relaxed_ne_start ((Position.history_dataInvariant fine).2.1 false).1 hl
  have hmarker := hfront.bodyMarker_of_body_length hstart hcount
  have hcurrent : q.position.board.left.currentLabel = fine.position.board.left.currentLabel := by
    simp only [LabeledWord.currentLabel, hqb]
  have hqUp : LabeledWord.UpToLeaf gamma q.position.board.left :=
    ⟨(of_decide_eq_true hql).2.1, hcurrent ▸ hgamma, hqbefore.le⟩
  have hOldBound : max old.position.bound (c old) ≤ B :=
    max_le ((le_max_left _ _).trans hB) (max_le ((le_max_right _ _).trans hB) le_rfl)
  obtain ⟨st, su, hst, hsu, hstn, hsun, hS, hstrel, hsurel, hstidx, hsuidx,
      hstlabels, hsulabels, hstother, hsuother⟩ :=
    shared_next_leaf_from_prefix hHN hH blue σ old q false false hpOld hpq
      hupOld hstrictOld hnextOld hqUp hqbefore hqnext hsame hfront
      (fun a ha => ⟨(hfrontPool a ha).1, hOldBound.trans_lt (hfrontPool a ha).2⟩)
      hcount hmarker
  have hqRoot : ∀ i ∈ q.position.board.left.rootLabel,
      i ≤ q.position.board.left.bodyLabels.length := by
    simpa only [hqroot, hqb] using hroot
  have hSlast := selected_last_leaf_exhausted hsu hqUp hqRoot
    (by simpa only [hcurrent] using hlast) hsulabels hsuidx
  have hUeq : su.position.board.right = q.position.board.right := hsuother
  have hlastSU : Relay.BothLast su.position.board := by
    intro side
    cases side
    · exact hSlast
    · simpa only [Board.get, hUeq] using hqno
  have hfull := hfq.tail hsu
  refine ⟨st, su,
    FiniteResponseGame.FollowStep.mono (exactGame N blue) (Set.Subset.refl H) hbc hst,
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) (Set.Subset.refl H) hbc hs)
      _ _ hfull,
    hstn, hsun, hS, hstrel, hsurel, ?_, hstidx, hsuidx,
    hstlabels, hsulabels.trans hqb, hstother, hlastSU, ?_, ?_, ?_⟩
  · simpa only [hUeq] using hqr
  · exact (FiniteResponseGame.FollowStep.next (exactGame N blue) hst).reply_separation hpOld
  · exact (FiniteResponseGame.FollowStep.next (exactGame N blue) hsu).reply_separation hpq
  · exact fun side => follow_word_inputs hfull B hBc side

#print axioms strict_middle_shared_leaf

end Erdos591.Positive.Game.Payoff
