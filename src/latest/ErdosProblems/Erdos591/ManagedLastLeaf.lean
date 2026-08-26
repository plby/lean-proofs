import ErdosProblems.Erdos591.ManagedReach
import ErdosProblems.Erdos591.FirstLeafGluingHistory
import ErdosProblems.Erdos591.NextMarkerAcceptance

/-!
# Exhaust one selected body while the opposite play stays managed

The supremum of the nonempty current label is its last selected leaf.
A strict-before start reaches it freshly; an already reached leaf may
be kept when the separation is supplied. For a future body, first reach
its marker and choose an actual first-leaf response.
-/

namespace Erdos591.Positive.Game.Relay

open Erdos591.Negative.Exact
open Payoff

theorem managed_current_body_last_leaf_from {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p) (s : Bool)
    (hp : p.position.pending = none) (hr : (p.position.board.get s).relaxed = true)
    (hprogress : (p.position.board.get s).leafIndex < (p.position.board.get s).currentLabel.sup id ∨
      ∀ y ∈ (p.position.board.get (!s)).coordinates,
        y ≤ (p.position.board.get s).coordinates.getLastD 0)
    {t mode : Bool} {other : LabeledWord} (origin : Concrete.Hist N)
    (hmanaged : ∃ M : Managed N H blue b σ t mode other (p.position.board.get (!s)),
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get s).relaxed = true ∧
      (q.position.board.get s).NoLeafPending ∧
      (q.position.board.get s).bodyLabels = (p.position.board.get s).bodyLabels ∧
      (q.position.board.get s).bodyMarker = (p.position.board.get s).bodyMarker ∧
      (∀ y ∈ (q.position.board.get (!s)).coordinates,
        y ≤ (q.position.board.get s).coordinates.getLastD 0) ∧
      ∃ M : Managed N H blue b σ t mode other (q.position.board.get (!s)),
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
  have hdata := of_decide_eq_true hr
  have hne : (p.position.board.get s).currentLabel.Nonempty := ⟨_, hdata.2.2⟩
  let j := (p.position.board.get s).currentLabel.sup id
  have hj : LabeledWord.UpToLeaf j (p.position.board.get s) :=
    ⟨hdata.2.1, by simpa [j] using Finset.sup_mem_of_nonempty (f := id) hne,
      Finset.le_sup (f := id) hdata.2.2⟩
  have hreach : ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get s).relaxed = true ∧
      (q.position.board.get s).leafIndex = j ∧
      (q.position.board.get s).bodyLabels = (p.position.board.get s).bodyLabels ∧
      (q.position.board.get s).bodyMarker = (p.position.board.get s).bodyMarker ∧
      (∀ y ∈ (q.position.board.get (!s)).coordinates,
        y ≤ (q.position.board.get s).coordinates.getLastD 0) ∧
      ∃ M : Managed N H blue b σ t mode other (q.position.board.get (!s)),
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
    rcases hprogress with hlt | hsep
    · exact managed_reach_selected_leaf_from hHN hH blue hwin s j hj hlt origin hmanaged
    · exact managed_reach_selected_leaf_le_from hHN hH blue hwin s j hp hj hsep origin hmanaged
  obtain ⟨q, hpath, hn, hrel, hidx, hlabels, hmarker, hsep, hM⟩ := hreach
  refine ⟨q, hpath, hn, hrel, ?_, hlabels, hmarker, hsep, hM⟩
  intro k hk
  have hk' : k ∈ (p.position.board.get s).currentLabel := by
    simpa only [LabeledWord.currentLabel, hlabels] using hk
  rw [hidx]
  exact Finset.le_sup (f := id) hk'

theorem managed_future_body_last_leaf_from {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p) (i : ℕ)
    (side : Bool)
    (hstart : (p.position.board.get side).parser ≠ .start)
    (hi : LabeledWord.BeforeBody i (p.position.board.get side))
    {t mode : Bool} {other : LabeledWord} (origin : Concrete.Hist N)
    (hmanaged : ∃ M : Managed N H blue b σ t mode other (p.position.board.get (!side)),
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).NoLeafPending ∧
      (q.position.board.get side).bodyLabels.length = i ∧
      (∀ y ∈ (q.position.board.get (!side)).coordinates,
        y ≤ (q.position.board.get side).coordinates.getLastD 0) ∧
      ∃ M : Managed N H blue b σ t mode other (q.position.board.get (!side)),
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
  obtain ⟨v, d, hpv, hvp, hd, hvm, hvi, hMv⟩ :=
    managed_reach_body_marker_from hHN hH blue hwin side i hstart hi origin hmanaged
  let B := max v.position.bound (b v)
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH B 1 d (by omega) hd
  obtain ⟨z, _z', hvz, _hvz', hzn, _hz'n, _hshape, hzr, _hz'r, _hidx, _hidx',
      hlabels, _hlabels', ho, _ho'⟩ := first_leaf_gluing hHN hH blue σ v v side side
    L L rfl rfl hvp hvp hvm hvm (LabeledWord.SameStructure.refl _) le_rfl le_rfl
  have hpz := hpv.tail hvz
  have hMz : ∃ M : Managed N H blue b σ t mode other (z.position.board.get (!side)),
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
    rw [ho]
    exact hMv
  have hsep := (FiniteResponseGame.FollowStep.next (exactGame N blue) hvz).reply_separation hvp
  obtain ⟨q, hzq, hqn, hqr, hqno, hqb, _hqm, hqsep, hMq⟩ :=
    managed_current_body_last_leaf_from hHN hH blue
      (hwin.of_reachable (exactGame N blue) hpz) side hzn hzr (Or.inr hsep) origin hMz
  refine ⟨q, hpz.trans hzq, hqn, hqr, hqno, ?_, hqsep, hMq⟩
  rw [hqb, hlabels, List.length_append, List.length_singleton]
  exact hvi

#print axioms managed_current_body_last_leaf_from
#print axioms managed_future_body_last_leaf_from

end Erdos591.Positive.Game.Relay
