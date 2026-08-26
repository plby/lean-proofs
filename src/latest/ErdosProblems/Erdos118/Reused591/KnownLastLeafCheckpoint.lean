import ErdosProblems.Erdos118.Reused591.OvertakenOtherRelaxed
import ErdosProblems.Erdos118.Reused591.InsideLastLeafBoundary
import ErdosProblems.Erdos118.Reused591.PendingOpposite
import ErdosProblems.Erdos118.Reused591.PendingNextLeaf

namespace Erdos118.Reused591

/-!
# The middle endpoint when all opposite selected bodies are already read

The next opposite selection lies in the current body, so its actual
size-zero reply can be chosen directly. No future-body reservation is
needed. The final first-word leaf remains unsubmitted.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem known_last_leaf_checkpoint {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some true) (hn : p.position.pending = none)
    (hr : p.position.board.left.relaxed = true)
    (hsep : ∀ y ∈ p.position.board.right.coordinates,
      y ≤ p.position.board.left.coordinates.getLastD 0)
    {j : ℕ} (htarget : LabeledWord.UpToLeaf j p.position.board.left)
    (hstrict : p.position.board.left.leafIndex < j)
    (hnext : ∀ k ∈ p.position.board.left.currentLabel,
      p.position.board.left.leafIndex < k → j ≤ k)
    (hrootLast : ∀ k ∈ p.position.board.left.rootLabel,
      k ≤ p.position.board.left.bodyLabels.length)
    (hleafLast : ∀ k ∈ p.position.board.left.currentLabel, k ≤ j)
    (hrootT : ∀ k ∈ p.position.board.right.rootLabel,
      k ≤ p.position.board.right.bodyLabels.length)
    (hposT : 0 < p.position.board.right.coordinates.length) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧
      q.position.board.left = p.position.board.left ∧ q.position.board.right.relaxed = true ∧
      ¬ Macro.Pending q.position.board.right := by
  classical
  obtain ⟨hTrel, _horder⟩ := winning_overtaken_other_relaxed hHN hH blue hwin false hr hposT hsep
  have hTstart := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant p).2.1 true).1 hTrel
  have hremain := winning_fresh_nonlast_other_pending hHN hH blue hwin false hn hr hsep
    (Or.inr ⟨htarget.selected, j, htarget.mem, hstrict⟩) hTstart
  have hlater : ∃ k ∈ p.position.board.right.currentLabel,
      p.position.board.right.leafIndex < k := by
    rcases hremain with ⟨i, hi, hlt⟩ | ⟨_, k, hk, hlt⟩
    · exact (not_lt_of_ge (hrootT i hi) hlt).elim
    · exact ⟨k, hk, hlt⟩
  let C := p.position.board.right.currentLabel.filter (p.position.board.right.leafIndex < ·)
  have hC : C.Nonempty := by
    obtain ⟨k, hk, hlt⟩ := hlater
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, hlt⟩⟩
  let k := C.min' hC
  have hkC : k ∈ C := Finset.min'_mem _ _
  have hk := Finset.mem_filter.mp hkC
  have hup : LabeledWord.UpToLeaf k p.position.board.right :=
    ⟨(of_decide_eq_true hTrel).2.1, hk.1, hk.2.le⟩
  have hknext : ∀ l ∈ p.position.board.right.currentLabel,
      p.position.board.right.leafIndex < l → k ≤ l :=
    fun l hl hlt => Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hl, hlt⟩)
  obtain ⟨v, hpv, hvboard, hpvRequest⟩ := winning_next_leaf_request_after_other
    hHN hH blue hwin true hup hk.2 hr hsep
  have hvkind : (exactGame N blue).kind v = .builder :=
    (Concrete.kind_builder_iff (payoff blue) v).mpr ⟨_, hpvRequest⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH v hvkind (b v)
  let w := Concrete.response v u
  have hvw : (exactGame N blue).FollowStep σ H b v w :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ v u hvkind hu huH hub
  have hreply := (Concrete.response_spec hu).reply_spec hpvRequest
  obtain ⟨hwr, _hwk, _hwb, _hwm⟩ := hreply.next_leaf_endpoint
    ((Position.history_dataInvariant v).2.1 true).1
    ((Position.history_dataInvariant w).2.1 true).1
    (fun x hx => (Nat.zero_le _).trans_lt (hub x hx))
    (by simpa only [hvboard, Board.get] using hup)
    (by simpa only [hvboard, Board.get] using hk.2)
    (by simpa only [hvboard, Board.get] using hknext)
  have hleft : w.position.board.left = p.position.board.left := by
    simpa only [Board.get, Bool.not_true, hvboard] using hreply.other_eq
  have hwsep :=
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hvw).reply_separation hpvRequest
  have hpw := hpv.tail hvw
  obtain ⟨q, hwq, hqboard, hpq⟩ := winning_next_leaf_request_after_other hHN hH blue
    (hwin.of_reachable (exactGame N blue) hpw) false
    (by simpa only [Board.get, hleft] using htarget)
    (by simpa only [Board.get, hleft] using hstrict) hwr hwsep
  have hpath := hpw.trans hwq
  have hql : q.position.board.left = p.position.board.left := by simpa only [hqboard] using hleft
  have hqr : q.position.board.right.relaxed = true := by simpa only [Board.get, hqboard] using hwr
  refine ⟨q, hpath, hpq, hql, hqr, ?_⟩
  exact winning_before_last_leaf_other_exhausted hHN hH blue
    (hwin.of_reachable (exactGame N blue) hpath) (follow_mode_some hpath hmode) hpq
    (by simpa only [hql] using htarget) (by simpa only [hql] using hstrict)
    (by simpa only [hql] using hnext) (by simpa only [hql] using hrootLast)
    (by simpa only [hql] using hleafLast)
    (LabeledWord.relaxed_ne_start ((Position.history_dataInvariant q).2.1 true).1 hqr)

#print axioms known_last_leaf_checkpoint

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
