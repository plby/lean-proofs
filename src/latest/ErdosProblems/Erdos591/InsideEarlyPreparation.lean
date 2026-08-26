import ErdosProblems.Erdos591.ManagedLastLeaf
import ErdosProblems.Erdos591.LastLastLabels
import ErdosProblems.Erdos591.PositiveSecondRequest
import ErdosProblems.Erdos591.PrepareRootHistory

/-!
# Common early root preparation for the multi-body inside constructions

Starting at a nonlast first selected leaf, install the delayed opposite
root and reach the last leaf of the penultimate first-word body. The
opposite managed origin is retained. No singleton or marker-order
assumption enters this preparation.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_early_preparation {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    (origin st : Concrete.Hist N) {B a : ℕ} (L : LastLastLabels H B a)
    (hwinOrigin : (exactGame N blue).ArchitectWins H b σ origin)
    (hopening : origin.position.pending = some ⟨false, .advance a⟩)
    (hboardOrigin : origin.position.board = Board.initial)
    (hmodeOrigin : origin.position.mode = some true)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin st)
    (hpST : st.position.pending = none) (hTinit : st.position.board.right = LabeledWord.initial)
    (hSrel : st.position.board.left.relaxed = true)
    (hSroot : st.position.board.left.rootLabel = L.lower)
    (hSbody : st.position.board.left.bodyLabels.length = L.firstLower)
    (hSstrict : st.position.board.left.leafIndex < st.position.board.left.currentLabel.sup id) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) st q ∧
      q.position.pending = none ∧ q.position.board.left.relaxed = true ∧
      q.position.board.left.NoLeafPending ∧ q.position.board.left.rootLabel = L.lower ∧
      q.position.board.left.bodyLabels.length = L.penultimate ∧
      (∀ y ∈ q.position.board.right.coordinates,
        y ≤ q.position.board.left.coordinates.getLastD 0) ∧
      ∃ M : Managed N H blue b σ false true LabeledWord.initial q.position.board.right,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
  have hwinST := hwinOrigin.of_reachable (exactGame N blue) hfrom
  obtain ⟨stR, e, hSTrequest, hSTboard, hpR, he⟩ :=
    winning_initial_right_request hHN hH blue htri hroot hwinST hpST hTinit hSrel
  let C := max (max stR.position.bound (b stR)) (max origin.position.bound (b origin))
  have ha : 0 < a := L.lower_card ▸ Finset.card_pos.mpr ⟨L.pivot, L.pivot_lower⟩
  obtain ⟨T⟩ := LastFirstLabels.exists_of_infinite hH C e a he ha
  obtain ⟨v, hRV, hvn, _hvm, hvOther, R, hRtarget, hRside, _hRlabels⟩ :=
    prepare_root hHN hH blue hwinOrigin true false T hpR hopening
      (by simpa [hSTboard, Board.get] using hTinit)
      (by simp [hboardOrigin, Board.initial, Board.get]) (le_max_left _ _) (le_max_right _ _)
  have hstv := (Relation.ReflTransGen.single hSTrequest).tail hRV
  have hwinV := hwinST.of_reachable (exactGame N blue) hstv
  have hSsame : v.position.board.left = st.position.board.left := by
    simpa [hSTboard, Board.get] using hvOther
  let M : Managed N H blue b σ false true LabeledWord.initial v.position.board.right :=
    .root R hRside
      (by simp [hRtarget, hRside, hboardOrigin, Board.initial, Board.get])
      (by simpa only [hRtarget] using hmodeOrigin)
  have hMfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
    change Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin R.target
    rw [hRtarget]
  have hM : ∃ M : Managed N H blue b σ false true LabeledWord.initial v.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := ⟨M, hMfrom⟩
  have hVrel : v.position.board.left.relaxed = true := by simpa only [hSsame] using hSrel
  have hVstart : v.position.board.left.parser ≠ .start :=
    LabeledWord.relaxed_ne_start ((Position.history_dataInvariant v).2.1 false).1 hVrel
  have hVroot : v.position.board.left.rootLabel = L.lower := by simpa only [hSsame] using hSroot
  have hVbody : v.position.board.left.bodyLabels.length = L.firstLower := by
    simpa only [hSsame] using hSbody
  have hstop : ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) v q ∧
      q.position.pending = none ∧ q.position.board.left.relaxed = true ∧
      q.position.board.left.NoLeafPending ∧
      q.position.board.left.bodyLabels.length = L.penultimate ∧
      (∀ y ∈ q.position.board.right.coordinates, y ≤ q.position.board.left.coordinates.getLastD 0) ∧
      ∃ M : Managed N H blue b σ false true LabeledWord.initial q.position.board.right,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
    rcases lt_or_eq_of_le L.firstLower_le_penultimate with hlt | heq
    · exact managed_future_body_last_leaf_from hHN hH blue hwinV L.penultimate false hVstart
        ⟨hVroot ▸ L.penultimate_lower, by simpa only [Board.get, hVbody] using hlt⟩ origin hM
    · obtain ⟨q, hvq, hqn, hqr, hqno, hqlabels, _hqm, hqsep, hMq⟩ :=
        managed_current_body_last_leaf_from hHN hH blue hwinV false hvn hVrel
          (Or.inl (by simpa only [hSsame, Board.get] using hSstrict)) origin hM
      refine ⟨q, hvq, hqn, hqr, hqno, ?_, hqsep, hMq⟩
      have hlen := congrArg List.length hqlabels
      exact hlen.trans (hVbody.trans heq)
  obtain ⟨q, hvq, hqn, hqrel, hqno, hqbody, hqsep, hMq⟩ := hstop
  obtain ⟨as, has, _⟩ := follow_word_inputs hvq 0 (fun _ => Nat.zero_le _) false
  have hqroot : q.position.board.left.rootLabel = L.lower :=
    (has.rootLabel_eq hVstart).trans hVroot
  exact ⟨q, hstv.trans hvq, hqn, hqrel, hqno, hqroot, hqbody, hqsep, hMq⟩

#print axioms inside_early_preparation

end Erdos591.Positive.Game.Payoff
