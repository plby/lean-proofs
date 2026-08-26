import ErdosProblems.Erdos591.ReachPenultimateBody
import ErdosProblems.Erdos591.AlignedReverseEndpoint
import ErdosProblems.Erdos591.FreshLeafNextMarker

/-!
# Both aligned penultimate endpoints with the first last-marker response pending

The new moves may be confined to a smaller infinite input set. The
terminal aligned identity is applied only after lifting their actual
path to the original winning pool. The first word is not advanced when
its next request is obtained.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem aligned_penultimate_request_on_subset {N H J : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (hJH : J ⊆ H) (hJ : J.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin p : Concrete.Hist N)
    {a : ℕ} (ha : 0 < a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true)
    (hn : p.position.pending = none) (hr : p.position.board.right.relaxed = true)
    (hpos : 0 < p.position.board.left.coordinates.length)
    (hbefore : p.position.board.right.bodyLabels.length < p.position.board.right.lastSelectedBody)
    (hsep : ∀ x ∈ p.position.board.left.coordinates,
      x ≤ p.position.board.right.coordinates.getLastD 0) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p q ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧
      q.position.board.left.relaxed = true ∧ q.position.board.left.NoLeafPending ∧
      q.position.board.left.bodyLabels.length < q.position.board.left.lastSelectedBody ∧
      (∀ k ∈ q.position.board.left.rootLabel,
        k < q.position.board.left.lastSelectedBody → k ≤ q.position.board.left.bodyLabels.length) ∧
      q.position.board.right.relaxed = true ∧ q.position.board.right.NoLeafPending ∧
      q.position.board.right.bodyLabels.length < q.position.board.right.lastSelectedBody ∧
      (∀ k ∈ q.position.board.right.rootLabel,
        k < q.position.board.right.lastSelectedBody →
          k ≤ q.position.board.right.bodyLabels.length) ∧
      ∀ x ∈ q.position.board.left.coordinates,
        x ≤ q.position.board.right.coordinates.getLastD 0 := by
  have pathH {u v : Concrete.Hist N}
      (hp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hp
  have hwinP := (hwin.of_reachable (exactGame N blue) hfrom).mono
    (exactGame N blue) hJH (fun _ => le_rfl)
  obtain ⟨v, hpv, _hvn, hvr, hvno, _hvroot, hvbefore, hvpen, hvsep⟩ :=
    winning_reach_penultimate_body (hJH.trans hHN) hJ blue hwinP true hn hr hbefore hsep
  have hvpos : 0 < v.position.board.left.coordinates.length := by
    obtain ⟨as, has, _⟩ := follow_word_inputs hpv 0 (fun _ => Nat.zero_le _) false
    have hle : p.position.board.left.coordinates.length ≤
        v.position.board.left.coordinates.length := has.coordinates_prefix.length_le
    omega
  obtain ⟨hvl, _hvorder, hvlbefore, hvlpen, hvlno⟩ := winning_aligned_reverse_endpoint
    hHN hH blue origin v ha hop hboard hmode hwin (hfrom.trans (pathH hpv)) hall
      hvr hvpos hvsep hvbefore hvpen hvno
  have hmem : v.position.board.left.lastSelectedBody ∈ v.position.board.left.rootLabel := by
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id)
      ⟨_, (of_decide_eq_true hvl).2.1⟩
  obtain ⟨q, hvq, hqboard, hqp⟩ := winning_next_body_after_fresh_leaf (hJH.trans hHN) hJ blue
    (hwinP.of_reachable (exactGame N blue) hpv) true hvr hvsep hvl ⟨hmem, hvlbefore⟩
  refine ⟨q, hpv.trans hvq, hqp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hqboard] using hvl
  · simpa only [hqboard] using hvlno
  · simpa only [hqboard] using hvlbefore
  · simpa only [hqboard] using hvlpen
  · simpa only [hqboard, Board.get] using hvr
  · simpa only [hqboard, Board.get] using hvno
  · simpa only [hqboard, Board.get] using hvbefore
  · simpa only [hqboard, Board.get] using hvpen
  · simpa only [hqboard, Board.get, Bool.not_true] using hvsep

#print axioms aligned_penultimate_request_on_subset

end Erdos591.Positive.Game.Payoff
