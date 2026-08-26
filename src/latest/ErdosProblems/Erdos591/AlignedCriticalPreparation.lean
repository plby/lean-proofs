import ErdosProblems.Erdos591.AlignedAnchorPreparation
import ErdosProblems.Erdos591.PreparedLeafReach
import ErdosProblems.Erdos591.AlignedReverseEndpoint

/-!
# Actual aligned critical histories with the upper body reply retained

Drive the second word to its saved penultimate body's last selected
leaf. The reversible aligned endpoint test locates the first word too.
The exact upper request, root label and unchanged other word are kept.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem aligned_critical_prepared_on_subset {N H J : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (hJH : J ⊆ H) (hJ : J.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin p : Concrete.Hist N)
    (R : AlignedRootPlan N J blue b σ p.position.board.right)
    {a : ℕ} (ha : 0 < a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hpos : 0 < p.position.board.left.coordinates.length)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p q ∧
      q.position.pending = none ∧ q.position.board.left.relaxed = true ∧
      q.position.board.left.bodyLabels.length < q.position.board.left.lastSelectedBody ∧
      (∀ k ∈ q.position.board.left.rootLabel,
        k < q.position.board.left.lastSelectedBody → k ≤ q.position.board.left.bodyLabels.length) ∧
      q.position.board.left.NoLeafPending ∧ q.position.board.right.relaxed = true ∧
      q.position.board.right.rootLabel = R.labels.lower ∧
      q.position.board.right.bodyLabels.length = R.labels.shared ∧
      q.position.board.right.NoLeafPending ∧
      (∀ y ∈ q.position.board.left.coordinates,
        y ≤ q.position.board.right.coordinates.getLastD 0) ∧
      ∃ P : PreparedLeaf N J blue b σ q.position.board.right,
        P.side = R.side ∧
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) R.target P.target ∧
        (P.target.position.board.get P.side).rootLabel = R.labels.upper ∧
        (P.target.position.board.get P.side).NoRootPassed ∧
        P.target.position.board.get (!P.side) = R.target.position.board.get (!R.side) ∧
        q.position.board.right.leafIndex = P.labels.pivot := by
  have pathH {u v : Concrete.Hist N}
      (hp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hp
  have hwinP := (hwin.of_reachable (exactGame N blue) hfrom).mono
    (exactGame N blue) hJH (fun _ => le_rfl)
  obtain ⟨v, hpv, hvn, _hvr, hvsep, P, hPs, hPpath, hProot, hPbody,
      hPupper, hPfirst, hPother⟩ :=
    R.prepare_shared true (hJH.trans hHN) hJ hwinP
  obtain ⟨q, hvq, hqn, hqr, hqsep, Q, hQt, hQs, _hQL, hQstem, hQlast⟩ :=
    P.reach_last (hJH.trans hHN) hJ blue true
      (hwinP.of_reachable (exactGame N blue) hpv) hvn hvsep
  have hpq := hpv.trans hvq
  have hroot : q.position.board.right.rootLabel = R.labels.lower :=
    Q.rootLabel.trans ((congrArg LabeledWord.rootLabel hQstem).trans hProot)
  have hbody : q.position.board.right.bodyLabels.length = R.labels.shared := by
    change (q.position.board.get true).bodyLabels.length = R.labels.shared
    rw [Q.body_length, hQstem]
    exact hPbody
  have hlast : q.position.board.right.lastSelectedBody = R.labels.last := by
    rw [LabeledWord.lastSelectedBody, hroot, R.labels.lower_sup]
  have hbefore : q.position.board.right.bodyLabels.length <
      q.position.board.right.lastSelectedBody := by
    rw [hbody, hlast]
    exact R.labels.shared_lt_last
  have hpen : ∀ k ∈ q.position.board.right.rootLabel,
      k < q.position.board.right.lastSelectedBody →
        k ≤ q.position.board.right.bodyLabels.length := by
    intro k hk hlt
    rw [hroot] at hk
    rw [hlast] at hlt
    rw [hbody]
    exact (R.labels.lower_bounds k hk).resolve_left (ne_of_lt hlt)
  have hno : q.position.board.right.NoLeafPending := by
    intro k hk
    change k ≤ (q.position.board.get true).leafIndex
    rw [hQlast]
    exact Q.labels.lower_le k (Q.currentLabel ▸ hk)
  have hqpos : 0 < q.position.board.left.coordinates.length := by
    obtain ⟨as, has, _⟩ := follow_word_inputs_above_bound hpq false
    have hle : p.position.board.left.coordinates.length ≤
        q.position.board.left.coordinates.length := has.coordinates_prefix.length_le
    omega
  obtain ⟨hql, _hqorder, hqbefore, hqpen, hqno⟩ :=
    winning_aligned_reverse_endpoint hHN hH blue origin q ha hop hboard hmode hwin
      (hfrom.trans (pathH hpq)) hall hqr hqpos hqsep hbefore hpen hno
  refine ⟨q, hpq, hqn, hql, hqbefore, hqpen, hqno, hqr, hroot, hbody, hno, hqsep,
    Q, hQs.trans hPs, ?_, ?_, ?_, ?_, hQlast⟩
  · simpa only [hQt] using hPpath
  · simpa only [hQt, hQs] using hPupper
  · simpa only [hQt, hQs] using hPfirst
  · simpa only [hQt, hQs] using hPother

theorem aligned_critical_prepared {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin p : Concrete.Hist N)
    (R : AlignedRootPlan N H blue b σ p.position.board.right)
    {a : ℕ} (ha : 0 < a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hpos : 0 < p.position.board.left.coordinates.length)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ q.position.board.left.relaxed = true ∧
      q.position.board.left.bodyLabels.length < q.position.board.left.lastSelectedBody ∧
      (∀ k ∈ q.position.board.left.rootLabel,
        k < q.position.board.left.lastSelectedBody → k ≤ q.position.board.left.bodyLabels.length) ∧
      q.position.board.left.NoLeafPending ∧ q.position.board.right.relaxed = true ∧
      q.position.board.right.rootLabel = R.labels.lower ∧
      q.position.board.right.bodyLabels.length = R.labels.shared ∧
      q.position.board.right.NoLeafPending ∧
      (∀ y ∈ q.position.board.left.coordinates,
        y ≤ q.position.board.right.coordinates.getLastD 0) ∧
      ∃ P : PreparedLeaf N H blue b σ q.position.board.right,
        P.side = R.side ∧
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) R.target P.target ∧
        (P.target.position.board.get P.side).rootLabel = R.labels.upper ∧
        (P.target.position.board.get P.side).NoRootPassed ∧
        P.target.position.board.get (!P.side) = R.target.position.board.get (!R.side) ∧
        q.position.board.right.leafIndex = P.labels.pivot :=
  aligned_critical_prepared_on_subset hHN hH (Set.Subset.refl H) hH blue origin p R ha hop
    hboard hmode hwin hfrom hpos hall

#print axioms aligned_critical_prepared_on_subset
#print axioms aligned_critical_prepared

end Erdos591.Positive.Game.Payoff
