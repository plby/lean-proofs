import ErdosProblems.Erdos591.LocalCriticalEndpoint
import ErdosProblems.Erdos591.PrepareSelectionHistory
import ErdosProblems.Erdos591.PreparedSelectionReach

/-!
# Reach a critical checkpoint with any proved prescribed-rank leaf pattern

Both actual body requests and both localized ranks are fixed before
the label is supplied. The full lower label is unchanged; its selected
pivot is the upper label's minimum. No upper body-size lower bound
beyond what the supplied finite label itself proves is required.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem critical_selection_prepared {N H K : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin lower upper : Concrete.Hist N) (side : Bool)
    {a B d c s : ℕ} (ha : 2 ≤ a)
    (D : Finset ℕ) (V : LastFirstLabels K B 1 c)
    (hD : D.card = d) (hPivot : V.pivot ∈ D)
    (hRank : (D.filter (fun x => x ≤ V.pivot)).card = s)
    (hFresh : ∀ x ∈ D, x ∈ K ∧ B < x ∧ x < V.marker)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin lower)
    (hupperFrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upper)
    (hpos : 0 < lower.position.board.left.coordinates.length)
    (hlower : lower.position.pending = some ⟨true, .advance d⟩)
    (hupper : upper.position.pending = some ⟨side, .advance c⟩)
    (hml : lower.position.board.right.markerEvent = true)
    (hmu : (upper.position.board.get side).markerEvent = true)
    (hsame : LabeledWord.SameStructure lower.position.board.right (upper.position.board.get side))
    (hBl : max lower.position.bound (b lower) ≤ B)
    (hBu : max upper.position.bound (b upper) ≤ B)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) lower z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card =
          (lower.position.board.right.rootLabel.filter
            (fun i => i ≤ lower.position.board.right.bodyLabels.length + 1)).card ∧
        z.position.board.right.criticalLeafRank z.position.board.left.lastSelectedLabel.card = s) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) lower q ∧
      q.position.pending = none ∧ CriticalCheckpoint q ∧
      q.position.board.right.rootLabel = lower.position.board.right.rootLabel ∧
      q.position.board.right.bodyLabels.length = lower.position.board.right.bodyLabels.length + 1 ∧
      q.position.board.right.currentLabel = D ∧ q.position.board.right.leafIndex = V.pivot ∧
      ∃ P : PreparedSelection N K blue b σ q.position.board.right,
        P.target = upper ∧ P.side = side ∧ HEq P.labels V ∧
        P.labels.pivot = V.pivot ∧ P.labels.upper = V.upper := by
  have pathH {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hKH (fun _ => le_rfl) hs) _ _ hpath
  have hwinUpper := (hwin.of_reachable (exactGame N blue) hupperFrom).mono
    (exactGame N blue) hKH (fun _ => le_rfl)
  obtain ⟨v, hlv, hvn, _hvr, _hvo, P, hPt, hPs, hPL, hPstem, hPD, hPpivot, hPupper⟩ :=
    prepare_selection (hKH.trans hHN) hK blue hwinUpper true side D hD V hPivot hFresh
      hlower hupper hml hmu hsame hBl hBu
  have hwinV := ((hwin.of_reachable (exactGame N blue) hfrom).mono
    (exactGame N blue) hKH (fun _ => le_rfl)).of_reachable (exactGame N blue) (.single hlv)
  have hvsep := (FiniteResponseGame.FollowStep.next (exactGame N blue) hlv).reply_separation hlower
  obtain ⟨q, hvq, hqn, hqr, hqsep, Q, hQt, hQs, hQL, hQstem, hQi, hQD, hQpivot, hQupper⟩ :=
    P.reach_target (hKH.trans hHN) hK blue true hwinV hvn hvsep
  have hlq := (Relation.ReflTransGen.single hlv).trans hvq
  have hroot : q.position.board.right.rootLabel = lower.position.board.right.rootLabel :=
    Q.rootLabel.trans (congrArg LabeledWord.rootLabel (hQstem.trans hPstem))
  have hbody : q.position.board.right.bodyLabels.length =
      lower.position.board.right.bodyLabels.length + 1 := by
    change (q.position.board.get true).bodyLabels.length = _
    rw [Q.body_length, hQstem, hPstem]
    rfl
  have hlabel : q.position.board.right.currentLabel = D := Q.currentLabel.trans (hQD.trans hPD)
  have hpivot : Q.labels.pivot = V.pivot := hQpivot.trans hPpivot
  have hindex : q.position.board.right.leafIndex = V.pivot := hQi.trans hpivot
  have hqpos : 0 < q.position.board.left.coordinates.length := by
    obtain ⟨as, has, _⟩ := follow_word_inputs_above_bound hlq false
    have hle : lower.position.board.left.coordinates.length ≤
        q.position.board.left.coordinates.length := has.coordinates_prefix.length_le
    omega
  have hcheckpoint : CriticalCheckpoint q := by
    apply winning_strict_reverse_endpoint_on_subset hHN hKH hK blue origin q ha hop hboard hmode
      hwin (hfrom.trans (pathH hlq)) hall ?_ hqr hqpos hqsep
    intro z w hqz hz
    have hvalues := hfixed z w (hlq.trans hqz) hz
    refine ⟨hvalues.1.trans ?_, hvalues.2.trans ?_⟩
    · rw [hroot, hbody]
    · rw [hlabel, hindex]
      exact hRank.symm
  exact ⟨q, hlq, hqn, hcheckpoint, hroot, hbody, hlabel, hindex, Q, hQt.trans hPt,
    hQs.trans hPs, hQL.trans hPL, hpivot, hQupper.trans hPupper⟩

#print axioms critical_selection_prepared

end Erdos591.Positive.Game.Payoff
