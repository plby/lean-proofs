import ErdosProblems.Erdos118.Reused591.LocalCriticalUniformization
import ErdosProblems.Erdos118.Reused591.LocalCriticalEndpoint
import ErdosProblems.Erdos118.Reused591.FirstRootMarkerRequests
import ErdosProblems.Erdos118.Reused591.RankedFirstLeafLabels
import ErdosProblems.Erdos118.Reused591.PrepareSelectionHistory
import ErdosProblems.Erdos118.Reused591.PreparedSelectionReach

namespace Erdos118.Reused591

/-!
# Nonlast-critical-lower preparation at an arbitrary saved upper root

The saved upper root may be on either side of a later actual history.
The lower critical root rank is fixed before its response. At its actual shared body
request, localize the leaf rank on a smaller future pool, choose the
full labels, reach that selection, and recover the first word's
exhausted penultimate body. The upper first-leaf reply remains saved,
including when its label is a singleton.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem strict_nonlast_critical_prepared_at_target {N H K : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p : Concrete.Hist N)
    (R : FirstRootPlan N K blue b σ p.position.board.right)
    (hRfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin R.target)
    {a : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hpos : 0 < p.position.board.left.coordinates.length)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card =
          R.criticalRank) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧ ∃ B d c s, ∃ D : RankedFirstLeafLabels L B d c s,
      0 < c ∧ 0 < s ∧ s < d ∧ ∃ q,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p q ∧
        q.position.pending = none ∧ CriticalCheckpoint q ∧
        q.position.board.right.rootLabel = R.labels.lower ∧
        q.position.board.right.bodyLabels.length = R.labels.shared ∧
        q.position.board.right.currentLabel = D.source ∧
        q.position.board.right.leafIndex = D.targetView.pivot ∧
        ∃ P : PreparedSelection N L blue b σ q.position.board.right,
          P.side = R.side ∧ HEq P.labels D.targetView ∧
          P.labels.pivot = D.targetView.pivot ∧ P.labels.upper = D.targetView.upper ∧
          Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin P.target ∧
          (P.target.position.board.get R.side).rootLabel = R.labels.upper ∧
          (P.target.position.board.get R.side).NoRootPassed ∧
          P.target.position.board.get (!R.side) = R.target.position.board.get (!R.side) ∧
          Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) R.target P.target := by
  have pathH {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hKH (fun _ => le_rfl) hs) _ _ hpath
  have hwinP := (hwin.of_reachable (exactGame N blue) hfrom).mono
    (exactGame N blue) hKH (fun _ => le_rfl)
  obtain ⟨m, upper, d, c, hpm, hupper, hmp, hup, _hd, hc, hm, hum, hsame,
      hmroot, hmi, hmrank, huroot, huno, huother⟩ :=
    R.request_shared true (hKH.trans hHN) hK hwinP
  have htoM := hfrom.trans (pathH hpm)
  have htoUpper := hRfrom.trans (pathH hupper)
  obtain ⟨L, hLK, hL, s, hs, hsd, hleaf⟩ := strict_critical_leaf_local_of_rank
    hHN hKH hK blue origin m ha hop hboard hmode hwin htoM hmp hm hall hmrank
      (fun z w hpath hz => hfixed z w (hpm.trans hpath) hz)
  have pathK {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hLK (fun _ => le_rfl) hs) _ _ hpath
  have hLN := (hLK.trans hKH).trans hHN
  obtain ⟨z, w, hmz, hz⟩ := (exactGame N blue).terminal_reachable_of_infinite hLN hL b σ m
  have hslt : s < d := by
    have hfalse := hlast z w (htoM.trans (pathH (pathK hmz))) hz
    have hiff := (hleaf z w hmz hz).2
    have hne : s ≠ d := fun heq => by
      simpa only [hfalse, Bool.false_eq_true] using hiff.mpr heq
    omega
  let B := max (max m.position.bound (b m)) (max upper.position.bound (b upper))
  obtain ⟨D⟩ := RankedFirstLeafLabels.exists_of_infinite hL B d c s hs hslt hc
  have hwinUpper := (hwin.of_reachable (exactGame N blue) htoUpper).mono
    (exactGame N blue) (hLK.trans hKH) (fun _ => le_rfl)
  obtain ⟨v, hmv, hvn, hvr, _hvo, P, hPt, hPs, hPL, hPstem, hPD, hPpivot, hPupper⟩ :=
    prepare_selection hLN hL blue hwinUpper true R.side D.source D.source_card D.targetView
      D.pivot_source D.source_fresh hmp hup hm hum hsame (le_max_left _ _) (le_max_right _ _)
  have hwinV := ((hwin.of_reachable (exactGame N blue) htoM).mono
    (exactGame N blue) (hLK.trans hKH) (fun _ => le_rfl)).of_reachable
      (exactGame N blue) (.single hmv)
  have hvsep := (FiniteResponseGame.FollowStep.next (exactGame N blue) hmv).reply_separation hmp
  obtain ⟨q, hvq, hqn, hqr, hqsep, Q, hQt, hQs, hQL, hQstem, hQi, hQD, hQpivot, hQupper⟩ :=
    P.reach_target hLN hL blue true hwinV hvn hvsep
  have hmq := (Relation.ReflTransGen.single hmv).trans hvq
  have hpq := hpm.trans (pathK hmq)
  have hroot : q.position.board.right.rootLabel = R.labels.lower := by
    exact Q.rootLabel.trans ((congrArg LabeledWord.rootLabel (hQstem.trans hPstem)).trans hmroot)
  have hbody : q.position.board.right.bodyLabels.length = R.labels.shared := by
    change (q.position.board.get true).bodyLabels.length = _
    rw [Q.body_length, hQstem, hPstem]
    exact hmi
  have hlabel : q.position.board.right.currentLabel = D.source :=
    Q.currentLabel.trans (hQD.trans hPD)
  have hpivot : Q.labels.pivot = D.targetView.pivot := hQpivot.trans hPpivot
  have hindex : q.position.board.right.leafIndex = D.targetView.pivot := hQi.trans hpivot
  have hqpos : 0 < q.position.board.left.coordinates.length := by
    obtain ⟨as, has, _⟩ := follow_word_inputs_above_bound hpq false
    have hle : p.position.board.left.coordinates.length ≤
        q.position.board.left.coordinates.length := has.coordinates_prefix.length_le
    omega
  have hcheckpoint : CriticalCheckpoint q := by
    apply winning_strict_reverse_endpoint_on_subset hHN (hLK.trans hKH) hL blue origin q
      ha hop hboard hmode hwin (hfrom.trans (pathH hpq)) hall ?_ hqr hqpos hqsep
    intro z w hqz hz
    have hB := hfixed z w (hpq.trans (pathK hqz)) hz
    have hS := (hleaf z w (hmq.trans hqz) hz).1
    refine ⟨hB.trans ?_, hS.trans ?_⟩
    · rw [hroot, hbody]
      exact R.labels.shared_rank.symm
    · rw [hlabel, hindex]
      exact D.pivot_rank.symm
  refine ⟨L, hLK, hL, B, d, c, s, D, hc, hs, hslt, q, hpq, hqn, hcheckpoint,
    hroot, hbody, hlabel, hindex, Q, hQs.trans hPs, hQL.trans hPL, hpivot,
      hQupper.trans hPupper, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hQt, hPt] using htoUpper
  · simpa only [hQt, hPt] using huroot
  · simpa only [hQt, hPt] using huno
  · simpa only [hQt, hPt] using huother
  · simpa only [hQt, hPt] using hupper

#print axioms strict_nonlast_critical_prepared_at_target

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
