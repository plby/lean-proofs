import ErdosProblems.Erdos591.LocalCriticalUniformization
import ErdosProblems.Erdos591.LocalCriticalEndpoint
import ErdosProblems.Erdos591.CriticalMarkerRequests
import ErdosProblems.Erdos591.CriticalLeafLabels
import ErdosProblems.Erdos591.PrepareSelectionHistory
import ErdosProblems.Erdos591.PreparedSelectionReach
import ErdosProblems.Erdos591.FirstRequestRecovery

/-!
# Actual first-upper/nonlast-critical-lower preparation

The root rank is fixed before its response. At its actual shared body
request, localize the leaf rank on a smaller future pool, choose the
full labels, reach that selection, and recover the first word's
exhausted penultimate body. The upper first-leaf reply remains saved.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem strict_nonlast_critical_prepared {N H K : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p : Concrete.Hist N)
    (R : CriticalRootPlan N K blue b σ p.position.board.right)
    (hRt : R.target = origin) (hRs : R.side = false)
    {a : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hpos : 0 < p.position.board.left.coordinates.length)
    (hfirst : ∀ q v d, (exactGame N blue).FollowStep σ H b origin q →
      (exactGame N blue).FollowStep σ H b q v →
      v.position.pending = some ⟨false, .advance d⟩ → 2 ≤ d)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card =
          R.criticalRank) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧ ∃ B d c s, ∃ D : CriticalLeafLabels L B d c s,
      2 ≤ c ∧ 0 < s ∧ s < d ∧ ∃ q,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p q ∧
        q.position.pending = none ∧ CriticalCheckpoint q ∧
        q.position.board.right.rootLabel = R.labels.lower ∧
        q.position.board.right.bodyLabels.length = R.labels.shared ∧
        q.position.board.right.currentLabel = D.lower ∧
        q.position.board.right.leafIndex = D.upperView.pivot ∧
        ∃ P : PreparedSelection N L blue b σ q.position.board.right,
          P.side = false ∧ HEq P.labels D.upperView ∧
          P.labels.pivot = D.upperView.pivot ∧ P.labels.upper = D.upperView.upper ∧
          Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin P.target ∧
          P.target.position.board.left.rootLabel = R.labels.upper ∧
          P.target.position.board.left.NoRootPassed ∧
          P.target.position.board.right = LabeledWord.initial := by
  have pathH {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hKH (fun _ => le_rfl) hs) _ _ hpath
  have hwinP := (hwin.of_reachable (exactGame N blue) hfrom).mono
    (exactGame N blue) hKH (fun _ => le_rfl)
  obtain ⟨m, upper, d, c, hpm, hupper, hmp, hup, hd, hc, hm, hum, hsame,
      hmroot, hmi, hmrank, huroot, huno, huother⟩ :=
    R.request_shared true (hKH.trans hHN) hK hwinP
  have htoM := hfrom.trans (pathH hpm)
  have htoUpper : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upper := by
    simpa only [hRt] using pathH hupper
  have hup' : upper.position.pending = some ⟨false, .advance c⟩ := by simpa [hRs] using hup
  have hum' : upper.position.board.left.markerEvent = true := by simpa [hRs, Board.get] using hum
  have huno' : upper.position.board.left.NoRootPassed := by simpa [hRs, Board.get] using huno
  have hcLarge : 2 ≤ c := first_body_request_large_of_reachable hHN (hK.mono hKH) blue
    origin upper hwin (by omega) hop (by simp [hboard, Board.initial]) hfirst htoUpper
      hup' hum' huno'
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
    have hne : s ≠ d := fun heq => by simpa only [hfalse, Bool.false_eq_true] using hiff.mpr heq
    omega
  let B := max (max m.position.bound (b m)) (max upper.position.bound (b upper))
  obtain ⟨D⟩ := CriticalLeafLabels.exists_of_infinite hL B d c s hs hslt hcLarge
  have hwinUpper := (hwin.of_reachable (exactGame N blue) htoUpper).mono
    (exactGame N blue) (hLK.trans hKH) (fun _ => le_rfl)
  obtain ⟨v, hmv, hvn, hvr, _hvo, P, hPt, hPs, hPL, hPstem, hPD, hPpivot, hPupper⟩ :=
    prepare_selection hLN hL blue hwinUpper true false D.lower D.lower_card D.upperView
      D.pivot_lower D.lower_fresh hmp hup' hm hum'
        (by simpa only [hRs, Board.get] using hsame) (le_max_left _ _) (le_max_right _ _)
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
  have hlabel : q.position.board.right.currentLabel = D.lower :=
    Q.currentLabel.trans (hQD.trans hPD)
  have hpivot : Q.labels.pivot = D.upperView.pivot := hQpivot.trans hPpivot
  have hindex : q.position.board.right.leafIndex = D.upperView.pivot := hQi.trans hpivot
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
  refine ⟨L, hLK, hL, B, d, c, s, D, hcLarge, hs, hslt, q, hpq, hqn, hcheckpoint,
    hroot, hbody, hlabel, hindex, Q, hQs.trans hPs, hQL.trans hPL, hpivot,
      hQupper.trans hPupper, ?_, ?_, ?_, ?_⟩
  · simpa only [hQt, hPt] using htoUpper
  · simpa only [hQt, hPt, hRs, Board.get] using huroot
  · simpa only [hQt, hPt] using huno'
  · simpa [hQt, hPt, hRs, hRt, hboard, Board.initial, Board.get] using huother

#print axioms strict_nonlast_critical_prepared

end Erdos591.Positive.Game.Payoff
