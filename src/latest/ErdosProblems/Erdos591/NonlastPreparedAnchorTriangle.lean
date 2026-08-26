import ErdosProblems.Erdos591.NonlastAnchorEndpoint
import ErdosProblems.Erdos591.StrictAnchorHandoffTriangle

/-!
# The nonlast marker pair and saved U anchor yield the strict triangle

The current U remainder determines the prescribed T anchor rank.
At the checked endpoint, U reaches its saved last selection while T
is immediately before its saved first lower leaf. No pool is changed
after the saved U response was constructed.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem nonlast_prepared_anchor_triangle {N H0 H HU : Set ℕ}
    (hH0N : H0 ⊆ N) (hHH0 : H ⊆ H0) (hH : H.Infinite)
    (hpositive : ∀ x ∈ H, 0 < x) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin checkpoint p oldT : Concrete.Hist N) {a R D BU e g j k : ℕ}
    (U : SplicedRootLabels HU BU e g j k)
    (PU : PreparedSelection N H blue b σ p.position.board.right)
    (ha : 2 ≤ a) (hD : 0 < D) (hAfterU : k < g)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H0 b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin checkpoint)
    (hCheckpointP : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) checkpoint p)
    (hCheckpoint : CriticalCheckpoint checkpoint)
    (hwinOldT : (exactGame N blue).ArchitectWins H b σ oldT)
    (hModeSU : PU.target.position.mode = some true) (hPUside : PU.side = true)
    (hp : p.position.pending = some ⟨false, .advance R⟩)
    (hpT : oldT.position.pending = some ⟨true, .advance D⟩)
    (hm : p.position.board.left.markerEvent = true)
    (hmT : oldT.position.board.right.markerEvent = true)
    (hTshape : LabeledWord.SameStructure p.position.board.left oldT.position.board.right)
    (hroot : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1)
    (hother : p.position.board.right = checkpoint.position.board.right)
    (hUlt : checkpoint.position.board.right.leafIndex <
      checkpoint.position.board.right.currentLabel.sup id)
    (hbound : checkpoint.position.board.right.currentLabel.card -
      (checkpoint.position.board.right.currentLabel.filter
        (fun x => x ≤ checkpoint.position.board.right.leafIndex)).card + 2 ≤ R)
    (hPUpivot : PU.labels.pivot = p.position.board.right.currentLabel.sup id)
    (hUroot : p.position.board.right.rootLabel = U.upper)
    (hUbody : p.position.board.right.bodyLabels.length = U.anchor)
    (hLowerRoot : PU.target.position.board.right.rootLabel = U.lower)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hSrel : PU.target.position.board.left.relaxed = true)
    (hS : LabeledWord.SameStructure oldT.position.board.left PU.target.position.board.left)
    {gamma : ℕ} (hSUp : LabeledWord.UpToLeaf gamma oldT.position.board.left)
    (hSstrict : oldT.position.board.left.leafIndex < gamma)
    (hSnext : ∀ i ∈ oldT.position.board.left.currentLabel,
      oldT.position.board.left.leafIndex < i → gamma ≤ i)
    (hSroot : ∀ i ∈ PU.target.position.board.left.rootLabel,
      i ≤ PU.target.position.board.left.bodyLabels.length)
    (hgamma : gamma ∈ PU.target.position.board.left.currentLabel)
    (hSlast : ∀ i ∈ PU.target.position.board.left.currentLabel, i ≤ gamma) :
    ¬ blue.CliqueFree 3 := by
  have hHN := hHH0.trans hH0N
  let rem := checkpoint.position.board.right.currentLabel.card -
    (checkpoint.position.board.right.currentLabel.filter
      (fun x => x ≤ checkpoint.position.board.right.leafIndex)).card
  let B := max (max p.position.bound (b p)) (max oldT.position.bound (b oldT))
  obtain ⟨T⟩ := RankedFirstLeafLabels.exists_of_infinite hH B R D (rem + 1)
    (by omega) (by dsimp only [rem]; omega) hD
  obtain ⟨q, hpq, _hqn, _hql, hqr, hqno, _hqTroot, _hqTlabels, hqLast,
      hqCurrent, hqUroot, hqUlabels, _hqUmarker, hqUindex, hqRank, _hqBefore, _hqNext,
      hqSep, PT, hPTtarget, hPTside, _hPTstem, hPTsource, hPTpivot, hPTupper,
      _bs, _hrunU, _hpoolU⟩ := nonlast_anchor_endpoint hH0N hHH0 hH blue
        origin checkpoint p oldT T ha hop hboard hmode hwin hfrom hCheckpointP hCheckpoint
        hwinOldT hp hpT hm hmT hTshape (le_max_left _ _) (le_max_right _ _)
        hroot hother hUlt rfl hpositive hall
  obtain ⟨as, has, hpool⟩ := follow_word_inputs_above_bound hpq true
  have hindex : q.position.board.right.leafIndex = PU.labels.pivot :=
    hqUindex.trans hPUpivot.symm
  have hup : LabeledWord.UpToLeaf PU.labels.pivot q.position.board.right :=
    ⟨(of_decide_eq_true hqr).2.1, by
      rw [← hindex]
      exact (of_decide_eq_true hqr).2.2, hindex.le⟩
  have hfresh : ∀ atom ∈ as, atom.2 ∈ H ∧ PU.budget < atom.2 := by
    intro atom ha
    have hPUbound := PreparedSelection.budget_lt_bound (p := p) (s := true) PU
    exact ⟨(hpool atom ha).1, hPUbound.trans (hpool atom ha).2⟩
  let QU := PU.move has hqUlabels hfresh hup
  have hNextRank : (q.position.board.left.currentLabel.filter
      (fun x => x ≤ PT.labels.pivot)).card =
      (q.position.board.left.currentLabel.filter
        (fun x => x ≤ q.position.board.left.leafIndex)).card + 1 := by
    rw [hqRank, hqCurrent, hPTpivot]
    exact T.pivot_rank
  have hwinP := (hwin.of_reachable (exactGame N blue) (hfrom.trans hCheckpointP)).mono
    (exactGame N blue) hHH0 (fun _ => le_rfl)
  have hmodeP := follow_mode_some (hfrom.trans hCheckpointP) hmode
  exact strict_anchor_handoff_triangle hHN hH blue q T U PT QU
    (hwinP.of_reachable (exactGame N blue) hpq) (follow_mode_some hpq hmodeP)
    hModeSU hPTside hPUside hPTsource hPTpivot hPTupper hqr hindex hqno
    (hqUroot.trans hUroot) (by simpa only [hqUlabels] using hUbody)
    hLowerRoot hAfterU hqSep hNextRank hqLast hSrel
    (by
      change LabeledWord.SameStructure PT.target.position.board.left PU.target.position.board.left
      simpa only [hPTtarget] using hS) (by simpa only [hPTtarget] using hSUp)
    (by simpa only [hPTtarget] using hSstrict) (by simpa only [hPTtarget] using hSnext)
    hSroot hgamma hSlast

#print axioms nonlast_prepared_anchor_triangle

end Erdos591.Positive.Game.Payoff
