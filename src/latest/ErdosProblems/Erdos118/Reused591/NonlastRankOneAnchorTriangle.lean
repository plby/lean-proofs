import ErdosProblems.Erdos118.Reused591.NonlastAnchorEndpoint
import ErdosProblems.Erdos118.Reused591.NextLeafAnchorTriangle

namespace Erdos118.Reused591

/-!
# The actual rank-one marker pair through the complete strict triangle

Choose the prescribed T anchor rank from the proved current U
remainder. The whole U prefix, including its earlier bridge segment,
is submitted as the lower next-leaf reply with its original bound.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem nonlast_rank_one_anchor_triangle {N H0 H J HU : Set ℕ}
    (hH0N : H0 ⊆ N) (hHH0 : H ⊆ H0) (hJH : J ⊆ H) (hJ : J.Infinite)
    (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin checkpoint p oldT oldU : Concrete.Hist N) {a R D BU e g j : ℕ}
    (U : SeparatedRootLabels HU BU e g j) (ha : 2 ≤ a) (hg : 2 ≤ g) (hD : 0 < D)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H0 b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin checkpoint)
    (hCheckpointP : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) checkpoint p)
    (hCheckpoint : CriticalCheckpoint checkpoint)
    (hwinOldT : (exactGame N blue).ArchitectWins H b σ oldT)
    (hwinOldU : (exactGame N blue).ArchitectWins H b σ oldU)
    (hModeSU : oldU.position.mode = some true)
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
    (hJfresh : ∀ x ∈ J, max oldU.position.bound (b oldU) < x)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hpU : oldU.position.pending = some ⟨true, .advance 0⟩)
    (hOldUrel : oldU.position.board.right.relaxed = true)
    (hUpTo : LabeledWord.UpToLeaf (p.position.board.right.currentLabel.sup id)
      oldU.position.board.right)
    (hStrict : oldU.position.board.right.leafIndex < p.position.board.right.currentLabel.sup id)
    (hNext : ∀ x ∈ oldU.position.board.right.currentLabel,
      oldU.position.board.right.leafIndex < x → p.position.board.right.currentLabel.sup id ≤ x)
    {anchor : LabeledWord} {front : List (Finset ℕ × ℕ)}
    (hUshape : LabeledWord.SameStructure oldU.position.board.right anchor)
    (hfront : LabeledWord.LegalRun anchor front p.position.board.right)
    (hpool : ∀ atom ∈ front, atom.2 ∈ H ∧ max oldU.position.bound (b oldU) < atom.2)
    (hcount : p.position.board.right.bodyLabels.length = anchor.bodyLabels.length)
    (hUroot : p.position.board.right.rootLabel = U.upper)
    (hUbody : p.position.board.right.bodyLabels.length = U.first)
    (hLowerRoot : oldU.position.board.right.rootLabel = U.lower)
    (hSrel : oldU.position.board.left.relaxed = true)
    (hS : LabeledWord.SameStructure oldT.position.board.left oldU.position.board.left)
    {gamma : ℕ} (hSUp : LabeledWord.UpToLeaf gamma oldT.position.board.left)
    (hSstrict : oldT.position.board.left.leafIndex < gamma)
    (hSnext : ∀ i ∈ oldT.position.board.left.currentLabel,
      oldT.position.board.left.leafIndex < i → gamma ≤ i)
    (hSroot : ∀ i ∈ oldU.position.board.left.rootLabel,
      i ≤ oldU.position.board.left.bodyLabels.length)
    (hgamma : gamma ∈ oldU.position.board.left.currentLabel)
    (hSlast : ∀ i ∈ oldU.position.board.left.currentLabel, i ≤ gamma) :
    ¬ blue.CliqueFree 3 := by
  have hHN := hHH0.trans hH0N
  let rem := checkpoint.position.board.right.currentLabel.card -
    (checkpoint.position.board.right.currentLabel.filter
      (fun x => x ≤ checkpoint.position.board.right.leafIndex)).card
  let B := max (max p.position.bound (b p)) (max oldT.position.bound (b oldT))
  obtain ⟨T⟩ := RankedFirstLeafLabels.exists_of_infinite hJ B R D (rem + 1)
    (by omega) (by dsimp only [rem]; omega) hD
  obtain ⟨q, hpq, _hqn, _hql, hqr, hqno, _hqTroot, _hqTlabels, hqLast,
      hqCurrent, hqUroot, hqUlabels, _hqUmarker, hqUindex, hqRank, _hqBefore, _hqNext,
      hqSep, PT, hPTtarget, hPTside, _hPTstem, hPTsource, hPTpivot, hPTupper,
      bs, hrunU, hpoolU⟩ := nonlast_anchor_endpoint hH0N (hJH.trans hHH0) hJ blue
        origin checkpoint p oldT T
        ha hop hboard hmode hwin hfrom hCheckpointP hCheckpoint
        (hwinOldT.mono (exactGame N blue) hJH (fun _ => le_rfl)) hp hpT hm hmT hTshape
        (le_max_left _ _) (le_max_right _ _) hroot hother hUlt rfl hJfresh hall
  have hfull := hfront.append hrunU
  have hFullPool : ∀ atom ∈ front ++ bs,
      atom.2 ∈ H ∧ max oldU.position.bound (b oldU) < atom.2 := by
    intro atom ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hpool atom ha
    · exact ⟨hJH (hpoolU atom ha).1, (hpoolU atom ha).2⟩
  have hFullCount : q.position.board.right.bodyLabels.length = anchor.bodyLabels.length := by
    rw [hqUlabels]
    exact hcount
  have hstartOld := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant oldU).2.1 true).1 hOldUrel
  have hstart : anchor.parser ≠ .start := fun hs => hstartOld (hUshape.parser_eq.trans hs)
  have hFullMarker := hfull.bodyMarker_of_body_length hstart hFullCount
  have hNextRank : (q.position.board.left.currentLabel.filter
      (fun x => x ≤ PT.labels.pivot)).card =
      (q.position.board.left.currentLabel.filter
        (fun x => x ≤ q.position.board.left.leafIndex)).card + 1 := by
    rw [hqRank, hqCurrent, hPTpivot]
    exact T.pivot_rank
  have hwinP := (hwin.of_reachable (exactGame N blue) (hfrom.trans hCheckpointP)).mono
    (exactGame N blue) (hJH.trans hHH0) (fun _ => le_rfl)
  have hmodeP := follow_mode_some (hfrom.trans hCheckpointP) hmode
  exact next_leaf_anchor_triangle hHN hJH hJ blue q oldU T U PT
    (hwinP.of_reachable (exactGame N blue) hpq) hwinOldU
    (follow_mode_some hpq hmodeP) hModeSU hPTside hPTsource hPTpivot hPTupper hpU hOldUrel
    hUpTo hStrict hNext hUshape hfull hFullPool hFullCount hFullMarker hqUindex hqr hqno
    (hqUroot.trans hUroot) (by simpa only [hqUlabels] using hUbody) hLowerRoot hg hqSep
    hNextRank hqLast hSrel (by simpa only [hPTtarget] using hS)
    (by simpa only [hPTtarget] using hSUp) (by simpa only [hPTtarget] using hSstrict)
    (by simpa only [hPTtarget] using hSnext) hSroot hgamma hSlast

#print axioms nonlast_rank_one_anchor_triangle

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
