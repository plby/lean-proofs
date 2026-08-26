import ErdosProblems.Erdos591.StrictNonlastRankOneMarkerBridge
import ErdosProblems.Erdos591.NonlastRankOneAnchorTriangle

/-!
# The full rank-one nonlast upper bridge through the strict triangle

The lower U next leaf is the upper first-body maximum. The marker
bridge retains that full label and the exact earlier critical
checkpoint. Its actual size estimate supplies the prescribed T
anchor, after which the checked next-leaf finishing argument applies.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem strict_nonlast_rank_one_bridge_triangle {N H0 H HT HU HE : Set ℕ}
    (hH0N : H0 ⊆ N) (hHH0 : H ⊆ H0) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin st su tu : Concrete.Hist N) {a BT eT dT jT BU e g j BE n c s : ℕ}
    (T : CriticalRootLabels HT BT eT dT jT) (U : SeparatedRootLabels HU BU e g j)
    (E : CriticalRootLabels HE BE n c s) (ha : 2 ≤ a) (hg : 2 ≤ g)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwinOrigin : (exactGame N blue).ArchitectWins H0 b σ origin)
    (hfromTU : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin tu)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    (hModeSU : su.position.mode = some true)
    (hpST : st.position.pending = some ⟨true, .advance 0⟩)
    (hpSU : su.position.pending = some ⟨true, .advance 0⟩)
    (hSTrel : st.position.board.right.relaxed = true)
    (hSTno : st.position.board.right.NoLeafPending)
    (hSTroot : st.position.board.right.rootLabel = T.lower)
    (hSTbody : st.position.board.right.bodyLabels.length = T.shared)
    (hT : LabeledWord.SameStructure st.position.board.right tu.position.board.left)
    (hTUrootT : tu.position.board.left.rootLabel = T.upper)
    (hTUrelT : tu.position.board.left.relaxed = true)
    (hTUrelU : tu.position.board.right.relaxed = true)
    (hTUrootU : tu.position.board.right.rootLabel = U.upper)
    (hTUbodyU : tu.position.board.right.bodyLabels.length = U.first)
    (hTUlabelU : tu.position.board.right.currentLabel = E.upper)
    (hTUsep : ∀ x ∈ tu.position.board.right.coordinates,
      x ≤ tu.position.board.left.coordinates.getLastD 0)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) tu z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = 1)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) tu z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false)
    (hSUrel : su.position.board.right.relaxed = true)
    (hSUroot : su.position.board.right.rootLabel = U.lower)
    (hSUlabel : su.position.board.right.currentLabel = E.lower)
    (hSUindex : su.position.board.right.leafIndex = E.shared)
    (hU : LabeledWord.SameStructure su.position.board.right tu.position.board.right)
    (hSrel : su.position.board.left.relaxed = true)
    (hS : LabeledWord.SameStructure st.position.board.left su.position.board.left)
    {gamma : ℕ} (hSUp : LabeledWord.UpToLeaf gamma st.position.board.left)
    (hSstrict : st.position.board.left.leafIndex < gamma)
    (hSnext : ∀ i ∈ st.position.board.left.currentLabel,
      st.position.board.left.leafIndex < i → gamma ≤ i)
    (hSroot : ∀ i ∈ su.position.board.left.rootLabel,
      i ≤ su.position.board.left.bodyLabels.length)
    (hgamma : gamma ∈ su.position.board.left.currentLabel)
    (hSlast : ∀ i ∈ su.position.board.left.currentLabel, i ≤ gamma) :
    ¬ blue.CliqueFree 3 := by
  have hTbefore : LabeledWord.BeforeBody T.next st.position.board.right :=
    ⟨hSTroot ▸ T.next_lower, by rw [hSTbody]; exact T.shared_lt_next⟩
  have hTnext : ∀ i ∈ st.position.board.right.rootLabel,
      st.position.board.right.bodyLabels.length < i → T.next ≤ i := by
    intro i hi hlt
    exact (T.lower_gap i (hSTroot ▸ hi)).resolve_left
      (by simpa only [hSTbody] using not_le_of_gt hlt)
  have hTlast : tu.position.board.left.lastSelectedBody = T.next := by
    simp only [LabeledWord.lastSelectedBody, hTUrootT]
    exact le_antisymm (Finset.sup_le (fun i hi => (T.upper_bounds i hi).2))
      (Finset.le_sup (f := id) T.next_upper)
  let B := max (max st.position.bound (b st)) (max su.position.bound (b su))
  obtain ⟨J, hJH, hJ, hJfresh, oldT, upper, D, R, hSTpath, hTUpath, _hwinUpper,
      hpT, hpUpper, hD, _hR, hTshape, hmT, hmUpper, _hiT, _hiUpper,
      _hrootT, _hrootUpper, hSTother, _hUpperUrel, hUpperUroot, hUpperUlabels,
      hUpperUbody, hUpperUcurrent, hUpperUbefore, _hUpperUrank, hRootLast, _hremPos,
      hBound, checkpoint, hCheckpoint, hTUcheckpoint, hCheckpointUpper, hUpperUcheckpoint,
      frontU, hfrontU, hfrontPool⟩ :=
    strict_nonlast_rank_one_marker_bridge hH0N hHH0 hH blue origin st tu U ha hop hboard
      hmode hwinOrigin hfromTU hall hwinST hwinTU hpST hSTrel hSTno hTbefore hTnext hT
      hTlast hTUrelT hTUrelU hTUrootU hTUbodyU (follow_mode_some hfromTU hmode)
      hTUsep hfixed hlast B (le_max_left _ _)
  have pathH0 {v w : Concrete.Hist N}
      (h : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) (hJH.trans hHH0)
        (fun _ => le_rfl) hs) _ _ h
  have hUpperSup : upper.position.board.right.currentLabel.sup id = E.next := by
    rw [hUpperUcurrent, hTUlabelU]
    exact le_antisymm (Finset.sup_le fun i hi => (E.upper_bounds i hi).2)
      (Finset.le_sup (f := id) E.next_upper)
  have hUpTo : LabeledWord.UpToLeaf (upper.position.board.right.currentLabel.sup id)
      su.position.board.right := by
    rw [hUpperSup]
    exact ⟨(of_decide_eq_true hSUrel).2.1, hSUlabel ▸ E.next_lower,
      by simpa only [hSUindex] using E.shared_lt_next.le⟩
  have hStrict : su.position.board.right.leafIndex <
      upper.position.board.right.currentLabel.sup id := by
    rw [hSUindex, hUpperSup]
    exact E.shared_lt_next
  have hNext : ∀ x ∈ su.position.board.right.currentLabel,
      su.position.board.right.leafIndex < x →
        upper.position.board.right.currentLabel.sup id ≤ x := by
    intro x hx hlt
    rw [hUpperSup]
    exact E.next_is_next x (hSUlabel ▸ hx) (by simpa only [hSUindex] using hlt)
  have hUlt : checkpoint.position.board.right.leafIndex <
      checkpoint.position.board.right.currentLabel.sup id := by
    rw [← hUpperUcheckpoint, hUpperUcurrent]
    exact hUpperUbefore
  exact nonlast_rank_one_anchor_triangle hH0N hHH0 hJH hJ blue origin checkpoint upper oldT su U
    ha hg hD hop hboard hmode hwinOrigin (hfromTU.trans (pathH0 hTUcheckpoint))
    (pathH0 hCheckpointUpper) hCheckpoint (hwinST.of_reachable (exactGame N blue) hSTpath)
    hwinSU hModeSU hpUpper hpT hmUpper hmT hTshape.symm hRootLast hUpperUcheckpoint hUlt
    (by simpa only [hUpperUcheckpoint] using hBound)
    (fun x hx => (le_max_right _ _).trans_lt (hJfresh x hx)) hall hpSU hSUrel
    hUpTo hStrict hNext hU hfrontU
    (fun atom ha => ⟨(hfrontPool atom ha).1, (le_max_right _ _).trans_lt (hfrontPool atom ha).2⟩)
    (congrArg List.length hUpperUlabels) hUpperUroot hUpperUbody hSUroot hSrel
    (by simpa only [hSTother] using hS) (by simpa only [hSTother] using hSUp)
    (by simpa only [hSTother] using hSstrict) (by simpa only [hSTother] using hSnext)
    hSroot hgamma hSlast

#print axioms strict_nonlast_rank_one_bridge_triangle

end Erdos591.Positive.Game.Payoff
