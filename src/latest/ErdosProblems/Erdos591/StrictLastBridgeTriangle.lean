import ErdosProblems.Erdos591.StrictLastUpperMarkerBridge
import ErdosProblems.Erdos591.StrictAnchorLocalization
import ErdosProblems.Erdos591.StrictAnchorRequestsTriangle

/-!
# The last-critical upper bridge through the strict triangle

The three plays already share their first last-body S leaf. Reach
the shared T anchor marker, localize the future U anchor size, and
derive every terminal-profile premise from the original actual opening.
Then choose both anchor labels and use the complete checked ending.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem strict_last_bridge_triangle {N H0 H HT HU : Set ℕ}
    (hH0N : H0 ⊆ N) (hHH0 : H ⊆ H0) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin st su tu : Concrete.Hist N) {a BT eT dT jT BU e g j k : ℕ}
    (T : CriticalRootLabels HT BT eT dT jT) (U : SplicedRootLabels HU BU e g j (k + 1))
    (ha : 2 ≤ a) (hAfter : k + 1 < g)
    (hwinOrigin : (exactGame N blue).ArchitectWins H0 b σ origin)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hfromTU : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin tu)
    (hfromSU : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin su)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    (hpST : st.position.pending = some ⟨true, .advance 0⟩)
    (hpSU : su.position.pending = some ⟨true, .advance 0⟩)
    (hnTU : tu.position.pending = none)
    (hSTrel : st.position.board.right.relaxed = true)
    (hSTno : st.position.board.right.NoLeafPending)
    (hSTroot : st.position.board.right.rootLabel = T.lower)
    (hSTbody : st.position.board.right.bodyLabels.length = T.shared)
    (hSUrel : su.position.board.right.relaxed = true)
    (hSUno : su.position.board.right.NoLeafPending)
    (hSUroot : su.position.board.right.rootLabel = U.lower)
    (hSUbody : su.position.board.right.bodyLabels.length = U.first)
    (hT : LabeledWord.SameStructure st.position.board.right tu.position.board.left)
    (hU : LabeledWord.SameStructure su.position.board.right tu.position.board.right)
    (hTUrootT : tu.position.board.left.rootLabel = T.upper)
    (hTUrootU : tu.position.board.right.rootLabel = U.upper)
    (hTUrel : tu.position.board.right.relaxed = true)
    (hTUsep : ∀ x ∈ tu.position.board.left.coordinates,
      x ≤ tu.position.board.right.coordinates.getLastD 0)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) tu z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) tu z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = true)
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
  have hHN := hHH0.trans hH0N
  have pathH0 {v w : Concrete.Hist N}
      (h : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hHH0 (fun _ => le_rfl) hs) _ _ h
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
  have hUbefore : LabeledWord.BeforeBody U.anchor su.position.board.right :=
    ⟨hSUroot ▸ U.anchor_lower, by rw [hSUbody]; exact U.first_lt_anchor⟩
  have hUnext : ∀ i ∈ su.position.board.right.rootLabel,
      su.position.board.right.bodyLabels.length < i → U.anchor ≤ i := by
    intro i hi hlt
    exact (U.lower_gap i (hSUroot ▸ hi)).resolve_left
      (by simpa only [hSUbody] using not_le_of_gt hlt)
  let B := max (max st.position.bound (b st)) (max su.position.bound (b su))
  obtain ⟨J, hJH, hJ, hJfresh, oldT, upper, D, R, hSTpath, hTUupper, hwinUpper,
      hpT, hpUpper, hD, _hR, hTshape, hmT, hmUpper, _hiT, hiUpper,
      _hRootT, hRootUpperT, hSTother, hUpperUrel, hUpperUno, hUpperUroot,
      hUpperBefore, hUpperNext, _hUpperRank, frontU, hfrontU, hfrontPool⟩ :=
    strict_last_upper_marker_bridge hHN hH blue st tu U hwinST hwinTU hpST hSTrel hSTno
      hTbefore hTnext hT hTlast hnTU hTUrel hTUrootU (follow_mode_some hfromTU hmode)
      hTUsep hfixed hlast B (le_max_left _ _)
  have pathJ {v w : Concrete.Hist N}
      (h : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ h
  have hfromUpper := hfromTU.trans (pathH0 (pathJ hTUupper))
  have hRootLast : ∀ i ∈ upper.position.board.left.rootLabel,
      i ≤ upper.position.board.left.bodyLabels.length + 1 := by
    intro i hi
    rw [hRootUpperT, hTUrootT] at hi
    rw [hiUpper]
    exact (T.upper_bounds i hi).2
  have hFixedUpper : ∀ z w,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upper z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k :=
    fun z w hpz hz => hfixed z w (pathJ (hTUupper.trans hpz)) hz
  obtain ⟨L, hLJ, hL, K, hK, hKR, hSize⟩ := strict_spliced_anchor_localization hH0N
    (hJH.trans hHH0) hJ blue origin upper U ha hAfter hop hboard hmode hwinOrigin
    hfromUpper hpUpper hmUpper hRootLast hUpperUrel hUpperUroot hall hFixedUpper
  have pathL {v w : Concrete.Hist N}
      (h : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hLJ (fun _ => le_rfl) hs) _ _ h
  have hValid := terminal_strict_profile_on_subset ((hLJ.trans hJH).trans hHH0) blue
    origin upper ha hop hboard hmode hwinOrigin hfromUpper hall
    (fun z w hpz hz => hFixedUpper z w (pathL hpz) hz)
    (fun z w hpz hz => hlast z w (pathJ (hTUupper.trans (pathL hpz))) hz)
  exact strict_anchor_requests_triangle hHN hH (hLJ.trans hJH) hL blue oldT su upper U
    hD hK hKR hAfter (hwinST.of_reachable (exactGame N blue) hSTpath) hwinSU
    (hwinUpper.mono (exactGame N blue) hLJ (fun _ => le_rfl))
    hpT hpUpper hmT hmUpper hTshape.symm hRootLast hpSU hSUrel hSUno hUbefore hUnext
    hSUroot hU hfrontU
    (fun a ha => ⟨(hfrontPool a ha).1, (le_max_right _ _).trans_lt (hfrontPool a ha).2⟩)
    (fun x hx => (le_max_right _ _).trans_lt (hJfresh x (hLJ hx)))
    hUpperUrel hUpperUno hUpperBefore hUpperNext hUpperUroot
    (follow_mode_some hfromUpper hmode) (follow_mode_some hfromSU hmode) hSize hValid
    hSrel (by simpa only [hSTother] using hS)
    (by simpa only [hSTother] using hSUp) (by simpa only [hSTother] using hSstrict)
    (by simpa only [hSTother] using hSnext) hSroot hgamma hSlast

#print axioms strict_last_bridge_triangle

end Erdos591.Positive.Game.Payoff
