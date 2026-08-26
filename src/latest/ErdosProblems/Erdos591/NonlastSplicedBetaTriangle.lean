import ErdosProblems.Erdos591.PreliminarySplicedBridgeStart
import ErdosProblems.Erdos591.NonlastSplicedBridgeTriangle
import ErdosProblems.Erdos591.CriticalRootLabels

/-! # The shared beta and retained upper U reply through the higher-rank triangle -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem nonlast_spliced_beta_triangle {N H0 J HT HU HE : Set ℕ}
    (hH0N : H0 ⊆ N) (hJH0 : J ⊆ H0) (hJ : J.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin oldU st su upper : Concrete.Hist N)
    {a BT eT dT jT BU e g j k BE n c s : ℕ}
    (T : CriticalRootLabels HT BT eT dT jT) (U : SplicedRootLabels HU BU e g j k)
    (E : RankedFirstLeafLabels HE BE n c s) (ha : 2 ≤ a) (hc : 0 < c) (hAfterU : k < g)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H0 b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin upper)
    (hwinST : (exactGame N blue).ArchitectWins J b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins J b σ su)
    (hpST : st.position.pending = some ⟨true, .advance 0⟩)
    (hpSU : su.position.pending = some ⟨true, .advance 0⟩)
    (hpUpper : upper.position.pending = some ⟨true, .advance 0⟩)
    (hSTrel : st.position.board.right.relaxed = true)
    (hSUrel : su.position.board.right.relaxed = true)
    (hSTno : st.position.board.right.NoLeafPending)
    (hSUno : su.position.board.right.NoLeafPending)
    (hSTroot : st.position.board.right.rootLabel = T.lower)
    (hSTbody : st.position.board.right.bodyLabels.length = T.shared)
    (hSUroot : su.position.board.right.rootLabel = U.lower)
    (hSUbody : su.position.board.right.bodyLabels.length = U.first)
    (hTshape : LabeledWord.SameStructure st.position.board.right upper.position.board.left)
    (hTroot : upper.position.board.left.rootLabel = T.upper)
    (hTrel : upper.position.board.left.relaxed = true)
    (hUshape : LabeledWord.SameStructure upper.position.board.right oldU.position.board.right)
    (hUrel : upper.position.board.right.relaxed = true)
    (hUroot : upper.position.board.right.rootLabel = U.upper)
    (hUbody : upper.position.board.right.bodyLabels.length = U.first)
    (hUlabel : upper.position.board.right.currentLabel = E.targetView.upper)
    (hUindex : upper.position.board.right.leafIndex = E.targetView.pivot)
    (hOldUrel : oldU.position.board.right.relaxed = true)
    (hSUlabels : su.position.board.right.bodyLabels = oldU.position.board.right.bodyLabels)
    (hSUindex : su.position.board.right.leafIndex = E.source.sup id)
    {bs : List (Finset ℕ × ℕ)}
    (hrun : LabeledWord.LegalRun oldU.position.board.right bs su.position.board.right)
    (hpool : ∀ atom ∈ bs, atom.2 ∈ J ∧ max upper.position.bound (b upper) < atom.2)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upper z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false)
    (hModeSU : su.position.mode = some true)
    (hSrel : su.position.board.left.relaxed = true)
    (hS : LabeledWord.SameStructure st.position.board.left su.position.board.left)
    {gamma : ℕ} (hSUp : LabeledWord.UpToLeaf gamma st.position.board.left)
    (hSstrict : st.position.board.left.leafIndex < gamma)
    (hSnext : ∀ m ∈ st.position.board.left.currentLabel,
      st.position.board.left.leafIndex < m → gamma ≤ m)
    (hSroot : ∀ m ∈ su.position.board.left.rootLabel,
      m ≤ su.position.board.left.bodyLabels.length)
    (hgamma : gamma ∈ su.position.board.left.currentLabel)
    (hSlast : ∀ m ∈ su.position.board.left.currentLabel, m ≤ gamma) :
    ¬ blue.CliqueFree 3 := by
  let C := max (max st.position.bound (b st)) (max su.position.bound (b su))
  obtain ⟨H, hHJ, hH, hFresh, p, hUpperP, hpn, hTother, hpUroot, hstart,
      anchorU, hAnchorUShape, as, has, hAsPool⟩ :=
    preliminary_spliced_bridge_start (hJH0.trans hH0N) hJ blue σ oldU su upper E U hc
      hpUpper hUshape hUrel hUlabel hUindex hUroot hUbody hSUbody hOldUrel
      hSUlabels hSUindex hrun hpool C
  have pathJ {v w : Concrete.Hist N}
      (hp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hHJ (fun _ => le_rfl) hs) _ _ hp
  have pathH0 {v w : Concrete.Hist N}
      (hp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH0 (fun _ => le_rfl) hs) _ _ hp
  have hbeforeT : LabeledWord.BeforeBody T.next st.position.board.right :=
    ⟨hSTroot ▸ T.next_lower, by simpa only [hSTbody] using T.shared_lt_next⟩
  have hnextT : ∀ m ∈ st.position.board.right.rootLabel,
      st.position.board.right.bodyLabels.length < m → T.next ≤ m := by
    simpa only [hSTroot, hSTbody] using T.next_is_next
  have hbeforeU : LabeledWord.BeforeBody U.anchor su.position.board.right :=
    ⟨hSUroot ▸ U.anchor_lower, by simpa only [hSUbody] using U.first_lt_anchor⟩
  have hnextU : ∀ m ∈ su.position.board.right.rootLabel,
      su.position.board.right.bodyLabels.length < m → U.anchor ≤ m := by
    intro m hm hgt
    exact (U.lower_gap m (hSUroot ▸ hm)).resolve_left
      (not_le_of_gt (by simpa only [hSUbody] using hgt))
  have hpTbody : p.position.board.left.bodyLabels.length = T.shared := by
    rw [hTother, ← hTshape.body_length, hSTbody]
  have hpTlast : p.position.board.left.lastSelectedBody = T.next := by
    rw [hTother, LabeledWord.lastSelectedBody, hTroot, T.upper_sup]
  have hpTshape : LabeledWord.SameStructure st.position.board.right p.position.board.left := by
    simpa only [hTother] using hTshape
  have hfromP := hfrom.trans (pathH0 (.single hUpperP))
  exact nonlast_spliced_bridge_triangle hH0N (hHJ.trans hJH0) hH blue origin p st su U
    ha hAfterU hop hboard hmode hwin hfromP
    (hwinST.mono (exactGame N blue) hHJ (fun _ => le_rfl))
    (hwinSU.mono (exactGame N blue) hHJ (fun _ => le_rfl)) hpn
    (by simpa only [hTother] using hTrel)
    (by simpa only [hpTbody, hpTlast] using T.shared_lt_next) hpTlast hpUroot hstart
    (fun z w hpz hz => hfixed z w ((Relation.ReflTransGen.single hUpperP).trans (pathJ hpz)) hz)
    (fun z w hpz hz => hlast z w (hfromP.trans (pathH0 (pathJ hpz))) hz)
    hpST hSTrel hSTno hbeforeT hnextT hpSU hSUrel hSUno hbeforeU hnextU hSUroot hModeSU
    hpTshape (.nil _) (by simp) hAnchorUShape has
    (fun atom ha => ⟨(hAsPool atom ha).1, (le_max_right _ _).trans_lt (hAsPool atom ha).2⟩)
    (fun x hx => (le_max_left _ _).trans_lt (hFresh x hx))
    (fun x hx => (le_max_right _ _).trans_lt (hFresh x hx)) hall
    hSrel hS hSUp hSstrict hSnext hSroot hgamma hSlast

#print axioms nonlast_spliced_beta_triangle

end Erdos591.Positive.Game.Payoff
