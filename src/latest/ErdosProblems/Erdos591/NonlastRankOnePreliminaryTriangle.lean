import ErdosProblems.Erdos591.PreliminaryRankOneStart
import ErdosProblems.Erdos591.StrictNonlastRankOneBridgeTriangle

/-!
# The actual empty-group preliminary start through the rank-one triangle

The initial lower critical checkpoint and both issued S-body requests
are genuine histories. Their full labels and the three preserved
paths supply every starting premise of the rank-one upper bridge.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem nonlast_rank_one_preliminary_triangle {N H J HT HU HD HE : Set ℕ}
    (hHN : H ⊆ N) (hJH : J ⊆ H) (hJ : J.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin old p q upper : Concrete.Hist N)
    {a B P Q r BT eT dT jT BU e g j BD nD cD sD BE nE cE sE : ℕ}
    (L : PreliminaryPivotLabels J B P Q r 0)
    (T : CriticalRootLabels HT BT eT dT jT) (U : SeparatedRootLabels HU BU e g j)
    (D : CriticalLeafLabels HD BD nD cD sD) (E : CriticalRootLabels HE BE nE cE sE)
    (ha : 2 ≤ a) (hg : 2 ≤ g)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfromOld : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (hOldP : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old p)
    (hfromQ : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q)
    (hfromUpper : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upper)
    (hOld : CriticalCheckpoint old)
    (hp : p.position.pending = some ⟨false, .advance P⟩)
    (hq : q.position.pending = some ⟨false, .advance Q⟩)
    (hstem : LabeledWord.SameStructure p.position.board.left q.position.board.left)
    (hmP : p.position.board.left.markerEvent = true)
    (hmQ : q.position.board.left.markerEvent = true)
    (hrootP : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1)
    (hrootQ : ∀ i ∈ q.position.board.left.rootLabel,
      i ≤ q.position.board.left.bodyLabels.length + 1)
    (hotherP : p.position.board.right = old.position.board.right)
    (hBP : max p.position.bound (b p) ≤ B) (hBQ : max q.position.bound (b q) ≤ B)
    (hOldLabel : old.position.board.right.currentLabel = D.lower)
    (hOldIndex : old.position.board.right.leafIndex = D.upperView.pivot)
    (hOldRoot : old.position.board.right.rootLabel = T.lower)
    (hOldBody : old.position.board.right.bodyLabels.length = T.shared)
    (hrank : old.position.board.right.currentLabel.card -
      (old.position.board.right.currentLabel.filter
        (fun x => x ≤ old.position.board.right.leafIndex)).card = r)
    (hTshape : LabeledWord.SameStructure upper.position.board.left old.position.board.right)
    (hTrel : upper.position.board.left.relaxed = true)
    (hTlabel : upper.position.board.left.currentLabel = D.upperView.upper)
    (hTindex : upper.position.board.left.leafIndex = D.upperView.pivot)
    (hTroot : upper.position.board.left.rootLabel = T.upper)
    (hUshape : LabeledWord.SameStructure q.position.board.right upper.position.board.right)
    (hUrel : upper.position.board.right.relaxed = true)
    (hUQrel : q.position.board.right.relaxed = true)
    (hUroot : upper.position.board.right.rootLabel = U.upper)
    (hUbody : upper.position.board.right.bodyLabels.length = U.first)
    (hUlabel : upper.position.board.right.currentLabel = E.upper)
    (hUQroot : q.position.board.right.rootLabel = U.lower)
    (hUQlabel : q.position.board.right.currentLabel = E.lower)
    (hUQindex : q.position.board.right.leafIndex = E.shared)
    (hUsep : ∀ x ∈ upper.position.board.left.coordinates,
      x ≤ upper.position.board.right.coordinates.getLastD 0)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upper z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = 1)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false) :
    ¬ blue.CliqueFree 3 := by
  have pathH {v w : Concrete.Hist N}
      (h : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ h
  have hfutureT : ∃ i ∈ old.position.board.right.rootLabel,
      old.position.board.right.bodyLabels.length < i :=
    ⟨T.next, hOldRoot ▸ T.next_lower, by simpa only [hOldBody] using T.shared_lt_next⟩
  have hUindex : upper.position.board.right.leafIndex = E.shared :=
    hUshape.leaf_eq.symm.trans hUQindex
  have hUpending : Macro.Pending upper.position.board.right := Or.inr
    ⟨(of_decide_eq_true hUrel).2.1, E.next, hUlabel ▸ E.next_upper,
      by simpa only [hUindex] using E.shared_lt_next⟩
  have hUQpending : Macro.Pending q.position.board.right := Or.inr
    ⟨(of_decide_eq_true hUQrel).2.1, E.next, hUQlabel ▸ E.next_lower,
      by simpa only [hUQindex] using E.shared_lt_next⟩
  obtain ⟨st, su, tu, hPST, hQSU, hUpperTU, hpST, hpSU, _hpTU, hS, hT, hU,
      hSTleft, hSUleft, hSTlabel, hSUlabel, hSTbeta, hSUbeta,
      _hSTrootS, _hSUrootS, _hSTlabelsS, _hSUlabelsS, _hSTlastS, hSUlastS,
      hSTrel, hSTno, hSTbody, _hSTindex, hSUother, hTUother, hTUrel,
      _hTUlabels, _hTUcurrent, _hTUindex, _hSTsep, _hSUsep, hTUsep⟩ :=
    preliminary_rank_one_start hHN hJH hJ blue origin old p q upper L D ha hop hboard hmode
      hwin hfromOld hOldP hfromQ hfromUpper hOld hp hq hstem hmP hmQ hrootP hrootQ hotherP
      hBP hBQ hOldLabel hOldIndex hrank hfutureT hTshape hTrel hTlabel hTindex
      hUshape hUrel hUQrel hUpending hUQpending hUsep hall
  obtain ⟨as, has, _⟩ := follow_word_inputs_above_bound hPST true
  have hSTroot : st.position.board.right.rootLabel = T.lower := by
    have hpRel : p.position.board.right.relaxed = true := by
      simpa only [hotherP] using hOld.right_relaxed
    have heq := has.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant p).2.1 true).1 hpRel)
    simpa only [Board.get, hotherP, hOldRoot] using heq
  obtain ⟨bs, hbs, _⟩ := follow_word_inputs_above_bound hUpperTU false
  have hTUroot : tu.position.board.left.rootLabel = T.upper :=
    (hbs.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant upper).2.1 false).1 hTrel)).trans hTroot
  have hfromST := hfromOld.trans (hOldP.trans (pathH hPST))
  have hfromSU := hfromQ.trans (pathH hQSU)
  have hfromTU := hfromUpper.trans (pathH hUpperTU)
  have hSUp : LabeledWord.UpToLeaf L.gamma st.position.board.left :=
    ⟨(of_decide_eq_true hSTleft).2.1, hSTlabel ▸ L.gamma_lower,
      by simpa only [hSTbeta] using L.beta_lt_gamma.le⟩
  exact strict_nonlast_rank_one_bridge_triangle hHN hJH hJ blue origin st su tu T U E ha hg
    hop hboard hmode hwin hfromTU hall
    ((hwin.of_reachable (exactGame N blue) hfromST).mono
      (exactGame N blue) hJH (fun _ => le_rfl))
    ((hwin.of_reachable (exactGame N blue) hfromSU).mono
      (exactGame N blue) hJH (fun _ => le_rfl))
    ((hwin.of_reachable (exactGame N blue) hfromTU).mono
      (exactGame N blue) hJH (fun _ => le_rfl))
    (follow_mode_some hfromSU hmode) hpST hpSU hSTrel hSTno hSTroot
    (by simpa only [hSTbody] using hOldBody) hT hTUroot hTUrel
    (by simpa only [hTUother] using hUrel) (by simpa only [hTUother] using hUroot)
    (by simpa only [hTUother] using hUbody) (by simpa only [hTUother] using hUlabel) hTUsep
    (fun z w hpath hz => hfixed z w (hUpperTU.trans hpath) hz)
    (fun z w hpath hz => hlast z w (hfromTU.trans (pathH hpath)) hz)
    (by simpa only [hSUother] using hUQrel) (by simpa only [hSUother] using hUQroot)
    (by simpa only [hSUother] using hUQlabel) (by simpa only [hSUother] using hUQindex)
    hU hSUleft hS hSUp (by simpa only [hSTbeta] using L.beta_lt_gamma)
    (by simpa only [hSTlabel, hSTbeta] using L.gamma_next_lower)
    hSUlastS (hSUlabel ▸ L.gamma_upper) (by simpa only [hSUlabel] using L.upper_le_gamma)

#print axioms nonlast_rank_one_preliminary_triangle

end Erdos591.Positive.Game.Payoff
