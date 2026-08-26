import ErdosProblems.Erdos591.StrictLastOpening
import ErdosProblems.Erdos591.PrepareCriticalRoot

/-!
# The first two strict last plays and the localized upper second root

Start after the actual first selected leaf of S. Localize T's critical
body, choose its root overlap, and obtain the two compatible critical
prefixes. The next upper root request is issued and localized before
any U root input is chosen. All previously read values stay unchanged.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_strict_last_early_histories {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G) (htri : blue.CliqueFree 3)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    (origin st : Concrete.Hist N) {a : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin st)
    (hpST : st.position.pending = none) (hTinit : st.position.board.right = LabeledWord.initial)
    (hSrel : st.position.board.left.relaxed = true)
    (hfirst : ∀ q v d, (exactGame N blue).FollowStep σ H b origin q →
      (exactGame N blue).FollowStep σ H b q v →
      v.position.pending = some ⟨false, .advance d⟩ → 2 ≤ d)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = true) :
    ∃ K, K ⊆ H ∧ K.Infinite ∧ ∃ C e j, ∃ T : CriticalRootLabels K C e a j,
      0 < j ∧ j + 1 < e ∧ ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∃ B d c s, ∃ D : LastFirstLabels L B d c, 2 ≤ c ∧ 0 < s ∧ s = d ∧
      ∃ old upper g, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) st old ∧
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upper ∧
        old.position.pending = some ⟨false, .advance 0⟩ ∧ CriticalCheckpoint old ∧
        old.position.board.right.rootLabel = T.lower ∧
        old.position.board.right.bodyLabels.length = T.shared ∧
        old.position.board.right.currentLabel = D.lower ∧
        old.position.board.right.leafIndex = D.upper_first_view.pivot ∧
        upper.position.pending = some ⟨true, .advance g⟩ ∧
        LabeledWord.SameStructure old.position.board.right upper.position.board.left ∧
        upper.position.board.left.relaxed = true ∧
        upper.position.board.left.rootLabel = T.upper ∧
        upper.position.board.left.bodyLabels.length = T.shared ∧
        upper.position.board.left.currentLabel = D.upper_first_view.upper ∧
        upper.position.board.left.leafIndex = D.upper_first_view.pivot ∧
        upper.position.board.right = LabeledWord.initial ∧ upper.position.mode = some true ∧
        ∃ M, M ⊆ L ∧ M.Infinite ∧ ∃ k, 0 < k ∧ k + 1 < g ∧ ∀ z w,
          Relation.ReflTransGen ((exactGame N blue).FollowStep σ M b) upper z →
          (exactGame N blue).kind z = .terminal w →
            z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card =
              k := by
  have hwinST := hwin.of_reachable (exactGame N blue) hfrom
  obtain ⟨stR, e, hSTrequest, hSTboard, hpR, he⟩ :=
    winning_initial_right_request hHN hH blue htri hroot hwinST hpST hTinit hSrel
  have htoR := hfrom.tail hSTrequest
  have hRinit : stR.position.board.right = LabeledWord.initial := by
    simpa only [hSTboard] using hTinit
  obtain ⟨K, hKH, hK, j, hj, hje, hfixT⟩ := strict_critical_body_local
    hHN (Set.Subset.refl H) hH blue origin stR ha he hop hboard hmode hwin htoR hpR hRinit hall
  have pathH {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hKH (fun _ => le_rfl) hs) _ _ hpath
  obtain ⟨zT, wT, hTtail, hzT⟩ := (exactGame N blue).terminal_reachable_of_infinite
    (hKH.trans hHN) hK b σ stR
  have hjMore : j + 1 < e := (hfixT zT wT hTtail hzT).2
    (hlast zT wT (htoR.trans (pathH hTtail)) hzT)
  let C := max (max stR.position.bound (b stR)) (max origin.position.bound (b origin))
  obtain ⟨T⟩ := CriticalRootLabels.exists_of_infinite hK C e a j hj hje ha
  obtain ⟨v, hRv, _hvn, _hvm, hvOther, R, hRt, hRs, _hRL, hRlower, hRupper, hRshared⟩ :=
    prepare_critical_root (hKH.trans hHN) hK blue
      (hwin.mono (exactGame N blue) hKH (fun _ => le_rfl)) true false T hpR hop
      (by simpa only [Board.get] using hRinit) (by simp [hboard, Board.initial, Board.get])
      (le_max_left _ _) (le_max_right _ _)
  have hstv := (Relation.ReflTransGen.single hSTrequest).trans (pathH (.single hRv))
  have hSsame : v.position.board.left = st.position.board.left := by
    simpa only [hSTboard, Board.get, Bool.not_true] using hvOther
  have hpos : 0 < v.position.board.left.coordinates.length := by
    rw [hSsame]
    obtain ⟨as, has⟩ := History.word_run st false
    exact has.relaxed_coordinates_pos hSrel
  have hRrank : R.criticalRank = j := by
    rw [← R.labels.shared_rank, hRlower, hRshared, T.shared_rank]
  obtain ⟨L, hLK, hL, B, d, c, s, D, hc, hs, hsd, old, tu, hvOld, hTU, hpOld, hcp,
      hOldRoot, hOldBody, hOldLabel, hOldIndex, hnTU, hshape, hTUrel, hTUroot, hTUbody,
      hTUlabel, hTUindex, hTUinit, hTUmode⟩ :=
    strict_last_critical_opening hHN hKH hK blue origin v R hRt hRs ha hop hboard hmode
      hwin (hfrom.trans hstv) hpos hfirst hall hlast (fun z w hpath hz => by
        simpa only [hRrank] using (hfixT z w ((Relation.ReflTransGen.single hRv).trans hpath) hz).1)
  obtain ⟨upper, g, hTUrequest, hTUboard, hpUpper, hg⟩ :=
    winning_initial_right_request hHN hH blue htri hroot
      (hwin.of_reachable (exactGame N blue) hTU) hnTU hTUinit hTUrel
  have htoUpper := hTU.tail hTUrequest
  have hupperInit : upper.position.board.right = LabeledWord.initial := by
    simpa only [hTUboard] using hTUinit
  obtain ⟨M, hML, hM, k, hk, _hkg, hfixU⟩ := strict_critical_body_local
    hHN (hLK.trans hKH) hL blue origin upper ha hg hop hboard hmode hwin htoUpper hpUpper
      hupperInit hall
  obtain ⟨zU, wU, hUtail, hzU⟩ := (exactGame N blue).terminal_reachable_of_infinite
    ((hML.trans hLK).trans hKH |>.trans hHN) hM b σ upper
  have hUtailH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upper zU :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue)
        ((hML.trans hLK).trans hKH) (fun _ => le_rfl) hs) _ _ hUtail
  have hkMore : k + 1 < g := (hfixU zU wU hUtail hzU).2
    (hlast zU wU (htoUpper.trans hUtailH) hzU)
  refine ⟨K, hKH, hK, C, e, j, T, hj, hjMore, L, hLK, hL, B, d, c, s, D, hc, hs, hsd,
    old, upper, g, hstv.trans (pathH hvOld), htoUpper, hpOld, hcp, ?_, ?_, hOldLabel,
    hOldIndex, hpUpper, ?_, ?_, ?_, ?_, ?_, ?_, hupperInit,
      follow_mode_some (.single hTUrequest) hTUmode, M, hML, hM, k, hk, hkMore, ?_⟩
  · simpa only [hRlower] using hOldRoot
  · simpa only [hRshared] using hOldBody
  · simpa only [hTUboard] using hshape
  · simpa only [hTUboard] using hTUrel
  · simpa only [hTUboard, hRupper] using hTUroot
  · simpa only [hTUboard, hRshared] using hTUbody
  · simpa only [hTUboard] using hTUlabel
  · simpa only [hTUboard] using hTUindex
  · intro z w hpath hz
    exact (hfixU z w hpath hz).1

#print axioms inside_strict_last_early_histories

end Erdos591.Positive.Game.Payoff
