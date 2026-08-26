import ErdosProblems.Erdos591.InsideStrictLastPivotStart
import ErdosProblems.Erdos591.StrictLastBridgeTriangle

/-!
# The actual last-critical three-play start yields the strict triangle

Use the checked second/last S-label pattern. The original opening
paths discharge the localized terminal profile in the upper bridge;
no new completion hypothesis is added after the label choices.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_strict_last_pivot_triangle {N H M HT : Set ℕ}
    (hHN : H ⊆ N) (hMH : M ⊆ H) (hM : M.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    (origin old upperOrigin : Concrete.Hist N) {B a CT eT jT g k : ℕ}
    (Sroot : LastLastLabels H B a) (T : CriticalRootLabels HT CT eT a jT)
    (ha : 2 ≤ a) (hk : 0 < k) (hkg : k + 1 < g)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hB : max origin.position.bound (b origin) ≤ B)
    (hfromOld : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (hfromUpper : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upperOrigin)
    (hpOld : old.position.pending = some ⟨false, .advance 0⟩) (hOld : CriticalCheckpoint old)
    (hOldRoot : old.position.board.left.rootLabel = Sroot.lower)
    (hOldBody : old.position.board.left.bodyLabels.length = Sroot.penultimate)
    (hTno : old.position.board.right.NoLeafPending)
    (hTroot : old.position.board.right.rootLabel = T.lower)
    (hTbody : old.position.board.right.bodyLabels.length = T.shared)
    (hTshape : LabeledWord.SameStructure old.position.board.right upperOrigin.position.board.left)
    (hUpperTroot : upperOrigin.position.board.left.rootLabel = T.upper)
    (hpUpper : upperOrigin.position.pending = some ⟨true, .advance g⟩)
    (hUpperInit : upperOrigin.position.board.right = LabeledWord.initial)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = true)
    (hfixedUpper : ∀ z w,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ M b) upperOrigin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k)
    (hlarge : ∀ v d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin v →
      v.position.pending = some ⟨false, .advance d⟩ → v.position.board.left.markerEvent = true →
      (∀ i ∈ v.position.board.left.rootLabel,
        i ≤ v.position.board.left.bodyLabels.length + 1) → 2 ≤ d)
    {as : List (Finset ℕ × ℕ)}
    (hraw : (LabeledCode.rootCursor Sroot.lower Sroot.marker).runAtoms as =
      some old.position.board.left)
    (hinc : (Sroot.marker :: as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ as.map Prod.snd, x ∈ H) :
    ¬ blue.CliqueFree 3 := by
  obtain ⟨K, hKM, _hK, CU, e, j, U, _hj, _hje, L, hLK, hL,
      D, p, q, S, _hp, _hq, st, su, tu, _hfromST, hfromSU, hfromTU,
      hwinST, hwinSU, hwinTU, hpST, hpSU, hnTU, hSshape, hSrelST, hSrelSU,
      hSlabelST, hSlabelSU, hSindexST, _hSindexSU, _hSrootST, hSrootSU,
      hSTrel, hSTno, hSTroot, hSTbody, hSUrel, hSUno, hSUroot, hSUbody,
      hTshared, hUshared, hTUrootT, hTUrootU, hTUrel, _hTUmode, hTUsep, hTUfixed⟩ :=
    inside_strict_last_pivot_start hHN hMH hM blue htri hroot origin old upperOrigin
      Sroot T ha hk hkg hwin hop hboard hmode hB hfromOld hfromUpper hpOld hOld
      hOldRoot hOldBody hTno hTroot hTbody hTshape hUpperTroot hpUpper hUpperInit
      hall hlast hfixedUpper hlarge hraw hinc hpool
  have hLH : L ⊆ H := (hLK.trans hKM).trans hMH
  have pathH {v w : Concrete.Hist N}
      (h : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hLH (fun _ => le_rfl) hs) _ _ h
  have hSUp : LabeledWord.UpToLeaf S.pivot st.position.board.left :=
    ⟨(of_decide_eq_true hSrelST).2.1, hSlabelST ▸ S.pivot_lower,
      by rw [hSindexST]; exact S.first_lt_pivot.le⟩
  have hSstrict : st.position.board.left.leafIndex < S.pivot := by
    rw [hSindexST]
    exact S.first_lt_pivot
  have hSnext : ∀ i ∈ st.position.board.left.currentLabel,
      st.position.board.left.leafIndex < i → S.pivot ≤ i := by
    intro i hi hlt
    rcases S.lower_gap i (hSlabelST ▸ hi) with heq | hle
    · rw [hSindexST, heq] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
    · exact hle
  have hgamma : S.pivot ∈ su.position.board.left.currentLabel := hSlabelSU ▸ S.pivot_upper
  have hSlast : ∀ i ∈ su.position.board.left.currentLabel, i ≤ S.pivot :=
    fun i hi => (S.upper_bounds i (hSlabelSU ▸ hi)).2
  exact strict_last_bridge_triangle hHN hLH hL blue origin st su tu T U ha hkg hwin
    hop hboard hmode hfromTU hfromSU hall hwinST hwinSU hwinTU hpST hpSU hnTU
    hSTrel hSTno hSTroot hSTbody hSUrel hSUno hSUroot hSUbody hTshared hUshared
    hTUrootT hTUrootU hTUrel hTUsep hTUfixed
    (fun z w hpz hz => hlast z w (hfromTU.trans (pathH hpz)) hz)
    hSrelSU hSshape hSUp hSstrict hSnext hSrootSU hgamma hSlast

#print axioms inside_strict_last_pivot_triangle

end Erdos591.Positive.Game.Payoff
