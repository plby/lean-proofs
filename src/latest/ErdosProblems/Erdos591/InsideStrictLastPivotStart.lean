import ErdosProblems.Erdos591.ReservedLastCheckpoint
import ErdosProblems.Erdos591.CommonLastMarkerRequests
import ErdosProblems.Erdos591.StrictFirstBodyOpening

/-!
# Three actual plays at the shared last-body first leaf with the strict second/last S pivot

Both lower last-body requests are issued before their full labels are
chosen. Their common first leaf is submitted on the latest future pool;
the two lower opposite responses stay pending while TU keeps its two
compatible critical prefixes and its localized upper critical rank.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_strict_last_pivot_start {N H M HT : Set ℕ}
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
    ∃ K, K ⊆ M ∧ K.Infinite ∧ ∃ CU e j, ∃ U : SplicedRootLabels K CU e g j (k + 1),
      0 < j ∧ j + 1 < e ∧ ∃ L, L ⊆ K ∧ L.Infinite ∧
        ∃ D p q, ∃ S : FirstSecondLastLabels L D p q, 2 ≤ p ∧ 2 ≤ q ∧ ∃ st su tu,
          Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin st ∧
          Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin su ∧
          Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin tu ∧
          (exactGame N blue).ArchitectWins L b σ st ∧
          (exactGame N blue).ArchitectWins L b σ su ∧
          (exactGame N blue).ArchitectWins L b σ tu ∧
          st.position.pending = some ⟨true, .advance 0⟩ ∧
          su.position.pending = some ⟨true, .advance 0⟩ ∧ tu.position.pending = none ∧
          LabeledWord.SameStructure st.position.board.left su.position.board.left ∧
          st.position.board.left.relaxed = true ∧ su.position.board.left.relaxed = true ∧
          st.position.board.left.currentLabel = S.lower ∧
          su.position.board.left.currentLabel = S.upper ∧
          st.position.board.left.leafIndex = S.first ∧ su.position.board.left.leafIndex = S.first ∧
          (∀ i ∈ st.position.board.left.rootLabel, i ≤ st.position.board.left.bodyLabels.length) ∧
          (∀ i ∈ su.position.board.left.rootLabel, i ≤ su.position.board.left.bodyLabels.length) ∧
          st.position.board.right.relaxed = true ∧ st.position.board.right.NoLeafPending ∧
          st.position.board.right.rootLabel = T.lower ∧
          st.position.board.right.bodyLabels.length = T.shared ∧
          su.position.board.right.relaxed = true ∧ su.position.board.right.NoLeafPending ∧
          su.position.board.right.rootLabel = U.lower ∧
          su.position.board.right.bodyLabels.length = U.first ∧
          LabeledWord.SameStructure st.position.board.right tu.position.board.left ∧
          LabeledWord.SameStructure su.position.board.right tu.position.board.right ∧
          tu.position.board.left.rootLabel = T.upper ∧ tu.position.board.right.rootLabel = U.upper ∧
          tu.position.board.right.relaxed = true ∧ tu.position.mode = some true ∧
          (∀ x ∈ tu.position.board.left.coordinates,
            x ≤ tu.position.board.right.coordinates.getLastD 0) ∧
          ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) tu z →
            (exactGame N blue).kind z = .terminal w →
              z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card =
                k := by
  obtain ⟨K, hKM, hK, CU, e, j, U, hj, hje, L, hLK, hL, hLfresh,
      _Dbound, _d, _c, _Ubody, fine, tu, hfromFine, hfromTU, _hUpperTU, hwinFine,
      hpFine, hFine, hFineRoot, hFineBody, hUno, hUroot, hUbody, _hUlabel, _hUindex,
      hnTU, hTUleft, hUshape, hTUrel, hTUroot, _hTUbody, _hTUlabel, _hTUindex,
      hTUmode, hTUsep, hTUfixed, frontAtoms, hfront, hfrontPool⟩ :=
    reserved_last_checkpoint hHN hMH hM blue htri hroot origin old upperOrigin Sroot ha hk hkg
      hwin hop hboard hmode hB hfromUpper hOldBody hpUpper hUpperInit hall hlast hfixedUpper
      hraw hinc hpool
  have hLH := (hLK.trans hKM).trans hMH
  have hLN := hLH.trans hHN
  have pathH {v w : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hLH (fun _ => le_rfl) hs) _ _ hpath
  obtain ⟨v, w, p, q, hOldV, hFineW, hpV, hpW, _hp, _hq, hS, hmV, hmW, _hiV, _hiW,
      _hrV, _hrW, hrootV, hrootW, hotherV, hotherW⟩ :=
    common_last_marker_requests hHN (hM.mono hMH) hLH hL blue old fine Sroot
      (hwin.of_reachable (exactGame N blue) hfromOld) hwinFine hpOld hpFine
      hOldRoot hOldBody hOld.left_relaxed hOld.left_exhausted
      hFineRoot hFineBody hFine.left_relaxed hFine.left_exhausted hfront hfrontPool hLfresh
  have hfromV := hfromOld.trans hOldV
  have hfromW := hfromFine.trans (pathH hFineW)
  have hpLarge := hlarge v p hfromV hpV hmV hrootV
  have hqLarge := hlarge w q hfromW hpW hmW hrootW
  let D := max (max v.position.bound (b v)) (max w.position.bound (b w))
  obtain ⟨S⟩ := FirstSecondLastLabels.exists_of_infinite hL D p q hpLarge hqLarge
  have hbeforeT : LabeledWord.BeforeBody T.next v.position.board.right := by
    rw [hotherV]
    exact ⟨hTroot ▸ T.next_lower, by simpa only [hTbody] using T.shared_lt_next⟩
  have hbeforeU : LabeledWord.BeforeBody U.anchor w.position.board.right := by
    rw [hotherW]
    exact ⟨hUroot ▸ U.anchor_lower, by simpa only [hUbody] using U.first_lt_anchor⟩
  have hwinV := (hwin.of_reachable (exactGame N blue) hfromV).mono
    (exactGame N blue) hLH (fun _ => le_rfl)
  have hwinW := hwinFine.of_reachable (exactGame N blue) hFineW
  obtain ⟨st, su, hVST, hWSU, hpST, hpSU, hSshape, hrST, hrSU, hlST, hlSU, hiST, hiSU,
      hrootsST, hrootsSU, hoST, hoSU, _hprefix⟩ := strict_first_body_opening hLN hL blue v w S
        hwinV hwinW hpV hpW hmV hmW hS hrootV hrootW
        (by simpa only [hotherV] using hOld.right_relaxed)
        (by simpa only [hotherW] using hFine.right_relaxed)
        hbeforeT hbeforeU (le_max_left _ _) (le_max_right _ _)
  have hSTright := hoST.trans hotherV
  have hSUright := hoSU.trans hotherW
  refine ⟨K, hKM, hK, CU, e, j, U, hj, hje, L, hLK, hL, D, p, q, S, hpLarge, hqLarge,
    st, su, tu, hfromV.trans (pathH hVST), hfromW.trans (pathH hWSU), hfromTU,
    hwinV.of_reachable (exactGame N blue) hVST, hwinW.of_reachable (exactGame N blue) hWSU,
    (hwin.of_reachable (exactGame N blue) hfromTU).mono
      (exactGame N blue) hLH (fun _ => le_rfl), hpST, hpSU, hnTU, hSshape, hrST, hrSU,
    hlST, hlSU, hiST, hiSU, hrootsST, hrootsSU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hTUroot, hTUrel, hTUmode, hTUsep, hTUfixed⟩
  · simpa only [hSTright] using hOld.right_relaxed
  · simpa only [hSTright] using hTno
  · simpa only [hSTright] using hTroot
  · simpa only [hSTright] using hTbody
  · simpa only [hSUright] using hFine.right_relaxed
  · simpa only [hSUright] using hUno
  · simpa only [hSUright] using hUroot
  · simpa only [hSUright] using hUbody
  · simpa only [hSTright, hTUleft] using hTshape
  · simpa only [hSUright] using hUshape
  · simpa only [hTUleft] using hUpperTroot

#print axioms inside_strict_last_pivot_start

end Erdos591.Positive.Game.Payoff
