import ErdosProblems.Erdos591.ReservedAlignedCheckpoint
import ErdosProblems.Erdos591.CommonLastMarkerRequests
import ErdosProblems.Erdos591.FirstLastBodyOpening

/-!
# The three aligned plays with both lower last-body first leaves submitted

The inserted play is first constructed on its reserved fresh tail.
Its actual path is lifted to the original pool before applying the
uniform last-body size bound. Only then are the common-first/common-last
labels chosen. The lower opposite requests remain pending.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_aligned_last_start {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    (origin old upperOrigin : Concrete.Hist N) {B a c C e : ℕ}
    (L : LastLastLabels H B a) (T : AlignedRootLabels H C e a) (ha : 2 ≤ a) (hc : 2 ≤ c)
    (hwinOrigin : (exactGame N blue).ArchitectWins H b σ origin)
    (hopening : origin.position.pending = some ⟨false, .advance a⟩)
    (hboardOrigin : origin.position.board = Board.initial)
    (hmodeOrigin : origin.position.mode = some true)
    (hB : max origin.position.bound (b origin) ≤ B)
    (hfromOld : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (hfromUpper : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upperOrigin)
    (hpOld : old.position.pending = some ⟨false, .advance 0⟩)
    (hOldRoot : old.position.board.left.rootLabel = L.lower)
    (hOldBody : old.position.board.left.bodyLabels.length = L.penultimate)
    (hOldRel : old.position.board.left.relaxed = true)
    (hOldNo : old.position.board.left.NoLeafPending)
    (hTrel : old.position.board.right.relaxed = true)
    (hTno : old.position.board.right.NoLeafPending)
    (hTroot : old.position.board.right.rootLabel = T.lower)
    (hTbody : old.position.board.right.bodyLabels.length = T.shared)
    (hTshape : LabeledWord.SameStructure old.position.board.right upperOrigin.position.board.left)
    (hUpperTroot : upperOrigin.position.board.left.rootLabel = T.upper)
    (hpUpper : upperOrigin.position.pending = some ⟨true, .advance c⟩)
    (hUpperInit : upperOrigin.position.board.right = LabeledWord.initial)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true)
    (hlarge : ∀ v d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin v →
      v.position.pending = some ⟨false, .advance d⟩ → v.position.board.left.markerEvent = true →
      (∀ k ∈ v.position.board.left.rootLabel,
        k ≤ v.position.board.left.bodyLabels.length + 1) → 2 ≤ d)
    {as : List (Finset ℕ × ℕ)}
    (hraw : (LabeledCode.rootCursor L.lower L.marker).runAtoms as = some old.position.board.left)
    (hinc : (L.marker :: as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ as.map Prod.snd, x ∈ H) :
    ∃ J, J ⊆ H ∧ J.Infinite ∧ ∃ CU f, ∃ U : AlignedRootLabels J CU f c,
      ∃ D p q, ∃ S : FirstLastLabels H D p q, 2 ≤ p ∧ 2 ≤ q ∧ ∃ st su tu,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin st ∧
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin su ∧
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin tu ∧
        st.position.pending = some ⟨true, .advance 0⟩ ∧
        su.position.pending = some ⟨true, .advance 0⟩ ∧ tu.position.pending = none ∧
        LabeledWord.SameStructure st.position.board.left su.position.board.left ∧
        st.position.board.left.relaxed = true ∧ su.position.board.left.relaxed = true ∧
        st.position.board.left.currentLabel = S.lower ∧
        su.position.board.left.currentLabel = S.upper ∧
        st.position.board.left.leafIndex = S.first ∧ su.position.board.left.leafIndex = S.first ∧
        (∀ k ∈ st.position.board.left.rootLabel, k ≤ st.position.board.left.bodyLabels.length) ∧
        (∀ k ∈ su.position.board.left.rootLabel, k ≤ su.position.board.left.bodyLabels.length) ∧
        st.position.board.right.relaxed = true ∧ st.position.board.right.NoLeafPending ∧
        st.position.board.right.rootLabel = T.lower ∧
        st.position.board.right.bodyLabels.length = T.shared ∧
        su.position.board.right.relaxed = true ∧ su.position.board.right.NoLeafPending ∧
        su.position.board.right.rootLabel = U.lower ∧
        su.position.board.right.bodyLabels.length = U.shared ∧
        LabeledWord.SameStructure st.position.board.right tu.position.board.left ∧
        LabeledWord.SameStructure su.position.board.right tu.position.board.right ∧
        tu.position.board.left.rootLabel = T.upper ∧
        tu.position.board.right.rootLabel = U.upper ∧
        tu.position.board.right.relaxed = true ∧
        (∀ x ∈ tu.position.board.left.coordinates,
          x ≤ tu.position.board.right.coordinates.getLastD 0) := by
  obtain ⟨J, hJH, hJ, hJfresh, CU, f, d, U, hdc, fine, tu, hfromFine, hfromTU,
      hwinFine, hpFine, hFineRoot, hFineBody, hFineRel, hFineNo, hUrel, hUno, hUroot,
      hUbody, hnTU, hTUleft, hUshape, hTUrel, hTUroot, _hTUbody, _hTUmode, hTUsep,
      frontAtoms, hfront, hfrontPool⟩ :=
    reserved_aligned_checkpoint hHN hH blue htri hroot origin old upperOrigin L ha hc
      hwinOrigin hopening hboardOrigin hmodeOrigin hB hfromUpper hOldBody hpUpper
      hUpperInit hall hraw hinc hpool
  subst d
  obtain ⟨v, w, p, q, hOldV, hFineW, hpV, hpW, _hposP, _hposQ, hS,
      hmV, hmW, _hiV, _hiW, _hrV, _hrW, hrootV, hrootW, hotherV, hotherW⟩ :=
    common_last_marker_requests hHN hH hJH hJ blue old fine L
      (hwinOrigin.of_reachable (exactGame N blue) hfromOld) hwinFine hpOld hpFine
      hOldRoot hOldBody hOldRel hOldNo hFineRoot hFineBody hFineRel hFineNo
      hfront hfrontPool hJfresh
  have hFineWH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) fine w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hFineW
  have hfromV := hfromOld.trans hOldV
  have hfromW := hfromFine.trans hFineWH
  have hpLarge := hlarge v p hfromV hpV hmV hrootV
  have hqLarge := hlarge w q hfromW hpW hmW hrootW
  let D := max (max v.position.bound (b v)) (max w.position.bound (b w))
  obtain ⟨S⟩ := FirstLastLabels.exists_of_infinite hH D p q hpLarge hqLarge
  have hbeforeT : LabeledWord.BeforeBody T.last v.position.board.right := by
    rw [hotherV]
    exact ⟨hTroot ▸ T.last_lower, by simpa only [hTbody] using T.shared_lt_last⟩
  have hbeforeU : LabeledWord.BeforeBody U.last w.position.board.right := by
    rw [hotherW]
    exact ⟨hUroot ▸ U.last_lower, by simpa only [hUbody] using U.shared_lt_last⟩
  obtain ⟨st, su, hVST, hWSU, hpST, hpSU, hSshape, hSTrel, hSUrel, hSTcurrent,
      hSUcurrent, hSTindex, hSUindex, hSTroot, hSUroot, hSTother, hSUother, _hprefix⟩ :=
    first_last_body_opening hHN hH blue v w S
      (hwinOrigin.of_reachable (exactGame N blue) hfromV)
      (hwinOrigin.of_reachable (exactGame N blue) hfromW) hpV hpW hmV hmW hS hrootV hrootW
      (by simpa only [hotherV] using hTrel) (by simpa only [hotherW] using hUrel)
      hbeforeT hbeforeU (le_max_left _ _) (le_max_right _ _)
  have hSTright := hSTother.trans hotherV
  have hSUright := hSUother.trans hotherW
  refine ⟨J, hJH, hJ, CU, f, U, D, p, q, S, hpLarge, hqLarge, st, su, tu,
    hfromV.trans hVST, hfromW.trans hWSU, hfromTU, hpST, hpSU, hnTU, hSshape,
    hSTrel, hSUrel, hSTcurrent, hSUcurrent, hSTindex, hSUindex, hSTroot, hSUroot,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hTUroot, hTUrel, hTUsep⟩
  · simpa only [hSTright] using hTrel
  · simpa only [hSTright] using hTno
  · exact (congrArg LabeledWord.rootLabel hSTright).trans hTroot
  · simpa only [hSTright] using hTbody
  · simpa only [hSUright] using hUrel
  · simpa only [hSUright] using hUno
  · exact (congrArg LabeledWord.rootLabel hSUright).trans hUroot
  · simpa only [hSUright] using hUbody
  · simpa only [hSTright, hTUleft] using hTshape
  · simpa only [hSUright] using hUshape
  · simpa only [hTUleft] using hUpperTroot

#print axioms inside_aligned_last_start

end Erdos591.Positive.Game.Payoff
