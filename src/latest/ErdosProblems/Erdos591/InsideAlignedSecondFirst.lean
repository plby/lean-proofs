import ErdosProblems.Erdos591.FirstSecondLabelChoice
import ErdosProblems.Erdos591.SharedFirstLeafHandoff
import ErdosProblems.Erdos591.InsideFirstLastSingleton
import ErdosProblems.Erdos591.InsideFirstLastNonsingleton

/-!
# Close the aligned bridge at its second paired last-body request

The three exact size identities and one common singleton alternative
are supplied by actual reachable requests. Choose the second pair of
body labels, submit its shared first leaf, and use the already checked
singleton or nonsingleton first/last ending.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_aligned_second_first_triangle {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (st su tu : Concrete.Hist N) {B C p q t r d e : ℕ}
    (S : FirstLastLabels H B p q)
    (TL : LastFirstLabels H C 1 t) (TV : LastFirstLabels H C 1 r)
    (hTfirst : TV.pivot = TL.pivot)
    (hTchoice : t = 1 ∨ (TL.pivot < TL.upper.sup id ∧ TL.upper.sup id ∈ TV.upper ∧
      ∀ i ∈ TV.upper, TL.pivot < i → TL.upper.sup id ≤ i))
    (hpSize : p = t + 1) (hqSize : q = d + 1) (hrSize : r = e + 1)
    (hd : 0 < d) (he : 0 < e)
    (hTD : t = 1 ↔ d = 1) (hDE : d = 1 ↔ e = 1)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    (hmodeST : st.position.mode = some true) (hmodeSU : su.position.mode = some true)
    (hpST : st.position.pending = some ⟨false, .advance 0⟩)
    (hpSU : su.position.pending = some ⟨true, .advance d⟩)
    (hpTU : tu.position.pending = some ⟨true, .advance e⟩)
    (hS : LabeledWord.SameStructure st.position.board.left su.position.board.left)
    (hrST : st.position.board.left.relaxed = true) (hrSU : su.position.board.left.relaxed = true)
    (hlabelST : st.position.board.left.currentLabel = S.lower)
    (hlabelSU : su.position.board.left.currentLabel = S.upper)
    (hindexST : st.position.board.left.leafIndex = S.first)
    (hindexSU : su.position.board.left.leafIndex = S.first)
    (hrootST : ∀ i ∈ st.position.board.left.rootLabel, i ≤ st.position.board.left.bodyLabels.length)
    (hrootSU : ∀ i ∈ su.position.board.left.rootLabel, i ≤ su.position.board.left.bodyLabels.length)
    (hT : LabeledWord.SameStructure st.position.board.right tu.position.board.left)
    (hrT : st.position.board.right.relaxed = true) (hrTV : tu.position.board.left.relaxed = true)
    (hlabelT : st.position.board.right.currentLabel = TL.upper)
    (hlabelTV : tu.position.board.left.currentLabel = TV.upper)
    (_hindexT : st.position.board.right.leafIndex = TL.pivot)
    (hindexTV : tu.position.board.left.leafIndex = TL.pivot)
    (hrootT : ∀ i ∈ st.position.board.right.rootLabel,
      i ≤ st.position.board.right.bodyLabels.length)
    (hU : LabeledWord.SameStructure su.position.board.right tu.position.board.right)
    (hmSU : su.position.board.right.markerEvent = true)
    (hmTU : tu.position.board.right.markerEvent = true)
    (hrootU : ∀ i ∈ su.position.board.right.rootLabel,
      i ≤ su.position.board.right.bodyLabels.length + 1) :
    ¬ blue.CliqueFree 3 := by
  let D := max (max su.position.bound (b su)) (max tu.position.bound (b tu))
  have hcompat : 2 ≤ d → 2 ≤ e := by
    intro hdLarge
    have hn : e ≠ 1 := fun h => by have := hDE.mpr h; omega
    omega
  obtain ⟨UL, UV, hUfirst, hUmarker, hUchoice⟩ :=
    first_second_label_choice hH D d e hd he hcompat
  have hSstrict : su.position.board.left.leafIndex < S.last := by
    rw [hindexSU]
    exact S.first_lt_last
  have hSup : LabeledWord.UpToLeaf S.last su.position.board.left :=
    ⟨(of_decide_eq_true hrSU).2.1, hlabelSU ▸ S.last_upper, hSstrict.le⟩
  have hTVstrict : tu.position.board.left.leafIndex < TV.upper.sup id := by
    rw [hindexTV, ← hTfirst]
    exact TV.pivot_lt_upper_sup (by omega)
  have hTVpending : Macro.Pending tu.position.board.left := Or.inr
    ⟨(of_decide_eq_true hrTV).2.1, TV.upper.sup id,
      by rw [hlabelTV]
         simpa using Finset.sup_mem_of_nonempty (f := id) ⟨_, TV.pivot_upper⟩, hTVstrict⟩
  obtain ⟨v, w, hSUv, hTUw, hpV, hpW, hUshape, hrV, hrW, hlV, hlW, hiV, hiW,
      hbV, _hbW, hrootV, _hrootW, hSsame, hTsame⟩ :=
    shared_first_leaf_handoff hHN hH blue su tu true UL UV hUfirst hUmarker
      hwinSU hwinTU hpSU hpTU hmSU hmTU hU hSup hSstrict hrTV hTVpending
      (le_max_left _ _) (le_max_right _ _)
  change w.position.board.left = tu.position.board.left at hTsame
  change w.position.pending = some ⟨false, .advance 0⟩ at hpW
  change LabeledWord.SameStructure v.position.board.right w.position.board.right at hUshape
  change w.position.board.right.relaxed = true at hrW
  change w.position.board.right.currentLabel = UV.upper at hlW
  change w.position.board.right.leafIndex = UL.pivot at hiW
  have hvRoot : ∀ i ∈ v.position.board.right.rootLabel,
      i ≤ v.position.board.right.bodyLabels.length := by
    simpa only [hrootV, hbV, List.length_append, List.length_singleton] using hrootU
  have hvS : LabeledWord.SameStructure st.position.board.left v.position.board.left := by
    simpa only [hSsame] using hS
  have hwT : LabeledWord.SameStructure st.position.board.right w.position.board.left := by
    simpa only [hTsame] using hT
  have hwinV := hwinSU.of_reachable (exactGame N blue) hSUv
  have hwinW := hwinTU.of_reachable (exactGame N blue) hTUw
  have hmodeV := follow_mode_some hSUv hmodeSU
  by_cases htOne : t = 1
  · have hdOne := hTD.mp htOne
    have singleton_exhausted (word : LabeledWord) (hrel : word.relaxed = true)
        (hcard : word.currentLabel.card = 1)
        (hroot : ∀ i ∈ word.rootLabel, i ≤ word.bodyLabels.length) :
        ¬ Macro.Pending word := by
      rintro (⟨i, hi, hlt⟩ | ⟨_, i, hi, hlt⟩)
      · exact not_lt_of_ge (hroot i hi) hlt
      · have heq := Finset.card_le_one.mp hcard.le i hi word.leafIndex
          (of_decide_eq_true hrel).2.2
        exact not_lt_of_ge heq.le hlt
    have hlastT := singleton_exhausted _ hrT (by rw [hlabelT, TL.upper_card, htOne]) hrootT
    have hlastU := singleton_exhausted _ hrV (by rw [hlV, UL.upper_card, hdOne]) hvRoot
    exact inside_first_last_singleton_triangle hHN hH blue st v w S
      (by omega) (by omega) hwinST hwinV hwinW hmodeST hmodeV hpST hpV hvS hrST
      (by simpa only [hSsame] using hrSU) hlabelST (by simpa only [hSsame] using hlabelSU)
      hindexST (by simpa only [hSsame] using hindexSU) hrootST
      (by simpa only [hSsame] using hrootSU) hrT hrV hlastT hlastU hwT hUshape
  · have hdNot : d ≠ 1 := fun h => htOne (hTD.mpr h)
    obtain ⟨hTstrict, hTmem, hTnext⟩ := hTchoice.resolve_left htOne
    obtain ⟨hUstrict, hUmem, hUnext⟩ := hUchoice.resolve_left hdNot
    have htPos : 0 < t := by
      rw [← TL.upper_card]
      exact Finset.card_pos.mpr ⟨_, TL.pivot_upper⟩
    have hTup : LabeledWord.UpToLeaf (st.position.board.right.currentLabel.sup id)
        w.position.board.left := by
      refine ⟨?_, ?_, ?_⟩
      · simpa only [hTsame] using (of_decide_eq_true hrTV).2.1
      · simpa only [hTsame, hlabelT, hlabelTV] using hTmem
      · simpa only [hTsame, hindexTV, hlabelT] using hTstrict.le
    have hUup : LabeledWord.UpToLeaf (v.position.board.right.currentLabel.sup id)
        w.position.board.right :=
      ⟨(of_decide_eq_true hrW).2.1, by simpa only [hlV, hlW] using hUmem,
        by simpa only [hiW, hlV] using hUstrict.le⟩
    exact inside_first_last_nonsingleton_triangle hHN hH blue st v w S
      (by omega) (by omega) hwinST hwinV hwinW hmodeST hmodeV hpV hpW hvS hrST
      (by simpa only [hSsame] using hrSU) hlabelST (by simpa only [hSsame] using hlabelSU)
      hindexST (by simpa only [hSsame] using hindexSU) hrootST
      (by simpa only [hSsame] using hrootSU) hrT hrV hrootT hvRoot hwT.symm hTup
      (by simpa only [hTsame, hindexTV, hlabelT] using hTstrict)
      (by simpa only [hTsame, hindexTV, hlabelT, hlabelTV] using hTnext)
      hUshape.symm hUup (by simpa only [hiW, hlV] using hUstrict)
      (by simpa only [hiW, hlV, hlW] using hUnext)

#print axioms inside_aligned_second_first_triangle

end Erdos591.Positive.Game.Payoff
