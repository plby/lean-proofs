import ErdosProblems.Erdos591.ReservedLateInsertion
import ErdosProblems.Erdos591.DeferredUpperRequest
import ErdosProblems.Erdos591.PairedMarkerRequests
import ErdosProblems.Erdos591.ManagedPool
import ErdosProblems.Erdos591.ReachableRootCard
import ErdosProblems.Erdos591.InsideSingletonMiddleBridge

/-!
# Join the reserved late-marker opening to both checked middle bridges

Every winning assertion on the original pool is recovered from an actual
path from its winning origin. The tail subpool is used for the paired
marker response, not assumed to contain arbitrary original-pool moves.
The upper U label is split into singleton and nonsingleton only after
its previously reserved response has actually been submitted.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_late_insertion_triangle {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    (origin old upperOrigin : Concrete.Hist N) {B a c : ℕ} (L : LastLastLabels H B a)
    (ha : 2 ≤ a) (hwinOrigin : (exactGame N blue).ArchitectWins H b σ origin)
    (hopening : origin.position.pending = some ⟨false, .advance a⟩)
    (hboardOrigin : origin.position.board = Board.initial)
    (hmodeOrigin : origin.position.mode = some true)
    (hB : max origin.position.bound (b origin) ≤ B)
    (hfromOld : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (hfromUpper : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upperOrigin)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → lateFirstMarkerColor z = true)
    (hlarge : ∀ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q →
      q.position.pending = some ⟨false, .advance d⟩ → q.position.board.left.markerEvent = true →
      (∀ k ∈ q.position.board.left.rootLabel,
        k ≤ q.position.board.left.bodyLabels.length + 1) → 2 ≤ d)
    (hfirst : ∀ q v d, (exactGame N blue).FollowStep σ H b origin q →
      (exactGame N blue).FollowStep σ H b q v →
      v.position.pending = some ⟨false, .advance d⟩ → 2 ≤ d)
    (hpOld : old.position.pending = some ⟨false, .advance 0⟩)
    (hOldRoot : old.position.board.left.rootLabel = L.lower)
    (hOldBody : old.position.board.left.bodyLabels.length = L.penultimate)
    (hOldRel : old.position.board.left.relaxed = true)
    (hOldNo : old.position.board.left.NoLeafPending)
    (hTRel : old.position.board.right.relaxed = true)
    (hTLastBody : old.position.board.right.lastSelectedBody =
      old.position.board.right.bodyLabels.length)
    (hTLater : ∃ j ∈ old.position.board.right.currentLabel,
      old.position.board.right.leafIndex < j)
    (hpUpper : upperOrigin.position.pending = some ⟨true, .advance c⟩) (hc : 0 < c)
    (hUpperInit : upperOrigin.position.board.right = LabeledWord.initial)
    (hUpperMode : upperOrigin.position.mode = some true)
    (hT : LabeledWord.SameStructure old.position.board.right upperOrigin.position.board.left)
    (hUpperRel : upperOrigin.position.board.left.relaxed = true)
    (hTSecond : old.position.board.right.currentLabel.sup id ∈
        upperOrigin.position.board.left.currentLabel ∧
      ∀ j ∈ upperOrigin.position.board.left.currentLabel,
        old.position.board.right.leafIndex < j →
          old.position.board.right.currentLabel.sup id ≤ j)
    (hTFirst : ∀ i ∈ upperOrigin.position.board.left.rootLabel,
      upperOrigin.position.board.left.bodyLabels.length ≤ i)
    (hMT : ∃ M : Managed N H blue b σ false true LabeledWord.initial old.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target)
    {as : List (Finset ℕ × ℕ)}
    (hraw : (LabeledCode.rootCursor L.lower L.marker).runAtoms as = some old.position.board.left)
    (hinc : (L.marker :: as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ as.map Prod.snd, x ∈ H) : ¬ blue.CliqueFree 3 := by
  obtain ⟨J, hJH, hJ, hJfresh, fine, hfromFine, hwinFine, hmodeFine, hpFine,
      hFineRoot, hFineBody, hFineRel, hFineNo, hURel, hULastBody, hULater, _hUCard,
      frontAtoms, hfront, hfrontPool, MU, hMUfrom⟩ :=
    reserved_late_insertion hHN hH blue htri hroot origin old upperOrigin L hwinOrigin
      hopening hboardOrigin hmodeOrigin hB hfromUpper hall hlarge hfirst hOldBody hpUpper
      hc hUpperInit hUpperMode hraw hinc hpool
  have hwinUpper := hwinOrigin.of_reachable (exactGame N blue) hfromUpper
  obtain ⟨MUH, _hMUtarget, hMUHfrom⟩ := MU.widen_from hJH upperOrigin hwinUpper hMUfrom
  have hTstrict : old.position.board.right.leafIndex <
      old.position.board.right.currentLabel.sup id := by
    obtain ⟨j, hj, hlt⟩ := hTLater
    exact hlt.trans_le (Finset.le_sup (f := id) hj)
  have hTup : LabeledWord.UpToLeaf (old.position.board.right.currentLabel.sup id)
      upperOrigin.position.board.left :=
    ⟨(of_decide_eq_true hUpperRel).2.1, hTSecond.1, hT.leaf_eq ▸ hTstrict.le⟩
  obtain ⟨tu, hupperTU, hwinTU, _hmodeTU, hpTU, hTUleft, hTUcoords, hTUrel, hTUindex,
      _hTUsingle, hTUsecond⟩ :=
    MUH.fire_deferred_then_other_next hHN hH blue
      ((Position.history_dataInvariant fine).2.1 true).2 hURel hULastBody hULater hTup
      (hT.leaf_eq ▸ hTstrict) upperOrigin hMUHfrom
  have hUshape : LabeledWord.SameStructure tu.position.board.right fine.position.board.right := by
    obtain ⟨bs, hbs⟩ := History.word_run tu true
    obtain ⟨cs, hcs⟩ := History.word_run fine true
    exact LabeledWord.sameStructure_of_initial_runs hbs.run hcs.run hTUcoords
  have hbeforeOld : LabeledWord.BeforeBody L.pivot old.position.board.left :=
    ⟨hOldRoot ▸ L.pivot_lower, by simpa only [hOldBody] using L.penultimate_lt_pivot⟩
  have hnextOld : ∀ k ∈ old.position.board.left.rootLabel,
      old.position.board.left.bodyLabels.length < k → L.pivot ≤ k := by
    intro k hk hlt
    rcases L.lower_bounds k (hOldRoot ▸ hk) with heq | hle
    · exact heq.ge
    · rw [hOldBody] at hlt
      exact (not_lt_of_ge hle hlt).elim
  have hbeforeFine : LabeledWord.BeforeBody L.pivot fine.position.board.left :=
    ⟨hFineRoot ▸ L.pivot_upper,
      by simpa only [hFineBody] using L.upperPenultimate_lt_pivot⟩
  have hnextFine : ∀ k ∈ fine.position.board.left.rootLabel,
      fine.position.board.left.bodyLabels.length < k → L.pivot ≤ k := by
    intro k hk hlt
    rcases L.upper_bounds_penultimate k (hFineRoot ▸ hk) with heq | hle
    · exact heq.ge
    · rw [hFineBody] at hlt
      exact (not_lt_of_ge hle hlt).elim
  obtain ⟨st, su, d, e, hOldST, hFineSU, hpST, hpSU, _hd, _he, hS,
      hmST, hmSU, hiST, hiSU, hrST, hrSU, hoST, hoSU⟩ :=
    paired_next_marker_requests hHN hH hJH hJ blue old fine
      (hwinOrigin.of_reachable (exactGame N blue) hfromOld) hwinFine false false hpOld hpFine
      (LabeledWord.rootRelabel_sameStructure L.upper old.position.board.left).symm
      hfront hfrontPool hJfresh hOldRel hOldNo hbeforeOld hnextOld
      hFineRel hFineNo hbeforeFine hnextFine
  change st.position.board.right = old.position.board.right at hoST
  change su.position.board.right = fine.position.board.right at hoSU
  change st.position.board.left.rootLabel = old.position.board.left.rootLabel at hrST
  change su.position.board.left.rootLabel = fine.position.board.left.rootLabel at hrSU
  change st.position.board.left.bodyLabels.length + 1 = L.pivot at hiST
  change su.position.board.left.bodyLabels.length + 1 = L.pivot at hiSU
  have hFineSUH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) fine su :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hFineSU
  have hfromST := hfromOld.trans hOldST
  have hfromSU := hfromFine.trans hFineSUH
  have hrootST : ∀ i ∈ st.position.board.left.rootLabel,
      i ≤ st.position.board.left.bodyLabels.length + 1 := by
    intro i hi
    rw [hiST]
    exact L.lower_le_pivot i (by simpa [hrST, hOldRoot] using hi)
  have hrootSU : ∀ i ∈ su.position.board.left.rootLabel,
      i ≤ su.position.board.left.bodyLabels.length + 1 := by
    intro i hi
    rw [hiSU]
    exact (L.upper_bounds i (by simpa [hrSU, hFineRoot] using hi)).2
  have hd := hlarge st d hfromST hpST hmST hrootST
  have he := hlarge su e hfromSU hpSU hmSU hrootSU
  have hrootT : ∀ i ∈ st.position.board.right.rootLabel,
      i ≤ st.position.board.right.bodyLabels.length := by
    intro i hi
    rw [hoST] at hi ⊢
    rw [← hTLastBody]
    exact Finset.le_sup (f := id) hi
  have hrootU : ∀ i ∈ su.position.board.right.rootLabel,
      i ≤ su.position.board.right.bodyLabels.length := by
    intro i hi
    rw [hoSU] at hi ⊢
    rw [← hULastBody]
    exact Finset.le_sup (f := id) hi
  have hTcard : upperOrigin.position.board.left.rootLabel.card = a :=
    reachable_opening_root_card blue origin upperOrigin false (by omega) hopening
      (by simp [hboardOrigin, Board.initial, Board.get]) hfromUpper
      (LabeledWord.relaxed_ne_start
        ((Position.history_dataInvariant upperOrigin).2.1 false).1 hUpperRel)
  have hMTst : ∃ M : Managed N H blue b σ false true LabeledWord.initial st.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
    rw [hoST]
    exact hMT
  have hMUsu : ∃ M : Managed N H blue b σ true true upperOrigin.position.board.left
      su.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upperOrigin M.target := by
    rw [hoSU]
    exact ⟨MUH, hMUHfrom⟩
  have hTshape : LabeledWord.SameStructure tu.position.board.left st.position.board.right := by
    simpa only [hTUleft, hoST] using hT.symm
  have hUshape' : LabeledWord.SameStructure tu.position.board.right su.position.board.right := by
    simpa only [hoSU] using hUshape
  have hTup' : LabeledWord.UpToLeaf (st.position.board.right.currentLabel.sup id)
      tu.position.board.left := by simpa only [hTUleft, hoST] using hTup
  have hTstrict' : tu.position.board.left.leafIndex <
      st.position.board.right.currentLabel.sup id := by
    simpa only [hTUleft, hoST] using (hT.leaf_eq ▸ hTstrict)
  have hTnext : ∀ i ∈ tu.position.board.left.currentLabel,
      tu.position.board.left.leafIndex < i → st.position.board.right.currentLabel.sup id ≤ i := by
    simpa only [hTUleft, hoST, ← hT.leaf_eq] using hTSecond.2
  have hUstrict : su.position.board.right.leafIndex <
      su.position.board.right.currentLabel.sup id := by
    obtain ⟨j, hj, hlt⟩ := hULater
    simpa only [hoSU] using hlt.trans_le (Finset.le_sup (f := id) hj)
  by_cases hsingle : tu.position.board.right.currentLabel.card = 1
  · exact inside_singleton_middle_bridge_triangle hHN hH blue st su tu
      (hwinOrigin.of_reachable (exactGame N blue) hfromST)
      (hwinOrigin.of_reachable (exactGame N blue) hfromSU) hwinTU
      (follow_mode_some hfromST hmodeOrigin) (follow_mode_some hFineSUH hmodeFine)
      hd he hpST hpSU hmST hmSU hS hrootST hrootSU
      (by simpa only [hoST] using hTRel) (by simpa only [hoSU] using hURel)
      hrootT hrootU hpTU hTshape hTup' hTstrict' hTnext
      (by simpa only [hTUleft, hTcard] using ha)
      (by simpa only [hTUleft] using hTFirst)
      hUshape' hTUrel hsingle hUstrict origin upperOrigin hMTst hMUsu
  · have hcardPos : 0 < tu.position.board.right.currentLabel.card :=
      Finset.card_pos.mpr ⟨_, (of_decide_eq_true hTUrel).2.2⟩
    have hcard : 2 ≤ tu.position.board.right.currentLabel.card := by omega
    have hsecond := hTUsecond hcard
    have hUstrict' : tu.position.board.right.leafIndex <
        su.position.board.right.currentLabel.sup id := by
      simpa only [hTUindex, hoSU] using hUstrict
    have hUup : LabeledWord.UpToLeaf (su.position.board.right.currentLabel.sup id)
        tu.position.board.right :=
      ⟨(of_decide_eq_true hTUrel).2.1, by simpa only [hoSU] using hsecond.1, hUstrict'.le⟩
    have hUnext : ∀ i ∈ tu.position.board.right.currentLabel,
        tu.position.board.right.leafIndex < i → su.position.board.right.currentLabel.sup id ≤ i :=
      by simpa only [hTUindex, hoSU] using hsecond.2
    exact inside_two_middle_bridge_triangle hHN hH blue st su tu
      (hwinOrigin.of_reachable (exactGame N blue) hfromST)
      (hwinOrigin.of_reachable (exactGame N blue) hfromSU) hwinTU
      (follow_mode_some hfromST hmodeOrigin) (follow_mode_some hFineSUH hmodeFine)
      hd he hpST hpSU hmST hmSU hS hrootST hrootSU
      (by simpa only [hoST] using hTRel) (by simpa only [hoSU] using hURel)
      hrootT hrootU hpTU hTshape hTup' hTstrict' hTnext hUshape' hUup hUstrict' hUnext
      origin upperOrigin hMTst hMUsu

#print axioms inside_late_insertion_triangle

end Erdos591.Positive.Game.Payoff
