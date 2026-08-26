import ErdosProblems.Erdos591.AlignedCriticalOpening
import ErdosProblems.Erdos591.PrepareAlignedRoot
import ErdosProblems.Erdos591.AlignedRootSize
import ErdosProblems.Erdos591.LastLastLabels

/-!
# The first two actual plays in the aligned inside construction

Choose the second word's root overlaps only after its actual root
request. Its upper first body is the lower penultimate body. The paired
critical history leaves the first word's last-marker response pending,
and obtains the actual upper second-root request of size at least two.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_aligned_early_histories {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    (origin st : Concrete.Hist N) {B a : ℕ} (L : LastLastLabels H B a) (ha : 2 ≤ a)
    (hwinOrigin : (exactGame N blue).ArchitectWins H b σ origin)
    (hopening : origin.position.pending = some ⟨false, .advance a⟩)
    (hboardOrigin : origin.position.board = Board.initial)
    (hmodeOrigin : origin.position.mode = some true)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin st)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true)
    (hpST : st.position.pending = none) (hTinit : st.position.board.right = LabeledWord.initial)
    (hSrel : st.position.board.left.relaxed = true)
    (hSroot : st.position.board.left.rootLabel = L.lower) :
    ∃ C e, ∃ T : AlignedRootLabels H C e a, ∃ old upper c, 2 ≤ e ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) st old ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upper ∧
      old.position.pending = some ⟨false, .advance 0⟩ ∧
      old.position.board.left.rootLabel = L.lower ∧
      old.position.board.left.bodyLabels.length = L.penultimate ∧
      old.position.board.left.relaxed = true ∧ old.position.board.left.NoLeafPending ∧
      old.position.board.right.relaxed = true ∧ old.position.board.right.NoLeafPending ∧
      old.position.board.right.rootLabel = T.lower ∧
      old.position.board.right.bodyLabels.length = T.shared ∧
      upper.position.pending = some ⟨true, .advance c⟩ ∧ 2 ≤ c ∧
      upper.position.board.right = LabeledWord.initial ∧ upper.position.mode = some true ∧
      LabeledWord.SameStructure old.position.board.right upper.position.board.left ∧
      upper.position.board.left.relaxed = true ∧ upper.position.board.left.rootLabel = T.upper ∧
      upper.position.board.left.bodyLabels.length = T.shared ∧
      (∀ k ∈ upper.position.board.left.rootLabel,
        upper.position.board.left.bodyLabels.length ≤ k) := by
  have hwinST := hwinOrigin.of_reachable (exactGame N blue) hfrom
  obtain ⟨stR, e, hSTrequest, hSTboard, hpR, he⟩ :=
    winning_initial_right_request hHN hH blue htri hroot hwinST hpST hTinit hSrel
  have htoR := hfrom.tail hSTrequest
  have heLarge := aligned_pending_right_root_large hHN hH blue origin stR ha he hopening
    hboardOrigin hmodeOrigin hwinOrigin htoR hpR
    (by simpa only [hSTboard] using hTinit) hall
  let C := max (max stR.position.bound (b stR)) (max origin.position.bound (b origin))
  obtain ⟨T⟩ := AlignedRootLabels.exists_of_infinite hH C e a heLarge ha
  obtain ⟨v, hRV, _hvn, _hvm, hvOther, R, hRt, hRs, _hRL, hRlower, hRupper, hRshared⟩ :=
    prepare_aligned_root hHN hH blue hwinOrigin true false T hpR hopening
      (by simpa only [hSTboard, Board.get] using hTinit)
      (by simp [hboardOrigin, Board.initial, Board.get]) (le_max_left _ _) (le_max_right _ _)
  have hstv := (Relation.ReflTransGen.single hSTrequest).tail hRV
  have hSsame : v.position.board.left = st.position.board.left := by
    simpa only [hSTboard, Board.get, Bool.not_true] using hvOther
  have hRfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin R.target := by
    rw [hRt]
  have hpos : 0 < v.position.board.left.coordinates.length := by
    rw [hSsame]
    obtain ⟨as, has⟩ := History.word_run st false
    exact has.relaxed_coordinates_pos hSrel
  obtain ⟨old, tu, hvOld, hTU, hpOld, hOldRel, hOldBefore, hOldPen, hOldNo, hTRel,
      hTroot, hTbody, hTno, hnTU, hshape, hTUrel, hTUroot, hTUbody, hTUfirst, hTUother,
      hTUmode, _hTUsep⟩ :=
    aligned_critical_opening hHN hH blue origin v R (by omega) hopening hboardOrigin
      hmodeOrigin hwinOrigin (hfrom.trans hstv) hRfrom hpos hall
  have hstOld := hstv.trans hvOld
  have hSstart := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant st).2.1 false).1 hSrel
  obtain ⟨as, has, _⟩ := follow_word_inputs_above_bound hstOld false
  have hOldRoot : old.position.board.left.rootLabel = L.lower :=
    (has.rootLabel_eq hSstart).trans hSroot
  have hOldLast : old.position.board.left.lastSelectedBody = L.pivot := by
    rw [LabeledWord.lastSelectedBody, hOldRoot, L.lower_sup]
  have hOldBody : old.position.board.left.bodyLabels.length = L.penultimate := by
    have hselected : old.position.board.left.bodyLabels.length ∈ L.lower :=
      hOldRoot ▸ (of_decide_eq_true hOldRel).2.1
    have hle := (L.lower_bounds _ hselected).resolve_left
      (by simpa only [hOldLast] using ne_of_lt hOldBefore)
    have hge := hOldPen L.penultimate (hOldRoot ▸ L.penultimate_lower)
      (by simpa only [hOldLast] using L.penultimate_lt_pivot)
    omega
  have hTUinit : tu.position.board.right = LabeledWord.initial := by
    simpa [hRs, hRt, hboardOrigin, Board.initial, Board.get] using hTUother
  obtain ⟨upper, c, hTUrequest, hTUboard, hpUpper, hc⟩ :=
    winning_initial_right_request hHN hH blue htri hroot
      (hwinOrigin.of_reachable (exactGame N blue) hTU) hnTU hTUinit
      (by simpa only [hRs, Board.get] using hTUrel)
  have htoUpper := hTU.tail hTUrequest
  have hcLarge := aligned_pending_right_root_large hHN hH blue origin upper ha hc hopening
    hboardOrigin hmodeOrigin hwinOrigin htoUpper hpUpper
    (by simpa only [hTUboard] using hTUinit) hall
  refine ⟨C, e, T, old, upper, c, heLarge, hstOld, htoUpper, hpOld, hOldRoot, hOldBody,
    hOldRel, hOldNo, hTRel, hTno, ?_, ?_, hpUpper, hcLarge,
    by simpa only [hTUboard] using hTUinit,
    follow_mode_some (Relation.ReflTransGen.single hTUrequest) hTUmode, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hRlower] using hTroot
  · simpa only [hRshared] using hTbody
  · simpa only [hTUboard, hRs, Board.get] using hshape
  · simpa only [hTUboard, hRs, Board.get] using hTUrel
  · simpa only [hTUboard, hRs, Board.get, hRupper] using hTUroot
  · simpa only [hTUboard, hRs, Board.get, hRshared] using hTUbody
  · simpa only [hTUboard, hRs, Board.get] using hTUfirst

#print axioms inside_aligned_early_histories

end Erdos591.Positive.Game.Payoff
