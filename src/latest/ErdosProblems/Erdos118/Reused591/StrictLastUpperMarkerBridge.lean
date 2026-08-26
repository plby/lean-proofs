import ErdosProblems.Erdos118.Reused591.ReachCriticalCheckpoint
import ErdosProblems.Erdos118.Reused591.LocalizedCheckpoint
import ErdosProblems.Erdos118.Reused591.PairedMarkerRequests
import ErdosProblems.Erdos118.Reused591.FreshLeafNextMarker

namespace Erdos118.Reused591

/-!
# The first shared marker in the strict last-critical-leaf upper bridge

The upper play reaches its critical checkpoint on a tail above both
paused lower bounds. Its first word then reaches its last selected body,
and that whole prefix is replayed in the old lower play. Both actual
positive body requests are issued. The second word stays at its last
critical leaf, immediately before the spliced root's upper anchor.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem strict_last_upper_marker_bridge {N H HU : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (old tu : Concrete.Hist N) {BU e g j k i : ℕ}
    (U : SplicedRootLabels HU BU e g j (k + 1))
    (hwinOld : (exactGame N blue).ArchitectWins H b σ old)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    (hpOld : old.position.pending = some ⟨true, .advance 0⟩)
    (hrelOld : old.position.board.right.relaxed = true)
    (hnoOld : old.position.board.right.NoLeafPending)
    (hbeforeOld : LabeledWord.BeforeBody i old.position.board.right)
    (hnextOld : ∀ m ∈ old.position.board.right.rootLabel,
      old.position.board.right.bodyLabels.length < m → i ≤ m)
    (hT : LabeledWord.SameStructure old.position.board.right tu.position.board.left)
    (hTlast : tu.position.board.left.lastSelectedBody = i)
    (hnTU : tu.position.pending = none) (hUrel : tu.position.board.right.relaxed = true)
    (hUroot : tu.position.board.right.rootLabel = U.upper)
    (hmode : tu.position.mode = some true)
    (hTUsep : ∀ x ∈ tu.position.board.left.coordinates,
      x ≤ tu.position.board.right.coordinates.getLastD 0)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) tu z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) tu z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = true)
    (B : ℕ) (hB : max old.position.bound (b old) ≤ B) :
    ∃ J, J ⊆ H ∧ J.Infinite ∧ (∀ x ∈ J, B < x) ∧ ∃ st upper d r,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old st ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) tu upper ∧
      (exactGame N blue).ArchitectWins J b σ upper ∧
      st.position.pending = some ⟨true, .advance d⟩ ∧
      upper.position.pending = some ⟨false, .advance r⟩ ∧ 0 < d ∧ 0 < r ∧
      LabeledWord.SameStructure st.position.board.right upper.position.board.left ∧
      st.position.board.right.markerEvent = true ∧ upper.position.board.left.markerEvent = true ∧
      st.position.board.right.bodyLabels.length + 1 = i ∧
      upper.position.board.left.bodyLabels.length + 1 = i ∧
      st.position.board.right.rootLabel = old.position.board.right.rootLabel ∧
      upper.position.board.left.rootLabel = tu.position.board.left.rootLabel ∧
      st.position.board.left = old.position.board.left ∧
      upper.position.board.right.relaxed = true ∧ upper.position.board.right.NoLeafPending ∧
      upper.position.board.right.rootLabel = U.upper ∧
      LabeledWord.BeforeBody U.anchor upper.position.board.right ∧
      (∀ m ∈ upper.position.board.right.rootLabel,
        upper.position.board.right.bodyLabels.length < m → U.anchor ≤ m) ∧
      (upper.position.board.right.rootLabel.filter
        (fun m => m ≤ upper.position.board.right.bodyLabels.length)).card = k ∧
      ∃ frontU, LabeledWord.LegalRun tu.position.board.right frontU upper.position.board.right ∧
        ∀ atom ∈ frontU, atom.2 ∈ H ∧ B < atom.2 := by
  let J := H \ Set.Iic B
  have hJH : J ⊆ H := fun _ hx => hx.1
  have hJ : J.Infinite := hH.sdiff (Set.finite_Iic B)
  have hJfresh : ∀ x ∈ J, B < x := fun _ hx => lt_of_not_ge hx.2
  have pathH {v w : Concrete.Hist N}
      (hp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hp
  have hpos : 0 < tu.position.board.left.coordinates.length := by
    obtain ⟨as, has⟩ := History.word_run old true
    simpa only [← hT.coordinates_eq, Board.get] using has.relaxed_coordinates_pos hrelOld
  have hwinJ := hwinTU.mono (exactGame N blue) hJH (fun _ => le_rfl)
  have hrelT := (winning_overtaken_other_relaxed (hJH.trans hHN) hJ blue hwinJ true
    hUrel hpos hTUsep).1
  have hbeforeT : tu.position.board.left.bodyLabels.length <
      tu.position.board.left.lastSelectedBody := by
    rw [hTlast, ← hT.body_length]
    exact hbeforeOld.2
  obtain ⟨q, hTUq, _hqn, hq⟩ := winning_reach_critical_checkpoint (hJH.trans hHN) hJ blue
    hwinJ hnTU hrelT hUrel hbeforeT hTUsep
  have hwinQ := hwinJ.of_reachable (exactGame N blue) hTUq
  obtain ⟨hUrank, hUno⟩ := hq.localized_body_last (hJH.trans hHN) hJ blue hwinQ
    (follow_mode_some hTUq hmode)
    (fun z w hp hz => hfixed z w (pathH (hTUq.trans hp)) hz)
    (fun z w hp hz => hlast z w (pathH (hTUq.trans hp)) hz)
  have hlastmem : q.position.board.left.lastSelectedBody ∈ q.position.board.left.rootLabel := by
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id)
      ⟨_, (of_decide_eq_true hq.left_relaxed).2.1⟩
  obtain ⟨v, hqv, hVboard, hpV⟩ := winning_next_body_after_fresh_leaf
    (hJH.trans hHN) hJ blue hwinQ true hq.right_relaxed hq.separation hq.left_relaxed
      ⟨hlastmem, hq.left_before⟩
  have hTUv := hTUq.trans hqv
  have hwinV := hwinJ.of_reachable (exactGame N blue) hTUv
  have hV := hq.of_board_eq hVboard
  obtain ⟨frontT, hfrontT, hpoolT⟩ := follow_word_inputs hTUv 0 (fun _ => Nat.zero_le _) false
  obtain ⟨frontU, hfrontU, hpoolU⟩ := follow_word_inputs hTUv 0 (fun _ => Nat.zero_le _) true
  have hstartOld := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant old).2.1 true).1 hrelOld
  have hstartTU : tu.position.board.left.parser ≠ .start :=
    fun hs => hstartOld (hT.parser_eq.trans hs)
  have hVroot : v.position.board.left.rootLabel = tu.position.board.left.rootLabel :=
    hfrontT.rootLabel_eq hstartTU
  have hVlast : v.position.board.left.lastSelectedBody = i := by
    simpa only [LabeledWord.lastSelectedBody, hVroot] using hTlast
  have hVmem : i ∈ v.position.board.left.rootLabel := by
    rw [← hVlast]
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id)
      ⟨_, (of_decide_eq_true hV.left_relaxed).2.1⟩
  have hVbefore : LabeledWord.BeforeBody i v.position.board.left :=
    ⟨hVmem, by simpa only [hVlast] using hV.left_before⟩
  have hVnext : ∀ m ∈ v.position.board.left.rootLabel,
      v.position.board.left.bodyLabels.length < m → i ≤ m := by
    intro m hm hlt
    by_contra hn
    have hle := hV.left_penultimate m hm (by simpa only [hVlast] using lt_of_not_ge hn)
    omega
  have hVUroot : v.position.board.right.rootLabel = U.upper :=
    (hfrontU.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant tu).2.1 true).1 hUrel)).trans hUroot
  have hVUrank : (v.position.board.right.rootLabel.filter
      (fun m => m ≤ v.position.board.right.bodyLabels.length)).card = k := by
    simpa only [hVboard] using hUrank
  have hVUno : v.position.board.right.NoLeafPending := by simpa only [hVboard] using hUno
  have hVU := spliced_next_body_of_rank U v.position.board.right hVUroot hVUrank
  obtain ⟨st, upper, d, r, hOldST, hVupper, hpST, hpUpper, hd, hr, hshape, hmST, hmUpper,
      hiST, hiUpper, hrootST, hrootUpper, hSTother, hUpperOther⟩ :=
    paired_next_marker_requests hHN hH hJH hJ blue old v hwinOld hwinV true false
      hpOld hpV hT hfrontT
      (fun atom hatom =>
        ⟨hJH (hpoolT atom hatom).1, hB.trans_lt (hJfresh atom.2 (hpoolT atom hatom).1)⟩)
      (fun x hx => hB.trans_lt (hJfresh x hx)) hrelOld hnoOld hbeforeOld hnextOld
      hV.left_relaxed hV.left_exhausted hVbefore hVnext
  change upper.position.board.right = v.position.board.right at hUpperOther
  change upper.position.board.left.rootLabel = v.position.board.left.rootLabel at hrootUpper
  refine ⟨J, hJH, hJ, hJfresh, st, upper, d, r, hOldST, hTUv.trans hVupper,
    hwinV.of_reachable (exactGame N blue) hVupper, hpST, hpUpper, hd, hr, hshape,
    hmST, hmUpper, hiST, hiUpper, hrootST, hrootUpper.trans hVroot, hSTother,
    ?_, ?_, ?_, ?_, ?_, ?_, frontU, ?_, ?_⟩
  · simpa only [hUpperOther] using hV.right_relaxed
  · simpa only [hUpperOther] using hVUno
  · exact hUpperOther ▸ hVUroot
  · simpa only [hUpperOther] using hVU.1
  · simpa only [hUpperOther] using hVU.2
  · simpa only [hUpperOther] using hVUrank
  · simpa only [hUpperOther, Board.get] using hfrontU
  · intro atom hatom
    exact ⟨hJH (hpoolU atom hatom).1, hJfresh atom.2 (hpoolU atom hatom).1⟩

#print axioms strict_last_upper_marker_bridge

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
