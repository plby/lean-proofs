import ErdosProblems.Erdos118.Reused591.ReachCriticalCheckpoint
import ErdosProblems.Erdos118.Reused591.LocalizedNonlastCheckpoint
import ErdosProblems.Erdos118.Reused591.PairedMarkerRequests
import ErdosProblems.Erdos118.Reused591.FreshLeafNextMarker
import ErdosProblems.Erdos118.Reused591.CriticalPreliminaryRequestBound

namespace Erdos118.Reused591

/-!
# The nonlast rank-one upper bridge to the common T-body marker

Only the upper play advances until its critical checkpoint. Its fixed
rank one keeps U in the same first body; its nonlast color keeps a
selected leaf unread. Replay the T prefix in the pending lower play
and retain the whole U prefix above both original lower bounds.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem strict_nonlast_rank_one_marker_bridge {N H0 H HU : Set ℕ}
    (hH0N : H0 ⊆ N) (hHH0 : H ⊆ H0) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin old tu : Concrete.Hist N) {a BU e g j i : ℕ}
    (U : SeparatedRootLabels HU BU e g j)
    (ha : 2 ≤ a) (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial)
    (hStartMode : origin.position.mode = some true)
    (hwinOrigin : (exactGame N blue).ArchitectWins H0 b σ origin)
    (hfromTU : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin tu)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
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
    (hTrel : tu.position.board.left.relaxed = true)
    (hUrel : tu.position.board.right.relaxed = true)
    (hUroot : tu.position.board.right.rootLabel = U.upper)
    (hUbody : tu.position.board.right.bodyLabels.length = U.first)
    (hmode : tu.position.mode = some true)
    (hTsep : ∀ x ∈ tu.position.board.right.coordinates,
      x ≤ tu.position.board.left.coordinates.getLastD 0)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) tu z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = 1)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) tu z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false)
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
      upper.position.board.right.relaxed = true ∧
      upper.position.board.right.rootLabel = U.upper ∧
      upper.position.board.right.bodyLabels = tu.position.board.right.bodyLabels ∧
      upper.position.board.right.bodyLabels.length = U.first ∧
      upper.position.board.right.currentLabel = tu.position.board.right.currentLabel ∧
      upper.position.board.right.leafIndex < tu.position.board.right.currentLabel.sup id ∧
      (upper.position.board.right.rootLabel.filter
        (fun m => m ≤ upper.position.board.right.bodyLabels.length)).card = 1 ∧
      (∀ m ∈ upper.position.board.left.rootLabel,
        m ≤ upper.position.board.left.bodyLabels.length + 1) ∧
      0 < upper.position.board.right.currentLabel.card -
        (upper.position.board.right.currentLabel.filter
          (fun x => x ≤ upper.position.board.right.leafIndex)).card ∧
      upper.position.board.right.currentLabel.card -
        (upper.position.board.right.currentLabel.filter
          (fun x => x ≤ upper.position.board.right.leafIndex)).card + 2 ≤ r ∧
      ∃ checkpoint, CriticalCheckpoint checkpoint ∧
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) tu checkpoint ∧
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) checkpoint upper ∧
        upper.position.board.right = checkpoint.position.board.right ∧
      ∃ frontU, LabeledWord.LegalRun tu.position.board.right frontU upper.position.board.right ∧
        ∀ atom ∈ frontU, atom.2 ∈ H ∧ B < atom.2 := by
  have hHN := hHH0.trans hH0N
  let J := H \ Set.Iic B
  have hJH : J ⊆ H := fun _ hx => hx.1
  have hJ : J.Infinite := hH.sdiff (Set.finite_Iic B)
  have hJfresh : ∀ x ∈ J, B < x := fun _ hx => lt_of_not_ge hx.2
  have hJN := hJH.trans hHN
  have pathH {v w : Concrete.Hist N}
      (hp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hp
  have pathH0 {v w : Concrete.Hist N}
      (hp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) (hJH.trans hHH0)
        (fun _ => le_rfl) hs) _ _ hp
  have hwinJ := hwinTU.mono (exactGame N blue) hJH (fun _ => le_rfl)
  have hbeforeT : tu.position.board.left.bodyLabels.length <
      tu.position.board.left.lastSelectedBody := by
    rw [hTlast, ← hT.body_length]
    exact hbeforeOld.2
  have hTlastmem : tu.position.board.left.lastSelectedBody ∈
      tu.position.board.left.rootLabel := by
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id)
      ⟨_, (of_decide_eq_true hTrel).2.1⟩
  obtain ⟨first, hTUfirst, hFirstNone, hFirstUrel, hFirstOther, hFirstSep⟩ :=
    winning_next_opposite_leaf hJN hJ blue hwinJ false hTrel
      (by simpa only [Board.get, Bool.not_false] using hTsep)
      (Or.inl ⟨_, hTlastmem, hbeforeT⟩)
  simp only [Board.get, Bool.not_false] at hFirstUrel hFirstOther hFirstSep
  obtain ⟨q, hFirstQ, _hQNone, hQ⟩ := winning_reach_critical_checkpoint hJN hJ blue
    (hwinJ.of_reachable (exactGame N blue) hTUfirst) hFirstNone
    (by simpa only [hFirstOther] using hTrel) hFirstUrel
    (by simpa only [hFirstOther] using hbeforeT) hFirstSep
  have hTUq := hTUfirst.trans hFirstQ
  have hwinQ := hwinJ.of_reachable (exactGame N blue) hTUq
  obtain ⟨hUrank, hUnot⟩ := hQ.localized_body_nonlast hJN hJ blue hwinQ
    (follow_mode_some hTUq hmode)
    (fun z w hp hz => hfixed z w (pathH (hTUq.trans hp)) hz)
    (fun z w hp hz => hlast z w (pathH (hTUq.trans hp)) hz)
  have hlastmem : q.position.board.left.lastSelectedBody ∈ q.position.board.left.rootLabel := by
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id)
      ⟨_, (of_decide_eq_true hQ.left_relaxed).2.1⟩
  obtain ⟨v, hqv, hVboard, hpV⟩ := winning_next_body_after_fresh_leaf hJN hJ blue hwinQ
    true hQ.right_relaxed hQ.separation hQ.left_relaxed ⟨hlastmem, hQ.left_before⟩
  have hTUv := hTUq.trans hqv
  have hwinV := hwinJ.of_reachable (exactGame N blue) hTUv
  have hV := hQ.of_board_eq hVboard
  obtain ⟨frontT, hfrontT, hpoolT⟩ := follow_word_inputs hTUv 0 (fun _ => Nat.zero_le _) false
  obtain ⟨frontU, hfrontU, hpoolU⟩ := follow_word_inputs hTUv 0 (fun _ => Nat.zero_le _) true
  have hstartT := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant tu).2.1 false).1 hTrel
  have hstartU := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant tu).2.1 true).1 hUrel
  have hVroot : v.position.board.left.rootLabel = tu.position.board.left.rootLabel :=
    hfrontT.rootLabel_eq hstartT
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
    (hfrontU.rootLabel_eq hstartU).trans hUroot
  have hVUrank : (v.position.board.right.rootLabel.filter
      (fun m => m ≤ v.position.board.right.bodyLabels.length)).card = 1 := by
    simpa only [hVboard] using hUrank
  have hVUbody := U.current_first_of_rank_one v.position.board.right
    hV.right_relaxed hVUroot hVUrank
  have hVUlabels : v.position.board.right.bodyLabels = tu.position.board.right.bodyLabels :=
    ((hfrontU.bodyLabels_prefix hstartU).eq_of_length_le
      (by simp only [Board.get, hVUbody, hUbody, le_refl])).symm
  have hVUcurrent : v.position.board.right.currentLabel = tu.position.board.right.currentLabel := by
    simp only [LabeledWord.currentLabel, hVUlabels]
  have hVUindex : v.position.board.right.leafIndex <
      tu.position.board.right.currentLabel.sup id := by
    by_contra hn
    apply hUnot
    intro x hx
    have hvx : x ∈ v.position.board.right.currentLabel := by simpa only [hVboard] using hx
    have hle : x ≤ tu.position.board.right.currentLabel.sup id :=
      Finset.le_sup (f := id) (hVUcurrent ▸ hvx)
    simpa only [hVboard] using hle.trans (le_of_not_gt hn)
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
  change upper.position.board.left.bodyLabels.length + 1 = i at hiUpper
  have hRootLast : ∀ m ∈ upper.position.board.left.rootLabel,
      m ≤ upper.position.board.left.bodyLabels.length + 1 := by
    intro m hm
    have hmem : m ∈ tu.position.board.left.rootLabel := (hrootUpper.trans hVroot) ▸ hm
    have hle : m ≤ tu.position.board.left.lastSelectedBody := Finset.le_sup (f := id) hmem
    simpa only [hiUpper, hTlast] using hle
  have hbound := critical_preliminary_request_bound hH0N (hJH.trans hHH0) hJ blue origin q upper ha
    hop hboard hStartMode hwinOrigin (hfromTU.trans (pathH0 hTUq))
      (pathH0 (hqv.trans hVupper)) hQ hpUpper hmUpper hRootLast hall
  have hmiss : ∃ x ∈ q.position.board.right.currentLabel,
      ¬ x ≤ q.position.board.right.leafIndex := by
    simpa only [LabeledWord.NoLeafPending, not_forall, not_le, exists_prop] using hUnot
  obtain ⟨x, hx, hnot⟩ := hmiss
  have hltRank := finite_rank_strict_of_lt q.position.board.right.currentLabel hx
    (lt_of_not_ge hnot)
  have hleRank := Finset.card_filter_le q.position.board.right.currentLabel (fun y => y ≤ x)
  have hrem : 0 < q.position.board.right.currentLabel.card -
      (q.position.board.right.currentLabel.filter
        (fun y => y ≤ q.position.board.right.leafIndex)).card := by omega
  refine ⟨J, hJH, hJ, hJfresh, st, upper, d, r, hOldST, hTUv.trans hVupper,
    hwinV.of_reachable (exactGame N blue) hVupper, hpST, hpUpper, hd, hr, hshape,
    hmST, hmUpper, hiST, hiUpper, hrootST, hrootUpper.trans hVroot, hSTother,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hRootLast, ?_, ?_,
    q, hQ, hTUq, hqv.trans hVupper, ?_, frontU, ?_, ?_⟩
  · simpa only [hUpperOther] using hV.right_relaxed
  · simpa only [hUpperOther] using hVUroot
  · simpa only [hUpperOther] using hVUlabels
  · simpa only [hUpperOther] using hVUbody
  · simpa only [hUpperOther] using hVUcurrent
  · simpa only [hUpperOther] using hVUindex
  · simpa only [hUpperOther] using hVUrank
  · simpa only [hUpperOther, hVboard] using hrem
  · simpa only [hUpperOther, hVboard] using hbound
  · simpa only [hVboard] using hUpperOther
  · simpa only [hUpperOther, Board.get] using hfrontU
  · intro atom hatom
    exact ⟨hJH (hpoolU atom hatom).1, hJfresh atom.2 (hpoolU atom hatom).1⟩

#print axioms strict_nonlast_rank_one_marker_bridge

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
