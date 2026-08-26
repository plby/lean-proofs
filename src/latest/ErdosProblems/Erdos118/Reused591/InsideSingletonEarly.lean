import ErdosProblems.Erdos118.Reused591.InsideSingletonCheckpoint
import ErdosProblems.Erdos118.Reused591.InsideEarlyPreparation

namespace Erdos118.Reused591

/-!
# The early histories in the last-singleton construction

Start just after a nonlast first selected S leaf. Install a delayed
T opening for TU, reach S's penultimate body last leaf, detect T's
last lower leaf, and fire its first upper leaf. The old S continuation
is left pending, while the TU request for U is now known.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_singleton_early_histories {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    (origin st : Concrete.Hist N) {B a : ℕ} (L : LastLastLabels H B a)
    (hwinOrigin : (exactGame N blue).ArchitectWins H b σ origin)
    (hopening : origin.position.pending = some ⟨false, .advance a⟩)
    (hboardOrigin : origin.position.board = Board.initial)
    (hmodeOrigin : origin.position.mode = some true)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin st)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → lastBodySingletonColor false z = true)
    (hpST : st.position.pending = none) (hTinit : st.position.board.right = LabeledWord.initial)
    (hSrel : st.position.board.left.relaxed = true)
    (hSroot : st.position.board.left.rootLabel = L.lower)
    (hSbody : st.position.board.left.bodyLabels.length = L.firstLower)
    (hSstrict : st.position.board.left.leafIndex < st.position.board.left.currentLabel.sup id) :
    ∃ old upper c, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) st old ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upper ∧
      old.position.pending = some ⟨false, .advance 0⟩ ∧
      old.position.board.left.rootLabel = L.lower ∧
      old.position.board.left.bodyLabels.length = L.penultimate ∧
      old.position.board.left.relaxed = true ∧ old.position.board.left.NoLeafPending ∧
      old.position.board.right.relaxed = true ∧ ¬ Macro.Pending old.position.board.right ∧
      upper.position.pending = some ⟨true, .advance c⟩ ∧ 0 < c ∧
      upper.position.board.right = LabeledWord.initial ∧ upper.position.mode = some true ∧
      LabeledWord.SameStructure old.position.board.right upper.position.board.left := by
  obtain ⟨q, hstq, _hqn, hqrel, hqno, hqroot, hqbody, hqsep, hMq⟩ :=
    inside_early_preparation hHN hH blue htri hroot origin st L hwinOrigin hopening
      hboardOrigin hmodeOrigin hfrom hpST hTinit hSrel hSroot hSbody hSstrict
  have horiginQ := hfrom.trans hstq
  have hwinQ := hwinOrigin.of_reachable (exactGame N blue) horiginQ
  have hbefore : LabeledWord.BeforeBody L.pivot q.position.board.left :=
    ⟨hqroot ▸ L.pivot_lower, by simpa only [hqbody] using L.penultimate_lt_pivot⟩
  have hnext : ∀ k ∈ q.position.board.left.rootLabel,
      q.position.board.left.bodyLabels.length < k → L.pivot ≤ k := by
    intro k hk hlt
    rcases L.lower_bounds k (hqroot ▸ hk) with heq | hle
    · exact heq.ge
    · rw [hqbody] at hlt
      exact (not_lt_of_ge hle hlt).elim
  have hlastRoot : ∀ k ∈ q.position.board.left.rootLabel, k ≤ L.pivot :=
    fun k hk => L.lower_le_pivot k (hqroot ▸ hk)
  obtain ⟨old, hqold, hpOld, hOldS, hOldTrel, _hOldSep, hOldLast, MOld, hMOld⟩ :=
    inside_singleton_critical_checkpoint hHN hH blue origin hwinQ horiginQ hall
      (follow_mode_some horiginQ hmodeOrigin) hqrel hqsep hqno hbefore hnext hlastRoot origin hMq
  obtain ⟨tu, htuPath, hwinTU, hnTU, hcTU, hrTU, hoTU, hmTU, _hTUfresh⟩ :=
    MOld.fire_from hHN ((Position.history_dataInvariant old).2.1 true).2 hOldLast origin hMOld
  obtain ⟨upper, c, hTUrequest, hTUboard, hpUpper, hc⟩ :=
    winning_initial_right_request hHN hH blue htri hroot hwinTU hnTU hoTU hrTU
  have hTshape : LabeledWord.SameStructure old.position.board.right upper.position.board.left := by
    obtain ⟨as, has⟩ := History.word_run old true
    obtain ⟨bs, hbs⟩ := History.word_run upper false
    apply LabeledWord.sameStructure_of_initial_runs has.run hbs.run
    simpa [hTUboard, Board.get] using hcTU.symm
  exact ⟨old, upper, c, hstq.trans hqold, htuPath.tail hTUrequest, hpOld,
    by simpa only [hOldS] using hqroot, by simpa only [hOldS] using hqbody,
    by simpa only [hOldS] using hqrel, by simpa only [hOldS] using hqno,
    hOldTrel, hOldLast, hpUpper, hc, by simpa [hTUboard, Board.get] using hoTU,
    follow_mode_some (Relation.ReflTransGen.single hTUrequest) hmTU, hTshape⟩

#print axioms inside_singleton_early_histories

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
