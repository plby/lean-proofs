import ErdosProblems.Erdos118.Reused591.InsideEarlyPreparation
import ErdosProblems.Erdos118.Reused591.LateMarkerCheckpoint
import ErdosProblems.Erdos118.Reused591.ManagedDeferred
import ErdosProblems.Erdos118.Reused591.FirstRequestRecovery

namespace Erdos118.Reused591

/-!
# Initial deferred histories in the late-marker inside construction

Reuse the early root preparation, reach the actual nonlast critical
opposite leaf, and submit its deferred upper response. The old first
word's continuation stays pending while the upper second-root request
is obtained. The upper body label's singleton and second-index data
are retained explicitly; no unjustified size-two assumption is added.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_late_early_histories {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
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
      (exactGame N blue).kind z = .terminal w → lateFirstMarkerColor z = true)
    (hlarge : ∀ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q →
      q.position.pending = some ⟨false, .advance d⟩ → q.position.board.left.markerEvent = true →
      (∀ k ∈ q.position.board.left.rootLabel,
        k ≤ q.position.board.left.bodyLabels.length + 1) → 2 ≤ d)
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
      old.position.board.right.relaxed = true ∧
      old.position.board.right.lastSelectedBody = old.position.board.right.bodyLabels.length ∧
      (∃ j ∈ old.position.board.right.currentLabel, old.position.board.right.leafIndex < j) ∧
      2 ≤ old.position.board.right.currentLabel.card ∧
      upper.position.pending = some ⟨true, .advance c⟩ ∧ 0 < c ∧
      upper.position.board.right = LabeledWord.initial ∧ upper.position.mode = some true ∧
      LabeledWord.SameStructure old.position.board.right upper.position.board.left ∧
      upper.position.board.left.relaxed = true ∧
      upper.position.board.left.leafIndex = old.position.board.right.leafIndex ∧
      (upper.position.board.left.currentLabel.card = 1 →
        upper.position.board.left.currentLabel = {old.position.board.right.leafIndex}) ∧
      (2 ≤ upper.position.board.left.currentLabel.card →
        old.position.board.right.currentLabel.sup id ∈ upper.position.board.left.currentLabel ∧
        ∀ j ∈ upper.position.board.left.currentLabel, old.position.board.right.leafIndex < j →
          old.position.board.right.currentLabel.sup id ≤ j) ∧
      ((∀ q v e, (exactGame N blue).FollowStep σ H b origin q →
          (exactGame N blue).FollowStep σ H b q v →
          v.position.pending = some ⟨false, .advance e⟩ → 2 ≤ e) →
        2 ≤ upper.position.board.left.currentLabel.card) ∧
      (∀ i ∈ upper.position.board.left.rootLabel,
        upper.position.board.left.bodyLabels.length ≤ i) ∧
      ∃ M : Managed N H blue b σ false true LabeledWord.initial old.position.board.right,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
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
  obtain ⟨old, hqold, hpOld, hOldS, hOldTrel, _hOldSep, hOldBody, hOldLater,
      hOldCard, MOld, hMOld⟩ :=
    inside_late_critical_checkpoint hHN hH blue origin hwinQ horiginQ hall hlarge
      hqrel hqsep hqno hbefore hnext hlastRoot origin hMq
  obtain ⟨tu, htuPath, hwinTU, hnTU, hcTU, hrTU, hiTU, hoTU, hmTU, _hTUfresh,
      hTUsingle, hTUsecond, hTUcard, hTUfirst⟩ :=
    MOld.fire_deferred_from hHN ((Position.history_dataInvariant old).2.1 true).2
      hOldTrel hOldBody hOldLater origin hMOld
  obtain ⟨upper, c, hTUrequest, hTUboard, hpUpper, hc⟩ :=
    winning_initial_right_request hHN hH blue htri hroot hwinTU hnTU hoTU hrTU
  have hTshape : LabeledWord.SameStructure old.position.board.right upper.position.board.left := by
    obtain ⟨as, has⟩ := History.word_run old true
    obtain ⟨bs, hbs⟩ := History.word_run upper false
    apply LabeledWord.sameStructure_of_initial_runs has.run hbs.run
    simpa [hTUboard, Board.get] using hcTU.symm
  refine ⟨old, upper, c, hstq.trans hqold, htuPath.tail hTUrequest, hpOld,
    by simpa only [hOldS] using hqroot, by simpa only [hOldS] using hqbody,
    by simpa only [hOldS] using hqrel, by simpa only [hOldS] using hqno,
    hOldTrel, hOldBody, hOldLater, hOldCard, hpUpper, hc,
    by simpa [hTUboard, Board.get] using hoTU,
    follow_mode_some (Relation.ReflTransGen.single hTUrequest) hmTU, hTshape,
    by simpa [hTUboard, Board.get] using hrTU, ?_, ?_, ?_, ?_,
    by simpa [hTUboard, Board.get] using hTUfirst, MOld, hMOld⟩
  · simpa [hTUboard, Board.get] using hiTU
  · simpa [hTUboard, Board.get] using hTUsingle
  · simpa [hTUboard, Board.get] using hTUsecond
  · intro hfirst
    obtain ⟨e, hepend, _he, hemarker, henopassed⟩ := MOld.first_request_of_last_body hOldBody
    have ha : 0 < a := L.lower_card ▸ Finset.card_pos.mpr ⟨L.pivot, L.pivot_lower⟩
    have he := first_body_request_large_of_reachable hHN hH blue origin MOld.target
      hwinOrigin ha hopening (by simp [hboardOrigin, Board.initial]) hfirst hMOld
      hepend hemarker henopassed
    have hcard : (tu.position.board.get false).currentLabel.card = e := by
      simpa [hepend, Request.size] using hTUcard
    simpa [hTUboard, Board.get] using (hcard ▸ he)

#print axioms inside_late_early_histories

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
