import ErdosProblems.Erdos591.InsideSecondMiddleStart
import ErdosProblems.Erdos591.InsideMiddleEndpoint
import ErdosProblems.Erdos591.LastBodyEndpoint
import ErdosProblems.Erdos591.FollowFreshInputs

/-!
# Second middle endpoint with both delayed coordinate runs retained

Complete the pending upper first-leaf response from the lower prefix,
then exhaust its nonlast selected leaves. The whole new first-word run
starts at the virtual old prefix and exceeds the old pending bound.
The opposite last-body run also exceeds the separately recorded bound,
whether its upper play stops at this leaf or continues to a future body.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_second_middle {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (p : Concrete.Hist N)
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (hmode : p.position.mode = some true)
    {B a c : ℕ} (L : LastLastLabels H B a c)
    (hp : p.position.pending = some ⟨false, .advance c⟩)
    (hm : p.position.board.left.markerEvent = true) {r : ℕ}
    (hparse : p.position.board.left.parser = .blocks (r + 1))
    (hroot : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1)
    (hB : max p.position.bound (b p) ≤ B) (xs : List ℕ)
    (hlen : xs.length = L.penultimate) (hinc : (L.marker :: xs).Pairwise (· < ·))
    (hpool : ∀ x ∈ xs, x ∈ H) (C : ℕ)
    (hrelOther : p.position.board.right.relaxed = true)
    (hrootOther : ∀ i ∈ p.position.board.right.rootLabel,
      i ≤ p.position.board.right.bodyLabels.length)
    {t mode : Bool} {other : LabeledWord} (upperOrigin : Concrete.Hist N)
    (hmanaged : ∃ M : Managed N H blue b σ t mode other p.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upperOrigin M.target) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧
      q.position.board.left.relaxed = true ∧ q.position.board.left.leafIndex = L.upperPenultimate ∧
      q.position.board.left.bodyLabels = p.position.board.left.bodyLabels ++ [L.upper] ∧
      q.position.board.left.bodyMarker = L.marker ∧
      (∀ i ∈ q.position.board.left.rootLabel, i ≤ q.position.board.left.bodyLabels.length) ∧
      q.position.board.right.relaxed = true ∧ ¬ Macro.Pending q.position.board.right ∧
      q.position.board.right.bodyLabels = p.position.board.right.bodyLabels ∧
      q.position.board.right.bodyMarker = p.position.board.right.bodyMarker ∧
      q.position.board.right.leafIndex = p.position.board.right.currentLabel.sup id ∧
      (∃ as, LabeledWord.LegalRun
        (LabeledWord.bodyLeafCursor p.position.board.left L.upper L.marker r xs)
        as q.position.board.left ∧ ∀ atom ∈ as, atom.2 ∈ H ∧ C < atom.2) ∧
      (∃ as, LabeledWord.LegalRun p.position.board.right as q.position.board.right ∧
        ∀ atom ∈ as, atom.2 ∈ H ∧ C < atom.2) := by
  obtain ⟨first, ys, hstep, hn, hr, htarget, hpivot, hleaves, hrootFirst,
      hlabelsFirst, hmarkerFirst, hother, hsep, hboundFirst, _hword, _hfullLen,
      _hfullInc, hys, hfirstRun⟩ :=
    inside_second_middle_start hHN hH blue σ p L hp hm hparse hroot hB xs hlen hinc hpool C
  have hMfirst : ∃ M : Managed N H blue b σ t mode other first.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upperOrigin M.target := by
    rw [hother]
    exact hmanaged
  obtain ⟨q, hmid, hpq, hqr, hqi, hqb, hqm, hqOther, hqLast, _Mq, _hMq⟩ :=
    inside_middle_endpoint hHN hH blue (hwin.of_reachable (exactGame N blue) (.single hstep))
      (follow_mode_some (.single hstep) hmode) hn hsep htarget L.upperPenultimate_lt_pivot
      hpivot hleaves hrootFirst upperOrigin hMfirst
  obtain ⟨Sas, hS, hSpool⟩ := follow_word_inputs_above_bound hmid false
  obtain ⟨Uas, hU, hUpool⟩ := follow_word_inputs_above_bound hmid true
  have hUold : LabeledWord.LegalRun p.position.board.right Uas q.position.board.right := by
    simpa only [Board.get, hother] using hU
  obtain ⟨hUlabels, hUmarker, hUidx⟩ := hUold.last_body_relaxed_endpoint
    (LabeledWord.relaxed_ne_start ((Position.history_dataInvariant p).2.1 true).1 hrelOther)
    hrootOther hqOther hqLast
  have hSwhole := hfirstRun.append hS
  have hSfresh : ∀ atom ∈ (ys.map fun y => (∅, y)) ++ Sas, atom.2 ∈ H ∧ C < atom.2 := by
    intro atom ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      exact hys y hy
    · exact ⟨(hSpool atom ha).1, hboundFirst.trans (hSpool atom ha).2⟩
  have hrootEq := hS.rootLabel_eq
    (LabeledWord.relaxed_ne_start ((Position.history_dataInvariant first).2.1 false).1 hr)
  have hrootQ : ∀ i ∈ q.position.board.left.rootLabel,
      i ≤ q.position.board.left.bodyLabels.length := by
    intro i hi
    rw [hqb]
    exact hrootFirst i (hrootEq ▸ hi)
  exact ⟨q, hmid.head hstep, hpq, hqr, hqi, hqb.trans hlabelsFirst, hqm.trans hmarkerFirst,
    hrootQ, hqOther, hqLast, hUlabels, hUmarker, hUidx,
    ⟨_, hSwhole, hSfresh⟩, ⟨Uas, hUold,
      fun atom ha => ⟨(hUpool atom ha).1, hboundFirst.trans (hUpool atom ha).2⟩⟩⟩

#print axioms inside_second_middle

end Erdos591.Positive.Game.Payoff
