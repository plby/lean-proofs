import ErdosProblems.Erdos118.Reused591.FirstLeafGluingHistory
import ErdosProblems.Erdos118.Reused591.LastLastUpper
import ErdosProblems.Erdos118.Reused591.ReplySeparation

namespace Erdos118.Reused591

/-!
# Enter a middle phase from its actual prescribed last-body request

Submit only the first selected leaf of the lower common-last label.
Its marker raises the actual history bound above every saved bound
dominated by the label budget. Retain the literal first-response prefix
and the unchanged opposite word for the subsequent delayed replays.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_middle_start {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    (σ : (exactGame N blue).ArchitectStrategy) (p : Concrete.Hist N)
    {B a c : ℕ} (L : LastLastLabels H B a c)
    (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hm : p.position.board.left.markerEvent = true)
    (hroot : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1)
    (hB : max p.position.bound (b p) ≤ B) :
    ∃ q, (exactGame N blue).FollowStep σ H b p q ∧ q.position.pending = none ∧
      q.position.board.left.relaxed = true ∧
      LabeledWord.UpToLeaf L.penultimate q.position.board.left ∧
      L.pivot ∈ q.position.board.left.currentLabel ∧
      (∀ i ∈ q.position.board.left.currentLabel, i = L.pivot ∨ i ≤ L.penultimate) ∧
      (∀ i ∈ q.position.board.left.rootLabel, i ≤ q.position.board.left.bodyLabels.length) ∧
      q.position.board.left.bodyLabels = p.position.board.left.bodyLabels ++ [L.lower] ∧
      q.position.board.left.bodyMarker = L.marker ∧
      q.position.board.right = p.position.board.right ∧
      (∀ y ∈ q.position.board.right.coordinates,
        y ≤ q.position.board.left.coordinates.getLastD 0) ∧ B < q.position.bound ∧
      ∃ r xs, p.position.board.left.parser = .blocks (r + 1) ∧
        q.position.board.left =
          LabeledWord.bodyLeafCursor p.position.board.left L.lower L.marker r xs ∧
        xs.length = L.firstLower ∧ (L.marker :: xs).Pairwise (· < ·) ∧
        (∀ x ∈ xs, x ∈ H ∧ L.marker < x) := by
  obtain ⟨q, _q', hs, _hs', hn, _hn', _hshape, hr, _hr', hi, _hi', hb, _hb',
      ho, _ho', r, xs, hparse, hword, _hword', hlen, hinc, hpool⟩ :=
    first_leaf_gluing_prefix hHN hH blue σ p p false false L.first_to_lower
      L.first_to_lower rfl rfl hp hp hm hm (LabeledWord.SameStructure.refl _) hB hB
  change q.position.board.left.relaxed = true at hr
  change q.position.board.left.leafIndex = L.firstLower at hi
  change q.position.board.left.bodyLabels = p.position.board.left.bodyLabels ++ [L.lower] at hb
  change q.position.board.right = p.position.board.right at ho
  change q.position.board.left =
    LabeledWord.bodyLeafCursor p.position.board.left L.lower L.marker r xs at hword
  have hcurrent : q.position.board.left.currentLabel = L.lower := by
    simp [LabeledWord.currentLabel, hb]
  have htarget : LabeledWord.UpToLeaf L.penultimate q.position.board.left :=
    ⟨(of_decide_eq_true hr).2.1, hcurrent ▸ L.penultimate_lower,
      by rw [hi]; exact L.firstLower_le_penultimate⟩
  have hrootQ : ∀ i ∈ q.position.board.left.rootLabel,
      i ≤ q.position.board.left.bodyLabels.length := by
    simpa [hword, LabeledWord.bodyLeafCursor] using hroot
  have hmarker : L.marker ∈ q.position.board.left.coordinates := by
    simp [hword, LabeledWord.bodyLeafCursor]
  have hbound : L.marker ≤ q.position.bound := ((Position.history_dataInvariant q).1 _
    (q.position.board.get_support_subset false (LabeledWord.coordinate_mem_support hmarker))).2.2
  have hsep := (FiniteResponseGame.FollowStep.next (exactGame N blue) hs).reply_separation hp
  exact ⟨q, hs, hn, hr, htarget, hcurrent ▸ L.pivot_lower,
    by simpa only [hcurrent] using L.lower_bounds, hrootQ, hb,
    by simp [hword, LabeledWord.bodyLeafCursor], ho, hsep, L.marker_fresh.2.trans_le hbound,
    r, xs, hparse, hword, hlen, hinc, hpool⟩

#print axioms inside_middle_start

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
