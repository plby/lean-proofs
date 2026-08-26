import ErdosProblems.Erdos591.CompletedOther
import ErdosProblems.Erdos591.DoubleOverlapLabels

/-!
# Two actual body responses with the same first selected leaf

Both body labels have a prescribed common minimum and marker. Choose
exactly that many increasing leaf coordinates above the marker, then
submit the resulting first-leaf response in each history. Both opposite
words are unchanged; no continuation of either play is used.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem first_leaf_gluing_prefix {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    (σ : (exactGame N blue).ArchitectStrategy) (lower upper : Concrete.Hist N) (s t : Bool)
    {B a c : ℕ} (L : LastFirstLabels H B 1 a) (U : LastFirstLabels H B 1 c)
    (hpivot : U.pivot = L.pivot) (hmarker : U.marker = L.marker)
    (hpL : lower.position.pending = some ⟨s, .advance a⟩)
    (hpU : upper.position.pending = some ⟨t, .advance c⟩)
    (hmL : (lower.position.board.get s).markerEvent = true)
    (hmU : (upper.position.board.get t).markerEvent = true)
    (hsame : LabeledWord.SameStructure (lower.position.board.get s)
      (upper.position.board.get t))
    (hbL : max lower.position.bound (b lower) ≤ B)
    (hbU : max upper.position.bound (b upper) ≤ B) :
    ∃ q v, (exactGame N blue).FollowStep σ H b lower q ∧
      (exactGame N blue).FollowStep σ H b upper v ∧
      q.position.pending = none ∧ v.position.pending = none ∧
      LabeledWord.SameStructure (q.position.board.get s) (v.position.board.get t) ∧
      (q.position.board.get s).relaxed = true ∧ (v.position.board.get t).relaxed = true ∧
      (q.position.board.get s).leafIndex = L.pivot ∧
      (v.position.board.get t).leafIndex = L.pivot ∧
      (q.position.board.get s).bodyLabels = (lower.position.board.get s).bodyLabels ++ [L.upper] ∧
      (v.position.board.get t).bodyLabels = (upper.position.board.get t).bodyLabels ++ [U.upper] ∧
      q.position.board.get (!s) = lower.position.board.get (!s) ∧
      v.position.board.get (!t) = upper.position.board.get (!t) ∧
      ∃ r xs, (lower.position.board.get s).parser = .blocks (r + 1) ∧
        (q.position.board.get s) =
          LabeledWord.bodyLeafCursor (lower.position.board.get s) L.upper L.marker r xs ∧
        (v.position.board.get t) =
          LabeledWord.bodyLeafCursor (upper.position.board.get t) U.upper U.marker r xs ∧
        xs.length = L.pivot ∧ (L.marker :: xs).Pairwise (· < ·) ∧
        (∀ x ∈ xs, x ∈ H ∧ L.marker < x) := by
  classical
  obtain ⟨f, hf, hfH, hfM, _⟩ :=
    FastSequence.exists_above_finite_bounds hH ∅ (fun _ => L.marker)
  let F := (Finset.range L.pivot).image f
  let xs := F.sort (· ≤ ·)
  have hlen : xs.length = L.pivot := by
    simp [xs, F, Finset.card_image_of_injective _ hf.injective]
  have hxs : ∀ x ∈ xs, x ∈ H ∧ L.marker < x := by
    intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp ((Finset.mem_sort (· ≤ ·)).mp hx)
    exact ⟨hfH i, hfM i⟩
  have hinc : (L.marker :: xs).Pairwise (· < ·) :=
    List.pairwise_cons.mpr ⟨fun x hx => (hxs x hx).2, (Finset.sortedLT_sort F).pairwise⟩
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hmL
  have hparseU : (upper.position.board.get t).parser = .blocks (r + 1) :=
    hsame.parser_eq.symm.trans hparse
  obtain ⟨uL, hrL, _hsortL, huLH, huLB⟩ := L.leaf_reply lower.position.board s r xs
    ((Position.history_dataInvariant lower).2.1 s).1 hparse hmL hlen hinc
    (fun x hx => (hxs x hx).1)
  obtain ⟨uU, hrU, _hsortU, huUH, huUB⟩ := U.leaf_reply upper.position.board t r xs
    ((Position.history_dataInvariant upper).2.1 t).1 hparseU hmU
    (by simpa [hpivot] using hlen) (by simpa [hmarker] using hinc)
    (fun x hx => (hxs x hx).1)
  obtain ⟨q, hsL, hboardL, hnL⟩ := Concrete.follow_reply hHN (payoff blue) σ lower hpL hrL huLH
    (fun x hx => ⟨((le_max_left _ _).trans hbL).trans_lt (huLB x hx),
      ((le_max_right _ _).trans hbL).trans_lt (huLB x hx)⟩)
  obtain ⟨v, hsU, hboardU, hnU⟩ := Concrete.follow_reply hHN (payoff blue) σ upper hpU hrU huUH
    (fun x hx => ⟨((le_max_left _ _).trans hbU).trans_lt (huUB x hx),
      ((le_max_right _ _).trans hbU).trans_lt (huUB x hx)⟩)
  have hwordL : q.position.board.get s =
      LabeledWord.bodyLeafCursor (lower.position.board.get s) L.upper L.marker r xs := by
    simp [hboardL]
  have hwordU : v.position.board.get t =
      LabeledWord.bodyLeafCursor (upper.position.board.get t) U.upper U.marker r xs := by
    simp [hboardU]
  have ha : 0 < a := L.upper_card ▸ Finset.card_pos.mpr ⟨L.pivot, L.pivot_upper⟩
  have hc : 0 < c := U.upper_card ▸ Finset.card_pos.mpr ⟨U.pivot, U.pivot_upper⟩
  refine ⟨q, v, hsL, hsU, hnL, hnU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hwordL, hwordU, hmarker]
    exact hsame.bodyLeafCursor L.upper U.upper L.marker r xs
  · simpa [hboardL] using hrL.advance_selected_leaf
      ((Position.history_dataInvariant lower).2.1 s).1 hmL ha
      (fun x hx => (Nat.zero_le B).trans_lt (huLB x hx))
  · simpa [hboardU] using hrU.advance_selected_leaf
      ((Position.history_dataInvariant upper).2.1 t).1 hmU hc
      (fun x hx => (Nat.zero_le B).trans_lt (huUB x hx))
  · simp [hwordL, LabeledWord.bodyLeafCursor, hlen]
  · simp [hwordU, LabeledWord.bodyLeafCursor, hlen]
  · simp [hwordL, LabeledWord.bodyLeafCursor]
  · simp [hwordU, LabeledWord.bodyLeafCursor]
  · simpa [hboardL] using hrL.other_eq
  · simpa [hboardU] using hrU.other_eq
  · exact ⟨r, xs, hparse, hwordL, hwordU, hlen, hinc, hxs⟩

theorem first_leaf_gluing {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    (σ : (exactGame N blue).ArchitectStrategy) (lower upper : Concrete.Hist N) (s t : Bool)
    {B a c : ℕ} (L : LastFirstLabels H B 1 a) (U : LastFirstLabels H B 1 c)
    (hpivot : U.pivot = L.pivot) (hmarker : U.marker = L.marker)
    (hpL : lower.position.pending = some ⟨s, .advance a⟩)
    (hpU : upper.position.pending = some ⟨t, .advance c⟩)
    (hmL : (lower.position.board.get s).markerEvent = true)
    (hmU : (upper.position.board.get t).markerEvent = true)
    (hsame : LabeledWord.SameStructure (lower.position.board.get s)
      (upper.position.board.get t))
    (hbL : max lower.position.bound (b lower) ≤ B)
    (hbU : max upper.position.bound (b upper) ≤ B) :
    ∃ q v, (exactGame N blue).FollowStep σ H b lower q ∧
      (exactGame N blue).FollowStep σ H b upper v ∧
      q.position.pending = none ∧ v.position.pending = none ∧
      LabeledWord.SameStructure (q.position.board.get s) (v.position.board.get t) ∧
      (q.position.board.get s).relaxed = true ∧ (v.position.board.get t).relaxed = true ∧
      (q.position.board.get s).leafIndex = L.pivot ∧
      (v.position.board.get t).leafIndex = L.pivot ∧
      (q.position.board.get s).bodyLabels = (lower.position.board.get s).bodyLabels ++ [L.upper] ∧
      (v.position.board.get t).bodyLabels = (upper.position.board.get t).bodyLabels ++ [U.upper] ∧
      q.position.board.get (!s) = lower.position.board.get (!s) ∧
      v.position.board.get (!t) = upper.position.board.get (!t) := by
  obtain ⟨q, v, hq, hv, hnq, hnv, he, hqr, hvr, hqi, hvi, hqb, hvb, hqo, hvo, _⟩ :=
    first_leaf_gluing_prefix hHN hH blue σ lower upper s t L U hpivot hmarker hpL hpU
      hmL hmU hsame hbL hbU
  exact ⟨q, v, hq, hv, hnq, hnv, he, hqr, hvr, hqi, hvi, hqb, hvb, hqo, hvo⟩

#print axioms first_leaf_gluing_prefix
#print axioms first_leaf_gluing

end Erdos591.Positive.Game.Payoff
