import ErdosProblems.Erdos591.BodyMarkerPositions
import ErdosProblems.Erdos591.CutSuffixCounts

/-!
# Exact selected pairs in a suffix starting at any actual leaf

The starting leaf is included if selected. Positions are compared in
the literal word, then identified with the lexicographic order on the
one-based body and leaf indices of the existing labels.
-/

namespace Erdos591.Positive.Game

def LabeledWord.selectedLeafPairsFrom (w : LabeledWord) (i j : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  w.selectedLeafPairs.filter fun p => i + 1 < p.1 ∨ i + 1 = p.1 ∧ j + 1 ≤ p.2

namespace Payoff

open Erdos591.Negative.Exact

theorem ClearSide.selected_pair_from_iff {w : LabeledWord} {s t : G} (h : ClearSide w s t)
    {i j : ℕ} (hi : i < s.val.length) (hj : j < (s.val.getD i []).length)
    {p : Σ _ : ℕ, ℕ} (hp : p ∈ w.selectedLeafPairs) :
    leafPosition s.val i j ≤ leafPosition s.val (p.1 - 1) (p.2 - 1) ↔
      i + 1 < p.1 ∨ i + 1 = p.1 ∧ j + 1 ≤ p.2 := by
  rcases p with ⟨k, l⟩
  obtain ⟨hk, hl⟩ := Finset.mem_sigma.mp hp
  have hcut := h.selected_pair_cut hk hl
  rw [leafPosition_le_iff s.val hi hj hcut.1 hcut.2.1]
  have hkpos := (h.root_bounds k hk).1
  have hlpos := (h.body_bounds _ hcut.1 l hl).1
  change (i < k - 1 ∨ i = k - 1 ∧ j ≤ l - 1) ↔ i + 1 < k ∨ i + 1 = k ∧ j + 1 ≤ l
  omega

theorem ClearSide.leaf_suffix_card {w : LabeledWord} {s t : G} (h : ClearSide w s t)
    {i j : ℕ} (hi : i < s.val.length) (hj : j < (s.val.getD i []).length) :
    (cutIndices ((word s.val).drop (leafPosition s.val i j)) (word t.val)).card =
      (w.selectedLeafPairsFrom i j).card := by
  rw [cutIndices_drop_card]
  symm
  apply Finset.card_bij
    (fun p _ => leafPosition s.val (p.1 - 1) (p.2 - 1))
  · intro p hp
    obtain ⟨hpair, hafter⟩ := Finset.mem_filter.mp hp
    obtain ⟨hk, hl⟩ := Finset.mem_sigma.mp hpair
    exact Finset.mem_filter.mpr
      ⟨(mem_cutIndices _ _ _).mpr (h.selected_pair_cut hk hl).2.2,
        (h.selected_pair_from_iff hi hj hpair).mpr hafter⟩
  · intro p hp q hq heq
    exact h.selected_pair_position_injective (Finset.mem_filter.mp hp).1
      (Finset.mem_filter.mp hq).1 heq
  · intro k hk
    obtain ⟨hcut, hpos⟩ := Finset.mem_filter.mp hk
    obtain ⟨a, b, hab, hkEq⟩ := h.all_cuts_leaves k ((mem_cutIndices _ _ _).mp hcut)
    have hpair : (⟨a + 1, b + 1⟩ : Σ _ : ℕ, ℕ) ∈ w.selectedLeafPairs := by
      apply Finset.mem_sigma.mpr
      exact ⟨(h.root_exact a).mpr ⟨b, hab⟩,
        by simpa only [Nat.add_sub_cancel] using (h.body_exact a hab.1 b).mpr hab⟩
    refine ⟨⟨a + 1, b + 1⟩, Finset.mem_filter.mpr ⟨hpair, ?_⟩, ?_⟩
    · apply (h.selected_pair_from_iff hi hj hpair).mp
      simpa only [Nat.add_sub_cancel] using (hkEq ▸ hpos)
    · simpa only [Nat.add_sub_cancel] using hkEq.symm

#print axioms ClearSide.selected_pair_from_iff
#print axioms ClearSide.leaf_suffix_card

end Payoff

end Erdos591.Positive.Game
