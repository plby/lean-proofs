import ErdosProblems.Erdos591.SelectedBodyCard
import ErdosProblems.Erdos591.WordPositions
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite selected-leaf counts and their exact coordinate-cut interpretation

The counts sum actual body-label cardinalities over one-based selected
root indices. A literal finite bijection identifies the selected pairs
with all coordinate cuts of a clear word. No alternation or total-count
identity for the two sides is assumed here.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

def selectedLeafPairs (w : LabeledWord) : Finset (Σ _ : ℕ, ℕ) :=
  w.rootLabel.sigma fun i => w.bodyLabels.getD (i - 1) ∅

def selectedLeafCount (w : LabeledWord) : ℕ :=
  ∑ i ∈ w.rootLabel, (w.bodyLabels.getD (i - 1) ∅).card

def beforeLastLeafCount (w : LabeledWord) : ℕ :=
  ∑ i ∈ w.rootLabel.erase w.lastSelectedBody, (w.bodyLabels.getD (i - 1) ∅).card

theorem selectedLeafPairs_card (w : LabeledWord) :
    w.selectedLeafPairs.card = w.selectedLeafCount := Finset.card_sigma _ _

theorem selectedLeafCount_decomposition {w : LabeledWord} (hne : w.rootLabel.Nonempty) :
    w.selectedLeafCount = w.beforeLastLeafCount + w.lastSelectedLabel.card := by
  have hm : w.lastSelectedBody ∈ w.rootLabel := by
    simpa [lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id) hne
  exact (Finset.sum_erase_add _ _ hm).symm

end LabeledWord

namespace Payoff

open Erdos591.Negative.Exact

noncomputable def cutIndices (xs ys : List ℕ) : Finset ℕ := by
  classical
  exact (Finset.range xs.length).filter (Cut xs ys)

theorem mem_cutIndices (xs ys : List ℕ) (k : ℕ) : k ∈ cutIndices xs ys ↔ Cut xs ys k := by
  classical
  simp only [cutIndices, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨by have := h.1; omega, h⟩⟩

theorem ClearSide.selected_pair_cut {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) {i j : ℕ} (hi : i ∈ w.rootLabel)
    (hj : j ∈ w.bodyLabels.getD (i - 1) ∅) :
    LeafCut s.val t.val (i - 1) (j - 1) := by
  have hbi := h.root_bounds i hi
  have hilen : i - 1 < s.val.length := by omega
  have hbj := h.body_bounds (i - 1) hilen j hj
  apply (h.body_exact (i - 1) hilen (j - 1)).mp
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hj

theorem ClearSide.cutIndices_card {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) :
    (cutIndices (word s.val) (word t.val)).card = w.selectedLeafCount := by
  rw [← w.selectedLeafPairs_card]
  symm
  apply Finset.card_bij
    (fun p _ => leafPosition s.val (p.1 - 1) (p.2 - 1))
  · intro p hp
    obtain ⟨hi, hj⟩ := Finset.mem_sigma.mp hp
    exact (mem_cutIndices _ _ _).mpr (h.selected_pair_cut hi hj).2.2
  · rintro ⟨i, j⟩ hij ⟨k, l⟩ hkl heq
    obtain ⟨hi, hj⟩ := Finset.mem_sigma.mp hij
    obtain ⟨hk, hl⟩ := Finset.mem_sigma.mp hkl
    have hcutij := h.selected_pair_cut hi hj
    have hcutkl := h.selected_pair_cut hk hl
    obtain ⟨hiEq, hjEq⟩ := LabeledCode.leafPosition_injective s.val
      hcutij.1 hcutij.2.1 hcutkl.1 hcutkl.2.1 heq
    change i - 1 = k - 1 at hiEq
    change j - 1 = l - 1 at hjEq
    have hipos := (h.root_bounds i hi).1
    have hkpos := (h.root_bounds k hk).1
    have hjpos := (h.body_bounds (i - 1) hcutij.1 j hj).1
    have hlpos := (h.body_bounds (k - 1) hcutkl.1 l hl).1
    have hik : i = k := by omega
    have hjl : j = l := by omega
    subst k
    subst l
    rfl
  · intro k hk
    obtain ⟨i, j, hij, hkEq⟩ := h.all_cuts_leaves k ((mem_cutIndices _ _ _).mp hk)
    refine ⟨⟨i + 1, j + 1⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      exact ⟨(h.root_exact i).mpr ⟨j, hij⟩,
        by simpa only [Nat.add_sub_cancel] using (h.body_exact i hij.1 j).mpr hij⟩
    · simpa only [Nat.add_sub_cancel] using hkEq.symm

theorem ClearSide.selected_pair_position_injective {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) {p q : Σ _ : ℕ, ℕ}
    (hp : p ∈ w.selectedLeafPairs) (hq : q ∈ w.selectedLeafPairs)
    (heq : leafPosition s.val (p.1 - 1) (p.2 - 1) =
      leafPosition s.val (q.1 - 1) (q.2 - 1)) : p = q := by
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, l⟩
  obtain ⟨hi, hj⟩ := Finset.mem_sigma.mp hp
  obtain ⟨hk, hl⟩ := Finset.mem_sigma.mp hq
  have hcutij := h.selected_pair_cut hi hj
  have hcutkl := h.selected_pair_cut hk hl
  obtain ⟨hiEq, hjEq⟩ := LabeledCode.leafPosition_injective s.val
    hcutij.1 hcutij.2.1 hcutkl.1 hcutkl.2.1 heq
  change i - 1 = k - 1 at hiEq
  change j - 1 = l - 1 at hjEq
  have hipos := (h.root_bounds i hi).1
  have hkpos := (h.root_bounds k hk).1
  have hjpos := (h.body_bounds (i - 1) hcutij.1 j hj).1
  have hlpos := (h.body_bounds (k - 1) hcutkl.1 l hl).1
  have hik : i = k := by omega
  have hjl : j = l := by omega
  subst k
  subst l
  rfl

theorem ClearSide.selected_body_card_pos {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) {i : ℕ} (hi : i ∈ w.rootLabel) :
    0 < (w.bodyLabels.getD (i - 1) ∅).card := by
  have hb := h.root_bounds i hi
  apply Finset.card_pos.mpr
  apply (h.root_mem_iff_body_nonempty (by omega : i - 1 < s.val.length)).mp
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using hi

theorem ClearSide.root_card_le_selectedLeafCount {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) : w.rootLabel.card ≤ w.selectedLeafCount := by
  calc
    w.rootLabel.card = ∑ _i ∈ w.rootLabel, 1 := by simp
    _ ≤ w.selectedLeafCount := Finset.sum_le_sum fun i hi => h.selected_body_card_pos hi

theorem ClearSide.root_card_sub_one_le_beforeLastLeafCount {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) (hne : w.rootLabel.Nonempty) :
    w.rootLabel.card - 1 ≤ w.beforeLastLeafCount := by
  have hm : w.lastSelectedBody ∈ w.rootLabel := by
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id) hne
  calc
    w.rootLabel.card - 1 = (w.rootLabel.erase w.lastSelectedBody).card :=
      (Finset.card_erase_of_mem hm).symm
    _ = ∑ _i ∈ w.rootLabel.erase w.lastSelectedBody, 1 := by simp
    _ ≤ w.beforeLastLeafCount := Finset.sum_le_sum fun i hi =>
      h.selected_body_card_pos (Finset.mem_of_mem_erase hi)

#print axioms ClearSide.cutIndices_card
#print axioms ClearSide.root_card_le_selectedLeafCount
#print axioms ClearSide.root_card_sub_one_le_beforeLastLeafCount
#print axioms LabeledWord.selectedLeafCount_decomposition

end Payoff

end Erdos591.Positive.Game
