import ErdosProblems.Erdos591.LeafSuffixCounts

/-!
# Exact finite-set test for the last leaf before the last selected body

A suffix from a selected leaf before the last body contains that leaf
and every selection in the last body. It has exactly this cardinality
if and only if there are no other remaining selected leaves.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

theorem selectedLeafPairsFrom_before_last_card_iff {w : LabeledWord} {i j : ℕ}
    (hi : i + 1 ∈ w.rootLabel) (hj : j + 1 ∈ w.bodyLabels.getD i ∅)
    (hbefore : i + 1 < w.lastSelectedBody)
    (hne : ∀ k ∈ w.rootLabel, (w.bodyLabels.getD (k - 1) ∅).Nonempty) :
    (w.selectedLeafPairsFrom i j).card = w.lastSelectedLabel.card + 1 ↔
      (∀ k ∈ w.rootLabel, k < w.lastSelectedBody → k ≤ i + 1) ∧
        (∀ l ∈ w.bodyLabels.getD i ∅, l ≤ j + 1) := by
  classical
  let tail : Finset (Σ _ : ℕ, ℕ) :=
    ({w.lastSelectedBody} : Finset ℕ).sigma fun k => w.bodyLabels.getD (k - 1) ∅
  let point : Σ _ : ℕ, ℕ := ⟨i + 1, j + 1⟩
  have hlast : w.lastSelectedBody ∈ w.rootLabel := by
    simpa [lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id) ⟨i + 1, hi⟩
  have hcard : (insert point tail).card = w.lastSelectedLabel.card + 1 := by
    have hnot : point ∉ tail := by
      simp only [tail, point, Finset.mem_sigma, Finset.mem_singleton]
      intro h
      omega
    rw [Finset.card_insert_of_notMem hnot, Finset.card_sigma]
    simp only [Finset.sum_singleton, lastSelectedLabel]
  have hsub : insert point tail ⊆ w.selectedLeafPairsFrom i j := by
    intro p hp
    rcases Finset.mem_insert.mp hp with heq | hp
    · subst p
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_sigma.mpr ⟨hi, by simpa only [point, Nat.add_sub_cancel] using hj⟩,
        Or.inr ⟨rfl, le_rfl⟩⟩
    · obtain ⟨hk, hl⟩ := Finset.mem_sigma.mp hp
      have hkEq : p.1 = w.lastSelectedBody := Finset.mem_singleton.mp hk
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_sigma.mpr ⟨hkEq ▸ hlast, hl⟩, Or.inl (by omega)⟩
  constructor
  · intro hcount
    have heq : insert point tail = w.selectedLeafPairsFrom i j :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    constructor
    · intro k hk hkLast
      by_contra hn
      obtain ⟨l, hl⟩ := hne k hk
      have hp : (⟨k, l⟩ : Σ _ : ℕ, ℕ) ∈ w.selectedLeafPairsFrom i j :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_sigma.mpr ⟨hk, hl⟩, Or.inl (show i + 1 < k by omega)⟩
      rw [← heq] at hp
      rcases Finset.mem_insert.mp hp with hp | hp
      · have hki := congrArg Sigma.fst hp
        change k = i + 1 at hki
        omega
      · have hki := Finset.mem_singleton.mp (Finset.mem_sigma.mp hp).1
        change k = w.lastSelectedBody at hki
        omega
    · intro l hl
      by_contra hn
      have hp : (⟨i + 1, l⟩ : Σ _ : ℕ, ℕ) ∈ w.selectedLeafPairsFrom i j :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_sigma.mpr ⟨hi, by simpa only [Nat.add_sub_cancel] using hl⟩,
            Or.inr ⟨rfl, show j + 1 ≤ l by omega⟩⟩
      rw [← heq] at hp
      rcases Finset.mem_insert.mp hp with hp | hp
      · have hlj := congrArg (fun p : Σ _ : ℕ, ℕ => p.2) hp
        change l = j + 1 at hlj
        omega
      · have hki := Finset.mem_singleton.mp (Finset.mem_sigma.mp hp).1
        change i + 1 = w.lastSelectedBody at hki
        omega
  · rintro ⟨hbody, hleaf⟩
    have hback : w.selectedLeafPairsFrom i j ⊆ insert point tail := by
      rintro ⟨k, l⟩ hp
      obtain ⟨hpair, hafter⟩ := Finset.mem_filter.mp hp
      obtain ⟨hk, hl⟩ := Finset.mem_sigma.mp hpair
      change i + 1 < k ∨ i + 1 = k ∧ j + 1 ≤ l at hafter
      have hkmax : k ≤ w.lastSelectedBody := Finset.le_sup (f := id) hk
      by_cases hklast : k = w.lastSelectedBody
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_sigma.mpr ⟨Finset.mem_singleton.mpr hklast, hl⟩
      · have hkle := hbody k hk (by omega)
        have hki : k = i + 1 := by omega
        subst k
        have hlle := hleaf l (by simpa only [Nat.add_sub_cancel] using hl)
        have hlj : l = j + 1 := by omega
        subst l
        exact Finset.mem_insert_self _ _
    rw [← Finset.Subset.antisymm hsub hback]
    exact hcard

theorem selectedLeafPairsFrom_last_body_card_le {w : LabeledWord} {i j : ℕ}
    (hi : i + 1 = w.lastSelectedBody) :
    (w.selectedLeafPairsFrom i j).card ≤ w.lastSelectedLabel.card := by
  classical
  let tail : Finset (Σ _ : ℕ, ℕ) :=
    ({w.lastSelectedBody} : Finset ℕ).sigma fun k => w.bodyLabels.getD (k - 1) ∅
  have hsub : w.selectedLeafPairsFrom i j ⊆ tail := by
    intro p hp
    obtain ⟨hpair, hafter⟩ := Finset.mem_filter.mp hp
    obtain ⟨hk, hl⟩ := Finset.mem_sigma.mp hpair
    have hkmax : p.1 ≤ w.lastSelectedBody := Finset.le_sup (f := id) hk
    exact Finset.mem_sigma.mpr ⟨Finset.mem_singleton.mpr (by omega), hl⟩
  have hcard := Finset.card_le_card hsub
  simpa only [tail, Finset.card_sigma, Finset.sum_singleton, lastSelectedLabel] using hcard

end LabeledWord

namespace Payoff

open Erdos591.Negative.Exact

theorem ClearSide.penultimate_endpoint_iff_suffix_card {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) {i j : ℕ}
    (hi : i + 1 ∈ w.rootLabel) (hj : j + 1 ∈ w.bodyLabels.getD i ∅) :
    (w.selectedLeafPairsFrom i j).card = w.lastSelectedLabel.card + 1 ↔
      i + 1 < w.lastSelectedBody ∧
        (∀ k ∈ w.rootLabel, k < w.lastSelectedBody → k ≤ i + 1) ∧
          (∀ l ∈ w.bodyLabels.getD i ∅, l ≤ j + 1) := by
  have hbound : i + 1 ≤ w.lastSelectedBody := Finset.le_sup (f := id) hi
  have hne : ∀ k ∈ w.rootLabel, (w.bodyLabels.getD (k - 1) ∅).Nonempty :=
    fun k hk => Finset.card_pos.mp (h.selected_body_card_pos hk)
  constructor
  · intro hcount
    have hbefore : i + 1 < w.lastSelectedBody := by
      by_contra hn
      have hle := LabeledWord.selectedLeafPairsFrom_last_body_card_le (w := w)
        (j := j) (by omega : i + 1 = w.lastSelectedBody)
      omega
    exact ⟨hbefore, (LabeledWord.selectedLeafPairsFrom_before_last_card_iff
      hi hj hbefore hne).mp hcount⟩
  · rintro ⟨hbefore, hbody, hleaf⟩
    exact (LabeledWord.selectedLeafPairsFrom_before_last_card_iff hi hj hbefore hne).mpr
      ⟨hbody, hleaf⟩

#print axioms LabeledWord.selectedLeafPairsFrom_before_last_card_iff
#print axioms LabeledWord.selectedLeafPairsFrom_last_body_card_le
#print axioms ClearSide.penultimate_endpoint_iff_suffix_card

end Payoff

end Erdos591.Positive.Game
