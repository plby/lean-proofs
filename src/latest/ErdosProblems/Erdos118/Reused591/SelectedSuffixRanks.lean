import ErdosProblems.Erdos118.Reused591.CriticalPair

namespace Erdos118.Reused591

/-!
# Exact suffix counts at a last-body leaf and across adjacent selected bodies

Ranks and suffixes both include their selected endpoint. Their sum is
the whole body cardinality plus one. Between the last leaves of adjacent
selected bodies, the suffix cardinality decreases by the second body's
full label cardinality, including when that label is a singleton.
-/

namespace Erdos591.Positive.Game

theorem finite_rank_add_suffix {α : Type*} [LinearOrder α] (C : Finset α)
    {x : α} (hx : x ∈ C) :
    (C.filter (fun z => z ≤ x)).card + (C.filter (fun z => x ≤ z)).card = C.card + 1 := by
  classical
  have he : C.filter (fun z => x ≤ z) = insert x (C.filter (fun z => ¬ z ≤ x)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hz, hle⟩
      rcases eq_or_lt_of_le hle with heq | hlt
      · exact Or.inl heq.symm
      · exact Or.inr ⟨hz, not_le_of_gt hlt⟩
    · rintro (rfl | ⟨hz, hlt⟩)
      · exact ⟨hx, le_rfl⟩
      · exact ⟨hz, (lt_of_not_ge hlt).le⟩
  have hnot : x ∉ C.filter (fun z => ¬ z ≤ x) := by simp
  rw [he, Finset.card_insert_of_notMem hnot, ← Nat.add_assoc,
    Finset.card_filter_add_card_filter_not]

namespace LabeledWord

theorem selectedLeafPairsFrom_last_rank {w : LabeledWord} {i j : ℕ}
    (hi : i = w.lastSelectedBody) (hipos : 0 < i) (hjpos : 0 < j)
    (hiRoot : i ∈ w.rootLabel) (hj : j ∈ w.bodyLabels.getD (i - 1) ∅) :
    (w.selectedLeafPairsFrom (i - 1) (j - 1)).card +
      ((w.bodyLabels.getD (i - 1) ∅).filter (fun x => x ≤ j)).card =
        (w.bodyLabels.getD (i - 1) ∅).card + 1 := by
  classical
  let D := (w.bodyLabels.getD (i - 1) ∅).filter (fun x => j ≤ x)
  have he : w.selectedLeafPairsFrom (i - 1) (j - 1) =
      ({i} : Finset ℕ).sigma (fun _ => D) := by
    ext p
    simp only [selectedLeafPairsFrom, selectedLeafPairs, Finset.mem_filter,
      Finset.mem_sigma, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hpRoot, hpLeaf⟩, hpAfter⟩
      have hle : p.1 ≤ w.lastSelectedBody := Finset.le_sup (f := id) hpRoot
      have hpi : p.1 = i := by omega
      refine ⟨hpi, Finset.mem_filter.mpr ⟨?_, by omega⟩⟩
      simpa only [hpi] using hpLeaf
    · rintro ⟨hpi, hpD⟩
      obtain ⟨hpLeaf, hjp⟩ := Finset.mem_filter.mp hpD
      exact ⟨⟨hpi ▸ hiRoot, by simpa only [hpi] using hpLeaf⟩,
        Or.inr ⟨by omega, by omega⟩⟩
  rw [he, Finset.card_sigma, Finset.sum_singleton]
  exact (Nat.add_comm _ _).trans (finite_rank_add_suffix _ hj)

theorem selectedLeafPairsFrom_adjacent_last {w : LabeledWord} {i j k l : ℕ}
    (hi : i ∈ w.rootLabel) (hj : j ∈ w.bodyLabels.getD (i - 1) ∅)
    (hk : k ∈ w.rootLabel) (hl : l ∈ w.bodyLabels.getD (k - 1) ∅)
    (hipos : 0 < i) (hjpos : 0 < j) (hkpos : 0 < k) (hlpos : 0 < l)
    (hik : i < k)
    (hnext : ∀ m ∈ w.rootLabel, i < m → k ≤ m)
    (hjl : ∀ x ∈ w.bodyLabels.getD (i - 1) ∅, x ≤ j)
    (hll : ∀ x ∈ w.bodyLabels.getD (k - 1) ∅, x ≤ l) :
    (w.selectedLeafPairsFrom (i - 1) (j - 1)).card =
      (w.selectedLeafPairsFrom (k - 1) (l - 1)).card +
        (w.bodyLabels.getD (k - 1) ∅).card := by
  classical
  let before := w.selectedLeafPairsFrom (i - 1) (j - 1)
  let after := w.selectedLeafPairsFrom (k - 1) (l - 1)
  let point : Σ _ : ℕ, ℕ := ⟨i, j⟩
  let body : Finset (Σ _ : ℕ, ℕ) :=
    ({k} : Finset ℕ).sigma fun _ => (w.bodyLabels.getD (k - 1) ∅).erase l
  have hsub : after ⊆ before := by
    intro p hp
    obtain ⟨hmem, hafter⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hmem, Or.inl (by omega)⟩
  have he : before \ after = insert point body := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpBefore, hpNot⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hmem, hafter⟩ := Finset.mem_filter.mp hpBefore
      obtain ⟨hpRoot, hpLeaf⟩ := Finset.mem_sigma.mp hmem
      have hpNot' : ¬ (k - 1 + 1 < p.1 ∨ k - 1 + 1 = p.1 ∧ l - 1 + 1 ≤ p.2) :=
        fun h => hpNot (Finset.mem_filter.mpr ⟨hmem, h⟩)
      by_cases hpi : p.1 = i
      · have hle := hjl p.2 (by simpa only [hpi] using hpLeaf)
        have hpj : p.2 = j := by omega
        exact Finset.mem_insert.mpr (Or.inl (Sigma.ext hpi (heq_of_eq hpj)))
      · have hpk : p.1 = k := by have := hnext p.1 hpRoot (by omega); omega
        apply Finset.mem_insert_of_mem
        refine Finset.mem_sigma.mpr ⟨Finset.mem_singleton.mpr hpk, Finset.mem_erase.mpr ?_⟩
        exact ⟨by omega, by simpa only [hpk] using hpLeaf⟩
    · intro hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · apply Finset.mem_sdiff.mpr
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨hi, hj⟩,
          Or.inr ⟨by change i - 1 + 1 = i; omega, by change j - 1 + 1 ≤ j; omega⟩⟩,
          fun h => by have := (Finset.mem_filter.mp h).2; dsimp [point] at this; omega⟩
      · obtain ⟨hpFirst, hpLeaf⟩ := Finset.mem_sigma.mp hp
        have hpk : p.1 = k := Finset.mem_singleton.mp hpFirst
        obtain ⟨hpne, hpLeaf⟩ := Finset.mem_erase.mp hpLeaf
        have hle := hll p.2 hpLeaf
        apply Finset.mem_sdiff.mpr
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr
          ⟨hpk ▸ hk, by simpa only [hpk] using hpLeaf⟩, Or.inl (by omega)⟩,
          fun h => by have := (Finset.mem_filter.mp h).2; omega⟩
  have hnot : point ∉ body := by
    intro h
    have heq := Finset.mem_singleton.mp (Finset.mem_sigma.mp h).1
    exact hik.ne heq
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [he, Finset.card_insert_of_notMem hnot, Finset.card_sigma, Finset.sum_singleton,
    Finset.card_erase_of_mem hl] at hcard
  have hpos := Finset.card_pos.mpr ⟨l, hl⟩
  dsimp only [before, after] at hcard
  omega

#print axioms selectedLeafPairsFrom_last_rank
#print axioms selectedLeafPairsFrom_adjacent_last

end LabeledWord

end Erdos591.Positive.Game

end Erdos118.Reused591
