import ErdosProblems.Erdos118.Reused591.SelectedSuffixRanks

namespace Erdos118.Reused591

/-!
# Suffix-rank conservation inside one selected body

The suffix starting at a selected leaf consists of the current body's
inclusive upper tail and all selected pairs in later bodies. Adding
the leaf's inclusive rank makes the count independent of that leaf.
-/

namespace Erdos591.Positive.Game.LabeledWord

theorem selectedLeafPairsFrom_card_add_rank {w : LabeledWord} {i j : ℕ}
    (hi : i ∈ w.rootLabel) (hj : j ∈ w.bodyLabels.getD (i - 1) ∅)
    (hipos : 0 < i) (hjpos : 0 < j) :
    (w.selectedLeafPairsFrom (i - 1) (j - 1)).card +
        ((w.bodyLabels.getD (i - 1) ∅).filter (fun x => x ≤ j)).card =
      (w.selectedLeafPairs.filter (fun p => i < p.1)).card +
        (w.bodyLabels.getD (i - 1) ∅).card + 1 := by
  classical
  let C := w.bodyLabels.getD (i - 1) ∅
  let current : Finset (Σ _ : ℕ, ℕ) :=
    ({i} : Finset ℕ).sigma fun _ => C.filter (fun x => j ≤ x)
  let later := w.selectedLeafPairs.filter (fun p => i < p.1)
  have heq : w.selectedLeafPairsFrom (i - 1) (j - 1) = later ∪ current := by
    ext p
    constructor
    · intro hp
      obtain ⟨hmem, hafter⟩ := Finset.mem_filter.mp hp
      rcases hafter with hlt | ⟨he, hle⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmem, by omega⟩)
      · have hpi : p.1 = i := by omega
        apply Finset.mem_union_right
        exact Finset.mem_sigma.mpr ⟨Finset.mem_singleton.mpr hpi,
          Finset.mem_filter.mpr ⟨by
            simpa only [C, hpi] using (Finset.mem_sigma.mp hmem).2, by omega⟩⟩
    · intro hp
      rcases Finset.mem_union.mp hp with hp | hp
      · obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨hmem, Or.inl (by omega)⟩
      · obtain ⟨hfirst, htail⟩ := Finset.mem_sigma.mp hp
        have hpi : p.1 = i := Finset.mem_singleton.mp hfirst
        obtain ⟨hmem, hle⟩ := Finset.mem_filter.mp htail
        exact Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr
          ⟨hpi ▸ hi, by simpa only [C, hpi] using hmem⟩,
          Or.inr ⟨by omega, by omega⟩⟩
  have hdis : Disjoint later current := by
    apply Finset.disjoint_left.mpr
    intro p hl hc
    have hlt := (Finset.mem_filter.mp hl).2
    have he := Finset.mem_singleton.mp (Finset.mem_sigma.mp hc).1
    omega
  rw [heq, Finset.card_union_of_disjoint hdis]
  simp only [current, Finset.card_sigma, Finset.sum_singleton]
  have hsum := finite_rank_add_suffix C hj
  dsimp only [C, later] at *
  omega

theorem selectedLeafPairsFrom_same_body_rank {w : LabeledWord} {i j l : ℕ}
    (hi : i ∈ w.rootLabel) (hj : j ∈ w.bodyLabels.getD (i - 1) ∅)
    (hl : l ∈ w.bodyLabels.getD (i - 1) ∅)
    (hipos : 0 < i) (hjpos : 0 < j) (hlpos : 0 < l) :
    (w.selectedLeafPairsFrom (i - 1) (j - 1)).card +
        ((w.bodyLabels.getD (i - 1) ∅).filter (fun x => x ≤ j)).card =
      (w.selectedLeafPairsFrom (i - 1) (l - 1)).card +
        ((w.bodyLabels.getD (i - 1) ∅).filter (fun x => x ≤ l)).card :=
  (selectedLeafPairsFrom_card_add_rank hi hj hipos hjpos).trans
    (selectedLeafPairsFrom_card_add_rank hi hl hipos hlpos).symm

#print axioms selectedLeafPairsFrom_card_add_rank
#print axioms selectedLeafPairsFrom_same_body_rank

end Erdos591.Positive.Game.LabeledWord

end Erdos118.Reused591
