import ErdosProblems.Erdos118.LeafSuffixCounts
import ErdosProblems.Erdos118.InsideCounts

/-! A selected suffix consists exactly of its current point and the whole
last-body fiber precisely at the penultimate selected-body last entry. -/

namespace Erdos118.SelectedEndpointCounts

open LabelledExtensions DecisionStates CutIndices SelectedGapCounts InsideCounts
open LastBodyRefinement LastMarkerRefinement LeafSuffixCounts

def lastFiber (S : Completed) : Finset (Σ _ : ℕ, ℕ) :=
  (selected S.stem).filter (fun a ↦ a.1 = lastIndex S)

theorem lastFiber_card (S : Completed) (hS : S.stem.rootLabel ≠ []) :
    (lastFiber S).card = (lastLabel S).length := by
  have hi : lastIndex S < S.stem.bodyLabels.length := by
    simpa only [Stem.bodyLabels, List.length_map] using lastIndex_lt S hS
  have hl : lastLabel S = S.stem.bodyLabels[lastIndex S] := by
    simp only [lastLabel, List.getElem?_eq_getElem hi, Option.getD_some]
  have hcard : (lastFiber S).card = (lastLabel S).toFinset.card := by
    apply Finset.card_bij (fun a _ ↦ a.2)
    · intro a ha
      obtain ⟨ha, he⟩ := Finset.mem_filter.mp ha
      obtain ⟨hai, haj⟩ := (mem_selected _ _ _).mp ha
      apply List.mem_toFinset.mpr
      rw [hl]
      simpa only [he] using haj
    · intro a ha b hb he
      have hai := (Finset.mem_filter.mp ha).2
      have hbi := (Finset.mem_filter.mp hb).2
      cases a
      cases b
      simp_all
    · intro j hj
      refine ⟨⟨lastIndex S, j⟩, Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
      exact (mem_selected _ _ _).mpr ⟨hi, by simpa only [hl] using List.mem_toFinset.mp hj⟩
  rw [hcard, List.toFinset_card_of_nodup]
  rw [hl]
  exact (ProjectionBounds.body_label_pairwise S.stem _ hi).nodup

theorem remaining_last_le (S : Completed) (T : Stem) (h : ExactAnnotations S.stem T)
    (hS : S.stem.rootLabel ≠ []) (j : ℕ) :
    (remaining S.stem (lastIndex S) j).card ≤ (lastLabel S).length := by
  rw [← lastFiber_card S hS]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨ha, hafter⟩ := Finset.mem_filter.mp ha
  have hle := selected_index_le_last S T h hS a ha
  exact Finset.mem_filter.mpr ⟨ha, by omega⟩

theorem remaining_card_iff (S : Completed) (T : Stem) (h : ExactAnnotations S.stem T)
    (hS : S.stem.rootLabel ≠ []) (i j : ℕ) (hij : (⟨i, j⟩ : Σ _ : ℕ, ℕ) ∈ selected S.stem) :
    (remaining S.stem i j).card = (lastLabel S).length + 1 ↔
      i < lastIndex S ∧
      (∀ a ∈ selected S.stem, a.1 < lastIndex S → a.1 ≤ i) ∧
      (∀ a ∈ selected S.stem, a.1 = i → a.2 ≤ j) := by
  classical
  have himax : i ≤ lastIndex S := selected_index_le_last S T h hS ⟨i, j⟩ hij
  have hbase (hi : i < lastIndex S) :
      insert (⟨i, j⟩ : Σ _ : ℕ, ℕ) (lastFiber S) ⊆ remaining S.stem i j := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_filter.mpr ⟨hij, Or.inr ⟨rfl, le_rfl⟩⟩
    · obtain ⟨ha, he⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨ha, Or.inl (hi.trans_eq he.symm)⟩
  have hcard (hi : i < lastIndex S) :
      (insert (⟨i, j⟩ : Σ _ : ℕ, ℕ) (lastFiber S)).card = (lastLabel S).length + 1 := by
    have hn : (⟨i, j⟩ : Σ _ : ℕ, ℕ) ∉ lastFiber S := by
      intro hm
      exact hi.ne (Finset.mem_filter.mp hm).2
    rw [Finset.card_insert_of_notMem hn, lastFiber_card S hS]
  constructor
  · intro hc
    have hi : i < lastIndex S := by
      by_contra hn
      have he : i = lastIndex S := by omega
      have hle := remaining_last_le S T h hS j
      rw [← he] at hle
      omega
    have he : insert (⟨i, j⟩ : Σ _ : ℕ, ℕ) (lastFiber S) = remaining S.stem i j :=
      Finset.eq_of_subset_of_card_le (hbase hi) (by rw [hc, hcard hi])
    refine ⟨hi, ?_, ?_⟩
    · intro a ha hbefore
      by_contra hn
      have hm : a ∈ remaining S.stem i j :=
        Finset.mem_filter.mpr ⟨ha, Or.inl (Nat.lt_of_not_ge hn)⟩
      rw [← he] at hm
      rcases Finset.mem_insert.mp hm with hp | hp
      · have hb := congrArg Sigma.fst hp
        change a.1 = i at hb
        omega
      · have hb := (Finset.mem_filter.mp hp).2
        omega
    · intro a ha hai
      by_contra hn
      have hm : a ∈ remaining S.stem i j :=
        Finset.mem_filter.mpr ⟨ha, Or.inr ⟨hai.symm, (Nat.lt_of_not_ge hn).le⟩⟩
      rw [← he] at hm
      rcases Finset.mem_insert.mp hm with hp | hp
      · have hj := congrArg (fun b : Σ _ : ℕ, ℕ ↦ b.2) hp
        change a.2 = j at hj
        omega
      · have hb := (Finset.mem_filter.mp hp).2
        omega
  · rintro ⟨hi, hbody, hleaf⟩
    have hback : remaining S.stem i j ⊆ insert (⟨i, j⟩ : Σ _ : ℕ, ℕ) (lastFiber S) := by
      intro a ha
      obtain ⟨ha, hafter⟩ := Finset.mem_filter.mp ha
      have hmax := selected_index_le_last S T h hS a ha
      by_cases he : a.1 = lastIndex S
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨ha, he⟩)
      · have hb := hbody a ha (lt_of_le_of_ne hmax he)
        have hai : a.1 = i := by omega
        have hl := hleaf a ha hai
        have haj : a.2 = j := by omega
        have hap : a = (⟨i, j⟩ : Σ _ : ℕ, ℕ) := by
          cases a
          simp_all
        exact Finset.mem_insert.mpr (Or.inl hap)
    rw [← Finset.Subset.antisymm (hbase hi) hback]
    exact hcard hi

end Erdos118.SelectedEndpointCounts
