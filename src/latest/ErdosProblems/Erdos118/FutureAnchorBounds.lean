import ErdosProblems.Erdos118.SplicedRootReserve
import ErdosProblems.Erdos118.StrictCriticalBounds

/-! A full future nonfinal body fiber leaves two additional pairs
in the critical suffix, giving the finite anchor-size bound. -/

namespace Erdos118.FutureAnchorBounds

open LabelledExtensions DecisionStates CutIndices SelectedGapCounts LeafSuffixCounts

theorem selected_body (S : Completed) (T : Stem) (h : ExactAnnotations S.stem T)
    (i : ℕ) (hi : i ∈ S.stem.rootLabel) :
    0 < i ∧ ∃ j : ℕ, (⟨i - 1, j⟩ : Σ _ : ℕ, ℕ) ∈ selected S.stem := by
  obtain ⟨a, j, hcut, rfl⟩ := (h.root i).mp hi
  have hbound : a < S.stem.bodyLabels.length := by
    have hb := S.stem.label_before_root _ hi
    have hf := S.full
    simp only [Stem.bodyLabels, List.length_map]
    omega
  refine ⟨by omega, j, ?_⟩
  simpa only [Nat.add_sub_cancel] using
    (mem_selected S.stem a j).mpr ⟨hbound, (h.body a hbound j).mpr hcut⟩

theorem body_add_two_le (S : Stem) {n : ℕ} {p : Σ _ : ℕ, ℕ}
    (hp : CriticalPair.Spec S n p) (i : ℕ) (hi : i < S.bodyLabels.length) (hpi : p.1 < i)
    (z : Σ _ : ℕ, ℕ) (hz : z ∈ selected S) (hiz : i < z.1) :
    (S.bodyLabels.getD i []).length + 2 ≤ n := by
  classical
  let body : Finset (Σ _ : ℕ, ℕ) := ({i} : Finset ℕ).sigma
    (fun j ↦ (S.bodyLabels.getD j []).toFinset)
  have hnotP : p ∉ body := by
    intro hm
    have he := Finset.mem_singleton.mp (Finset.mem_sigma.mp hm).1
    omega
  have hnotZ : z ∉ insert p body := by
    intro hm
    rcases Finset.mem_insert.mp hm with he | hm
    · have he' := congrArg Sigma.fst he
      omega
    · have he := Finset.mem_singleton.mp (Finset.mem_sigma.mp hm).1
      omega
  have hsub : insert z (insert p body) ⊆ remaining S p.1 p.2 := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_filter.mpr ⟨hz, Or.inl (hpi.trans hiz)⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_filter.mpr ⟨hp.1, Or.inr ⟨rfl, le_rfl⟩⟩
    · obtain ⟨hqFirst, hqLeaf⟩ := Finset.mem_sigma.mp hq
      have he : q.1 = i := Finset.mem_singleton.mp hqFirst
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (he ▸ hi), hqLeaf⟩,
          Or.inl (he ▸ hpi)⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnotZ, Finset.card_insert_of_notMem hnotP, hp.2] at hcard
  have hnd : (S.bodyLabels.getD i []).Nodup := by
    rw [List.getD_eq_getElem _ _ hi]
    exact (ProjectionBounds.body_label_pairwise S i hi).nodup
  simpa only [body, Finset.card_sigma, Finset.sum_singleton,
    List.toFinset_card_of_nodup hnd, Nat.add_assoc] using hcard

theorem spliced_anchor {H : Set ℕ} {b k l v r n : ℕ}
    (L : SplicedRootReserve.Labels H b k l v r) (hr : r < l + 1)
    (S : Completed) (T : Stem) (h : ExactAnnotations S.stem T)
    (hroot : S.stem.rootLabel = L.upper)
    (hp : CriticalPair.Spec S.stem n (CriticalPair.pair S.stem n))
    (hrank : CriticalPair.bodyRank S.stem n + 1 = r) :
    0 < (S.stem.bodyLabels.getD (L.next - 1) []).length ∧
      (S.stem.bodyLabels.getD (L.next - 1) []).length + 2 ≤ n := by
  classical
  let p := CriticalPair.pair S.stem n
  have hanchor : L.next ∈ S.stem.rootLabel := hroot ▸ L.nextUpper
  have hpRoot : p.1 + 1 ∈ S.stem.rootLabel := StrictCriticalBounds.selected_root S.stem T h p hp.1
  have hanchorRank : LabelRanks.rank S.stem.rootLabel L.next = r := hroot ▸ L.upperRank
  have hpairRank : LabelRanks.rank S.stem.rootLabel (p.1 + 1) + 1 = r := hrank
  have hpa : p.1 + 1 < L.next := by
    rcases lt_trichotomy (p.1 + 1) L.next with hlt | he | hlt
    · exact hlt
    · rw [he, hanchorRank] at hpairRank
      omega
    · have hc := LabelRanks.rank_lt hpRoot hlt
      omega
  have hlater : ∃ z ∈ S.stem.rootLabel, L.next < z := by
    by_contra hn
    have hall : ∀ z ∈ S.stem.rootLabel, z ≤ L.next := by
      intro z hz
      by_contra he
      exact hn ⟨z, hz, Nat.lt_of_not_ge he⟩
    have he : S.stem.rootLabel.toFinset.filter (· ≤ L.next) = S.stem.rootLabel.toFinset :=
      Finset.filter_eq_self.mpr (fun z hz ↦ hall z (List.mem_toFinset.mp hz))
    have hfull : LabelRanks.rank S.stem.rootLabel L.next = S.stem.rootLabel.length := by
      rw [LabelRanks.rank, he, List.toFinset_card_of_nodup S.stem.label_pairwise.nodup]
    rw [hanchorRank, hroot, L.upperCard] at hfull
    omega
  obtain ⟨z, hz, haz⟩ := hlater
  obtain ⟨haPos, a, ha⟩ := selected_body S T h L.next hanchor
  obtain ⟨hzPos, c, hc⟩ := selected_body S T h z hz
  obtain ⟨haBound, haMem⟩ := (mem_selected S.stem (L.next - 1) a).mp ha
  have hlabelPos : 0 < (S.stem.bodyLabels.getD (L.next - 1) []).length := by
    rw [List.getD_eq_getElem _ _ haBound]
    exact List.length_pos_iff.mpr (List.ne_nil_of_mem haMem)
  exact ⟨hlabelPos, body_add_two_le S.stem hp (L.next - 1) haBound
    (by change p.1 < L.next - 1; omega)
    ⟨z - 1, c⟩ hc (by dsimp only; omega)⟩

end Erdos118.FutureAnchorBounds
