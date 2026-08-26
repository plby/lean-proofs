import ErdosProblems.Erdos118.CriticalPair

/-! Exact prefix ranks in a finite increasing label list. -/

namespace Erdos118.LabelRanks

def rank (C : List ℕ) (i : ℕ) : ℕ := (C.toFinset.filter (· ≤ i)).card

theorem rank_lt {C : List ℕ} {i j : ℕ} (hj : j ∈ C) (hij : i < j) :
    rank C i < rank C j := by
  have hsub : C.toFinset.filter (· ≤ i) ⊆ C.toFinset.filter (· ≤ j) := by
    intro x hx
    obtain ⟨hx, hxi⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx, hxi.trans hij.le⟩
  have hm : j ∈ C.toFinset.filter (· ≤ j) :=
    Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hj, le_rfl⟩
  have hn : j ∉ C.toFinset.filter (· ≤ i) := by
    intro hx
    exact (not_le_of_gt hij) (Finset.mem_filter.mp hx).2
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun he ↦ hn (he ▸ hm)⟩)

theorem rank_injective {C : List ℕ} {i j : ℕ} (hi : i ∈ C) (hj : j ∈ C)
    (he : rank C i = rank C j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hlt := rank_lt hj h
    omega
  · exact h
  · have hlt := rank_lt hi h
    omega

theorem exists_label (C : List ℕ) (hC : C.Nodup) (n : ℕ) (hn : 0 < n)
    (hbound : n ≤ C.length) : ∃ i ∈ C, rank C i = n := by
  have hcard : C.toFinset.card = C.length := List.toFinset_card_of_nodup hC
  have hsub : C.toFinset.image (rank C) ⊆ Finset.Icc 1 C.length := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have hm : i ∈ C.toFinset.filter (· ≤ i) := Finset.mem_filter.mpr ⟨hi, le_rfl⟩
    have hpos := Finset.card_pos.mpr ⟨i, hm⟩
    have hle := Finset.card_filter_le C.toFinset (· ≤ i)
    exact Finset.mem_Icc.mpr ⟨hpos, hcard ▸ hle⟩
  have hinj : Set.InjOn (rank C) C.toFinset := by
    intro i hi j hj he
    exact rank_injective (List.mem_toFinset.mp hi) (List.mem_toFinset.mp hj) he
  have he : C.toFinset.image (rank C) = Finset.Icc 1 C.length := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injOn hinj, hcard, Nat.card_Icc]
    omega
  have hm : n ∈ C.toFinset.image (rank C) := he ▸ Finset.mem_Icc.mpr ⟨hn, hbound⟩
  obtain ⟨i, hi, hri⟩ := Finset.mem_image.mp hm
  exact ⟨i, List.mem_toFinset.mp hi, hri⟩

end Erdos118.LabelRanks
