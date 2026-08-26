import Mathlib.Data.Finset.Card

/-! # A selected element is determined by its one-based rank in a finite linear order -/

namespace Erdos591.Positive.Game

theorem finite_rank_mono {α : Type*} [LinearOrder α] (C : Finset α)
    {x y : α} (hxy : x ≤ y) :
    (C.filter (fun z => z ≤ x)).card ≤ (C.filter (fun z => z ≤ y)).card := by
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzC, hzx⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hzC, hzx.trans hxy⟩

theorem finite_rank_strict_of_lt {α : Type*} [LinearOrder α] (C : Finset α)
    {x y : α} (hy : y ∈ C) (hxy : x < y) :
    (C.filter (fun z => z ≤ x)).card < (C.filter (fun z => z ≤ y)).card := by
  have hsub : C.filter (fun z => z ≤ x) ⊆ C.filter (fun z => z ≤ y) := by
    intro z hz
    obtain ⟨hzC, hzx⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hzC, hzx.trans hxy.le⟩
  have hmem : y ∈ C.filter (fun z => z ≤ y) := Finset.mem_filter.mpr ⟨hy, le_rfl⟩
  have hnot : y ∉ C.filter (fun z => z ≤ x) := by
    intro h
    exact not_le_of_gt hxy (Finset.mem_filter.mp h).2
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub, fun heq => hnot (heq ▸ hmem)⟩)

theorem finite_rank_successor {α : Type*} [LinearOrder α] (C : Finset α)
    {x y : α} (hy : y ∈ C)
    (hrank : (C.filter (fun z => z ≤ y)).card = (C.filter (fun z => z ≤ x)).card + 1) :
    x < y ∧ ∀ z ∈ C, x < z → y ≤ z := by
  constructor
  · by_contra h
    have hm := finite_rank_mono C (le_of_not_gt h)
    omega
  · intro z hz hxz
    by_contra hyz
    have hfirst := finite_rank_strict_of_lt C hz hxz
    have hsecond := finite_rank_strict_of_lt C hy (lt_of_not_ge hyz)
    omega

theorem finite_rank_injective {α : Type*} [LinearOrder α] (C : Finset α)
    {x y : α} (hx : x ∈ C) (hy : y ∈ C)
    (hrank : (C.filter (fun z => z ≤ x)).card = (C.filter (fun z => z ≤ y)).card) : x = y := by
  have increasing {a b : α} (hb : b ∈ C) (hab : a < b) :
      (C.filter (fun z => z ≤ a)).card < (C.filter (fun z => z ≤ b)).card := by
    have hsub : C.filter (fun z => z ≤ a) ⊆ C.filter (fun z => z ≤ b) := by
      intro z hz
      obtain ⟨hzC, hza⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hzC, hza.trans hab.le⟩
    have hmem : b ∈ C.filter (fun z => z ≤ b) := Finset.mem_filter.mpr ⟨hb, le_rfl⟩
    have hnot : b ∉ C.filter (fun z => z ≤ a) := by
      intro h
      exact not_le_of_gt hab (Finset.mem_filter.mp h).2
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hsub, fun heq => hnot (heq ▸ hmem)⟩)
  rcases lt_trichotomy x y with h | h | h
  · have hlt := increasing hy h
    rw [hrank] at hlt
    exact (Nat.lt_irrefl _ hlt).elim
  · exact h
  · have hlt := increasing hx h
    rw [hrank] at hlt
    exact (Nat.lt_irrefl _ hlt).elim

#print axioms finite_rank_injective
#print axioms finite_rank_successor

end Erdos591.Positive.Game
