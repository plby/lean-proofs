import ErdosProblems.Erdos118.Reused591.FastSequence

namespace Erdos118.Reused591

/-! # Exact ranks and maxima of increasing finite labels -/

namespace Erdos591.Positive.Game

theorem image_range_filter_le (f : ℕ → ℕ) (hf : StrictMono f) {n i : ℕ} (hi : i < n) :
    ((Finset.range n).image f).filter (fun x => x ≤ f i) = (Finset.range (i + 1)).image f := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hle⟩ := Finset.mem_filter.mp hx
    obtain ⟨m, _hm, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr
      ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le (hf.le_iff_le.mp hle)), rfl⟩
  · intro hx
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
    have hmi : m ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (hmi.trans_lt hi), rfl⟩, hf.monotone hmi⟩

theorem image_range_rank (f : ℕ → ℕ) (hf : StrictMono f) {n i : ℕ} (hi : i < n) :
    (((Finset.range n).image f).filter (fun x => x ≤ f i)).card = i + 1 := by
  rw [image_range_filter_le f hf hi, Finset.card_image_of_injective _ hf.injective]
  exact Finset.card_range _

theorem image_range_sup (f : ℕ → ℕ) (hf : StrictMono f) {n : ℕ} (hn : 0 < n) :
    ((Finset.range n).image f).sup id = f (n - 1) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hf.monotone (by have := Finset.mem_range.mp hi; omega)
  · exact Finset.le_sup (f := id)
      (Finset.mem_image.mpr ⟨n - 1, Finset.mem_range.mpr (by omega), rfl⟩)

#print axioms image_range_rank

end Erdos591.Positive.Game

end Erdos118.Reused591
