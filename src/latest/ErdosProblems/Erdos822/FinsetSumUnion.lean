/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

namespace Erdos822

open scoped BigOperators

theorem sum_union_le_add_sum
    {α : Type*} [DecidableEq α] {s t : Finset α} {f : α → ℝ}
    (hf : ∀ a ∈ t, 0 ≤ f a) :
    ∑ a ∈ s ∪ t, f a ≤ (∑ a ∈ s, f a) + ∑ a ∈ t, f a := by
  let u := t \ s
  have hdisj : Disjoint s u := by
    rw [Finset.disjoint_left]
    intro a has hau
    exact (Finset.mem_sdiff.mp hau).2 has
  have hunion : s ∪ t = s ∪ u := by
    ext a
    simp [u]
  rw [hunion, Finset.sum_union hdisj]
  have hu : ∑ a ∈ u, f a ≤ ∑ a ∈ t, f a := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    intro a ha hnot
    exact hf a ha
  linarith

theorem sum_biUnion_le_sum
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (s : Finset ι) (t : ι → Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ s, ∀ a ∈ t i, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      have hnonneg : ∀ a ∈ t i, 0 ≤ f a := fun a ha => hf i (by simp) a ha
      have htail : ∀ j ∈ s, ∀ a ∈ t j, 0 ≤ f a := by
        intro j hj a ha
        exact hf j (by simp [hj]) a ha
      calc
        (∑ a ∈ (insert i s).biUnion t, f a) =
            ∑ a ∈ t i ∪ s.biUnion t, f a := by simp [his]
        _ ≤ (∑ a ∈ t i, f a) + ∑ a ∈ s.biUnion t, f a :=
          sum_union_le_add_sum (fun a ha => by
            rw [Finset.mem_biUnion] at ha
            obtain ⟨j, hj, haj⟩ := ha
            exact htail j hj a haj)
        _ ≤ (∑ a ∈ t i, f a) + ∑ j ∈ s, ∑ a ∈ t j, f a := by
          linarith [ih htail]
        _ = ∑ j ∈ insert i s, ∑ a ∈ t j, f a := by simp [his]

end Erdos822
