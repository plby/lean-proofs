import Mathlib

open Finset

namespace Erdos767

/-!
A finite set of pairwise nonconsecutive natural numbers in the interval
`[ℓ + 1, c - ℓ - 1]` has at most half the size of the interval obtained by
adjoining one extra point at its right end.

The proof pairs every `i ∈ S` with `i + 1`.  The original set and the set
of successors are disjoint, while their union is contained in
`[ℓ + 1, c - ℓ]`.
-/
theorem two_mul_card_le_of_no_consecutive
    (S : Finset ℕ) (ell c : ℕ)
    (hlo : ∀ i ∈ S, ell + 1 ≤ i)
    (hhi : ∀ i ∈ S, i ≤ c - ell - 1)
    (hnc : ∀ i ∈ S, i + 1 ∉ S) :
    2 * S.card ≤ c - 2 * ell := by
  let T : Finset ℕ := S.image (fun i ↦ i + 1)
  have hTcard : T.card = S.card := by
    dsimp [T]
    exact card_image_of_injective S (fun _ _ h ↦ Nat.add_right_cancel h)
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    change i ∈ S.image (fun j ↦ j + 1) at hiT
    rw [mem_image] at hiT
    obtain ⟨j, hjS, rfl⟩ := hiT
    exact hnc j hjS hiS
  have hunion : S ∪ T ⊆ Finset.Icc (ell + 1) (c - ell) := by
    intro i hi
    rw [mem_union] at hi
    rw [Finset.mem_Icc]
    rcases hi with hiS | hiT
    · exact ⟨hlo i hiS, by have := hhi i hiS; omega⟩
    · change i ∈ S.image (fun j ↦ j + 1) at hiT
      rw [mem_image] at hiT
      obtain ⟨j, hjS, rfl⟩ := hiT
      constructor
      · have := hlo j hjS
        omega
      · have := hhi j hjS
        have := hlo j hjS
        omega
  calc
    2 * S.card = S.card + T.card := by rw [hTcard]; omega
    _ = (S ∪ T).card := by rw [card_union_of_disjoint hdisj]
    _ ≤ (Finset.Icc (ell + 1) (c - ell)).card := card_le_card hunion
    _ = c - 2 * ell := by rw [Nat.card_Icc]; omega

end Erdos767

