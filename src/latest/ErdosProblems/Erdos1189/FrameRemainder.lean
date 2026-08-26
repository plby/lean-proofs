/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The size budget for large-coordinate frame families and their remainder.
Informal source: BBMST equations (29)--(32).
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.LargeCoordinateWeights
import ErdosProblems.Erdos1189.GeneralizedFrame

namespace Erdos1189

open Finset

variable {N : ℕ} {H : ℕ → Grid.Box (@coordinateSize N)} {D : Finset ℕ} {δ : ℝ}

def largeFrameUnion (frame : Grid.GeneralizedFrame H D δ) (T : ℕ) : Finset ℕ :=
  (largeCoordinates N T).biUnion frame.families

lemma largeFrameUnion_subset (frame : Grid.GeneralizedFrame H D δ) (T : ℕ) :
    largeFrameUnion frame T ⊆ D := by
  intro d hd
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hd
  exact frame.subset i hi

lemma largeFrameUnion_card (frame : Grid.GeneralizedFrame H D δ) {T : ℕ}
    (hT : 1 / δ ≤ (T : ℝ)) :
    (largeFrameUnion frame T).card = ∑ i ∈ largeCoordinates N T, (frame.families i).card := by
  apply card_biUnion
  intro i hi j hj hij
  have hlarge : ∀ c ∈ largeCoordinates N T, 1 / δ ≤ (coordinateSize c : ℝ) := by
    intro c hc
    have hct : T ≤ coordinateSize c := (mem_filter.mp hc).2.le
    exact hT.trans (by exact_mod_cast hct)
  exact frame.disjoint i j hij (hlarge i hi) (hlarge j hj)

lemma largeFrameUnion_size_lower (frame : Grid.GeneralizedFrame H D δ) {T : ℕ}
    (hT : 1 / δ ≤ (T : ℝ)) {η : ℝ}
    (hsize : (1 - η) * simpsonWeight N ≤ ∑ i, ((frame.families i).card : ℝ)) :
    (largeCoordinateWeight N T : ℝ) - η * simpsonWeight N ≤ (largeFrameUnion frame T).card := by
  let w := fun c : PrimeCoordinate N => ((coordinateSize c - 1 : ℕ) : ℝ)
  let r := fun c : PrimeCoordinate N => ((frame.families c).card : ℝ)
  have hnonneg : ∀ c : PrimeCoordinate N, 0 ≤ w c - r c := by
    intro c
    have h : r c ≤ w c := by
      dsimp only [r, w]
      exact_mod_cast frame.card_le c
    linarith
  have hdeficit : (∑ c ∈ largeCoordinates N T, (w c - r c)) ≤ (∑ c, (w c - r c)) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun c _ _ => hnonneg c)
  have hwall : (∑ c, w c) = (simpsonWeight N : ℝ) := by
    rw [← sum_coordinateSize]
    exact (Nat.cast_sum _ _).symm
  have hwlarge : (∑ c ∈ largeCoordinates N T, w c) = (largeCoordinateWeight N T : ℝ) :=
    (Nat.cast_sum _ _).symm
  have hrlarge : (∑ c ∈ largeCoordinates N T, r c) = (largeFrameUnion frame T).card := by
    rw [largeFrameUnion_card frame hT]
    exact (Nat.cast_sum _ _).symm
  rw [sum_sub_distrib, sum_sub_distrib, hwall, hwlarge, hrlarge] at hdeficit
  change (1 - η) * simpsonWeight N ≤ ∑ c, r c at hsize
  linarith

lemma largeFrame_remainder_budget (frame : Grid.GeneralizedFrame H D δ) {T : ℕ}
    (hT : 1 / δ ≤ (T : ℝ)) {η : ℝ}
    (hsize : (1 - η) * simpsonWeight N ≤ ∑ i, ((frame.families i).card : ℝ)) :
    (largeCoordinateWeight N T : ℝ) + (D \ largeFrameUnion frame T).card ≤
      D.card + η * simpsonWeight N := by
  have hlow := largeFrameUnion_size_lower frame hT hsize
  have hcard := card_sdiff_add_card_eq_card (largeFrameUnion_subset frame T)
  have hcard' : ((D \ largeFrameUnion frame T).card : ℝ) + (largeFrameUnion frame T).card =
      D.card := by exact_mod_cast hcard
  linarith

end Erdos1189
