import Wikipedia.HopfProblem.OrbitPairFiniteChainEnumeration
import Wikipedia.HopfProblem.OrbitPairSimplexWeightRestriction

/-!
# The exact image of a native finite-poset realization

A geometric probability vector lies in the coordinate image precisely
when its positive support is a chain. The reverse implication constructs
an actual nerve simplex and actual restricted geometric weights.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder
open scoped BigOperators Classical

namespace Wikipedia.HopfProblem.OrbitPair.FinitePoset

open FirstHurewicz RealizationSimplex SimplexSupport

variable (P : Type u) [PartialOrder P] [Fintype P]

theorem coordinates_support_isChain (z : SSet.toTop.obj (nerve P)) :
    IsChain (· ≤ ·) {p | 0 < coordinates P z p} := by
  obtain ⟨n, x, t, rfl⟩ := exists_characteristic (nerve P) z
  rw [coordinates_characteristic]
  intro a ha b hb hab
  obtain ⟨i, rfl, hi⟩ := (map_pos_iff x.obj t a).mp ha
  obtain ⟨j, rfl, hj⟩ := (map_pos_iff x.obj t b).mp hb
  rcases le_total i j with hij | hji
  · exact Or.inl (x.monotone hij)
  · exact Or.inr (x.monotone hji)

def positiveChain (t : stdSimplex ℝ P) (ht : IsChain (· ≤ ·) {p | 0 < t p}) :
    NonemptyFiniteChains P where
  finset := Finset.univ.filter (fun p ↦ 0 < t p)
  nonempty := by
    have hsum : 0 < ∑ p, t p := by rw [stdSimplex.sum_eq_one]; exact zero_lt_one
    obtain ⟨p, hp, hpos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun p _ ↦ stdSimplex.zero_le t p)).mp hsum
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpos⟩⟩
  comparable a b := ht.total (Finset.mem_filter.mp a.property).2
    (Finset.mem_filter.mp b.property).2

theorem positiveChain_mem (t : stdSimplex ℝ P)
    (ht : IsChain (· ≤ ·) {p | 0 < t p}) (p : P) :
    p ∈ (positiveChain P t ht).finset ↔ 0 < t p := by
  change p ∈ Finset.univ.filter (fun p ↦ 0 < t p) ↔ _
  simp

theorem mem_coordinates_range_iff (t : stdSimplex ℝ P) :
    t ∈ Set.range (coordinates P) ↔ IsChain (· ≤ ·) {p | 0 < t p} := by
  constructor
  · rintro ⟨z, rfl⟩
    exact coordinates_support_isChain P z
  · intro ht
    let A := positiveChain P t ht
    have hz : ∀ p, p ∉ Set.range (chainVertices A) → t p = 0 := by
      intro p hp
      have hp' : p ∉ A.finset := by
        change p ∉ (A.finset : Set P)
        rwa [chainVertices_range] at hp
      apply le_antisymm
      · apply le_of_not_gt
        intro hpos
        exact hp' ((positiveChain_mem P t ht p).mpr hpos)
      · exact stdSimplex.zero_le t p
    let s := restrictWeights (chainVertices A) (chainVertices_injective A) t hz
    refine ⟨characteristic (nerve P) (A.finset.card - 1) (chainSimplex A) s, ?_⟩
    exact (coordinates_characteristic P (A.finset.card - 1) (chainSimplex A) s).trans
      (map_restrictWeights (chainVertices A) (chainVertices_injective A) t hz)

end Wikipedia.HopfProblem.OrbitPair.FinitePoset
