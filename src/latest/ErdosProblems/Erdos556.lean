import ErdosProblems.Erdos556.RamseyNumber
import ErdosProblems.Erdos556.UniformProfileRefinement
import ErdosProblems.Erdos556.FourMatchingFinisher

/-!
# Erdős problem 556: the sharp result for sufficiently large odd cycles

The main theorem `Erdos556.erdos556` states that there is a natural threshold
above which every odd cycle has three-colour Ramsey number `4 * n - 3`.
It does not assert the unrestricted finite-order conjecture.

The upper bound uses the proved odd-cycle decomposition and spectrum theorems,
the finite cube-profile inequality and its stability theorem, refinement of
face profiles by the proved two-colour structure theorem, and the two exact
four-core finishers. All of these ingredients are proved in the supporting
directory. The lower bound is the explicit four-block colouring
`sharpColouring`, on `Bool × Bool × Fin (n - 1)`.
-/

namespace Erdos556

open SimpleGraph

/-- Every sufficiently large odd cycle is forced on `4 * n - 3` vertices. -/
theorem eventually_isRamseyOrder_odd_cycle :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Odd n → IsRamseyOrder n (4 * n - 3) := by
  obtain ⟨n₁, hclean⟩ := exists_clean_profile_system profileRefinementError profileRefinementError_pos
  obtain ⟨R₀, hrefine⟩ := exists_uniform_profile_refinements
  refine ⟨max n₁ (2 * max R₀ 4 + 1), ?_⟩
  intro n hn hodd c
  classical
  obtain ⟨r, hr⟩ := hodd
  have hnrepr : n = 2 * r + 1 := by omega
  subst n
  have hlarge : n₁ ≤ 2 * r + 1 := (le_max_left _ _).trans hn
  have hr₀ : R₀ ≤ r := by omega
  have hr4 : 4 ≤ r := by omega
  have hodd : Odd (2 * r + 1) := ⟨r, by omega⟩
  by_contra hnot
  have hno : ∀ i, ¬ cycleGraph (2 * r + 1) ⊑ c.graph i := fun i hi => hnot ⟨i, hi⟩
  obtain ⟨h⟩ := hclean c (2 * r + 1) hlarge hodd (by simp only [Fintype.card_fin]) hno
  obtain ⟨cores⟩ := four_matching_cores_of_refinements h (hrefine c r hr₀ hno h)
  have horder : 8 * r < Fintype.card (Fin (4 * (2 * r + 1) - 3)) := by
    simp only [Fintype.card_fin]
    omega
  exact hnot (monochromatic_cycle_of_four_matching_cores c r h.defect hr4 horder cores)

/-- The explicit sharpness construction has `4 * n - 4` vertices and avoids
the monochromatic odd `n`-cycle in every colour. -/
theorem explicit_sharpness (n : ℕ) (hn : 2 < n) (hodd : Odd n) :
    Fintype.card (SharpVertex n) = 4 * n - 4 ∧
      ∀ i : Fin 3, ¬ cycleGraph n ⊑ (sharpColouring n).graph i :=
  ⟨card_sharpVertex n, sharpColouring_no_cycle n hn hodd⟩

/-- The sharp three-colour cycle Ramsey equality, for every sufficiently large odd order. -/
theorem erdos556 :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Odd n → ramseyNumber n = 4 * n - 3 := by
  obtain ⟨n₁, hupper⟩ := eventually_isRamseyOrder_odd_cycle
  refine ⟨max n₁ 3, ?_⟩
  intro n hn hodd
  apply le_antisymm
  · exact ramseyNumber_le_of_isRamseyOrder (hupper n (by omega) hodd)
  · exact four_mul_sub_three_le_ramseyNumber n (by omega) hodd

theorem erdos_556 :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Odd n →
      ramseyNumber n = 4 * n - 3 :=
  erdos556

#print axioms eventually_isRamseyOrder_odd_cycle
#print axioms explicit_sharpness
#print axioms erdos556

end Erdos556
