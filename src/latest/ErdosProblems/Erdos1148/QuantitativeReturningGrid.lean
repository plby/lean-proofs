import ErdosProblems.Erdos1148.QuantitativeGaussCandidates
import ErdosProblems.Erdos1148.ReturningGaussGrid

/-! # Explicit parameter dependence in the returning unstable grid -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_quantitative_returningGauss_unstable_grid {A c δ : ℝ}
    (hA : 0 ≤ A) (hc : 0 < c) (hδ : 0 < δ)
    (g : SL(2, ℝ)) (hg : ∀ i j : Fin 2, |g i j| ≤ A) {S : ℝ}
    (hS : 0 ≤ S) (hsmall : 96 * Real.exp (-S) ≤ c) :
    ∃ (N : ℕ) (a : Fin N → ℝ),
      (N : ℝ) ≤ (((64 * A + 3) ^ 2 + 1) * (32 / (Real.sqrt c * δ) + 1)) * Real.exp (S / 2) ∧
      ∀ p ∈ ReturningGaussParameters g S c, ∃ i : Fin N,
        p.val.1 ∈ Set.Icc (a i) (a i + δ * Real.exp (-S)) := by
  obtain ⟨V, hcard, hV⟩ := exists_uniform_returningGauss_candidates_card_bound hA
  obtain ⟨N, a, hN, hcov⟩ := exists_returningGauss_unstable_grid_from_candidates
    hc hδ V g (hV g hg) hS hsmall
  refine ⟨N, a, hN.trans ?_, hcov⟩
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right (add_le_add hcard le_rfl) (by positivity)

end Erdos1148.DukeArithmetic
