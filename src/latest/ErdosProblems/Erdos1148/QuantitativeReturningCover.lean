import ErdosProblems.Erdos1148.QuantitativeReturningGrid
import ErdosProblems.Erdos1148.GaussLiftGridCover

/-! # Explicit polynomial dependence in the returning forward lift cover -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_quantitative_returningGauss_lift_cover {A c δ : ℝ}
    (hA : 0 ≤ A) (hc : 0 < c) (hδ : 0 < δ)
    (g : SL(2, ℝ)) (hg : ∀ i j : Fin 2, |g i j| ≤ A) {S : ℝ}
    (hS : 0 ≤ S) (hsmall : 96 * Real.exp (-S) ≤ c) :
    ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
      (N : ℝ) ≤ (((64 * A + 3) ^ 2 + 1) * (32 / (Real.sqrt c * δ) + 1) *
        (2 / δ + 1) ^ 2) * Real.exp (S / 2) ∧ (∀ i, IsCompact (B i)) ∧
      gaussParameterFrame g '' ReturningGaussParameters g S c ⊆ ⋃ i, B i ∧
      ∀ i, LiftForwardClose (8 * δ) S (B i) := by
  obtain ⟨Nr, a, hNr, hrcov⟩ := exists_quantitative_returningGauss_unstable_grid
    hA hc hδ g hg hS hsmall
  obtain ⟨N, B, hN, hcompact, hcov, hclose⟩ := exists_gauss_lift_cover_of_unstable_grid
    hδ hS g (ReturningGaussParameters g S c) a hrcov
  refine ⟨N, B, hN.trans ?_, hcompact, hcov, hclose⟩
  calc
    _ ≤ ((((64 * A + 3) ^ 2 + 1) * (32 / (Real.sqrt c * δ) + 1)) * Real.exp (S / 2)) *
        (2 / δ + 1) ^ 2 := mul_le_mul_of_nonneg_right hNr (sq_nonneg _)
    _ = _ := by ring

end Erdos1148.DukeArithmetic
