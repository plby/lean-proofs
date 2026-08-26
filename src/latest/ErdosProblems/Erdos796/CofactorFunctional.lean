import ErdosProblems.Erdos796.GammaBasic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Uniform majorants for the cofactor functional

This module separates the analytic summation argument from the finite
multiplicative-Sidon estimate.  Any pointwise excess majorant with a summable
weighted series immediately bounds every score and hence the supremum
`Gamma`.
-/

namespace Erdos796

/-- Weighted version of a proposed fibre-excess majorant. -/
noncomputable def weightedMajorant (B : ℕ → ℝ) (k : ℕ) : ℝ :=
  cofactorWeight (k + 1) * B (k + 1)

theorem cofactorTerm_le_weightedMajorant {U : ℕ → Finset ℕ}
    {B : ℕ → ℝ} (hB : ∀ j : ℕ, excess U j ≤ B j) (k : ℕ) :
    cofactorTerm U k ≤ weightedMajorant B k := by
  rw [cofactorTerm, weightedMajorant]
  exact mul_le_mul_of_nonneg_left (hB (k + 1))
    (cofactorWeight_nonneg (k + 1))

/-- A summable pointwise majorant bounds the value of one scoreable family. -/
theorem cofactorValue_le_majorant {U : ℕ → Finset ℕ} {B : ℕ → ℝ}
    (hU : HasCofactorValue U)
    (hB : ∀ j : ℕ, excess U j ≤ B j)
    (hSummable : Summable (weightedMajorant B)) :
    cofactorValue U ≤ ∑' k : ℕ, weightedMajorant B k := by
  rw [cofactorValue]
  exact Summable.tsum_le_tsum
    (cofactorTerm_le_weightedMajorant hB)
    hU hSummable

/-- A uniform summable majorant proves that the score set is bounded above. -/
theorem gammaScores_bddAbove_of_uniform_majorant {B : ℕ → ℝ}
    (hBound : ∀ (U : ℕ → Finset ℕ), Compatible U →
      ∀ j : ℕ, excess U j ≤ B j)
    (hSummable : Summable (weightedMajorant B)) :
    BddAbove gammaScores := by
  refine ⟨∑' k : ℕ, weightedMajorant B k, ?_⟩
  intro x hx
  rcases hx with ⟨U, hCompat, hValue, rfl⟩
  exact cofactorValue_le_majorant hValue (hBound U hCompat) hSummable

/-- The same hypotheses give an explicit upper bound on `Gamma`. -/
theorem Gamma_le_tsum_majorant {B : ℕ → ℝ}
    (hBound : ∀ (U : ℕ → Finset ℕ), Compatible U →
      ∀ j : ℕ, excess U j ≤ B j)
    (hSummable : Summable (weightedMajorant B)) :
    Gamma ≤ ∑' k : ℕ, weightedMajorant B k := by
  rw [Gamma_eq_sSup_gammaScores]
  apply csSup_le gammaScores_nonempty
  intro x hx
  rcases hx with ⟨U, hCompat, hValue, rfl⟩
  exact cofactorValue_le_majorant hValue (hBound U hCompat) hSummable

theorem Gamma_nonneg_of_bddAbove (hBdd : BddAbove gammaScores) :
    0 ≤ Gamma := by
  rw [Gamma_eq_sSup_gammaScores]
  exact le_csSup hBdd zero_mem_gammaScores

end Erdos796
