import ErdosProblems.Erdos327.Analytic.SourceBoxAssembly
import ErdosProblems.Erdos327.Analytic.ThreeFormBoxAllCutoffs

/-!
# Source dyadic assembly in both sieve-cutoff orderings
-/

namespace Erdos327.Analytic

open Real

noncomputable section

/-- Sharp source sieve factor with the piecewise Euler-product envelope. -/
def sourceAllCutoffSharpSieveBound
    (L z X R : ℕ) : ℝ :=
  8 * (X : ℝ) ^ 2 *
      exp (sourceAllCutoffMertensEnvelope L z) +
    8 * (X : ℝ) ^ 2 *
      ((3 * primeInvSum z) ^ (2 * R + 1) /
        ((2 * R + 1).factorial : ℝ)) +
    ((2 * R + 1 : ℕ) : ℝ) *
      (z : ℝ) ^ (2 * R) * (3 : ℝ) ^ (2 * R) *
      (9 * (X : ℝ) + (z : ℝ) ^ (2 * R))

/-- Finite source block estimate valid whether `z < L` or `L ≤ z`. -/
theorem card_sourceDyadicCoordinateSet_le_allCutoffs_mul_residual
    {L N z X R : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hX : 0 < X) (hz : 2 ≤ z)
    (hA : 0 ≤ A) :
    ((sourceDyadicCoordinateSet L N A K X).card : ℝ) ≤
      sourceDyadicBudget L X A K *
        sourceAllCutoffSharpSieveBound L z X R *
        sourceDyadicResidualMoment L X (2 * N / X ^ 2) := by
  have hbase :=
    card_sourceDyadicCoordinateSet_le_box_mul_residual
      (N := N) (z := z) (K := K) hL hX hA
  have hsieve :=
    source_threeFormBoxSum_le_allCutoffs
      (L := L) (z := z) (X := X) (R := R)
      (by omega : 2 ≤ L) hz
  have hbudget :
      0 ≤ sourceDyadicBudget L X A K := by
    unfold sourceDyadicBudget
    positivity
  have hresidual :
      0 ≤ sourceDyadicResidualMoment L X (2 * N / X ^ 2) := by
    unfold sourceDyadicResidualMoment
    positivity
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_right _ hresidual
  apply mul_le_mul_of_nonneg_left _ hbudget
  simpa [sourceAllCutoffSharpSieveBound] using hsieve

/-- Fully explicit source block estimate in both cutoff orderings. -/
theorem card_sourceDyadicCoordinateSet_le_allCutoffs_explicit
    {L N z X R : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hz : 2 ≤ z)
    (hY : 2 ≤ 2 * N / X ^ 2) (hA : 0 ≤ A) :
    ((sourceDyadicCoordinateSet L N A K X).card : ℝ) ≤
      sourceDyadicBudget L X A K *
        sourceAllCutoffSharpSieveBound L z X R *
        sourceDyadicResidualEnvelope L X (2 * N / X ^ 2) := by
  have hX : 0 < X := by omega
  have hbase :=
    card_sourceDyadicCoordinateSet_le_allCutoffs_mul_residual
      (N := N) (R := R) (K := K)
      hL hX hz hA
  have hresidual :=
    sourceDyadicResidualMoment_le_envelope hL hLX hY
  have hfactor :
      0 ≤ sourceDyadicBudget L X A K *
        sourceAllCutoffSharpSieveBound L z X R := by
    have hprimeInv : 0 ≤ primeInvSum z :=
      primeInvSum_nonneg z
    unfold sourceDyadicBudget sourceAllCutoffSharpSieveBound
    positivity
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hresidual hfactor)

end

end Erdos327.Analytic
