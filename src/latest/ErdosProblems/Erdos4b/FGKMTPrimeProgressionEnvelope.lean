/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCenteredProgressionEnvelope
import ErdosProblems.Erdos4b.FGKMTCoprimeModulusRange
import BoundedGaps.BombieriVinogradov.Analytic.CenteredPrimeAbel

/-!
# The effective envelope for the literal prime-counting discrepancy sum

Abel summation and prime-power removal are applied pointwise before summing
over the retained moduli. The conductor and modulus cutoffs remain explicit.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

theorem coprimeModulusDiscrepancySum_le_centered (B L x : ℕ) (hx : 2 ≤ x) :
    coprimeModulusDiscrepancySum B L x ≤ (Real.log 2)⁻¹ *
      (coprimeCenteredDiscrepancySum B L x +
        (L : ℝ) * (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) := by
  let S := (Finset.Icc 1 L).filter (fun q => q.Coprime B)
  have hinv : 0 ≤ (Real.log 2)⁻¹ := (inv_pos.mpr (Real.log_pos one_lt_two)).le
  have hrem : 0 ≤ Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) :=
    sub_nonneg.mpr (Chebyshev.theta_le_psi _)
  have hcard : S.card ≤ L := (Finset.card_filter_le _ _).trans (by simp)
  calc
    _ ≤ ∑ q ∈ S, (Real.log 2)⁻¹ * (maxCenteredProgressionDiscrepancyUpTo x q +
        (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
      exact (maxProgressionDiscrepancy_le_inv_log_two_mul_maxCenteredThetaUpTo hx hq1).trans
        (mul_le_mul_of_nonneg_left (maxCenteredThetaProgressionDiscrepancyUpTo_le hq1) hinv)
    _ = (Real.log 2)⁻¹ * (coprimeCenteredDiscrepancySum B L x +
        (S.card : ℝ) * (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hrem)) hinv

theorem coprimeModulusDiscrepancySum_le_centered_sqrt (B L x : ℕ) (hx : 2 ≤ x) :
    coprimeModulusDiscrepancySum B L x ≤ (Real.log 2)⁻¹ *
      (coprimeCenteredDiscrepancySum B L x +
        2 * (L : ℝ) * Real.sqrt (x : ℝ) * Real.log (x : ℝ)) := by
  have hrem := Chebyshev.psi_sub_theta_le
    (x := (x : ℝ)) (by exact_mod_cast (by omega : 1 ≤ x))
  apply (coprimeModulusDiscrepancySum_le_centered B L x hx).trans
  apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr (Real.log_pos one_lt_two)).le
  have hmul := mul_le_mul_of_nonneg_left hrem (Nat.cast_nonneg L)
  linarith

def primeProgressionVaughanRemainder (L R x : ℕ) : ℝ :=
  (L : ℝ) * Real.log ((L * x : ℕ) : ℝ) ^ 2 +
    (5 * vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4)) *
      vaughanPrimitiveMeanAbelEnvelope x R L * vaughanPrimitiveMeanEquationOneTwoLogPower x +
        2 * (L : ℝ) * Real.sqrt (x : ℝ) * Real.log (x : ℝ)

theorem coprimeModulusDiscrepancySum_le_vaughan (B L R x : ℕ) (hx : 4 ≤ x)
    (hL : (L : ℝ) ≤ Real.sqrt (x : ℝ)) (hR : 1 ≤ R) (hRL : R ≤ L) :
    coprimeModulusDiscrepancySum B L x ≤ (Real.log 2)⁻¹ *
      ((4 * (1 + Real.log (L : ℝ))) * coprimePrimitiveCenteredMass B R x +
        primeProgressionVaughanRemainder L R x) := by
  have hcenter := coprimeCenteredDiscrepancySum_le_vaughan B L R x hx hL hR hRL
  apply (coprimeModulusDiscrepancySum_le_centered_sqrt B L x (by omega)).trans
  apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr (Real.log_pos one_lt_two)).le
  dsimp [primeProgressionVaughanRemainder]
  linarith

theorem exists_exceptionalPrime_primeProgressionEnvelope_bound :
    ∃ C a c : ℝ, 0 < C ∧ 0 < a ∧ 0 < c ∧ ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ R : ℕ, 2 ≤ R → ∃ B : ℕ, 1 ≤ B ∧ B ≤ R ∧ (B = 1 ∨ B.Prime) ∧
        ∀ x : ℕ, X0 ≤ x → (R : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) →
          ∀ L : ℕ, R ≤ L → (L : ℝ) ≤ Real.sqrt (x : ℝ) →
            coprimeModulusDiscrepancySum B L x ≤ (Real.log 2)⁻¹ *
              ((4 * (1 + Real.log (L : ℝ))) *
                (C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ))))) +
                  primeProgressionVaughanRemainder L R x) := by
  obtain ⟨C, a, c, hC, ha, hc, X0, hX0, hsmall⟩ :=
    exists_exceptionalPrime_smallConductorMass_bound
  refine ⟨C, a, c, hC, ha, hc, X0, hX0, ?_⟩
  intro R hR
  obtain ⟨B, hBpos, hBR, hB, hmass⟩ := hsmall R hR
  refine ⟨B, hBpos, hBR, hB, ?_⟩
  intro x hx hRexp L hRL hL
  have hlogL := Real.log_natCast_nonneg L
  apply (coprimeModulusDiscrepancySum_le_vaughan B L R x (hX0.trans hx) hL
    (by omega) hRL).trans
  apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr (Real.log_pos one_lt_two)).le
  exact add_le_add (mul_le_mul_of_nonneg_left (hmass x hx hRexp) (by positivity)) le_rfl

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.coprimeModulusDiscrepancySum_le_centered
#print axioms Erdos4b.FGKMT.coprimeModulusDiscrepancySum_le_vaughan
#print axioms Erdos4b.FGKMT.exists_exceptionalPrime_primeProgressionEnvelope_bound
