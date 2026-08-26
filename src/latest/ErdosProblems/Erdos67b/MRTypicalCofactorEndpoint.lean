import ErdosProblems.Erdos67b.MRTypicalCofactorNear
import ErdosProblems.Erdos67b.MRGSA10HalfEndpointOrdinaryScalar

/-!
# The inclusive endpoint of the actual cofactor Perron projection

The prime-prime term contributes the classical logarithmic square.
All remaining terms are the existing ordinary higher-prime-power
remainder, which is bounded by reciprocal masses without a divisor count.
-/

open scoped BigOperators Classical
open Finset

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrShiftedPrimeLambdaWindowWeight_le_vonMangoldt
    (y X : ℕ) {rho : ℝ} (hrho : 0 ≤ rho) (n : ℕ) :
    gsA10ShiftedPrimeLambdaWindowWeight y X rho n ≤ ArithmeticFunction.vonMangoldt n := by
  unfold gsA10ShiftedPrimeLambdaWindowWeight
  split_ifs with hwin hp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hp.one_le
    have hexp : Real.exp (-rho * Real.log (n : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_mul]
      exact neg_nonpos.mpr (mul_nonneg hrho (Real.log_nonneg hn1))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp
      (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  · simpa only [mul_zero] using (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  · exact ArithmeticFunction.vonMangoldt_nonneg

theorem mrNorm_typicalCofactorTailored_endpoint_le_log_sq_add_hpp {ι : Type*}
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y X : ℕ}
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    (hX : 0 < X) {alpha beta : ℝ} (ha : 0 ≤ alpha) (hb : 0 ≤ beta) :
    ‖mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta X‖ ≤
      (Real.log (X : ℝ)) ^ 2 + gsA10OrdinaryHalfEndpointHPPError hmul y X alpha beta := by
  apply (mrNorm_typicalCofactorTailored_apply_le_nested A hA J B hB hmul hbound y X
    hAy hBy ha hb X).trans
  let P := gsA10ShiftedPrimeLambdaWindowWeight y X alpha
  let Q := gsA10ShiftedPrimeLambdaWindowWeight y X (alpha + 2 * beta)
  have hsplit : (∑ uv ∈ X.divisorsAntidiagonal, ∑ ab ∈ uv.1.divisorsAntidiagonal,
      gsA10OrdinaryLambdaNearWeight hmul y X alpha ab.1 *
        gsA10OrdinaryLambdaNearWeight hmul y X (alpha + 2 * beta) ab.2) =
      (∑ uv ∈ X.divisorsAntidiagonal, ∑ ab ∈ uv.1.divisorsAntidiagonal, P ab.1 * Q ab.2) +
        gsA10OrdinaryHalfEndpointHPPError hmul y X alpha beta := by
    unfold gsA10OrdinaryHalfEndpointHPPError gsA10OrdinaryLambdaNearWeight
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro uv _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ab _
    dsimp only [P, Q]
    ring
  rw [hsplit]
  refine add_le_add ?_ le_rfl
  apply (Finset.sum_le_sum (fun uv _ ↦ Finset.sum_le_sum (fun ab _ ↦
    mul_le_mul (mrShiftedPrimeLambdaWindowWeight_le_vonMangoldt y X ha ab.1)
      (mrShiftedPrimeLambdaWindowWeight_le_vonMangoldt y X (by linarith) ab.2)
      (gsA10ShiftedPrimeLambdaWindowWeight_nonneg y X (alpha + 2 * beta) ab.2)
      ArithmeticFunction.vonMangoldt_nonneg))).trans
  exact sum_nested_vonMangoldt_le_log_sq hX

theorem mrNorm_typicalCofactorTailored_halfEndpoint_le_mass {ι : Type*}
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y X : ℕ}
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    (hX : 2 ≤ X) {alpha beta : ℝ} (ha : 0 ≤ alpha) (hb : 0 ≤ beta) :
    ‖mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta X‖ / (2 * (X : ℝ)) ≤
      (Real.log (X : ℝ)) ^ 2 / (2 * (X : ℝ)) +
        gsA10HalfEndpointPrimeMass X * gsA10HigherPrimePowerGeometricMass y X +
        (gsA10HigherPrimePowerGeometricMass y X) ^ 2 / 2 := by
  have hpoint := mrNorm_typicalCofactorTailored_endpoint_le_log_sq_add_hpp A hA J B hB
    hmul hbound (X := X) (alpha := alpha) (beta := beta) hAy hBy (by omega) ha hb
  have hzero := gsA10OrdinaryHalfEndpointHPPError_le_zero hmul y X ha hb
  have hmass := gsA10OrdinaryHalfEndpointHPPError_le_mass hmul hbound (y := y) hX
  have hden : (0 : ℝ) < 2 * X := by positivity
  calc
    _ ≤ ((Real.log (X : ℝ)) ^ 2 +
        (X : ℝ) * (2 * gsA10HalfEndpointPrimeMass X * gsA10HigherPrimePowerGeometricMass y X +
          (gsA10HigherPrimePowerGeometricMass y X) ^ 2)) / (2 * (X : ℝ)) :=
      div_le_div_of_nonneg_right (hpoint.trans (add_le_add le_rfl (hzero.trans hmass))) hden.le
    _ = _ := by field_simp; ring

end

end Erdos67b
