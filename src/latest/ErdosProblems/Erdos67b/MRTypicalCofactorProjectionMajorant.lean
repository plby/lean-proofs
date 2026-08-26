import ErdosProblems.Erdos67b.MRTypicalCofactorMass
import ErdosProblems.Erdos67b.MRTypicalCofactorEndpoint
import ErdosProblems.Erdos67b.MRGSA10OrdinaryMovingProjectionAverage

/-!
# Complete pointwise projection majorant for the actual cofactor

All three errors in the inclusive Perron projection are bounded by the
existing ordinary source majorant. The moving powers stay together in
the mass term, ready for the auxiliary rectangle average.
-/

open scoped BigOperators Classical

namespace Erdos67b

open MRHalaszBands EulerResidue BoundedGaps.Maynard

noncomputable section

theorem mrNorm_positivePrefix_typicalCofactorTailored_sub_perron_le_ordinaryMajorant
    {ι : Type*} (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ι) (B : ι → Finset ℕ) (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ)) (hlogy : 6 ≤ Real.log (y : ℝ))
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    {alpha beta : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hb0 : 0 ≤ beta) (hb : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖positivePrefixSum (mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta) X -
      mrTypicalCofactorMovingPerronIntegral A J B f hmul y X alpha beta ((Real.log (X : ℝ)) ^ 2)‖ ≤
      gsA10OrdinaryMovingProjectionMajorant hmul y X ((Real.log (X : ℝ)) ^ 2) alpha beta := by
  have hT : 0 < (Real.log (X : ℝ)) ^ 2 := sq_pos_of_pos (zero_lt_one.trans_le hlogX)
  have hbase := mrNorm_positivePrefix_typicalCofactorTailored_sub_perron_le_source A J B
    hmul hbound (by omega : 1 < X) hlogX hlogy ha0 ha hb0 hb hT
  have hnear := mrDirichletPerronNearMass_typicalCofactorTailored_le A hA J B hB hmul hbound
    hAy hBy (by omega : 0 < X) hT ha0 hb0
  have hmass := mrCofactorTailoredCoefficientMass_fixedTao_le A J B hmul hbound hy
    (by omega : 1 < X) hlogy ha0 ha hb0 hb
  have hend := mrNorm_typicalCofactorTailored_halfEndpoint_le_mass A hA J B hB hmul hbound
    hAy hBy hX ha0 hb0
  let a := mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta
  let sigma := taoExponent X - alpha - 2 * beta
  have hmass' : (32 * (X : ℝ) ^ sigma / (Real.log (X : ℝ)) ^ 2) *
      dirichletPerronCoefficientMass a sigma ≤ gsA10OrdinaryMovingProjectionMass y X alpha beta := by
    calc
      _ ≤ (32 * (X : ℝ) ^ sigma / (Real.log (X : ℝ)) ^ 2) *
          ((gsA10SourceCoefficientMassConstant * (1 + Real.log (X : ℝ))) *
            ((gsA10OrdinaryLambdaWindowMassBase y X) ^ 2 *
              (X : ℝ) ^ (1 - min (taoExponent X - 2 * beta) 1))) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := by
        unfold gsA10OrdinaryMovingProjectionMass gsA10MovingPerronMassConstant
        dsimp only [sigma]
        ring
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hend' : (1 / 2 : ℝ) * ‖a X‖ ≤ (X : ℝ) * gsA10OrdinaryHalfEndpointBound y X := by
    have hscaled := mul_le_mul_of_nonneg_left hend hXR.le
    calc
      _ = (X : ℝ) * (‖a X‖ / (2 * (X : ℝ))) := by field_simp
      _ ≤ _ := hscaled
  apply hbase.trans
  exact add_le_add (add_le_add hnear hmass') hend'

end

end Erdos67b
