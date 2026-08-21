import ErdosProblems.Erdos239.External.Erdos67.EulerResidueBounds
import ErdosProblems.Erdos239.External.Erdos67.PrimitiveCharacterReduction

/-!
# The final Euler-to-BCC bridge in Section 4

The finite-scale Euler package already converts Tao's shifted-convolution
estimate into the normalized cyclic-good prefix energy.  This file connects
that result directly to the stored BCC parameter contradiction, including the
conductor-one branch.
-/

open scoped BigOperators

namespace Erdos67

noncomputable section

/-- A same-scale Euler certificate and the corresponding shifted-convolution
bound contradict the BCC parameters stored in the Section 4 selection. -/
theorem Section4CharacterData.primitive_contradiction_of_taoTransferReady
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    {X : ℕ} {D eta K J : ℝ}
    (P : EulerResidueBounds.TaoTransferReady W.primitiveCorrectionHom
      W.primitiveQ S.k X D eta)
    (hconvolution :
      ∑ L ∈ Finset.Ioc S.H (2 * S.H),
          shiftedResidueConvolutionEnergy W.primitiveCorrectionHom
            (EulerResidue.taoExponent X) W.primitiveModifiedResidueValue
            (cyclicGoodResidues W.primitiveQ S.k S.H) L ≤
        K * ‖EulerResidue.singularSeries W.primitiveCorrectionHom X /
            ((W.primitiveQ ^ S.k : ℕ) : ℂ)‖ ^ 2 *
          ((W.primitiveQ ^ S.k : ℕ) : ℝ) * S.H)
    (hsmall : 4 * (S.H : ℝ) ^ 2 * eta ^ 2 ≤ J)
    (hbudget : 2 * K + 2 * J ≤ S.B) : False := by
  have henergy := P.normalized_shiftedResiduePrefixEnergy_le
    W.primitiveCorrectionHom_hasUnitNorm
    W.primitiveCorrectionHom_prime_dvd
    W.primitiveModifiedResidueValue
    W.norm_primitiveModifiedResidueValue_le_one
    S.H S.H_pos K J hconvolution hsmall
  have henergy' :
      (1 / (((W.primitiveQ ^ S.k : ℕ) : ℝ) * S.H)) *
          ∑ L ∈ Finset.Ioc S.H (2 * S.H),
            ∑ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H,
              Complex.normSq
                (cyclicPrimeExtensionIccPrefix
                  W.primitiveModifiedAssignment L a) ≤ S.B := by
    simpa only [W.shiftedResiduePrefix_primitiveModified_eq] using
      henergy.trans hbudget
  by_cases hq : W.primitiveQ = 1
  · exact (not_lt_of_ge henergy') (W.primitiveQ_one_prefixEnergy_gt_B hq)
  · exact W.primitive_bcc_contradiction_of_discrepancy
      (lt_of_le_of_ne
        (Nat.one_le_iff_ne_zero.mpr (NeZero.ne W.primitiveQ))
        (Ne.symm hq)) henergy'

end

end Erdos67
