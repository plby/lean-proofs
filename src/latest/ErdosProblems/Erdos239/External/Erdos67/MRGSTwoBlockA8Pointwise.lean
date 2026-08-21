import ErdosProblems.Erdos239.External.Erdos67.MRGSTwoBlockA8Scalar
import ErdosProblems.Erdos239.External.Erdos67.MRGSArchimedeanFactorDecay

/-!
# Pointwise consequence of two-block A.8 and a central A.9 bound

This is the final elementary bridge between the completed A.8
renormalization and the still-separate central A.9 estimate.  It includes
the zero displacement exactly.
-/

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The scalar two-block A.8 estimate converts any central mean bound into
the reciprocal pointwise estimate, with the flat `log^(-1/16)` remainder
kept explicit. -/
theorem norm_twoBlock_normalized_prefix_le_reciprocal_add_window
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (t₁ u : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (hlogOne : 1 ≤ Real.log (N : ℝ))
    (hu : |u| ≤ (Real.log (N : ℝ)) ^ (1 / 16 : ℝ))
    (hdist : pretentiousDistSq f (archimedeanTwist t₁) N ≤
      PrimeEstimates.primeReciprocals N / 8)
    (hmass₂ : primeBandReciprocalMass (fun p ↦ ¬ P₁ p ∧ P₂ p) N ≤
      PrimeEstimates.primeReciprocals N / 2)
    (hmass₃ : primeBandReciprocalMass (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N ≤
      PrimeEstimates.primeReciprocals N / 2)
    (hmass₂₃ :
      primeBandReciprocalMass
          (fun p ↦ (¬ P₁ p ∧ P₂ p) ∨ (¬ P₁ p ∧ ¬ P₂ p)) N ≤
        PrimeEstimates.primeReciprocals N / 2)
    {E : ℝ} (hE : 0 ≤ E)
    (hcentral :
      ‖positivePrefixMean
        (archimedeanUntwist
          (finiteHalaszTypicalCoefficient f P₁ P₂) t₁) N‖ ≤ E) :
    ‖gsTwistedPositivePrefixSum
        (finiteHalaszTypicalCoefficient f P₁ P₂) (t₁ + u) N /
        (N : ℂ)‖ ≤
      2 * E * (1 + |u|)⁻¹ +
        gsA8TwoBlockErrorConstant *
          (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) := by
  let D : ℝ := gsA8TwoBlockErrorConstant *
    (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ)
  have hlog : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlogOne
  have hD : 0 ≤ D := mul_nonneg gsA8TwoBlockErrorConstant_nonneg
    (Real.rpow_nonneg hlog.le _)
  have hrenorm (hu0 : u ≠ 0) :
      ‖gsTwistedPositivePrefixSum
            (finiteHalaszTypicalCoefficient f P₁ P₂) (t₁ + u) N /
            (N : ℂ) -
          gsPrefixArchimedeanFactor u N *
            positivePrefixMean
              (archimedeanUntwist
                (finiteHalaszTypicalCoefficient f P₁ P₂) t₁) N‖ ≤ D := by
    exact norm_twoBlock_gsPrefixRenormalization_centered_le_window
      hmul hbound P₁ P₂ t₁ u hN hu0 hlogOne hu hdist
        hmass₂ hmass₃ hmass₂₃
  simpa only [D] using
    norm_normalized_twistedPrefix_le_reciprocal_add_of_centered
      (finiteHalaszTypicalCoefficient f P₁ P₂) t₁ u
      (show 0 < N by omega) hE hD hcentral hrenorm

end

end Erdos67.MRHalaszBands
