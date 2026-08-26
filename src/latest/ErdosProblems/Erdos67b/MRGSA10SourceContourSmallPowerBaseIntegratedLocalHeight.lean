import ErdosProblems.Erdos67b.MRGSA10SourcePerronIntegratedRawScheduleLocalHeight
import ErdosProblems.Erdos67b.MRGSA10SourceSmallPowerContourBaseSubOneScalar

/-!
# Small-power source contour from a local `log^2` distance window
-/

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- Fixed-source A.10 at `Z ∈ [X,3X]`, requiring pretentious separation
only for `|t| ≤ log(Z)^2`. -/
theorem exists_norm_gsA10TwoBlockSourcePerronIntegrated_div_le_smallPower_base_sub_one_of_localDistance :
    ∃ Cbeta : ℝ, ∃ Nrow : ℕ, 1 ≤ Cbeta ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
        (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
        {X Z y : ℕ},
        Nrow ≤ y → 3 ≤ X → X ≤ Z → Z ≤ 3 * X →
        23 ≤ y → y ≤ Z → 4 ≤ Z → 2 ≤ Z / y →
        6 ≤ Real.log (y : ℝ) → 1 ≤ Real.log (Z : ℝ) →
        Real.log (Z : ℝ) ^ 2 ≤ Z →
        Erdos67b.PrimeEstimates.primeReciprocals Z ≤ Real.log (Z : ℝ) →
        Real.log (Z : ℝ) ^ 4 ≤ (y : ℝ) →
        Real.log (Z : ℝ) ^ 6 ≤ (y : ℝ) →
        1 ≤ Erdos67b.realPrefixMovingThreshold X →
        (∀ u : ℝ, |u| ≤ Real.log (Z : ℝ) ^ 2 →
          ((Erdos67b.realPrefixMovingThreshold X - 1 : ℕ) : ℝ) ≤
            pretentiousDistSq f (archimedeanTwist u) Z) →
        ‖gsA10TwoBlockSourcePerronIntegrated f hmul P₁ P₂ y Z
            (Real.log (y : ℝ))⁻¹ (Real.log (Z : ℝ) ^ 2)‖ /
            (Z : ℝ) ≤
          2 * gsA10SmallPowerSourceContourBaseSubOneConstant Cbeta *
            (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
  obtain ⟨Cbeta, Nrow, hCbeta, hraw⟩ :=
    exists_norm_gsA10TwoBlockSourcePerronIntegrated_le_rawSchedule_of_localHeight
  refine ⟨Cbeta, Nrow, hCbeta, ?_⟩
  intro f hmul hbound P₁ P₂ _ _ hsmall X Z y hNrowy hX hXZ hZX hy
    hyZ hZ hquot hlogy hlogZ hlogSq hprime hlogFour hlogSix hthreshold
    hdist
  let R : ℝ :=
    ((2 * Real.pi)⁻¹ * (3 * gsA9SmallPrimeEulerBound) *
        Real.exp
          (28 * Real.exp 4 *
              Erdos67b.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) * Real.exp 1) *
      (gsA10SourceMaximumModulusSqrtScalar
          (Erdos67b.realPrefixMovingThreshold X - 1) Z /
        Real.sqrt (Real.log (Z : ℝ))) *
      (2 *
          (Real.exp 1 * Real.sqrt Real.pi *
            (gsA10PrimeSourceAffineRowConstant Cbeta +
              gsA10PrimeSourceAffineRowSlope Cbeta y Z *
                Real.log (Z : ℝ) ^ 2)) *
          (2 * gsA10PrimeLambdaSymmetricBetaScalarConstant) +
        4 * Real.log (Z : ℝ) ^ 2 *
          (2 * gsA10PrimeLambdaHarmonicBudget Z *
              gsA10HigherPrimePowerGeometricMass y Z +
            (gsA10HigherPrimePowerGeometricMass y Z) ^ 2) *
          (Real.log (y : ℝ))⁻¹)
  have heta : 0 ≤ (Real.log (y : ℝ))⁻¹ := by
    have : 0 < Real.log (y : ℝ) := by linarith
    positivity
  have hetaQuarter : (Real.log (y : ℝ))⁻¹ ≤ 1 / 4 := by
    have hfour : (4 : ℝ) ≤ Real.log (y : ℝ) := by linarith
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 4) hfour
  have hTOne : 1 ≤ Real.log (Z : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (Z : ℝ) - 1)]
  have hlogyZ : Real.log (y : ℝ) ≤ Real.log (Z : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · simp only [Set.mem_Ioi]
      positivity
    · simp only [Set.mem_Ioi]
      positivity
    · exact_mod_cast hyZ
  have hlogZSix : (6 : ℝ) ≤ Real.log (Z : ℝ) := hlogy.trans hlogyZ
  have hlogT : 1 + Real.log (Z : ℝ) ≤
      (Real.log (Z : ℝ) ^ 2) ^ 2 := by
    have hfirst : 1 + Real.log (Z : ℝ) ≤ Real.log (Z : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (Z : ℝ) - 1)]
    have hsquare : Real.log (Z : ℝ) ^ 2 ≤
        (Real.log (Z : ℝ) ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (Z : ℝ) ^ 2 - 1)]
    exact hfirst.trans hsquare
  have hraw' :
      ‖gsA10TwoBlockSourcePerronIntegrated f hmul P₁ P₂ y Z
          (Real.log (y : ℝ))⁻¹ (Real.log (Z : ℝ) ^ 2)‖ / (Z : ℝ) ≤
        2 * R := by
    simpa only [R] using
      (hraw hmul hbound P₁ P₂ hsmall hNrowy hy hyZ
        (show 2 ≤ Z by omega) hquot (by linarith) hlogZ
          heta le_rfl hetaQuarter hTOne hlogT hdist)
  have hscalar : R ≤
      gsA10SmallPowerSourceContourBaseSubOneConstant Cbeta *
        (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
    simpa only [R] using
      gsA10_fixedSource_normalizedBudget_smallPower_base_sub_one_le
        hCbeta hX hXZ hZX hZ (show 3 ≤ y by omega) hthreshold hlogZ
          hprime hlogFour hlogSix
  calc
    _ ≤ 2 * R := hraw'
    _ ≤ 2 *
        (gsA10SmallPowerSourceContourBaseSubOneConstant Cbeta *
          (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ))) :=
      mul_le_mul_of_nonneg_left hscalar (show (0 : ℝ) ≤ 2 by norm_num)
    _ = _ := by ring

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.exists_norm_gsA10TwoBlockSourcePerronIntegrated_div_le_smallPower_base_sub_one_of_localDistance
