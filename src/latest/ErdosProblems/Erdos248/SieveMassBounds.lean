import ErdosProblems.Erdos248.CorrelationBounds

/-!
# Erdős Problem 248: a quantitative lower bound for the sieve mass

The normalization files prove that the exact CRT main bracket contains half
of the independent product energy.  The interval error is much smaller: the
geometric separation between `radiusProduct` and `intervalStart` absorbs it
inside one quarter of that energy.  This gives the denominator bound used by
all subsequent weighted probability estimates.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

theorem one_div_sixteen_pow_le_productCoordinateEnergy {K : ℕ}
    (hK : 0 < K) :
    (1 / 16 : ℝ) ^ K ≤ productCoordinateEnergy K := by
  have hinner := sixteenthPow_innerMass_le_productEnergy hK
  have hone := one_le_innerTupleMass K
  have hscale : 0 ≤ (1 / 16 : ℝ) ^ K := by positivity
  calc
    (1 / 16 : ℝ) ^ K ≤ (1 / 16 : ℝ) ^ K * innerTupleMass K := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hscale
    _ ≤ productCoordinateEnergy K := hinner

theorem abs_sieveIntervalError_lt_quarter_scaled_energy {K : ℕ}
    (hK : 0 < K) :
    |compatibleDivisorPairErrorSum (nearShifts K) (sieveDivisorSupport K)
        0 (preSieveModulus K) (intervalStart K) (sieveCoefficient K)| <
      (intervalStart K : ℝ) / preSieveModulus K *
        ((1 / 4 : ℝ) * productCoordinateEnergy K) := by
  let E : ℝ := compatibleDivisorPairErrorSum (nearShifts K)
    (sieveDivisorSupport K) 0 (preSieveModulus K) (intervalStart K)
      (sieveCoefficient K)
  have hW : (0 : ℝ) < preSieveModulus K := by
    exact_mod_cast preSieveModulus_pos K
  have hx : (0 : ℝ) < intervalStart K := by
    exact_mod_cast intervalStart_pos K
  have hs : (0 : ℝ) < (16 : ℝ) ^ K := by positivity
  have hfactor : (0 : ℝ) <
      (preSieveModulus K : ℝ) * 4 * 16 ^ K := by positivity
  have hscaled : |E| *
      ((preSieveModulus K : ℝ) * 4 * 16 ^ K) < intervalStart K := by
    simpa [E] using scaled_abs_sieveIntervalError_lt_intervalStart hK
  have herror : |E| <
      (intervalStart K : ℝ) /
        ((preSieveModulus K : ℝ) * 4 * 16 ^ K) :=
    (lt_div_iff₀ hfactor).2 hscaled
  have henergy := one_div_sixteen_pow_le_productCoordinateEnergy hK
  calc
    |compatibleDivisorPairErrorSum (nearShifts K) (sieveDivisorSupport K)
        0 (preSieveModulus K) (intervalStart K) (sieveCoefficient K)| =
        |E| := rfl
    _ < (intervalStart K : ℝ) /
        ((preSieveModulus K : ℝ) * 4 * 16 ^ K) := herror
    _ = (intervalStart K : ℝ) / preSieveModulus K *
        ((1 / 4 : ℝ) * (1 / 16 : ℝ) ^ K) := by
      have hpow : (16 : ℝ) ^ K ≠ 0 := by positivity
      field_simp
      simpa [div_pow, hpow] using
        (inv_mul_cancel₀ hpow).symm
    _ ≤ (intervalStart K : ℝ) / preSieveModulus K *
        ((1 / 4 : ℝ) * productCoordinateEnergy K) := by
      gcongr

/-- The exact unnormalized sieve mass contains a fixed fraction of the
independent product energy. -/
theorem quarter_scaled_energy_lt_sieveMass {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) :
    (intervalStart K : ℝ) / preSieveModulus K *
        ((1 / 4 : ℝ) * productCoordinateEnergy K) < sieveMass K := by
  let X : ℝ := (intervalStart K : ℝ) / preSieveModulus K
  let G : ℝ := productCoordinateEnergy K
  let B : ℝ := maynardYDiagonalSum (nearShifts K) (globalRadius K)
      (preSieveModulus K) (sieveY K) -
    incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
      (sieveDivisorSupport K) (sieveCoefficient K)
  let E : ℝ := compatibleDivisorPairErrorSum (nearShifts K)
    (sieveDivisorSupport K) 0 (preSieveModulus K) (intervalStart K)
      (sieveCoefficient K)
  have hX : 0 < X := by
    dsimp [X]
    exact div_pos
      (by exact_mod_cast intervalStart_pos K)
      (by exact_mod_cast preSieveModulus_pos K)
  have hG : 0 ≤ G := productCoordinateEnergy_nonneg K
  have hbracket : (1 / 2 : ℝ) * G ≤ B := by
    simpa [B, G] using half_productEnergy_le_sieveBracket hA hreg
  have herr : |E| < X * ((1 / 4 : ℝ) * G) := by
    simpa [E, X, G] using
      abs_sieveIntervalError_lt_quarter_scaled_energy hreg.1
  have hE : -X * ((1 / 4 : ℝ) * G) < E := by
    linarith [neg_abs_le E]
  rw [sieveMass_eq_main_add_error, sieveMain_eq_diagonal_sub_cross]
  change X * ((1 / 4 : ℝ) * G) < X * B + E
  have hmain : X * ((1 / 2 : ℝ) * G) ≤ X * B :=
    mul_le_mul_of_nonneg_left hbracket hX.le
  nlinarith

end Erdos248
