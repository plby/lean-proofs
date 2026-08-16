import ErdosProblems.Erdos6.GenericFiberDiagonalLower

/-!
# Asymptotic lower bound for the large-tuple fiber diagonal
-/

namespace Erdos6.Maynard

open Filter MeasureTheory Set

noncomputable section

def largeFiberLowerCoefficient : ℝ :=
  largeShortMass ^ 2 *
    ((1 : ℝ) / 8 * largeBaseMass ^ (largeK - 1))

theorem largeFiberLowerCoefficient_pos : 0 < largeFiberLowerCoefficient := by
  unfold largeFiberLowerCoefficient
  have hm : 0 < largeShortMass := by
    have hden : 0 < 3 * (largeK : ℝ) :=
      mul_pos (by norm_num) (Nat.cast_pos.mpr largeK_pos)
    exact (inv_pos.mpr hden).trans inv_threeK_lt_largeShortMass
  exact mul_pos (sq_pos_of_pos hm)
    (mul_pos (by norm_num) (pow_pos largeBaseMass_pos _))

theorem tendsto_largeFiberRelativeError_zero
    {alpha : ℝ} (halpha : 0 < alpha) (K C : ℝ) :
    Tendsto (fun N : ℕ => largeFiberRelativeError K C
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
  let L : ℕ → ℝ := fun N =>
    Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
  let D : ℕ → ℕ := fun N =>
    BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  have hL : Tendsto L atTop atTop := by
    simpa [L] using
      BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hK : Tendsto (fun N : ℕ => K / L N) atTop (nhds 0) :=
    hL.const_div_atTop K
  have hD : Tendsto (fun N : ℕ => Real.log (D N) / L N)
      atTop (nhds 0) := by
    simpa [D, L] using
      BoundedGaps.Maynard.tendsto_log_tripleLogCutoff_div_logRadius_zero
        halpha
  have hlogL : Tendsto (fun N : ℕ => Real.log (L N) / L N)
      atTop (nhds 0) := by
    simpa using
      (Real.isLittleO_log_id_atTop.comp_tendsto hL).tendsto_div_nhds_zero
  have hC : Tendsto (fun N : ℕ => C / L N) atTop (nhds 0) :=
    hL.const_div_atTop C
  have htwo : Tendsto (fun N : ℕ => (2 : ℝ) / L N)
      atTop (nhds 0) := hL.const_div_atTop 2
  have hlog2 : Tendsto (fun N : ℕ => Real.log 2 / L N)
      atTop (nhds 0) := hL.const_div_atTop (Real.log 2)
  have hsum := (((hK.add hD).add ((hlogL.add hC).add htwo)).add hlog2)
  have hratio : Tendsto (fun N : ℕ =>
      (K + Real.log (D N) + (Real.log (L N) + C + 2) + Real.log 2) /
        L N) atTop (nhds 0) := by
    convert hsum using 1
    · funext N
      ring
    · norm_num
  have hscaled := hratio.const_mul (22 : ℝ)
  convert hscaled using 1
  · funext N
    unfold largeFiberRelativeError
    dsimp [D, L]
    ring
  · norm_num

theorem eventually_largeFiber_conditions
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ BoundedGaps.Maynard.tripleLogCutoff (N - 1) ∧
      2 ≤ Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ∧
      Real.log 2 / Real.log
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤ (1 : ℝ) / 56 ∧
      Real.log 3 / Real.log
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤ (1 : ℝ) / 56 := by
  obtain ⟨N₀, hN₀⟩ := BoundedGaps.Maynard.exists_tripleLogCutoff_ge 2
  have hL :=
    BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hlog2 : Tendsto (fun N : ℕ => Real.log 2 /
      Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := hL.const_div_atTop (Real.log 2)
  have hlog3 : Tendsto (fun N : ℕ => Real.log 3 /
      Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := hL.const_div_atTop (Real.log 3)
  have he2 := hlog2.eventually (eventually_le_nhds (by norm_num :
    (0 : ℝ) < 1 / 56))
  have he3 := hlog3.eventually (eventually_le_nhds (by norm_num :
    (0 : ℝ) < 1 / 56))
  filter_upwards [eventually_ge_atTop (N₀ + 1),
      hL.eventually (eventually_ge_atTop 2), he2, he3] with N hN hLN h2 h3
  exact ⟨hN₀ (N - 1) (by omega), hLN, h2, h3⟩

theorem eventually_largeCoordinateFiberSquareDiagonal_normalized_gt
    (m : largePowerTuple) {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      largeFiberLowerCoefficient <
        tupleCoordinateFiberSquareDiagonal largePowerTuple alpha N m /
          (BoundedGaps.Maynard.preSieveSingularSeries
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ^ 2 *
            tupleNaturalScale (largeOffFace m) alpha N) := by
  obtain ⟨K, C, hK, hC, hAbel⟩ :=
    exists_uniform_tupleFiberScalarSum_abel_bound
  let eta : ℕ → ℝ := fun N => largeFiberRelativeError K C
    (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
  let A : ℕ → ℝ := fun N =>
    normalizedTupleOuterMaynardWeightedMoment (largeOffFace m) alpha
      largeOuterSquaredIntegrand N
  let B : ℕ → ℝ := fun N =>
    normalizedTupleOuterMaynardWeightedMoment (largeOffFace m) alpha
      largeOuterContinuousDensity N
  let IA := ∫ t in BoundedGaps.Maynard.finiteSimplexOf (largeOffFace m),
    largeOuterSquaredIntegrand t
  let IB := ∫ t in BoundedGaps.Maynard.finiteSimplexOf (largeOffFace m),
    largeOuterContinuousDensity t
  have heta : Tendsto eta atTop (nhds 0) := by
    simpa [eta] using tendsto_largeFiberRelativeError_zero halpha K C
  have hA : Tendsto A atTop (nhds IA) := by
    simpa [A, IA, tupleOffFace_largePowerTuple] using
      tendsto_normalizedLargeOffFaceMaynardSquaredOuterMoment m halpha
  have hB : Tendsto B atTop (nhds IB) := by
    simpa [B, IB, tupleOffFace_largePowerTuple] using
      tendsto_normalizedLargeOffFaceMaynardDensityMoment m halpha
  have herr : Tendsto (fun N : ℕ => (2 * eta N + eta N ^ 2) * B N)
      atTop (nhds 0) := by
    have he : Tendsto (fun N : ℕ => 2 * eta N + eta N ^ 2)
        atTop (nhds 0) := by
      convert (heta.const_mul 2).add (heta.pow 2) using 1 <;> norm_num
    simpa using he.mul hB
  have hbracket : Tendsto (fun N : ℕ =>
      largeShortMass ^ 2 * A N - (2 * eta N + eta N ^ 2) * B N)
      atTop (nhds (largeShortMass ^ 2 * IA)) := by
    simpa using (hA.const_mul (largeShortMass ^ 2)).sub herr
  have hlimit : largeFiberLowerCoefficient < largeShortMass ^ 2 * IA := by
    unfold largeFiberLowerCoefficient IA
    exact mul_lt_mul_of_pos_left (largeOffFaceSquaredOuterMoment_limit_gt m)
      (sq_pos_of_pos (by
        have hden : 0 < 3 * (largeK : ℝ) :=
          mul_pos (by norm_num) (Nat.cast_pos.mpr largeK_pos)
        exact (inv_pos.mpr hden).trans inv_threeK_lt_largeShortMass))
  have hbracketEventually := hbracket.eventually (eventually_gt_nhds hlimit)
  have hconditions := eventually_largeFiber_conditions halpha
  have houterScale := eventually_tupleNaturalScale_pos
    (H := largeOffFace m) halpha
  filter_upwards [hbracketEventually, hconditions, houterScale] with
      N hbracketN hcond hscale
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let P := BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 *
    Real.log R ^ 2
  have hP : 0 < P := by
    dsimp [P]
    have hS := BoundedGaps.Maynard.preSieveSingularSeries_pos D
    have hL : 0 < Real.log R := by linarith [hcond.2.1]
    exact mul_pos (sq_pos_of_pos hS) (sq_pos_of_pos hL)
  have hfinite := tupleCoordinateFiberSquareDiagonal_lower hK hC hAbel m
    hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
  have hdiv := div_le_div_of_nonneg_right hfinite
    (mul_nonneg hP.le hscale.le)
  have heq :
      P * (largeShortMass ^ 2 *
            tupleOuterMaynardWeightedMoment (largeOffFace m) alpha
              largeOuterSquaredIntegrand N -
          (2 * eta N + eta N ^ 2) *
            tupleOuterMaynardWeightedMoment (largeOffFace m) alpha
              largeOuterContinuousDensity N) /
          (P * tupleNaturalScale (largeOffFace m) alpha N) =
        largeShortMass ^ 2 * A N -
          (2 * eta N + eta N ^ 2) * B N := by
    dsimp [A, B]
    unfold normalizedTupleOuterMaynardWeightedMoment
    field_simp [hP.ne', hscale.ne']
  rw [tupleOffFace_largePowerTuple] at hdiv
  change P * (largeShortMass ^ 2 *
            tupleOuterMaynardWeightedMoment (largeOffFace m) alpha
              largeOuterSquaredIntegrand N -
          (2 * eta N + eta N ^ 2) *
            tupleOuterMaynardWeightedMoment (largeOffFace m) alpha
              largeOuterContinuousDensity N) /
          (P * tupleNaturalScale (largeOffFace m) alpha N) ≤
        tupleCoordinateFiberSquareDiagonal largePowerTuple alpha N m /
          (P * tupleNaturalScale (largeOffFace m) alpha N) at hdiv
  rw [heq] at hdiv
  exact hbracketN.trans_le (by
    simpa [D, R, P, eta, tupleOffFace_largePowerTuple] using hdiv)

end

end Erdos6.Maynard
