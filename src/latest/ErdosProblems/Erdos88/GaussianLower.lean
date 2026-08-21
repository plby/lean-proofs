import ErdosProblems.Erdos88.GaussianInfluentialSelection
import ErdosProblems.Erdos88.GaussianDensityLower
import ErdosProblems.Erdos88.GaussianDensity
import ErdosProblems.Erdos88.GaussianNonuniformSmallCoordinates

/-!
# Lower intervals for ordered Gaussian quadratics

This module assembles the two branches of the lower half of KSSS
Theorem 5.2(2): Petrov density comparison when every coordinate is small,
and the influential-coordinate argument otherwise.
-/

open MeasureTheory ProbabilityTheory Set

namespace Erdos88.GaussianQuadratic

/-- In the no-influential-coordinate regime, the actual continuous density
is uniformly close to the standard normal density. -/
theorem exists_continuousDensity_diagonal_comparison_of_small_coordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) {rho : ℝ}
    (hsum : totalVariance a lam = 1)
    (hrho : 0 < rho) (hrhoHalf : rho ≤ 1 / 2)
    (hsmall : ∀ i, coordinateSigma (a i) (lam i) < rho) :
    ∃ p : ℝ → ℝ,
      Erdos88.Esseen.HasContinuousDensity (diagonalCenteredLaw a lam) p ∧
        ∀ u : ℝ, |p u - standardNormalDensity u| ≤
          (2 * Real.pi)⁻¹ * (1408 * rho) := by
  let p := inverseFourierDensityCandidate (diagonalCenteredCharProduct a lam)
  have hsmallVar : ∀ i, coordinateVariance (a i) (lam i) ≤ 1 / 4 := by
    intro i
    have hsquare :=
      (sq_le_sq₀ (coordinateSigma_nonneg (a i) (lam i)) hrho.le).mpr
        (hsmall i).le
    rw [coordinateSigma_sq] at hsquare
    nlinarith [sq_nonneg rho]
  have hcube : sigmaCubeSum a lam ≤ rho := by
    unfold sigmaCubeSum
    calc
      (∑ i, coordinateSigma (a i) (lam i) ^ 3) ≤
          ∑ i, rho * coordinateVariance (a i) (lam i) := by
        apply Finset.sum_le_sum
        intro i hi
        have hmul := mul_le_mul_of_nonneg_right (hsmall i).le
          (sq_nonneg (coordinateSigma (a i) (lam i)))
        calc
          coordinateSigma (a i) (lam i) ^ 3 =
              coordinateSigma (a i) (lam i) *
                coordinateSigma (a i) (lam i) ^ 2 := by ring
          _ ≤ rho * coordinateSigma (a i) (lam i) ^ 2 := hmul
          _ = rho * coordinateVariance (a i) (lam i) := by
            rw [coordinateSigma_sq]
      _ = rho * totalVariance a lam := by
        unfold totalVariance
        rw [Finset.mul_sum]
      _ = rho := by rw [hsum, mul_one]
  have hcubePos : 0 < sigmaCubeSum a lam :=
    sigmaCubeSum_pos_of_totalVariance_eq_one a lam hsum
  have hGamma : 0 < lyapunovGamma a lam :=
    lyapunovGamma_pos_of_totalVariance_eq_one a lam hsum
  have hGammaInv : 1 / lyapunovGamma a lam = sigmaCubeSum a lam := by
    rw [lyapunovGamma_eq_inv_sigmaCubeSum_of_normalized hsum]
    field_simp [hcubePos.ne']
  have hchar : Integrable (diagonalCenteredCharProduct a lam) :=
    diagonalCenteredCharProduct_integrable_of_small_coordinates
      a lam hsum hsmallVar
  have hthird : 0 < totalThirdAbsMoment a lam := by
    have hL := lyapunovL_pos_of_coordinate_moments a lam hsum
      (fun i ↦ coordinateThirdAbsMoment_lower (a i) (lam i))
      (fun i ↦ coordinateThirdAbsMoment_upper (a i) (lam i))
    rw [lyapunovL_eq_totalThirdAbsMoment_of_normalized hsum] at hL
    exact hL
  have hstandard : ∀ t : ℝ,
      |t| ≤ 1 / (4 * lyapunovL a lam) →
      ‖diagonalCenteredCharProduct a lam t - standardNormalChar t‖ ≤
        16 * lyapunovL a lam * localCLTEnvelope t := by
    intro t ht
    rw [lyapunovL_eq_totalThirdAbsMoment_of_normalized hsum] at ht ⊢
    exact norm_diagonalCenteredCharProduct_sub_standardNormalChar_le
      a lam hsum hthird t ht
  have htail :
      ∫ t : ℝ in
          Set.Iic (-(lyapunovGamma a lam / 32)) ∪
            Set.Ioi (lyapunovGamma a lam / 32),
          diagonalCharModulus a lam t ≤ 128 / lyapunovGamma a lam := by
    have h := diagonalCharModulus_integral_twoSided_le
      a lam hsum hsmallVar hchar
        (K := lyapunovGamma a lam / 32) (by positivity)
    calc
      (∫ t : ℝ in
          Set.Iic (-(lyapunovGamma a lam / 32)) ∪
            Set.Ioi (lyapunovGamma a lam / 32),
          diagonalCharModulus a lam t) ≤
          4 / (lyapunovGamma a lam / 32) := h
      _ = 128 / lyapunovGamma a lam := by
        field_simp [hGamma.ne']
        norm_num
  letI : IsProbabilityMeasure (diagonalCenteredLaw a lam) :=
    diagonalCenteredLaw_isProbabilityMeasure a lam
  have hlawChar : Integrable (charFun (diagonalCenteredLaw a lam)) := by
    rw [charFun_diagonalCenteredLaw]
    exact hchar
  have hdens : Erdos88.Esseen.HasContinuousDensity
      (diagonalCenteredLaw a lam) p := by
    have h := hasContinuousDensity_inverseFourierDensityCandidate
      (diagonalCenteredLaw a lam) hlawChar
    simpa only [p, charFun_diagonalCenteredLaw] using h
  refine ⟨p, hdens, ?_⟩
  intro u
  have hraw := diagonalDensityComparison_of_coordinateMoments_of_inverseFourier
    a lam hsum
      (fun i ↦ coordinateThirdAbsMoment_lower (a i) (lam i))
      (fun i ↦ coordinateThirdAbsMoment_upper (a i) (lam i))
      hchar (inverseFourierDensityCandidate_diagonal_hasInverse a lam)
      standardNormal_hasInverseFourierDensity hstandard htail u
  calc
    |p u - standardNormalDensity u| ≤
        (2 * Real.pi)⁻¹ *
          (1280 / lyapunovGamma a lam + 128 / lyapunovGamma a lam) := hraw
    _ = (2 * Real.pi)⁻¹ *
          (1408 * (1 / lyapunovGamma a lam)) := by ring
    _ = (2 * Real.pi)⁻¹ * (1408 * sigmaCubeSum a lam) := by rw [hGammaInv]
    _ ≤ (2 * Real.pi)⁻¹ * (1408 * rho) := by gcongr

/-- The no-influential-coordinate interval lower bound on a fixed compact
positive half-line. -/
theorem diagonal_lower_of_small_coordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) {rho M x eps : ℝ}
    (hsum : totalVariance a lam = 1)
    (hrho : 0 < rho) (hrhoHalf : rho ≤ 1 / 2)
    (hsmall : ∀ i, coordinateSigma (a i) (lam i) < rho)
    (hM : 0 ≤ M)
    (hdelta : 2 * ((2 * Real.pi)⁻¹ * (1408 * rho)) ≤
      standardNormalDensity (M + 1))
    (hx : 0 ≤ x) (hxM : x ≤ M)
    (heps : 0 ≤ eps) (hepsOne : eps ≤ 1) :
    (standardNormalDensity (M + 1) / 2) * eps ≤
      (Measure.pi fun _ : ι ↦ standardGaussian).real
        ((diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps)) := by
  by_cases hepsZero : eps = 0
  · subst eps
    simp only [mul_zero]
    exact measureReal_nonneg
  have hepsPos : 0 < eps := lt_of_le_of_ne heps (Ne.symm hepsZero)
  obtain ⟨p, hdens, hclose⟩ :=
    exists_continuousDensity_diagonal_comparison_of_small_coordinates
      a lam hsum hrho hrhoHalf hsmall
  let delta := (2 * Real.pi)⁻¹ * (1408 * rho)
  let center := x + eps / 2
  let radius := eps / 2
  letI : IsProbabilityMeasure (diagonalCenteredLaw a lam) :=
    diagonalCenteredLaw_isProbabilityMeasure a lam
  have hwindow : |center| + radius ≤ M + 1 := by
    have hcenter : 0 ≤ center := by dsimp only [center]; positivity
    rw [abs_of_nonneg hcenter]
    dsimp only [center, radius]
    linarith
  have hball := smallBall_ge_of_uniform_standardNormal_close
    (diagonalCenteredLaw a lam) hdens
      (delta := delta) (M := M + 1) (eps := radius) (x := center)
      (by linarith) (by dsimp only [radius]; positivity) hwindow
      (by simpa only [delta] using hclose)
  have hmass : eps * (standardNormalDensity (M + 1) - delta) ≤
      (diagonalCenteredLaw a lam).real (Set.Icc x (x + eps)) := by
    change 2 * radius * (standardNormalDensity (M + 1) - delta) ≤
      (diagonalCenteredLaw a lam).real
        (Set.Icc (center - radius) (center + radius)) at hball
    convert hball using 1 <;> dsimp only [center, radius] <;> ring
  have hlower : (standardNormalDensity (M + 1) / 2) * eps ≤
      eps * (standardNormalDensity (M + 1) - delta) := by
    have hdelta' : 2 * delta ≤ standardNormalDensity (M + 1) := by
      simpa only [delta] using hdelta
    nlinarith
  have hpull : (diagonalCenteredLaw a lam).real (Set.Icc x (x + eps)) =
      (Measure.pi fun _ : ι ↦ standardGaussian).real
        ((diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps)) := by
    rw [← map_diagonalPartialSum_univ_eq_diagonalCenteredLaw a lam]
    rw [map_measureReal_apply
      (continuous_diagonalPartialSum a lam Finset.univ).measurable measurableSet_Icc]
  rw [← hpull]
  exact hlower.trans hmass

/-- The small-coordinate cutoff used in the complete ordered lower theorem. -/
noncomputable def orderedGaussianSmallThreshold (M : ℝ) : ℝ :=
  min (1 / 2)
    (standardNormalDensity (M + 1) * (2 * Real.pi) / (2 * 1408))

/-- A coefficient-uniform constant for the full ordered Gaussian lower
theorem. -/
noncomputable def orderedGaussianLowerConstant (M : ℝ) : ℝ :=
  min (influentialLowerConstant M (orderedGaussianSmallThreshold M))
    (standardNormalDensity (M + 1) / 2)

lemma orderedGaussianSmallThreshold_pos (M : ℝ) :
    0 < orderedGaussianSmallThreshold M := by
  unfold orderedGaussianSmallThreshold
  exact lt_min (by norm_num)
    (div_pos (mul_pos (standardNormalDensity_pos _) (by positivity)) (by norm_num))

lemma orderedGaussianLowerConstant_pos {M : ℝ} (hM : 0 ≤ M) :
    0 < orderedGaussianLowerConstant M := by
  unfold orderedGaussianLowerConstant
  exact lt_min
    (influentialLowerConstant_pos hM (orderedGaussianSmallThreshold_pos M))
    (div_pos (standardNormalDensity_pos _) (by norm_num))

/-- Complete normalized lower half of KSSS Theorem 5.2(2) for an ordered
diagonal quadratic Gaussian. -/
theorem uniform_diagonal_lower_of_ordered_eigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (k : ι) {M x eps : ℝ}
    (hsum : totalVariance a lam = 1)
    (hM : 0 ≤ M)
    (hlamk : 0 ≤ lam k)
    (hmax : ∀ i, |lam i| ≤ lam k)
    (hx : 0 ≤ x) (hxM : x ≤ M)
    (heps : 0 ≤ eps) (hepsOne : eps ≤ 1) :
    orderedGaussianLowerConstant M * eps ≤
      (Measure.pi fun _ : ι ↦ standardGaussian).real
        ((diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps)) := by
  let rho := orderedGaussianSmallThreshold M
  have hrho : 0 < rho := orderedGaussianSmallThreshold_pos M
  have hrhoHalf : rho ≤ 1 / 2 := by
    dsimp only [rho, orderedGaussianSmallThreshold]
    exact min_le_left _ _
  have hrhoOne : rho ≤ 1 := hrhoHalf.trans (by norm_num)
  have hdelta : 2 * ((2 * Real.pi)⁻¹ * (1408 * rho)) ≤
      standardNormalDensity (M + 1) := by
    have hrhoBound : rho ≤
        standardNormalDensity (M + 1) * (2 * Real.pi) / (2 * 1408) := by
      dsimp only [rho, orderedGaussianSmallThreshold]
      exact min_le_right _ _
    have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    calc
      2 * ((2 * Real.pi)⁻¹ * (1408 * rho)) ≤
          2 * ((2 * Real.pi)⁻¹ *
            (1408 * (standardNormalDensity (M + 1) *
              (2 * Real.pi) / (2 * 1408)))) := by gcongr
      _ = standardNormalDensity (M + 1) := by
        field_simp [hpi.ne']
  by_cases hinf : ∃ i, rho ≤ coordinateSigma (a i) (lam i)
  · have hbase := uniform_diagonal_lower_of_ordered_eigenvalues_influential
      a lam k hsum hrho hrhoOne hM hlamk hmax hinf hx hxM heps hepsOne
    exact (mul_le_mul_of_nonneg_right
      (min_le_left
        (influentialLowerConstant M rho)
        (standardNormalDensity (M + 1) / 2)) heps).trans
      (by simpa only [rho, orderedGaussianLowerConstant] using hbase)
  · have hsmall : ∀ i, coordinateSigma (a i) (lam i) < rho := by
      intro i
      exact lt_of_not_ge (fun hi ↦ hinf ⟨i, hi⟩)
    have hbase := diagonal_lower_of_small_coordinates
      a lam hsum hrho hrhoHalf hsmall hM hdelta hx hxM heps hepsOne
    exact (mul_le_mul_of_nonneg_right
      (min_le_right
        (influentialLowerConstant M rho)
        (standardNormalDensity (M + 1) / 2)) heps).trans
      (by simpa only [rho, orderedGaussianLowerConstant] using hbase)

end Erdos88.GaussianQuadratic
