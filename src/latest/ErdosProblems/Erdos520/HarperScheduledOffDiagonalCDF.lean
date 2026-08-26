import ErdosProblems.Erdos520.HarperScheduledOffDiagonal
import ErdosProblems.Erdos520.HarperScheduledRelativeProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal

namespace Erdos
namespace Problem520

/-!
# Off-diagonal scheduled Gaussian replacement

The evaluation height may vary from block to block, provided that its
displacement from the tilt height is at most the reciprocal local logarithmic
scale.  The off-diagonal moment bounds keep every variance in `[1/4,1/2]`.
This is enough for the same strong-frequency CDF error, the same summable
relative cell losses, and hence the same fixed `exp 2` finite-slicing loss as
on the diagonal.
-/

theorem inv_sqrt_le_two_of_one_quarter_lt {v : ℝ}
    (hv : (1 / 4 : ℝ) < v) :
    (Real.sqrt v)⁻¹ ≤ 2 := by
  have hquarter : (1 / 2 : ℝ) ^ 2 ≤ v := by nlinarith
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt v :=
    (Real.le_sqrt' (by norm_num)).2 hquarter
  have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hsqrt
  norm_num at hinv ⊢
  exact hinv

/-- The Gaussian density lower bound used for relative cells remains valid
throughout the wider off-diagonal variance window `[1/4,1/2]`. -/
theorem gaussianPDFReal_zero_ge_of_variance_quarter_half
    {v : ℝ≥0} (hvLower : (1 / 4 : ℝ) ≤ (v : ℝ))
    (hvUpper : (v : ℝ) ≤ 1 / 2)
    {a delta x : ℝ} (hdelta1 : delta ≤ 1)
    (hx : x ∈ Ioc a (a + delta)) :
    (1 / 2 : ℝ) * Real.exp (-2 * (|a| + 1) ^ 2) ≤
      gaussianPDFReal 0 v x := by
  have hv : v ≠ 0 := by
    intro hzero
    simp only [hzero, NNReal.coe_zero] at hvLower
    norm_num at hvLower
  have hvpos : 0 < (v : ℝ) := by linarith
  have hdenpos : 0 < Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    apply Real.sqrt_pos.2
    positivity
  have hinside : 2 * Real.pi * (v : ℝ) ≤ 4 := by
    calc
      2 * Real.pi * (v : ℝ) ≤ 2 * Real.pi * (1 / 2 : ℝ) := by gcongr
      _ ≤ 4 := by nlinarith [Real.pi_lt_four]
  have hdensqrt : Real.sqrt (2 * Real.pi * (v : ℝ)) ≤ 2 := by
    apply (Real.sqrt_le_left (by norm_num)).2
    nlinarith [hinside]
  have hcoef : (1 / 2 : ℝ) ≤
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
    simpa only [one_div] using!
      one_div_le_one_div_of_le hdenpos hdensqrt
  have hxsub0 : 0 ≤ x - a := by linarith [hx.1]
  have hxsub : x - a ≤ delta := by linarith [hx.2]
  have hxabs : |x| ≤ |a| + 1 := by
    calc
      |x| = |a + (x - a)| := by ring_nf
      _ ≤ |a| + |x - a| := abs_add_le _ _
      _ = |a| + (x - a) := by rw [abs_of_nonneg hxsub0]
      _ ≤ |a| + delta := by linarith
      _ ≤ |a| + 1 := by linarith
  have hxsq : x ^ 2 ≤ (|a| + 1) ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ (abs_nonneg x) hxabs 2
  have hbase : 0 ≤ (|a| + 1) ^ 2 := sq_nonneg _
  have hdenLower : (1 / 2 : ℝ) ≤ 2 * (v : ℝ) := by linarith
  have hquot : x ^ 2 / (2 * (v : ℝ)) ≤ 2 * (|a| + 1) ^ 2 := by
    calc
      x ^ 2 / (2 * (v : ℝ)) ≤
          (|a| + 1) ^ 2 / (2 * (v : ℝ)) := by gcongr
      _ ≤ (|a| + 1) ^ 2 / (1 / 2 : ℝ) := by
        exact div_le_div_of_nonneg_left hbase (by norm_num) hdenLower
      _ = 2 * (|a| + 1) ^ 2 := by ring
  have hexp : Real.exp (-2 * (|a| + 1) ^ 2) ≤
      Real.exp (-x ^ 2 / (2 * (v : ℝ))) := by
    apply Real.exp_le_exp.mpr
    calc
      -2 * (|a| + 1) ^ 2 = -(2 * (|a| + 1) ^ 2) := by ring
      _ ≤ -(x ^ 2 / (2 * (v : ℝ))) := neg_le_neg hquot
      _ = -x ^ 2 / (2 * (v : ℝ)) := by ring
  unfold gaussianPDFReal
  simp only [sub_zero]
  exact mul_le_mul hcoef hexp (by positivity) (by positivity)

/-- Every short interval has the same elementary Gaussian mass lower bound,
uniformly for variances in the off-diagonal window `[1/4,1/2]`. -/
theorem gaussianReal_real_Ioc_ge_of_variance_quarter_half
    {v : ℝ≥0} (hvLower : (1 / 4 : ℝ) ≤ (v : ℝ))
    (hvUpper : (v : ℝ) ≤ 1 / 2)
    {a delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (delta / 2) * Real.exp (-2 * (|a| + 1) ^ 2) ≤
      (gaussianReal 0 v).real (Ioc a (a + delta)) := by
  have hv : v ≠ 0 := by
    intro hzero
    simp only [hzero, NNReal.coe_zero] at hvLower
    norm_num at hvLower
  rw [Measure.real, gaussianReal_apply_eq_integral 0 hv]
  rw [ENNReal.toReal_ofReal]
  · calc
      (delta / 2) * Real.exp (-2 * (|a| + 1) ^ 2) =
          ∫ _x in Ioc a (a + delta),
            (1 / 2 : ℝ) * Real.exp (-2 * (|a| + 1) ^ 2) := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith : 0 ≤ a + delta - a)]
        simp only [smul_eq_mul]
        ring
      _ ≤ ∫ x in Ioc a (a + delta), gaussianPDFReal 0 v x := by
        apply setIntegral_mono_on
        · exact MeasureTheory.integrableOn_const
            (μ := volume) (s := Ioc a (a + delta))
            (C := (1 / 2 : ℝ) * Real.exp (-2 * (|a| + 1) ^ 2))
            (hs := by rw [Real.volume_Ioc]; simp)
        · exact (integrable_gaussianPDFReal 0 v).integrableOn
        · exact measurableSet_Ioc
        · intro x hx
          exact gaussianPDFReal_zero_ge_of_variance_quarter_half
            hvLower hvUpper hdelta1 hx
  · exact integral_nonneg fun x ↦ gaussianPDFReal_nonneg 0 v x

/-- Strong-frequency Kolmogorov replacement for a nearby evaluation height.
The exact Fejer identity is already unconditional for arbitrary `t,u`. -/
theorem exists_eventually_harperScheduledOffDiagonalCDFDistance_le_strong
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : ℝ,
          |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
              (1 / 64 : ℝ) →
            harperCDFDistance
              (harperCenteredLinearBlockLaw y
                (harperScheduledPrimeBlock y j) t u)
              (harperGaussianBlockLaw y
                (harperScheduledPrimeBlock y j) t u) ≤
              130 / harperScheduledStrongComparisonFrequency j := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledOffDiagonalVariance_quarter_half M
  refine ⟨J, ?_⟩
  intro j hj y hy t htLower htUpper u hscale
  have hv := (hJ j hj y hy t htLower htUpper u hscale).1
  let V : ℝ := harperLinearBlockVariance y
    (harperScheduledPrimeBlock y j) t u
  let T : ℝ := harperScheduledStrongComparisonFrequency j
  have hV : (1 / 4 : ℝ) < V := hv
  have hVnn : harperLinearBlockVarianceNNReal y
      (harperScheduledPrimeBlock y j) t u ≠ 0 := by
    intro hzero
    have hcoezero : V = 0 := by
      simpa only [V, coe_harperLinearBlockVarianceNNReal] using!
        congrArg ((↑·) : NNReal → ℝ) hzero
    linarith
  have hT : 0 < T := harperScheduledStrongComparisonFrequency_pos j
  have hfrequency : 2 * T ≤ Real.sqrt (harperBlockEndpoint j : ℝ) :=
    harperScheduledStrongComparisonFrequency_condition j
  have hbase := harperCDFDistance_scheduledBlock_le_of_fejer_identity
    y j t u T hT hfrequency hVnn
      (by simpa only [T] using!
        harperScheduledStrongFejerSmoothedCDFIdentity y j t u)
  have hkernel :
      (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
          (32 * T ^ 3 + T ^ 4) ≤ 33 / T := by
    simpa only [T] using!
      harperScheduledStrongComparisonFrequency_kernel_budget j
  have hkernel' :
      (2 * Real.pi)⁻¹ *
          (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
            (32 * T ^ 3 + T ^ 4) ≤ 33 / T := by
    calc
      (2 * Real.pi)⁻¹ *
          (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
            (32 * T ^ 3 + T ^ 4) =
          (2 * Real.pi)⁻¹ *
            ((Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
              (32 * T ^ 3 + T ^ 4)) := by ring
      _ ≤ (2 * Real.pi)⁻¹ * (33 / T) := by gcongr
      _ ≤ 1 * (33 / T) := by
        gcongr
        exact fejer_coefficient_le_one
      _ = 33 / T := by ring
  have hvarinv : (Real.sqrt V)⁻¹ ≤ 2 :=
    inv_sqrt_le_two_of_one_quarter_lt hV
  have hvariance : 16 * (Real.sqrt V)⁻¹ / T ≤ 32 / T := by
    rw [div_le_div_iff_of_pos_right hT]
    nlinarith
  calc
    harperCDFDistance
          (harperCenteredLinearBlockLaw y
            (harperScheduledPrimeBlock y j) t u)
          (harperGaussianBlockLaw y
            (harperScheduledPrimeBlock y j) t u) ≤
        2 * ((2 * Real.pi)⁻¹ *
            (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
              (32 * T ^ 3 + T ^ 4) +
          16 * (Real.sqrt V)⁻¹ / T) := by
      simpa only [T, V, coe_harperLinearBlockVarianceNNReal] using! hbase
    _ ≤ 2 * (33 / T + 32 / T) := by gcongr
    _ = 130 / T := by ring
    _ = 130 / harperScheduledStrongComparisonFrequency j := rfl

/-- A moderate off-diagonal cell incurs only the summable multiplicative
loss `1 + (j+1)⁻²`. -/
theorem exists_eventually_harperScheduledOffDiagonalRelativeIntervalProbability_le_one_add_width_mul_gaussian
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : ℝ,
          |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
              (1 / 64 : ℝ) →
            ∀ a : ℝ,
              |a| + 1 ≤ (1 / 4 : ℝ) *
                Real.sqrt (((2 ^ j : ℕ) : ℝ)) →
              (harperCenteredLinearBlockLaw y
                (harperScheduledPrimeBlock y j) t u).real
                  (Ioc a (a + harperScheduledRelativeIntervalWidth j)) ≤
                (1 + harperScheduledRelativeIntervalWidth j) *
                  (harperGaussianBlockLaw y
                    (harperScheduledPrimeBlock y j) t u).real
                      (Ioc a
                        (a + harperScheduledRelativeIntervalWidth j)) := by
  obtain ⟨Jcdf, hJcdf⟩ :=
    exists_eventually_harperScheduledOffDiagonalCDFDistance_le_strong M
  obtain ⟨Jvar, hJvar⟩ :=
    exists_eventually_harperScheduledOffDiagonalVariance_quarter_half M
  obtain ⟨Jbudget, hJbudget⟩ := eventually_atTop.1
    eventually_harperScheduledStrongBudget_le_width_mul_relativeGaussianMass
  refine ⟨max (max Jcdf Jvar) Jbudget, ?_⟩
  intro j hj y hy t htLower htUpper u hscale a ha
  have hjcdf : Jcdf ≤ j :=
    (le_max_left Jcdf Jvar).trans (le_max_left _ Jbudget) |>.trans hj
  have hjvar : Jvar ≤ j :=
    (le_max_right Jcdf Jvar).trans (le_max_left _ Jbudget) |>.trans hj
  have hjbudget : Jbudget ≤ j := (le_max_right _ Jbudget).trans hj
  let rho := harperCenteredLinearBlockLaw y
    (harperScheduledPrimeBlock y j) t u
  let nu := harperGaussianBlockLaw y
    (harperScheduledPrimeBlock y j) t u
  let delta := harperScheduledRelativeIntervalWidth j
  have hdist : harperCDFDistance rho nu ≤
      130 / harperScheduledStrongComparisonFrequency j :=
    hJcdf j hjcdf y hy t htLower htUpper u hscale
  have habs : |rho.real (Ioc a (a + delta)) -
      nu.real (Ioc a (a + delta))| ≤ 2 * harperCDFDistance rho nu :=
    abs_measureReal_Ioc_sub_le_two_mul_cdfDistance rho nu
      (by dsimp [delta]; linarith [harperScheduledRelativeIntervalWidth_pos j])
  have hvar := hJvar j hjvar y hy t htLower htUpper u hscale
  have hgaussian :
      (delta / 2) * Real.exp (-2 * (|a| + 1) ^ 2) ≤
        nu.real (Ioc a (a + delta)) := by
    dsimp only [nu, harperGaussianBlockLaw]
    exact gaussianReal_real_Ioc_ge_of_variance_quarter_half
      (v := harperLinearBlockVarianceNNReal y
        (harperScheduledPrimeBlock y j) t u)
      (by simpa only [coe_harperLinearBlockVarianceNNReal] using! hvar.1.le)
      (by simpa only [coe_harperLinearBlockVarianceNNReal] using! hvar.2.le)
      (by simpa only [delta] using! harperScheduledRelativeIntervalWidth_pos j)
      (by simpa only [delta] using! harperScheduledRelativeIntervalWidth_le_one j)
  have hbudget := hJbudget j hjbudget a ha
  have herr : rho.real (Ioc a (a + delta)) -
      nu.real (Ioc a (a + delta)) ≤
        delta * nu.real (Ioc a (a + delta)) := by
    calc
      rho.real (Ioc a (a + delta)) - nu.real (Ioc a (a + delta)) ≤
          |rho.real (Ioc a (a + delta)) -
            nu.real (Ioc a (a + delta))| := le_abs_self _
      _ ≤ 2 * harperCDFDistance rho nu := habs
      _ ≤ 2 * (130 / harperScheduledStrongComparisonFrequency j) := by gcongr
      _ = 260 / harperScheduledStrongComparisonFrequency j := by ring
      _ ≤ delta * ((delta / 2) *
          Real.exp (-2 * (|a| + 1) ^ 2)) := by
        simpa only [delta] using! hbudget
      _ ≤ delta * nu.real (Ioc a (a + delta)) := by
        gcongr
        exact (harperScheduledRelativeIntervalWidth_pos j).le
  dsimp only [rho, nu, delta] at herr ⊢
  linarith

/-- Every moderate off-diagonal product cell is dominated with the fixed
factor `exp 2`, uniformly in the path length. -/
theorem exists_eventually_harperScheduledOffDiagonalModerateCoordinateCell_le_exp_two_mul_gaussian
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : Fin n → ℝ,
          (∀ i : Fin n,
            |u i - t| *
                Real.log (harperBlockEndpoint
                  (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
            ∀ z : Fin n → ℤ,
              (∀ i : Fin n,
                |(z i : ℝ) *
                    harperScheduledRelativeIntervalWidth
                      (start + (i : ℕ))| + 1 ≤
                  (1 / 4 : ℝ) *
                    Real.sqrt
                      (((2 ^ (start + (i : ℕ)) : ℕ) : ℝ))) →
              (Measure.pi (fun i : Fin n ↦
                harperCenteredLinearBlockLaw y
                  (harperScheduledPrimeBlock y
                    (start + (i : ℕ))) t (u i))).real
                  (harperLatticeIocCell
                    (fun i : Fin n ↦
                      harperScheduledRelativeIntervalWidth
                        (start + (i : ℕ))) z) ≤
                Real.exp 2 *
                  (Measure.pi (fun i : Fin n ↦
                    harperGaussianBlockLaw y
                      (harperScheduledPrimeBlock y
                        (start + (i : ℕ))) t (u i))).real
                    (harperLatticeIocCell
                      (fun i : Fin n ↦
                        harperScheduledRelativeIntervalWidth
                          (start + (i : ℕ))) z) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledOffDiagonalRelativeIntervalProbability_le_one_add_width_mul_gaussian M
  refine ⟨J, ?_⟩
  intro start hstart n y hy t htLower htUpper u hscale z hz
  let rho : Fin n → Measure ℝ := fun i ↦
    harperCenteredLinearBlockLaw y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)
  let nu : Fin n → Measure ℝ := fun i ↦
    harperGaussianBlockLaw y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)
  let delta : Fin n → ℝ := fun i ↦
    harperScheduledRelativeIntervalWidth (start + (i : ℕ))
  let C : Fin n → ℝ := fun i ↦ 1 + delta i
  have hendpoint (i : Fin n) :
      harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
    exact (monotone_harperBlockEndpoint (by omega)).trans hy
  have hstarti (i : Fin n) : J ≤ start + (i : ℕ) := by omega
  have hcoord (i : Fin n) :
      (rho i).real (Ioc ((z i : ℝ) * delta i)
        ((z i : ℝ) * delta i + delta i)) ≤
        C i * (nu i).real (Ioc ((z i : ℝ) * delta i)
          ((z i : ℝ) * delta i + delta i)) := by
    exact hJ (start + (i : ℕ)) (hstarti i) y (hendpoint i)
      t htLower htUpper (u i) (hscale i)
      ((z i : ℝ) * delta i) (by simpa only [delta] using! hz i)
  have hprod := measureReal_pi_coordinateCell_le_prod_mul rho nu C
    (fun i ↦ (z i : ℝ) * delta i) delta hcoord
  have hCprod : (∏ i, C i) ≤ Real.exp 2 := by
    simpa only [C, delta] using!
      prod_one_add_harperScheduledRelativeIntervalWidth_le_exp_two start n
  calc
    (Measure.pi rho).real (harperLatticeIocCell delta z) ≤
        (∏ i, C i) *
          (Measure.pi nu).real (harperLatticeIocCell delta z) := by
      simpa only [harperLatticeIocCell] using! hprod
    _ ≤ Real.exp 2 *
        (Measure.pi nu).real (harperLatticeIocCell delta z) := by
      exact mul_le_mul_of_nonneg_right hCprod (by positivity)

/-- Finite slicing for the off-diagonal product law.  The entire moderate
barrier event costs only `exp 2`, with no dependence on the number of
blocks. -/
theorem exists_eventually_harperScheduledOffDiagonalModerateBoxBarrierProbability_le_exp_two_mul_gaussian
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : Fin n → ℝ,
          (∀ i : Fin n,
            |u i - t| *
                Real.log (harperBlockEndpoint
                  (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
            ∀ lower upper : Fin n → ℝ,
              (Measure.pi (fun i : Fin n ↦
                harperCenteredLinearBlockLaw y
                  (harperScheduledPrimeBlock y
                    (start + (i : ℕ))) t (u i))).real
                  (harperPartialSumBarrierSet lower upper ∩
                    harperCoordinateBox
                      (harperScheduledModerateRadius start n)) ≤
                Real.exp 2 *
                  (Measure.pi (fun i : Fin n ↦
                    harperGaussianBlockLaw y
                      (harperScheduledPrimeBlock y
                        (start + (i : ℕ))) t (u i))).real
                    (harperExpandedPartialSumBarrierSet lower upper
                      (harperScheduledRelativeCellWidth start n)) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledOffDiagonalModerateCoordinateCell_le_exp_two_mul_gaussian M
  refine ⟨J, ?_⟩
  intro start hstart n y hy t htLower htUpper u hscale lower upper
  apply measureReal_inter_barrier_box_le_expandedBarrier
    (P := Measure.pi (fun i : Fin n ↦
      harperCenteredLinearBlockLaw y
        (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)))
    (Q := Measure.pi (fun i : Fin n ↦
      harperGaussianBlockLaw y
        (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)))
    (C := Real.exp 2) (by positivity)
    (delta := harperScheduledRelativeCellWidth start n)
    (R := harperScheduledModerateRadius start n)
    (lower := lower) (upper := upper)
    (harperScheduledRelativeCellWidth_pos start n)
  intro z hz
  have hmoderate : ∀ i : Fin n,
      |(z i : ℝ) *
          harperScheduledRelativeIntervalWidth (start + (i : ℕ))| + 1 ≤
        (1 / 4 : ℝ) *
          Real.sqrt (((2 ^ (start + (i : ℕ)) : ℕ) : ℝ)) := by
    intro i
    simpa only [harperScheduledRelativeCellWidth,
      harperScheduledModerateThreshold] using!
        abs_scheduledLatticeCell_lowerCorner_add_one_le_of_mem_activeSlice
          hz i
  simpa only [harperScheduledRelativeCellWidth] using!
    hJ start hstart n y hy t htLower htUpper u hscale z hmoderate

end Problem520
end Erdos
