import ErdosProblems.Erdos520.HarperScheduledCDF

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Doubly-exponential scheduled Gaussian replacement

The stronger frequency `T_j = 2^(2^j)` is still far below the admissible
Fourier range of block `j`.  It yields a one-block CDF error of order
`2^(-2^j)`, leaving ample room for later finite path discretizations.
-/

noncomputable def harperScheduledStrongComparisonFrequency (j : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 ^ j)

theorem harperScheduledStrongComparisonFrequency_pos (j : ℕ) :
    0 < harperScheduledStrongComparisonFrequency j := by
  unfold harperScheduledStrongComparisonFrequency
  positivity

theorem two_le_harperScheduledStrongComparisonFrequency (j : ℕ) :
    2 ≤ harperScheduledStrongComparisonFrequency j := by
  unfold harperScheduledStrongComparisonFrequency
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2)
    Nat.one_le_two_pow

theorem harperScheduledStrongComparisonFrequency_pow_five_le_sqrt_endpoint
    (j : ℕ) :
    harperScheduledStrongComparisonFrequency j ^ 5 ≤
      Real.sqrt (harperBlockEndpoint j : ℝ) := by
  have hexp : 10 * 2 ^ j ≤ 16 * 2 ^ j := by omega
  have hnat : 2 ^ (10 * 2 ^ j) ≤ 2 ^ (16 * 2 ^ j) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have hreal : ((2 ^ (10 * 2 ^ j) : ℕ) : ℝ) ≤
      ((2 ^ (16 * 2 ^ j) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hsq : (harperScheduledStrongComparisonFrequency j ^ 5) ^ 2 ≤
      (harperBlockEndpoint j : ℝ) := by
    have hexp' : 2 ^ j * 5 * 2 = 10 * 2 ^ j := by omega
    simpa only [harperScheduledStrongComparisonFrequency,
      harperBlockEndpoint, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul,
      hexp'] using! hreal
  exact Real.le_sqrt_of_sq_le hsq

theorem harperScheduledStrongComparisonFrequency_condition (j : ℕ) :
    2 * harperScheduledStrongComparisonFrequency j ≤
      Real.sqrt (harperBlockEndpoint j : ℝ) := by
  let T := harperScheduledStrongComparisonFrequency j
  have htwo : 2 ≤ T :=
    two_le_harperScheduledStrongComparisonFrequency j
  have hone : 1 ≤ T := htwo.trans' (by norm_num)
  have h2le5 : 2 * T ≤ T ^ 5 := by
    calc
      2 * T ≤ T * T := mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = T ^ 2 := by ring
      _ ≤ T ^ 5 := pow_le_pow_right₀ hone (by norm_num)
  exact h2le5.trans
    (harperScheduledStrongComparisonFrequency_pow_five_le_sqrt_endpoint j)

theorem harperScheduledStrongComparisonFrequency_kernel_budget (j : ℕ) :
    (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
        (32 * harperScheduledStrongComparisonFrequency j ^ 3 +
          harperScheduledStrongComparisonFrequency j ^ 4) ≤
      33 / harperScheduledStrongComparisonFrequency j := by
  let T := harperScheduledStrongComparisonFrequency j
  let S := Real.sqrt (harperBlockEndpoint j : ℝ)
  have hT : 0 < T := harperScheduledStrongComparisonFrequency_pos j
  have hT1 : 1 ≤ T :=
    (two_le_harperScheduledStrongComparisonFrequency j).trans'
      (by norm_num)
  have hSbound : T ^ 5 ≤ S :=
    harperScheduledStrongComparisonFrequency_pow_five_le_sqrt_endpoint j
  have hS : 0 < S := (pow_pos hT 5).trans_le hSbound
  have h45 : T ^ 4 ≤ T ^ 5 := pow_le_pow_right₀ hT1 (by norm_num)
  have hnum : (32 * T ^ 3 + T ^ 4) * T ≤ 33 * S := by
    calc
      (32 * T ^ 3 + T ^ 4) * T = 32 * T ^ 4 + T ^ 5 := by ring
      _ ≤ 32 * T ^ 5 + T ^ 5 := by gcongr
      _ = 33 * T ^ 5 := by ring
      _ ≤ 33 * S := by gcongr
  change S⁻¹ * (32 * T ^ 3 + T ^ 4) ≤ 33 / T
  rw [show S⁻¹ * (32 * T ^ 3 + T ^ 4) =
      (32 * T ^ 3 + T ^ 4) / S by ring]
  exact (div_le_div_iff₀ hS hT).2 hnum

/-- Late diagonal scheduled blocks have a doubly-exponentially small
Kolmogorov replacement error, conditional only on the exact inversion
identity (which is discharged in the inversion module). -/
theorem exists_eventually_harperScheduledDiagonalCDFDistance_le_strong
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          HarperFejerSmoothedCDFIdentity
            (harperCenteredLinearBlockLaw y
              (harperScheduledPrimeBlock y j) t t)
            (harperGaussianBlockLaw y
              (harperScheduledPrimeBlock y j) t t)
            (harperScheduledStrongComparisonFrequency j) →
          harperCDFDistance
            (harperCenteredLinearBlockLaw y
              (harperScheduledPrimeBlock y j) t t)
            (harperGaussianBlockLaw y
              (harperScheduledPrimeBlock y j) t t) ≤
            130 / harperScheduledStrongComparisonFrequency j := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledDiagonalVariance_third_threeEighths M
  refine ⟨J, ?_⟩
  intro j hj y hy t htLower htUpper hidentity
  have hv := (hJ j hj y hy t htLower htUpper).1
  let V : ℝ := harperLinearBlockVariance y
    (harperScheduledPrimeBlock y j) t t
  let T : ℝ := harperScheduledStrongComparisonFrequency j
  have hV : (1 / 3 : ℝ) < V := hv
  have hVnn : harperLinearBlockVarianceNNReal y
      (harperScheduledPrimeBlock y j) t t ≠ 0 := by
    intro hzero
    have hcoezero : V = 0 := by
      simpa only [V, coe_harperLinearBlockVarianceNNReal] using!
        congrArg ((↑·) : NNReal → ℝ) hzero
    linarith
  have hT : 0 < T := harperScheduledStrongComparisonFrequency_pos j
  have hfrequency : 2 * T ≤ Real.sqrt (harperBlockEndpoint j : ℝ) :=
    harperScheduledStrongComparisonFrequency_condition j
  have hbase := harperCDFDistance_scheduledBlock_le_of_fejer_identity
    y j t t T hT hfrequency hVnn (by simpa only [T] using! hidentity)
  have hkernel :
      (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
          (32 * T ^ 3 + T ^ 4) ≤ 33 / T := by
    simpa only [T] using!
      harperScheduledStrongComparisonFrequency_kernel_budget j
  have hcoef : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
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
    inv_sqrt_le_two_of_one_third_lt hV
  have hvariance : 16 * (Real.sqrt V)⁻¹ / T ≤ 32 / T := by
    rw [div_le_div_iff_of_pos_right hT]
    nlinarith
  calc
    harperCDFDistance
          (harperCenteredLinearBlockLaw y
            (harperScheduledPrimeBlock y j) t t)
          (harperGaussianBlockLaw y
            (harperScheduledPrimeBlock y j) t t) ≤
        2 * ((2 * Real.pi)⁻¹ *
            (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
              (32 * T ^ 3 + T ^ 4) +
          16 * (Real.sqrt V)⁻¹ / T) := by
      simpa only [T, V, coe_harperLinearBlockVarianceNNReal] using! hbase
    _ ≤ 2 * (33 / T + 32 / T) := by gcongr
    _ = 130 / T := by ring
    _ = 130 / harperScheduledStrongComparisonFrequency j := rfl

theorem harperScheduledStrongComparisonFrequency_succ (j : ℕ) :
    harperScheduledStrongComparisonFrequency (j + 1) =
      harperScheduledStrongComparisonFrequency j ^ 2 := by
  unfold harperScheduledStrongComparisonFrequency
  rw [pow_succ, pow_mul]

theorem inv_harperScheduledStrongComparisonFrequency_succ_le
    (j : ℕ) :
    1 / harperScheduledStrongComparisonFrequency (j + 1) ≤
      (1 / 2 : ℝ) *
        (1 / harperScheduledStrongComparisonFrequency j) := by
  let T := harperScheduledStrongComparisonFrequency j
  have hT : 0 < T := harperScheduledStrongComparisonFrequency_pos j
  have htwo : 2 ≤ T :=
    two_le_harperScheduledStrongComparisonFrequency j
  have htwoT : 2 * T ≤ T ^ 2 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right htwo hT.le
  rw [harperScheduledStrongComparisonFrequency_succ]
  change 1 / T ^ 2 ≤ (1 / 2 : ℝ) * (1 / T)
  have hdenom : 0 < 2 * T := mul_pos (by norm_num) hT
  calc
    1 / T ^ 2 ≤ 1 / (2 * T) := by
      exact one_div_le_one_div_of_le hdenom htwoT
    _ = (1 / 2 : ℝ) * (1 / T) := by field_simp

theorem inv_harperScheduledStrongComparisonFrequency_add_le
    (start k : ℕ) :
    1 / harperScheduledStrongComparisonFrequency (start + k) ≤
      (1 / harperScheduledStrongComparisonFrequency start) *
        (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep :=
        inv_harperScheduledStrongComparisonFrequency_succ_le (start + k)
      rw [show start + (k + 1) = (start + k) + 1 by omega]
      calc
        1 / harperScheduledStrongComparisonFrequency (start + k + 1) ≤
            (1 / 2 : ℝ) *
              (1 / harperScheduledStrongComparisonFrequency (start + k)) :=
          hstep
        _ ≤ (1 / 2 : ℝ) *
              ((1 / harperScheduledStrongComparisonFrequency start) *
                (1 / 2 : ℝ) ^ k) := by gcongr
        _ = (1 / harperScheduledStrongComparisonFrequency start) *
              (1 / 2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

theorem sum_harperScheduledStrongComparisonBudget_le
    (start n : ℕ) :
    (∑ k ∈ Finset.range n,
        130 / harperScheduledStrongComparisonFrequency (start + k)) ≤
      260 / harperScheduledStrongComparisonFrequency start := by
  have hpoint : ∀ k ∈ Finset.range n,
      130 / harperScheduledStrongComparisonFrequency (start + k) ≤
        (130 / harperScheduledStrongComparisonFrequency start) *
          (1 / 2 : ℝ) ^ k := by
    intro k hk
    have h := inv_harperScheduledStrongComparisonFrequency_add_le start k
    simpa only [div_eq_mul_inv, one_mul, mul_assoc] using!
      mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 130)
  calc
    (∑ k ∈ Finset.range n,
        130 / harperScheduledStrongComparisonFrequency (start + k)) ≤
      ∑ k ∈ Finset.range n,
        (130 / harperScheduledStrongComparisonFrequency start) *
          (1 / 2 : ℝ) ^ k := Finset.sum_le_sum hpoint
    _ = (130 / harperScheduledStrongComparisonFrequency start) *
        (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k) := by
          rw [Finset.mul_sum]
    _ ≤ (130 / harperScheduledStrongComparisonFrequency start) * 2 := by
      exact mul_le_mul_of_nonneg_left (sum_geometric_two_le n)
        (div_nonneg (by norm_num)
          (harperScheduledStrongComparisonFrequency_pos start).le)
    _ = 260 / harperScheduledStrongComparisonFrequency start := by ring

theorem exists_eventually_sum_harperScheduledDiagonalCDFDistance_le_strong
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          (∀ k ∈ Finset.range n,
            HarperFejerSmoothedCDFIdentity
              (harperCenteredLinearBlockLaw y
                (harperScheduledPrimeBlock y (start + k)) t t)
              (harperGaussianBlockLaw y
                (harperScheduledPrimeBlock y (start + k)) t t)
              (harperScheduledStrongComparisonFrequency (start + k))) →
          (∑ k ∈ Finset.range n,
            2 * harperCDFDistance
              (harperCenteredLinearBlockLaw y
                (harperScheduledPrimeBlock y (start + k)) t t)
              (harperGaussianBlockLaw y
                (harperScheduledPrimeBlock y (start + k)) t t)) ≤
            520 / harperScheduledStrongComparisonFrequency start := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledDiagonalCDFDistance_le_strong M
  refine ⟨J, ?_⟩
  intro start hstart n y hy t htLower htUpper hidentity
  have hpoint : ∀ k ∈ Finset.range n,
      2 * harperCDFDistance
          (harperCenteredLinearBlockLaw y
            (harperScheduledPrimeBlock y (start + k)) t t)
          (harperGaussianBlockLaw y
            (harperScheduledPrimeBlock y (start + k)) t t) ≤
        2 * (130 /
          harperScheduledStrongComparisonFrequency (start + k)) := by
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    have hindex : J ≤ start + k := hstart.trans (Nat.le_add_right start k)
    have hendpoint :
        harperBlockEndpoint (start + k + 1) ≤ y := by
      exact (monotone_harperBlockEndpoint (by omega)).trans hy
    gcongr
    exact hJ (start + k) hindex y hendpoint t htLower htUpper
      (hidentity k hk)
  calc
    (∑ k ∈ Finset.range n,
        2 * harperCDFDistance
          (harperCenteredLinearBlockLaw y
            (harperScheduledPrimeBlock y (start + k)) t t)
          (harperGaussianBlockLaw y
            (harperScheduledPrimeBlock y (start + k)) t t)) ≤
      ∑ k ∈ Finset.range n,
        2 * (130 /
          harperScheduledStrongComparisonFrequency (start + k)) := by
            exact Finset.sum_le_sum hpoint
    _ = 2 * (∑ k ∈ Finset.range n,
        130 / harperScheduledStrongComparisonFrequency (start + k)) := by
          rw [Finset.mul_sum]
    _ ≤ 2 * (260 /
        harperScheduledStrongComparisonFrequency start) := by
          gcongr
          exact sum_harperScheduledStrongComparisonBudget_le start n
    _ = 520 / harperScheduledStrongComparisonFrequency start := by ring

/-- On a moderate interval whose Gaussian mass lower bound dominates the
strong Berry--Esseen error, the exact scheduled block probability is at most
twice its Gaussian counterpart. -/
theorem exists_eventually_harperScheduledIntervalProbability_le_two_mul_gaussian
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          HarperFejerSmoothedCDFIdentity
            (harperCenteredLinearBlockLaw y
              (harperScheduledPrimeBlock y j) t t)
            (harperGaussianBlockLaw y
              (harperScheduledPrimeBlock y j) t t)
            (harperScheduledStrongComparisonFrequency j) →
          ∀ a delta : ℝ, 0 < delta → delta ≤ 1 →
            260 / harperScheduledStrongComparisonFrequency j ≤
              (delta / 2) * Real.exp (-2 * (|a| + 1) ^ 2) →
            (harperCenteredLinearBlockLaw y
              (harperScheduledPrimeBlock y j) t t).real
                (Ioc a (a + delta)) ≤
              2 * (harperGaussianBlockLaw y
                (harperScheduledPrimeBlock y j) t t).real
                  (Ioc a (a + delta)) := by
  obtain ⟨Jcdf, hJcdf⟩ :=
    exists_eventually_harperScheduledDiagonalCDFDistance_le_strong M
  obtain ⟨Jvar, hJvar⟩ :=
    exists_eventually_harperScheduledDiagonalVariance_third_threeEighths M
  refine ⟨max Jcdf Jvar, ?_⟩
  intro j hj y hy t htLower htUpper hidentity a delta
    hdelta0 hdelta1 hbudget
  have hjcdf : Jcdf ≤ j := (le_max_left Jcdf Jvar).trans hj
  have hjvar : Jvar ≤ j := (le_max_right Jcdf Jvar).trans hj
  let rho := harperCenteredLinearBlockLaw y
    (harperScheduledPrimeBlock y j) t t
  let nu := harperGaussianBlockLaw y
    (harperScheduledPrimeBlock y j) t t
  have hdist : harperCDFDistance rho nu ≤
      130 / harperScheduledStrongComparisonFrequency j := by
    exact hJcdf j hjcdf y hy t htLower htUpper hidentity
  have habs : |rho.real (Ioc a (a + delta)) -
      nu.real (Ioc a (a + delta))| ≤
        2 * harperCDFDistance rho nu :=
    abs_measureReal_Ioc_sub_le_two_mul_cdfDistance rho nu
      (by linarith : a ≤ a + delta)
  have hvar := hJvar j hjvar y hy t htLower htUpper
  have hgaussian :
      (delta / 2) * Real.exp (-2 * (|a| + 1) ^ 2) ≤
        nu.real (Ioc a (a + delta)) := by
    dsimp only [nu, harperGaussianBlockLaw]
    exact gaussianReal_real_Ioc_ge_of_variance_mem
      (v := harperLinearBlockVarianceNNReal y
        (harperScheduledPrimeBlock y j) t t)
      (by simpa only [coe_harperLinearBlockVarianceNNReal] using! hvar.1.le)
      (by simpa only [coe_harperLinearBlockVarianceNNReal] using! hvar.2.le)
      hdelta0 hdelta1
  have herr : rho.real (Ioc a (a + delta)) -
      nu.real (Ioc a (a + delta)) ≤
        nu.real (Ioc a (a + delta)) := by
    calc
      rho.real (Ioc a (a + delta)) -
          nu.real (Ioc a (a + delta)) ≤
        |rho.real (Ioc a (a + delta)) -
          nu.real (Ioc a (a + delta))| := le_abs_self _
      _ ≤ 2 * harperCDFDistance rho nu := habs
      _ ≤ 2 * (130 /
          harperScheduledStrongComparisonFrequency j) := by gcongr
      _ = 260 / harperScheduledStrongComparisonFrequency j := by ring
      _ ≤ (delta / 2) * Real.exp (-2 * (|a| + 1) ^ 2) := hbudget
      _ ≤ nu.real (Ioc a (a + delta)) := hgaussian
  linarith

end Problem520
end Erdos
