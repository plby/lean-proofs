import ErdosProblems.Erdos520.HarperFejerSmoothing
import ErdosProblems.Erdos520.HarperPrimeBlockAsymptotic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set

namespace Erdos
namespace Problem520

/-!
# A summable scheduled one-block Gaussian replacement rate

Choosing the Fejér frequency `T = 2^j` is far below the square root of the
doubly-exponential lower endpoint of block `j`.  The characteristic-function
error and Gaussian smoothing loss are then both bounded by a geometric
multiple of `2^(-j)`.  This is the form needed for long product paths.
-/

noncomputable def harperScheduledComparisonFrequency (j : ℕ) : ℝ :=
  (2 : ℝ) ^ j

theorem nat_le_two_pow (j : ℕ) : j ≤ 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      omega

theorem harperScheduledComparisonFrequency_pow_five_le_sqrt_endpoint
    (j : ℕ) :
    harperScheduledComparisonFrequency j ^ 5 ≤
      Real.sqrt (harperBlockEndpoint j : ℝ) := by
  have hj : j ≤ 2 ^ j := nat_le_two_pow j
  have hexp : 10 * j ≤ 16 * 2 ^ j := by omega
  have hnat : 2 ^ (10 * j) ≤ 2 ^ (16 * 2 ^ j) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have hreal : ((2 ^ (10 * j) : ℕ) : ℝ) ≤
      ((2 ^ (16 * 2 ^ j) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hsq : (harperScheduledComparisonFrequency j ^ 5) ^ 2 ≤
      (harperBlockEndpoint j : ℝ) := by
    have hexp' : j * 5 * 2 = 10 * j := by omega
    simpa only [harperScheduledComparisonFrequency, harperBlockEndpoint,
      Nat.cast_pow,
      Nat.cast_ofNat, ← pow_mul, hexp'] using! hreal
  exact Real.le_sqrt_of_sq_le hsq

theorem harperScheduledComparisonFrequency_pos (j : ℕ) :
    0 < harperScheduledComparisonFrequency j := by
  unfold harperScheduledComparisonFrequency
  positivity

theorem one_le_harperScheduledComparisonFrequency (j : ℕ) :
    1 ≤ harperScheduledComparisonFrequency j := by
  unfold harperScheduledComparisonFrequency
  exact one_le_pow₀ (by norm_num)

theorem harperScheduledComparisonFrequency_condition
    {j : ℕ} (hj : 1 ≤ j) :
    2 * harperScheduledComparisonFrequency j ≤
      Real.sqrt (harperBlockEndpoint j : ℝ) := by
  have htwo : 2 ≤ harperScheduledComparisonFrequency j := by
    unfold harperScheduledComparisonFrequency
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 0 < 2) hj)
  have hone := one_le_harperScheduledComparisonFrequency j
  have h2le5 : 2 * harperScheduledComparisonFrequency j ≤
      harperScheduledComparisonFrequency j ^ 5 := by
    calc
      2 * harperScheduledComparisonFrequency j ≤
          harperScheduledComparisonFrequency j *
            harperScheduledComparisonFrequency j := by
        exact mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = harperScheduledComparisonFrequency j ^ 2 := by ring
      _ ≤ harperScheduledComparisonFrequency j ^ 5 := by
        exact pow_le_pow_right₀ hone (by norm_num)
  exact h2le5.trans
    (harperScheduledComparisonFrequency_pow_five_le_sqrt_endpoint j)

theorem harperScheduledComparisonFrequency_kernel_budget (j : ℕ) :
    (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
        (32 * harperScheduledComparisonFrequency j ^ 3 +
          harperScheduledComparisonFrequency j ^ 4) ≤
      33 / harperScheduledComparisonFrequency j := by
  let T := harperScheduledComparisonFrequency j
  let S := Real.sqrt (harperBlockEndpoint j : ℝ)
  have hT : 0 < T := harperScheduledComparisonFrequency_pos j
  have hT1 : 1 ≤ T := one_le_harperScheduledComparisonFrequency j
  have hSbound : T ^ 5 ≤ S :=
    harperScheduledComparisonFrequency_pow_five_le_sqrt_endpoint j
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

theorem inv_sqrt_le_two_of_one_third_lt {v : ℝ} (hv : (1 / 3 : ℝ) < v) :
    (Real.sqrt v)⁻¹ ≤ 2 := by
  have hquarter : (1 / 2 : ℝ) ^ 2 ≤ v := by nlinarith
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt v :=
    (Real.le_sqrt' (by norm_num)).2 hquarter
  have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hsqrt
  norm_num at hinv ⊢
  exact hinv

theorem fejer_coefficient_le_one : (2 * Real.pi)⁻¹ ≤ (1 : ℝ) := by
  apply inv_le_one_of_one_le₀
  nlinarith [Real.pi_gt_three]

theorem exists_eventually_harperScheduledDiagonalCDFDistance_le_geometric
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          HarperFejerSmoothedCDFIdentity
            (harperCenteredLinearBlockLaw y
              (harperScheduledPrimeBlock y j) t t)
            (harperGaussianBlockLaw y
              (harperScheduledPrimeBlock y j) t t)
            (harperScheduledComparisonFrequency j) →
          harperCDFDistance
            (harperCenteredLinearBlockLaw y
              (harperScheduledPrimeBlock y j) t t)
            (harperGaussianBlockLaw y
              (harperScheduledPrimeBlock y j) t t) ≤
            130 / harperScheduledComparisonFrequency j := by
  obtain ⟨J0, hJ0⟩ :=
    exists_eventually_harperScheduledDiagonalVariance_third_threeEighths M
  refine ⟨max J0 1, ?_⟩
  intro j hj y hy t htLower htUpper hidentity
  have hj0 : J0 ≤ j := (le_max_left J0 1).trans hj
  have hj1 : 1 ≤ j := (le_max_right J0 1).trans hj
  have hv := (hJ0 j hj0 y hy t htLower htUpper).1
  let V : ℝ := harperLinearBlockVariance y
    (harperScheduledPrimeBlock y j) t t
  let T : ℝ := harperScheduledComparisonFrequency j
  have hV : (1 / 3 : ℝ) < V := hv
  have hVnn : harperLinearBlockVarianceNNReal y
      (harperScheduledPrimeBlock y j) t t ≠ 0 := by
    intro hzero
    have hcoezero : V = 0 := by
      simpa only [V, coe_harperLinearBlockVarianceNNReal] using!
        congrArg ((↑·) : NNReal → ℝ) hzero
    linarith
  have hT : 0 < T := harperScheduledComparisonFrequency_pos j
  have hfrequency : 2 * T ≤ Real.sqrt (harperBlockEndpoint j : ℝ) :=
    harperScheduledComparisonFrequency_condition hj1
  have hbase := harperCDFDistance_scheduledBlock_le_of_fejer_identity
    y j t t T hT hfrequency hVnn (by simpa only [T] using! hidentity)
  have hkernel :
      (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
          (32 * T ^ 3 + T ^ 4) ≤ 33 / T := by
    simpa only [T] using!
      harperScheduledComparisonFrequency_kernel_budget j
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
    _ = 130 / harperScheduledComparisonFrequency j := rfl

/-- The geometric one-block comparison errors stay bounded independently of
the number of consecutive blocks. -/
theorem sum_harperScheduledComparisonBudget_le
    (start n : ℕ) :
    (∑ k ∈ Finset.range n,
        130 / harperScheduledComparisonFrequency (start + k)) ≤
      260 / harperScheduledComparisonFrequency start := by
  have hpoint (k : ℕ) :
      130 / harperScheduledComparisonFrequency (start + k) =
        (130 / harperScheduledComparisonFrequency start) *
          (1 / (2 : ℝ)) ^ k := by
    unfold harperScheduledComparisonFrequency
    simp only [pow_add, div_eq_mul_inv, mul_inv_rev]
    simp only [one_mul, ← inv_pow]
    ring
  simp_rw [hpoint]
  rw [← Finset.mul_sum]
  have hfactor :
      0 ≤ 130 / harperScheduledComparisonFrequency start := by
    exact div_nonneg (by norm_num)
      (harperScheduledComparisonFrequency_pos start).le
  calc
    (130 / harperScheduledComparisonFrequency start) *
        (∑ k ∈ Finset.range n, (1 / (2 : ℝ)) ^ k) ≤
      (130 / harperScheduledComparisonFrequency start) * 2 := by
        gcongr
        exact sum_geometric_two_le n
    _ = 260 / harperScheduledComparisonFrequency start := by ring

/-- The total interval-probability replacement budget for any consecutive
path is geometric in its first block and independent of its length. -/
theorem exists_eventually_sum_harperScheduledDiagonalCDFDistance_le
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
              (harperScheduledComparisonFrequency (start + k))) →
          (∑ k ∈ Finset.range n,
            2 * harperCDFDistance
              (harperCenteredLinearBlockLaw y
                (harperScheduledPrimeBlock y (start + k)) t t)
              (harperGaussianBlockLaw y
                (harperScheduledPrimeBlock y (start + k)) t t)) ≤
            520 / harperScheduledComparisonFrequency start := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledDiagonalCDFDistance_le_geometric M
  refine ⟨J, ?_⟩
  intro start hstart n y hy t htLower htUpper hidentity
  have hpoint : ∀ k ∈ Finset.range n,
      2 * harperCDFDistance
          (harperCenteredLinearBlockLaw y
            (harperScheduledPrimeBlock y (start + k)) t t)
          (harperGaussianBlockLaw y
            (harperScheduledPrimeBlock y (start + k)) t t) ≤
        2 * (130 /
          harperScheduledComparisonFrequency (start + k)) := by
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
          harperScheduledComparisonFrequency (start + k)) := by
            exact Finset.sum_le_sum hpoint
    _ = 2 * (∑ k ∈ Finset.range n,
        130 / harperScheduledComparisonFrequency (start + k)) := by
          rw [Finset.mul_sum]
    _ ≤ 2 * (260 / harperScheduledComparisonFrequency start) := by
          gcongr
          exact sum_harperScheduledComparisonBudget_le start n
    _ = 520 / harperScheduledComparisonFrequency start := by ring

end Problem520
end Erdos
