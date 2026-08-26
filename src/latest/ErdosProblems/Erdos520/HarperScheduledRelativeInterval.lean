import ErdosProblems.Erdos520.HarperScheduledUnconditional

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace Erdos
namespace Problem520

/-!
# Unconditional relative interval comparison on moderate cells

The strong scheduled Fourier cutoff is doubly exponential in the block
index.  Consequently its CDF replacement error is eventually much smaller
than the Gaussian mass of an interval of width `(j + 1)\u207b\u00b2`, uniformly on
a growing moderate range.
-/

/-- The polynomial cell width used for the relative interval comparison. -/
noncomputable def harperScheduledRelativeIntervalWidth (j : ℕ) : ℝ :=
  (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹

theorem harperScheduledRelativeIntervalWidth_pos (j : ℕ) :
    0 < harperScheduledRelativeIntervalWidth j := by
  unfold harperScheduledRelativeIntervalWidth
  positivity

theorem harperScheduledRelativeIntervalWidth_le_one (j : ℕ) :
    harperScheduledRelativeIntervalWidth j ≤ 1 := by
  unfold harperScheduledRelativeIntervalWidth
  rw [inv_le_one₀]
  · norm_cast
    exact one_le_pow₀ (by omega : 1 ≤ j + 1)
  · positivity

/-- A fixed polynomial is eventually dominated by an exponential with
rate `1/4`. -/
private theorem eventually_const_mul_pow_le_exp_quarter_nat
    (A : ℝ) (d : ℕ) :
    ∀ᶠ j : ℕ in atTop,
      A * (j : ℝ) ^ d ≤ Real.exp ((j : ℝ) / 4) := by
  have ht : Tendsto
      (fun x : ℝ ↦ Real.exp ((1 / 4 : ℝ) * x) / x ^ (d : ℝ))
      atTop atTop :=
    tendsto_exp_mul_div_rpow_atTop (d : ℝ) (1 / 4 : ℝ) (by norm_num)
  have htNat := ht.comp tendsto_natCast_atTop_atTop
  filter_upwards [htNat.eventually (eventually_ge_atTop A),
      eventually_ge_atTop (1 : ℕ)] with j hj hjOne
  have hjPos : (0 : ℝ) < j := by positivity
  have hden : 0 < (j : ℝ) ^ d := by positivity
  change A ≤ Real.exp ((1 / 4 : ℝ) * (j : ℝ)) /
    (j : ℝ) ^ (d : ℝ) at hj
  rw [Real.rpow_natCast] at hj
  rw [le_div_iff₀ hden] at hj
  calc
    A * (j : ℝ) ^ d ≤ Real.exp ((1 / 4 : ℝ) * (j : ℝ)) := hj
    _ = Real.exp ((j : ℝ) / 4) := by
      congr 1
      ring

/-- On the moderate range
`|a| + 1 ≤ (1/4) sqrt(2^j)`, the total interval-probability replacement
budget is eventually no larger than the elementary Gaussian mass lower
bound for a cell of width `(j+1)\u207b\u00b2`. -/
theorem eventually_harperScheduledStrongBudget_le_relativeGaussianMass :
    ∀ᶠ j : ℕ in atTop, ∀ a : ℝ,
      |a| + 1 ≤ (1 / 4 : ℝ) * Real.sqrt (((2 ^ j : ℕ) : ℝ)) →
        260 / harperScheduledStrongComparisonFrequency j ≤
          (harperScheduledRelativeIntervalWidth j / 2) *
            Real.exp (-2 * (|a| + 1) ^ 2) := by
  have hpoly := eventually_const_mul_pow_le_exp_quarter_nat (2080 : ℝ) 2
  filter_upwards [hpoly, eventually_ge_atTop (1 : ℕ)] with j hpolyJ hjOne
  intro a ha
  let n : ℝ := ((2 ^ j : ℕ) : ℝ)
  let D : ℝ := (((j + 1 : ℕ) : ℝ) ^ 2)
  let q : ℝ := 2 * (|a| + 1) ^ 2
  let T : ℝ := harperScheduledStrongComparisonFrequency j
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hnPos : 0 < n := by dsimp [n]; positivity
  have hDPos : 0 < D := by dsimp [D]; positivity
  have hTPos : 0 < T := by
    dsimp [T]
    exact harperScheduledStrongComparisonFrequency_pos j
  have hjCast : ((j : ℝ) + 1) ≤ 2 * (j : ℝ) := by
    exact_mod_cast (show j + 1 ≤ 2 * j by omega)
  have hpoly' : 520 * D ≤ Real.exp ((j : ℝ) / 4) := by
    calc
      520 * D = 520 * (((j : ℝ) + 1) ^ 2) := by
        dsimp [D]
        push_cast
        rfl
      _ ≤ 520 * (2 * (j : ℝ)) ^ 2 := by gcongr
      _ = 2080 * (j : ℝ) ^ 2 := by ring
      _ ≤ Real.exp ((j : ℝ) / 4) := hpolyJ
  have hjnNat : j ≤ 2 ^ j := (Nat.lt_two_pow_self (n := j)).le
  have hjn : (j : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast hjnNat
  have hpolyN : 520 * D ≤ Real.exp (n / 4) := by
    exact hpoly'.trans (Real.exp_le_exp.mpr (by linarith))
  have hsqrtSq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
  have haNonneg : 0 ≤ |a| + 1 := by positivity
  have hrightNonneg : 0 ≤ (1 / 4 : ℝ) * Real.sqrt n := by positivity
  have haSq : (|a| + 1) ^ 2 ≤
      ((1 / 4 : ℝ) * Real.sqrt n) ^ 2 :=
    (sq_le_sq₀ haNonneg hrightNonneg).2 (by simpa only [n] using! ha)
  have hq : q ≤ n / 8 := by
    dsimp [q]
    nlinarith
  have hexpQ : Real.exp q ≤ Real.exp (n / 8) :=
    Real.exp_le_exp.mpr hq
  have hlog : (3 / 8 : ℝ) ≤ Real.log 2 := by
    exact le_of_lt ((by norm_num : (3 / 8 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9)
  have hTexp : Real.exp (Real.log 2 * n) = T := by
    dsimp [n, T, harperScheduledStrongComparisonFrequency]
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hcross : 520 * D * Real.exp q ≤ T := by
    calc
      520 * D * Real.exp q ≤ Real.exp (n / 4) * Real.exp q := by
        gcongr
      _ ≤ Real.exp (n / 4) * Real.exp (n / 8) := by
        gcongr
      _ = Real.exp ((3 / 8 : ℝ) * n) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (Real.log 2 * n) := by
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlog hn0)
      _ = T := hTexp
  have hdenPos : 0 < 2 * D * Real.exp q := by positivity
  have hdiv : 260 / T ≤ 1 / (2 * D * Real.exp q) := by
    apply (div_le_div_iff₀ hTPos hdenPos).2
    convert! hcross using 1 <;> ring
  calc
    260 / harperScheduledStrongComparisonFrequency j = 260 / T := rfl
    _ ≤ 1 / (2 * D * Real.exp q) := hdiv
    _ = (harperScheduledRelativeIntervalWidth j / 2) *
        Real.exp (-2 * (|a| + 1) ^ 2) := by
      dsimp only [harperScheduledRelativeIntervalWidth, D, q]
      rw [show -2 * (|a| + 1) ^ 2 = -(2 * (|a| + 1) ^ 2) by ring,
        Real.exp_neg]
      field_simp [Real.exp_ne_zero]

/-- Unconditional relative interval comparison for late scheduled blocks.
The cell width is `(j+1)\u207b\u00b2`, and the moderate range grows like
`sqrt(2^j)` (hence like `sqrt(log harperBlockEndpoint j)`). -/
theorem exists_eventually_harperScheduledRelativeIntervalProbability_le_two_mul_gaussian
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          ∀ a : ℝ,
            |a| + 1 ≤ (1 / 4 : ℝ) *
              Real.sqrt (((2 ^ j : ℕ) : ℝ)) →
            (harperCenteredLinearBlockLaw y
              (harperScheduledPrimeBlock y j) t t).real
                (Ioc a (a + harperScheduledRelativeIntervalWidth j)) ≤
              2 * (harperGaussianBlockLaw y
                (harperScheduledPrimeBlock y j) t t).real
                  (Ioc a (a + harperScheduledRelativeIntervalWidth j)) := by
  obtain ⟨Jrel, hJrel⟩ :=
    exists_eventually_harperScheduledIntervalProbability_le_two_mul_gaussian M
  obtain ⟨Jbudget, hJbudget⟩ :=
    eventually_atTop.1 eventually_harperScheduledStrongBudget_le_relativeGaussianMass
  refine ⟨max Jrel Jbudget, ?_⟩
  intro j hj y hy t htLower htUpper a ha
  have hjRel : Jrel ≤ j := (le_max_left Jrel Jbudget).trans hj
  have hjBudget : Jbudget ≤ j := (le_max_right Jrel Jbudget).trans hj
  exact hJrel j hjRel y hy t htLower htUpper
    (harperScheduledStrongFejerSmoothedCDFIdentity y j t t)
    a (harperScheduledRelativeIntervalWidth j)
    (harperScheduledRelativeIntervalWidth_pos j)
    (harperScheduledRelativeIntervalWidth_le_one j)
    (hJbudget j hjBudget a ha)

end Problem520
end Erdos
