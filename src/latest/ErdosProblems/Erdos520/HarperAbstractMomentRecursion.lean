import ErdosProblems.Erdos520.HarperOmegaGoodEvent
import ErdosProblems.Erdos520.HarperWeightedRecursion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# Abstract good--bad iteration for an Euler-set energy

This is the assembly layer between exponent-dependent prefix good events and
`HarperWeightedRecursion`.  It applies to any nonnegative integrable random
variable on a probability space, so the same theorem can be used for a
translated unit interval, a dyadic band, or a normalized sum of bands.

At step `m` the caller supplies:

* a measurable good event with restricted `q_m` moment at most `A * W_m`;
* a bad-event probability bounded first by an explicit prefix budget and
  then by `Kbad * exp (-2*C/(1-q_m))`;
* one terminal first-moment bound, used through Jensen.

The conclusion retains the initial weight
`W_0 = (3/N)^(2/3)`, rather than losing the desired decay when the Holder
power is linearized.
-/

/-! ## A fixed prefactor in the bad-event estimate -/

/-- For an exponent in `[0,1]`, a nonnegative constant raised to that
exponent is at most its maximum with one. -/
theorem rpow_le_max_one_self {x theta : ℝ}
    (hx : 0 ≤ x) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    x ^ theta ≤ max 1 x := by
  by_cases hx1 : x ≤ 1
  · exact (Real.rpow_le_one hx hx1 htheta0).trans (le_max_left _ _)
  · have h1x : 1 ≤ x := le_of_not_ge hx1
    exact (Real.rpow_le_self_of_one_le h1x htheta1).trans
      (le_max_right _ _)

/-- The exact weighted bad-branch estimate when Key Proposition 4 carries a
fixed multiplicative prefactor `Kbad`. -/
theorem harperDyadicBadWeight_transfer_with_prefactor
    {N C Kbad : ℝ} (hN : 0 < N) (hC : 0 ≤ C) (hKbad : 0 ≤ Kbad)
    (m : ℕ) :
    (Kbad * Real.exp (-2 * C / harperDyadicMomentGap m)) ^
          (harperDyadicBadHolderExponent m) *
        (harperDyadicMomentWeight N (m + 1)) ^
          (harperDyadicMomentExponent m /
            harperDyadicMomentExponent (m + 1)) ≤
      (2 * max 1 Kbad * Real.exp (-C)) *
        harperDyadicMomentWeight N m := by
  have htheta0 := harperDyadicBadHolderExponent_nonneg m
  have htheta1 := harperDyadicBadHolderExponent_le_one m
  have hKpow :
      Kbad ^ harperDyadicBadHolderExponent m ≤ max 1 Kbad :=
    rpow_le_max_one_self hKbad htheta0 htheta1
  have hbare := harperDyadicBadWeight_transfer hN hC m
  rw [Real.mul_rpow hKbad (Real.exp_pos _).le]
  have hbare0 : 0 ≤
      (Real.exp (-2 * C / harperDyadicMomentGap m)) ^
          (harperDyadicBadHolderExponent m) *
        (harperDyadicMomentWeight N (m + 1)) ^
          (harperDyadicMomentExponent m /
            harperDyadicMomentExponent (m + 1)) :=
    mul_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _)
      (Real.rpow_nonneg
        (harperDyadicMomentWeight_pos hN (m + 1)).le _)
  have hmax0 : 0 ≤ max 1 Kbad := le_trans (by norm_num) (le_max_left _ _)
  calc
    (Kbad ^ harperDyadicBadHolderExponent m *
          Real.exp (-2 * C / harperDyadicMomentGap m) ^
            harperDyadicBadHolderExponent m) *
        harperDyadicMomentWeight N (m + 1) ^
          (harperDyadicMomentExponent m /
            harperDyadicMomentExponent (m + 1)) =
      Kbad ^ harperDyadicBadHolderExponent m *
        ((Real.exp (-2 * C / harperDyadicMomentGap m)) ^
            harperDyadicBadHolderExponent m *
          (harperDyadicMomentWeight N (m + 1)) ^
            (harperDyadicMomentExponent m /
              harperDyadicMomentExponent (m + 1))) := by ring
    _ ≤ max 1 Kbad *
        ((Real.exp (-2 * C / harperDyadicMomentGap m)) ^
            harperDyadicBadHolderExponent m *
          (harperDyadicMomentWeight N (m + 1)) ^
            (harperDyadicMomentExponent m /
              harperDyadicMomentExponent (m + 1))) :=
      mul_le_mul_of_nonneg_right hKpow hbare0
    _ ≤ max 1 Kbad *
        ((2 * Real.exp (-C)) * harperDyadicMomentWeight N m) :=
      mul_le_mul_of_nonneg_left hbare hmax0
    _ = (2 * max 1 Kbad * Real.exp (-C)) *
        harperDyadicMomentWeight N m := by ring

/-- A convenient explicit choice ensuring the preceding uniform coefficient
is at most one half. -/
theorem two_mul_max_mul_exp_neg_le_half
    {C Kbad : ℝ}
    (hC : Real.log (4 * max 1 Kbad) ≤ C) :
    2 * max 1 Kbad * Real.exp (-C) ≤ 1 / 2 := by
  have hmax : 0 < max 1 Kbad :=
    lt_of_lt_of_le (by norm_num) (le_max_left 1 Kbad)
  have hfour : 0 < 4 * max 1 Kbad := mul_pos (by norm_num) hmax
  have hExp : Real.exp (-C) ≤
      Real.exp (-Real.log (4 * max 1 Kbad)) := by
    rw [Real.exp_le_exp]
    linarith
  have hlog : Real.exp (-Real.log (4 * max 1 Kbad)) =
      (4 * max 1 Kbad)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hfour]
  rw [hlog] at hExp
  have hnonneg : 0 ≤ 2 * max 1 Kbad := by positivity
  calc
    2 * max 1 Kbad * Real.exp (-C) ≤
        2 * max 1 Kbad * (4 * max 1 Kbad)⁻¹ :=
      mul_le_mul_of_nonneg_left hExp hnonneg
    _ = 1 / 2 := by field_simp; norm_num

/-! ## Complete exponent-dependent event iteration -/

/-- Complete weighted good--bad iteration for one arbitrary nonnegative
Euler-set energy.

`prefixBudget m` is kept as a separate input so that this theorem consumes
the exact output of the finite prefix-window union bound.  The next
hypothesis is precisely the still-needed analytic specialization of that
budget to Harper's exponential failure probability. -/
theorem integral_rpow_twoThird_le_of_harperDyadicPrefixBudgets
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν]
    (Z : α → ℝ) (G : ℕ → Set α) (prefixBudget : ℕ → ℝ)
    {N C Kbad A T : ℝ} {L : ℕ}
    (hN : 0 < N) (hKbad : 0 ≤ Kbad)
    (hC : Real.log (4 * max 1 Kbad) ≤ C)
    (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hZ : Integrable Z ν) (hZnonneg : ∀ omega, 0 ≤ Z omega)
    (hG : ∀ m, m < L → MeasurableSet (G m))
    (hgood : ∀ m, m < L →
      (∫ omega in G m,
          Z omega ^ harperDyadicMomentExponent m ∂ν) ≤
        A * harperDyadicMomentWeight N m)
    (hbad : ∀ m, m < L → ν.real (G m)ᶜ ≤ prefixBudget m)
    (hbudget : ∀ m, m < L →
      prefixBudget m ≤
        Kbad * Real.exp (-2 * C / harperDyadicMomentGap m))
    (hfirst : (∫ omega, Z omega ∂ν) ≤ T)
    (hstop : harperDyadicMomentGap L * N ≤ 2) :
    (∫ omega, Z omega ^ harperTwoThird ∂ν) ≤
      harperDyadicMomentWeight N 0 *
        (2 * (A + 2 * max 1 Kbad * Real.exp (-C)) +
          2 * max 1 T) := by
  let M : ℕ → ℝ := fun m ↦
    ∫ omega, Z omega ^ harperDyadicMomentExponent m ∂ν
  let theta : ℕ → ℝ := fun m ↦
    harperDyadicMomentExponent m /
      harperDyadicMomentExponent (m + 1)
  let badCoefficient : ℕ → ℝ := fun m ↦
    (Kbad * Real.exp (-2 * C / harperDyadicMomentGap m)) ^
      (harperDyadicBadHolderExponent m)
  let rho : ℝ := 2 * max 1 Kbad * Real.exp (-C)
  let B : ℝ := 2 * max 1 T
  have hC0 : 0 ≤ C := by
    have harg : 1 ≤ 4 * max 1 Kbad := by
      have hmax : 1 ≤ max 1 Kbad := le_max_left _ _
      nlinarith
    have hlog0 : 0 ≤ Real.log (4 * max 1 Kbad) := Real.log_nonneg harg
    linarith
  have hq0 (m : ℕ) : 0 < harperDyadicMomentExponent m :=
    harperDyadicMomentExponent_pos m
  have hq1 (m : ℕ) : harperDyadicMomentExponent m ≤ 1 :=
    (harperDyadicMomentExponent_lt_one m).le
  have hM0 : ∀ m, m ≤ L → 0 ≤ M m := by
    intro m hm
    exact integral_nonneg fun omega ↦
      Real.rpow_nonneg (hZnonneg omega) _
  have htheta0 : ∀ m, m < L → 0 ≤ theta m := by
    intro m hm
    exact div_nonneg (hq0 m).le (hq0 (m + 1)).le
  have htheta1 : ∀ m, m < L → theta m ≤ 1 := by
    intro m hm
    exact (div_le_one (hq0 (m + 1))).2
      (harperDyadicMomentExponent_strictMono (Nat.lt_succ_self m)).le
  have hbadCoefficient0 : ∀ m, m < L → 0 ≤ badCoefficient m := by
    intro m hm
    exact Real.rpow_nonneg
      (mul_nonneg hKbad (Real.exp_pos _).le) _
  have hrec : ∀ m, m < L →
      M m ≤ A * harperDyadicMomentWeight N m +
        badCoefficient m * (M (m + 1)) ^ (theta m) := by
    intro m hm
    let q : ℝ := harperDyadicMomentExponent m
    let r : ℝ := harperDyadicMomentExponent (m + 1)
    have hqr : q < r :=
      harperDyadicMomentExponent_strictMono (Nat.lt_succ_self m)
    have hZq : Integrable (fun omega ↦ Z omega ^ q) ν :=
      integrable_rpow_of_integrable_nonneg hZ hZnonneg (hq0 m).le (hq1 m)
    have hZr : Integrable (fun omega ↦ Z omega ^ r) ν :=
      integrable_rpow_of_integrable_nonneg hZ hZnonneg
        (hq0 (m + 1)).le (hq1 (m + 1))
    have hZqLp : MemLp (fun omega ↦ Z omega ^ q)
        (ENNReal.ofReal (r / q)) ν :=
      memLp_rpow_of_integrable_rpow (hq0 m) (hq0 (m + 1))
        hZ hZnonneg hZr
    have hstep := integral_rpow_le_of_good_bad_at_larger_exponent
      (hG m hm) (hq0 m) hqr hZnonneg hZq hZqLp
        (hgood m hm) ((hbad m hm).trans (hbudget m hm))
    simpa only [M, theta, badCoefficient,
      harperDyadicBadHolderExponent, q, r] using! hstep
  have htransfer : ∀ m, m < L →
      badCoefficient m *
          harperDyadicMomentWeight N (m + 1) ^ (theta m) ≤
        rho * harperDyadicMomentWeight N m := by
    intro m hm
    exact harperDyadicBadWeight_transfer_with_prefactor
      hN hC0 hKbad m
  have hJensen : M L ≤ (∫ omega, Z omega ∂ν) ^
      harperDyadicMomentExponent L := by
    have h := integralOn_rpow_le_rpow_integralOn_of_le_one
      (ν := ν) (Z := Z) (G := Set.univ)
      (q := harperDyadicMomentExponent L)
      MeasurableSet.univ (hq0 L) (hq1 L) hZ hZnonneg
    simpa only [M, Measure.restrict_univ] using! h
  have hintegral0 : 0 ≤ ∫ omega, Z omega ∂ν :=
    integral_nonneg hZnonneg
  have hterminalT : M L ≤ max 1 T := by
    calc
      M L ≤ (∫ omega, Z omega ∂ν) ^
          harperDyadicMomentExponent L := hJensen
      _ ≤ T ^ harperDyadicMomentExponent L :=
        Real.rpow_le_rpow hintegral0 hfirst (hq0 L).le
      _ ≤ max 1 T :=
        rpow_le_max_one_self hT (hq0 L).le (hq1 L)
  have hterminalWeight : 1 ≤
      2 * harperDyadicMomentWeight N L :=
    one_le_two_mul_harperDyadicMomentWeight_of_paper_stop hN hstop
  have hbase : M L ≤ B * harperDyadicMomentWeight N L := by
    have hmax0 : 0 ≤ max 1 T :=
      le_trans (by norm_num) (le_max_left _ _)
    calc
      M L ≤ max 1 T := hterminalT
      _ ≤ max 1 T *
          (2 * harperDyadicMomentWeight N L) :=
        (by simpa only [mul_one] using!
          mul_le_mul_of_nonneg_left hterminalWeight hmax0)
      _ = B * harperDyadicMomentWeight N L := by
        dsimp only [B]
        ring
  have hweighted := finite_weighted_fractional_contraction_recursion
    M (harperDyadicMomentWeight N) theta badCoefficient
      hA (by dsimp only [rho]; positivity)
      (by dsimp only [rho]; exact
        two_mul_max_mul_exp_neg_le_half hC)
      (fun m hm ↦ harperDyadicMomentWeight_pos hN m)
      hM0 htheta0 htheta1 hbadCoefficient0 hrec htransfer
      hbase (by dsimp only [B]; positivity)
  simpa only [M, rho, B, harperDyadicMomentExponent_zero] using! hweighted

end Problem520
end Erdos
