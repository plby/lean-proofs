import ErdosProblems.Erdos520.HarperAbstractMomentRecursion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# Direct weighted iteration of concrete Harper recurrences

The restricted vertical-set theorem already returns the full good--bad
recurrence at consecutive dyadic exponents.  This file packages the last
purely numerical step: once those concrete recurrences have the standard
good weight and exponentially small bad coefficient, they imply the
`2/3` moment bound directly.

This avoids reconstructing an auxiliary good event after the prefix-window
argument has already eliminated it.
-/

/-- Along the exponent ladder, Jensen's terminal power retains a small
first-moment factor.  This is the form needed for the shrinking central
dyadic bands, where replacing the first moment by `max 1 T` would destroy
summability. -/
theorem rpow_le_harperTwoThird_add_self
    {z q : ℝ} (hz : 0 ≤ z)
    (hqLower : harperTwoThird ≤ q) (hqUpper : q ≤ 1) :
    z ^ q ≤ z ^ harperTwoThird + z := by
  rcases hz.eq_or_lt with rfl | hzPos
  · have htwo : 0 < harperTwoThird := by norm_num [harperTwoThird]
    have hq : 0 < q := htwo.trans_le hqLower
    simp [Real.zero_rpow hq.ne', Real.zero_rpow htwo.ne']
  by_cases hzOne : z ≤ 1
  · have hpow : z ^ q ≤ z ^ harperTwoThird :=
      Real.rpow_le_rpow_of_exponent_ge hzPos hzOne hqLower
    exact hpow.trans (le_add_of_nonneg_right hz)
  · have hzGe : 1 ≤ z := le_of_not_ge hzOne
    have hpow : z ^ q ≤ z ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hzGe hqUpper
    rw [Real.rpow_one] at hpow
    exact hpow.trans (le_add_of_nonneg_left (Real.rpow_nonneg hz _))

/-- Direct moment-sequence form of the weighted Harper iteration, including
a fixed prefactor in the bad-event estimate and the terminal Jensen step. -/
theorem integral_rpow_twoThird_le_of_harperDyadicRecurrences
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν]
    (Z : α → ℝ) {N C Kbad A T : ℝ} {L : ℕ}
    (hN : 0 < N) (hKbad : 0 ≤ Kbad)
    (hC : Real.log (4 * max 1 Kbad) ≤ C)
    (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hZ : Integrable Z ν) (hZnonneg : ∀ omega, 0 ≤ Z omega)
    (hrec : ∀ m, m < L →
      (∫ omega,
          Z omega ^ harperDyadicMomentExponent m ∂ν) ≤
        A * harperDyadicMomentWeight N m +
          (Kbad * Real.exp
              (-2 * C / harperDyadicMomentGap m)) ^
                harperDyadicBadHolderExponent m *
            (∫ omega,
                Z omega ^ harperDyadicMomentExponent (m + 1) ∂ν) ^
              (harperDyadicMomentExponent m /
                harperDyadicMomentExponent (m + 1)))
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
      harperDyadicBadHolderExponent m
  let rho : ℝ := 2 * max 1 Kbad * Real.exp (-C)
  let B : ℝ := 2 * max 1 T
  have hC0 : 0 ≤ C := by
    have harg : 1 ≤ 4 * max 1 Kbad := by
      have hmax : 1 ≤ max 1 Kbad := le_max_left _ _
      nlinarith
    have hlog0 : 0 ≤ Real.log (4 * max 1 Kbad) :=
      Real.log_nonneg harg
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
      (harperDyadicMomentExponent_strictMono
        (Nat.lt_succ_self m)).le
  have hbadCoefficient0 : ∀ m, m < L →
      0 ≤ badCoefficient m := by
    intro m hm
    exact Real.rpow_nonneg
      (mul_nonneg hKbad (Real.exp_pos _).le) _
  have hrecM : ∀ m, m < L →
      M m ≤ A * harperDyadicMomentWeight N m +
        badCoefficient m * (M (m + 1)) ^ theta m := by
    intro m hm
    simpa only [M, theta, badCoefficient] using! hrec m hm
  have htransfer : ∀ m, m < L →
      badCoefficient m *
          harperDyadicMomentWeight N (m + 1) ^ theta m ≤
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
      hM0 htheta0 htheta1 hbadCoefficient0 hrecM htransfer
      hbase (by dsimp only [B]; positivity)
  simpa only [M, rho, B,
    harperDyadicMomentExponent_zero] using! hweighted

/-- Small-first-moment-preserving version of the direct Harper iteration.

The recurrence and bad-branch estimates are identical to
`integral_rpow_twoThird_le_of_harperDyadicRecurrences`.  The difference is
only at the terminal Jensen step: because every dyadic exponent lies in
`[2/3,1]`, `T ^ q_L` is bounded by `T^(2/3) + T`.  Thus a set whose first
moment tends to zero keeps that small factor all the way to the initial
`2/3` moment. -/
theorem
    integral_rpow_twoThird_le_of_harperDyadicRecurrences_preserving_first
    {alpha : Type*} [MeasurableSpace alpha] {nu : Measure alpha}
    [IsProbabilityMeasure nu]
    (Z : alpha → ℝ) {N C Kbad A T : ℝ} {L : ℕ}
    (hN : 0 < N) (hKbad : 0 ≤ Kbad)
    (hC : Real.log (4 * max 1 Kbad) ≤ C)
    (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hZ : Integrable Z nu) (hZnonneg : ∀ omega, 0 ≤ Z omega)
    (hrec : ∀ m, m < L →
      (∫ omega,
          Z omega ^ harperDyadicMomentExponent m ∂nu) ≤
        A * harperDyadicMomentWeight N m +
          (Kbad * Real.exp
              (-2 * C / harperDyadicMomentGap m)) ^
                harperDyadicBadHolderExponent m *
            (∫ omega,
                Z omega ^ harperDyadicMomentExponent (m + 1) ∂nu) ^
              (harperDyadicMomentExponent m /
                harperDyadicMomentExponent (m + 1)))
    (hfirst : (∫ omega, Z omega ∂nu) ≤ T)
    (hstop : harperDyadicMomentGap L * N ≤ 2) :
    (∫ omega, Z omega ^ harperTwoThird ∂nu) ≤
      harperDyadicMomentWeight N 0 *
        (2 * (A + 2 * max 1 Kbad * Real.exp (-C)) +
          2 * (T ^ harperTwoThird + T)) := by
  let M : ℕ → ℝ := fun m ↦
    ∫ omega, Z omega ^ harperDyadicMomentExponent m ∂nu
  let theta : ℕ → ℝ := fun m ↦
    harperDyadicMomentExponent m /
      harperDyadicMomentExponent (m + 1)
  let badCoefficient : ℕ → ℝ := fun m ↦
    (Kbad * Real.exp (-2 * C / harperDyadicMomentGap m)) ^
      harperDyadicBadHolderExponent m
  let rho : ℝ := 2 * max 1 Kbad * Real.exp (-C)
  let B : ℝ := 2 * (T ^ harperTwoThird + T)
  have hC0 : 0 ≤ C := by
    have harg : 1 ≤ 4 * max 1 Kbad := by
      have hmax : 1 ≤ max 1 Kbad := le_max_left _ _
      nlinarith
    have hlog0 : 0 ≤ Real.log (4 * max 1 Kbad) :=
      Real.log_nonneg harg
    linarith
  have hq0 (m : ℕ) : 0 < harperDyadicMomentExponent m :=
    harperDyadicMomentExponent_pos m
  have hq1 (m : ℕ) : harperDyadicMomentExponent m ≤ 1 :=
    (harperDyadicMomentExponent_lt_one m).le
  have hqLower (m : ℕ) :
      harperTwoThird ≤ harperDyadicMomentExponent m := by
    rw [← harperDyadicMomentExponent_zero]
    exact harperDyadicMomentExponent_strictMono.monotone (Nat.zero_le m)
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
      (harperDyadicMomentExponent_strictMono
        (Nat.lt_succ_self m)).le
  have hbadCoefficient0 : ∀ m, m < L →
      0 ≤ badCoefficient m := by
    intro m hm
    exact Real.rpow_nonneg
      (mul_nonneg hKbad (Real.exp_pos _).le) _
  have hrecM : ∀ m, m < L →
      M m ≤ A * harperDyadicMomentWeight N m +
        badCoefficient m * (M (m + 1)) ^ theta m := by
    intro m hm
    simpa only [M, theta, badCoefficient] using! hrec m hm
  have htransfer : ∀ m, m < L →
      badCoefficient m *
          harperDyadicMomentWeight N (m + 1) ^ theta m ≤
        rho * harperDyadicMomentWeight N m := by
    intro m hm
    exact harperDyadicBadWeight_transfer_with_prefactor
      hN hC0 hKbad m
  have hJensen : M L ≤ (∫ omega, Z omega ∂nu) ^
      harperDyadicMomentExponent L := by
    have h := integralOn_rpow_le_rpow_integralOn_of_le_one
      (ν := nu) (Z := Z) (G := Set.univ)
      (q := harperDyadicMomentExponent L)
      MeasurableSet.univ (hq0 L) (hq1 L) hZ hZnonneg
    simpa only [M, Measure.restrict_univ] using! h
  have hintegral0 : 0 ≤ ∫ omega, Z omega ∂nu :=
    integral_nonneg hZnonneg
  have hterminalT :
      M L ≤ T ^ harperTwoThird + T := by
    calc
      M L ≤ (∫ omega, Z omega ∂nu) ^
          harperDyadicMomentExponent L := hJensen
      _ ≤ T ^ harperDyadicMomentExponent L :=
        Real.rpow_le_rpow hintegral0 hfirst (hq0 L).le
      _ ≤ T ^ harperTwoThird + T :=
        rpow_le_harperTwoThird_add_self hT (hqLower L) (hq1 L)
  have hterminalWeight : 1 ≤
      2 * harperDyadicMomentWeight N L :=
    one_le_two_mul_harperDyadicMomentWeight_of_paper_stop hN hstop
  have hterminal0 : 0 ≤ T ^ harperTwoThird + T :=
    add_nonneg (Real.rpow_nonneg hT _) hT
  have hbase : M L ≤ B * harperDyadicMomentWeight N L := by
    calc
      M L ≤ T ^ harperTwoThird + T := hterminalT
      _ ≤ (T ^ harperTwoThird + T) *
          (2 * harperDyadicMomentWeight N L) :=
        (by simpa only [mul_one] using!
          mul_le_mul_of_nonneg_left hterminalWeight hterminal0)
      _ = B * harperDyadicMomentWeight N L := by
        dsimp only [B]
        ring
  have hweighted := finite_weighted_fractional_contraction_recursion
    M (harperDyadicMomentWeight N) theta badCoefficient
      hA (by dsimp only [rho]; positivity)
      (by dsimp only [rho]; exact
        two_mul_max_mul_exp_neg_le_half hC)
      (fun m hm ↦ harperDyadicMomentWeight_pos hN m)
      hM0 htheta0 htheta1 hbadCoefficient0 hrecM htransfer
      hbase (by dsimp only [B]; positivity)
  simpa only [M, rho, B,
    harperDyadicMomentExponent_zero] using! hweighted

end Problem520
end Erdos

#print axioms Erdos.Problem520.rpow_le_harperTwoThird_add_self
#print axioms Erdos.Problem520.integral_rpow_twoThird_le_of_harperDyadicRecurrences_preserving_first
