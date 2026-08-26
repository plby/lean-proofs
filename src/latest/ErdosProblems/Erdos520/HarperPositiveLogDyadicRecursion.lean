import ErdosProblems.Erdos520.HarperPositiveLogRestrictedRecursion
import ErdosProblems.Erdos520.HarperDirectMomentRecursion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Erdos.Problem520

/-!
# Positive-log one-step bounds in dyadic-recursion form

The sharp ballot input needed downstream has the form

`H ≤ K * (x + κ) / N`,

where `N = sqrt n`.  At dyadic exponent `q_m` we choose the free prefix
height `B = C / (1-q_m)`.  Writing the remaining fixed offset as `X`, the
probability numerator is `X + C / (1-q_m)`.  The lemmas below show exactly
that this gives the standard Harper weight, with a constant independent of
`m`; the bad branch is already the required exponential coefficient.
-/

/-- Fixed good-branch constant produced by a sharp positive-log ballot
estimate. -/
noncomputable def harperPositiveLogDyadicGoodConstant
    (V K X C : ℝ) : ℝ :=
  max 1 (harperExplicitMertensConstant * V * K * (X + C))

/-- Volume-preserving good-branch coefficient.  Unlike the convenient
`max 1` envelope above, this tends to zero with the vertical-set volume and
is therefore the correct form on shrinking central bands. -/
noncomputable def harperPositiveLogDyadicSmallGoodConstant
    (V K X C : ℝ) : ℝ :=
  let Q := harperExplicitMertensConstant * V * K * (X + C)
  Q ^ harperTwoThird + Q

theorem harperDyadicMomentGap_le_one (m : ℕ) :
    harperDyadicMomentGap m ≤ 1 := by
  unfold harperDyadicMomentGap
  linarith [harperDyadicMomentExponent_pos m]

/-- A numerator `X + C/gap` is bounded by `(X+C)/gap`; this is the precise
algebra that makes the good-branch constant uniform along the dyadic
iteration. -/
theorem harper_positiveLogBallotNumerator_div_le
    {N K X C : ℝ} (hN : 0 < N) (hK : 0 ≤ K)
    (hX : 0 ≤ X) (m : ℕ) :
    K * (X + C / harperDyadicMomentGap m) / N ≤
      K * (X + C) /
        (harperDyadicMomentGap m * N) := by
  let g := harperDyadicMomentGap m
  have hg : 0 < g := harperDyadicMomentGap_pos m
  have hg1 : g ≤ 1 := harperDyadicMomentGap_le_one m
  have hinside : X + C / g ≤ (X + C) / g := by
    apply (le_div_iff₀ hg).2
    calc
      (X + C / g) * g = X * g + C := by field_simp
      _ ≤ X + C := by
        exact add_le_add
          (by simpa only [mul_one] using!
            mul_le_mul_of_nonneg_left hg1 hX) le_rfl
  have hmul := mul_le_mul_of_nonneg_left hinside hK
  apply (div_le_div_iff₀ hN (mul_pos hg hN)).2
  calc
    K * (X + C / g) * (g * N) =
        (K * (X + C / g)) * g * N := by ring
    _ ≤ (K * ((X + C) / g)) * g * N := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmul hg.le) hN.le
    _ = K * (X + C) * N := by field_simp

/-- A sharp positive-log probability estimate gives exactly the good weight
required by `integral_rpow_twoThird_le_of_harperDyadicRecurrences`. -/
theorem harper_positiveLogGoodTerm_le_dyadicMomentWeight
    {V N K X C H q : ℝ} (m : ℕ)
    (hV : 0 ≤ V) (hN : 0 < N) (hK : 0 ≤ K)
    (hX : 0 ≤ X) (hC : 0 ≤ C) (hH0 : 0 ≤ H)
    (hH : H ≤ K * (X + C / harperDyadicMomentGap m) / N)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (harperExplicitMertensConstant * (V * H)) ^ q ≤
      harperPositiveLogDyadicGoodConstant V K X C *
        ((((harperDyadicMomentGap m) * N)⁻¹) ^ q) := by
  let Q : ℝ := harperExplicitMertensConstant * V * K * (X + C)
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg harperExplicitMertensConstant_pos.le hV) hK)
      (add_nonneg hX hC)
  have hH' := hH.trans
    (harper_positiveLogBallotNumerator_div_le hN hK hX m)
  have hbase :
      harperExplicitMertensConstant * (V * H) ≤
        Q * ((harperDyadicMomentGap m * N)⁻¹) := by
    have hmul := mul_le_mul_of_nonneg_left hH'
      (mul_nonneg harperExplicitMertensConstant_pos.le hV)
    calc
      harperExplicitMertensConstant * (V * H) =
          harperExplicitMertensConstant * V * H := by ring
      _ ≤ harperExplicitMertensConstant * V *
          (K * (X + C) / (harperDyadicMomentGap m * N)) := hmul
      _ = Q * ((harperDyadicMomentGap m * N)⁻¹) := by
        dsimp [Q]
        rw [div_eq_mul_inv]
        ring
  have hbase0 : 0 ≤ harperExplicitMertensConstant * (V * H) := by
    exact mul_nonneg harperExplicitMertensConstant_pos.le
      (mul_nonneg hV hH0)
  have hscale0 : 0 ≤
      (harperDyadicMomentGap m * N)⁻¹ := by
    exact inv_nonneg.mpr (mul_nonneg
      (harperDyadicMomentGap_pos m).le hN.le)
  calc
    (harperExplicitMertensConstant * (V * H)) ^ q ≤
        (Q * (harperDyadicMomentGap m * N)⁻¹) ^ q :=
      Real.rpow_le_rpow hbase0 hbase hq0
    _ = Q ^ q * ((harperDyadicMomentGap m * N)⁻¹) ^ q := by
      rw [Real.mul_rpow hQ hscale0]
    _ ≤ max 1 Q * ((harperDyadicMomentGap m * N)⁻¹) ^ q :=
      mul_le_mul_of_nonneg_right
        (rpow_le_max_one_self hQ hq0 hq1)
        (Real.rpow_nonneg hscale0 q)
    _ = harperPositiveLogDyadicGoodConstant V K X C *
          ((harperDyadicMomentGap m * N)⁻¹) ^ q := by
      rfl

/-- The same good-term conversion without replacing a small coefficient by
one.  The dyadic exponents all lie in `[2/3,1]`, so `Q^q` is bounded by
`Q^(2/3)+Q`. -/
theorem harper_positiveLogGoodTerm_le_dyadicMomentWeight_preserving_small
    {V N K X C H : ℝ} (m : ℕ)
    (hV : 0 ≤ V) (hN : 0 < N) (hK : 0 ≤ K)
    (hX : 0 ≤ X) (hC : 0 ≤ C) (hH0 : 0 ≤ H)
    (hH : H ≤ K * (X + C / harperDyadicMomentGap m) / N) :
    (harperExplicitMertensConstant * (V * H)) ^
        harperDyadicMomentExponent m ≤
      harperPositiveLogDyadicSmallGoodConstant V K X C *
        harperDyadicMomentWeight N m := by
  let Q : ℝ := harperExplicitMertensConstant * V * K * (X + C)
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg harperExplicitMertensConstant_pos.le hV) hK)
      (add_nonneg hX hC)
  have hH' := hH.trans
    (harper_positiveLogBallotNumerator_div_le hN hK hX m)
  have hbase :
      harperExplicitMertensConstant * (V * H) ≤
        Q * ((harperDyadicMomentGap m * N)⁻¹) := by
    have hmul := mul_le_mul_of_nonneg_left hH'
      (mul_nonneg harperExplicitMertensConstant_pos.le hV)
    calc
      harperExplicitMertensConstant * (V * H) =
          harperExplicitMertensConstant * V * H := by ring
      _ ≤ harperExplicitMertensConstant * V *
          (K * (X + C) / (harperDyadicMomentGap m * N)) := hmul
      _ = Q * ((harperDyadicMomentGap m * N)⁻¹) := by
        dsimp [Q]
        rw [div_eq_mul_inv]
        ring
  have hbase0 : 0 ≤ harperExplicitMertensConstant * (V * H) := by
    exact mul_nonneg harperExplicitMertensConstant_pos.le
      (mul_nonneg hV hH0)
  have hscale0 : 0 ≤
      (harperDyadicMomentGap m * N)⁻¹ := by
    exact inv_nonneg.mpr (mul_nonneg
      (harperDyadicMomentGap_pos m).le hN.le)
  have hqLower :
      harperTwoThird ≤ harperDyadicMomentExponent m := by
    rw [← harperDyadicMomentExponent_zero]
    exact harperDyadicMomentExponent_strictMono.monotone (Nat.zero_le m)
  have hQpow :
      Q ^ harperDyadicMomentExponent m ≤
        Q ^ harperTwoThird + Q :=
    rpow_le_harperTwoThird_add_self hQ hqLower
      (harperDyadicMomentExponent_lt_one m).le
  calc
    (harperExplicitMertensConstant * (V * H)) ^
          harperDyadicMomentExponent m ≤
        (Q * (harperDyadicMomentGap m * N)⁻¹) ^
          harperDyadicMomentExponent m :=
      Real.rpow_le_rpow hbase0 hbase
        (harperDyadicMomentExponent_pos m).le
    _ = Q ^ harperDyadicMomentExponent m *
        ((harperDyadicMomentGap m * N)⁻¹) ^
          harperDyadicMomentExponent m := by
      rw [Real.mul_rpow hQ hscale0]
    _ ≤ (Q ^ harperTwoThird + Q) *
        ((harperDyadicMomentGap m * N)⁻¹) ^
          harperDyadicMomentExponent m :=
      mul_le_mul_of_nonneg_right hQpow
        (Real.rpow_nonneg hscale0 _)
    _ = harperPositiveLogDyadicSmallGoodConstant V K X C *
        harperDyadicMomentWeight N m := by
      rfl

/-- Direct conversion of one explicit positive-log recursion step into the
recurrence consumed by the existing weighted dyadic iterator. -/
theorem harperDyadicRecurrence_of_explicitPositiveLogStep
    {V N K X C H Mq Mr : ℝ} (m : ℕ)
    (hV : 0 ≤ V) (hN : 0 < N) (hK : 0 ≤ K)
    (hX : 0 ≤ X) (hC : 0 ≤ C) (hH0 : 0 ≤ H)
    (hH : H ≤ K * (X + C / harperDyadicMomentGap m) / N)
    (hstep : Mq ≤
      (harperExplicitMertensConstant * (V * H)) ^
          harperDyadicMomentExponent m +
        Real.exp (-2 * C / harperDyadicMomentGap m) ^
            harperDyadicBadHolderExponent m *
          Mr ^ (harperDyadicMomentExponent m /
            harperDyadicMomentExponent (m + 1))) :
    Mq ≤
      harperPositiveLogDyadicGoodConstant V K X C *
          harperDyadicMomentWeight N m +
        Real.exp (-2 * C / harperDyadicMomentGap m) ^
            harperDyadicBadHolderExponent m *
          Mr ^ (harperDyadicMomentExponent m /
            harperDyadicMomentExponent (m + 1)) := by
  have hgood := harper_positiveLogGoodTerm_le_dyadicMomentWeight
    m hV hN hK hX hC hH0 hH
      (harperDyadicMomentExponent_pos m).le
      (harperDyadicMomentExponent_lt_one m).le
  unfold harperDyadicMomentWeight
  exact hstep.trans (add_le_add hgood le_rfl)

/-- Volume-preserving recurrence conversion for central dyadic bands. -/
theorem
    harperDyadicRecurrence_of_explicitPositiveLogStep_preserving_small
    {V N K X C H Mq Mr : ℝ} (m : ℕ)
    (hV : 0 ≤ V) (hN : 0 < N) (hK : 0 ≤ K)
    (hX : 0 ≤ X) (hC : 0 ≤ C) (hH0 : 0 ≤ H)
    (hH : H ≤ K * (X + C / harperDyadicMomentGap m) / N)
    (hstep : Mq ≤
      (harperExplicitMertensConstant * (V * H)) ^
          harperDyadicMomentExponent m +
        Real.exp (-2 * C / harperDyadicMomentGap m) ^
            harperDyadicBadHolderExponent m *
          Mr ^ (harperDyadicMomentExponent m /
            harperDyadicMomentExponent (m + 1))) :
    Mq ≤
      harperPositiveLogDyadicSmallGoodConstant V K X C *
          harperDyadicMomentWeight N m +
        Real.exp (-2 * C / harperDyadicMomentGap m) ^
            harperDyadicBadHolderExponent m *
          Mr ^ (harperDyadicMomentExponent m /
            harperDyadicMomentExponent (m + 1)) := by
  have hgood :=
    harper_positiveLogGoodTerm_le_dyadicMomentWeight_preserving_small
      m hV hN hK hX hC hH0 hH
  exact hstep.trans (add_le_add hgood le_rfl)

end Erdos.Problem520

#print axioms Erdos.Problem520.harper_positiveLogGoodTerm_le_dyadicMomentWeight_preserving_small
#print axioms Erdos.Problem520.harperDyadicRecurrence_of_explicitPositiveLogStep_preserving_small
