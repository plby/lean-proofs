import ErdosProblems.Erdos67b.LogSecondDerivativeReal
import ErdosProblems.Erdos67b.LogControlledWeylRealStart

/-!
# Coverage of the transition between the first two logarithmic bands

The one-step estimate applies while `8 H a ≤ U²`.  On its complement,
provided the lag budget grows more slowly than `X^(1/4)`, the height is
already large enough for the robust depth-two controlled-Weyl boundary.
-/

open Filter

namespace Erdos67b.LogBandCoverage

noncomputable section

open Erdos1149
open Erdos67b.LogWeylParameters

/-- A slowly growing lag budget used in the one-step band. -/
def rOneLagBudget (X : ℕ) : ℕ :=
  ⌈(X : ℝ) ^ (1 / 16 : ℝ)⌉₊

theorem rOneLagBudget_pos {X : ℕ} (hX : 0 < X) :
    0 < rOneLagBudget X := by
  unfold rOneLagBudget
  exact AnalyticParameters.natCeil_pos
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hX) _)

theorem rpow_le_rOneLagBudget (X : ℕ) :
    (X : ℝ) ^ (1 / 16 : ℝ) ≤ (rOneLagBudget X : ℝ) := by
  unfold rOneLagBudget
  exact Nat.le_ceil _

/-- Elementary decay of the square-root coefficient occurring in the
one-step van der Corput estimate. -/
theorem sqrt_log_div_le_nine_mul_rpow_neg
    {H : ℝ} (hH : 1 ≤ H) :
    Real.sqrt (38 * (1 + Real.log H) / H) ≤
      9 * H ^ (-1 / 4 : ℝ) := by
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hHnonneg : 0 ≤ H := hHpos.le
  have hsqrtPos : 0 < Real.sqrt H := Real.sqrt_pos.2 hHpos
  have hlogSqrt := Real.log_le_sub_one_of_pos hsqrtPos
  have hlogEq : Real.log H = 2 * Real.log (Real.sqrt H) := by
    calc
      Real.log H = Real.log ((Real.sqrt H) ^ 2) := by
        rw [Real.sq_sqrt hHnonneg]
      _ = (2 : ℕ) * Real.log (Real.sqrt H) := by rw [Real.log_pow]
      _ = 2 * Real.log (Real.sqrt H) := by norm_num
  have hlogBound : 1 + Real.log H ≤ 2 * Real.sqrt H := by
    rw [hlogEq]
    linarith [Real.sqrt_nonneg H]
  have hsqrtDiv : Real.sqrt H / H = H ^ (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv,
      ← Real.rpow_neg_one H, ← Real.rpow_add hHpos]
    norm_num
  have hradNonneg : 0 ≤ 38 * (1 + Real.log H) / H := by
    have hlogNonneg : 0 ≤ Real.log H := Real.log_nonneg hH
    positivity
  have hradLe : 38 * (1 + Real.log H) / H ≤
      76 * H ^ (-1 / 2 : ℝ) := by
    calc
      38 * (1 + Real.log H) / H ≤
          38 * (2 * Real.sqrt H) / H := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogBound (by norm_num)) hHnonneg
      _ = 76 * (Real.sqrt H / H) := by ring
      _ = 76 * H ^ (-1 / 2 : ℝ) := by rw [hsqrtDiv]
  have hpowSq : (H ^ (-1 / 4 : ℝ)) ^ 2 =
      H ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hHnonneg]
    norm_num
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      38 * (1 + Real.log H) / H ≤
          76 * H ^ (-1 / 2 : ℝ) := hradLe
      _ ≤ 81 * H ^ (-1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by norm_num)
          (Real.rpow_nonneg hHnonneg _)
      _ = (9 * H ^ (-1 / 4 : ℝ)) ^ 2 := by
        rw [mul_pow, hpowSq]
        norm_num

/-- With the canonical growing lag budget, the one-step coefficient has a
uniform `X^(-1/64)` power saving. -/
theorem rOneLagBudget_sqrt_le_power {X : ℕ} (hX : 1 ≤ X) :
    Real.sqrt
        (38 * (1 + Real.log (rOneLagBudget X : ℝ)) /
          (rOneLagBudget X : ℝ)) ≤
      9 * (X : ℝ) ^ (-1 / 64 : ℝ) := by
  have hHpos : 0 < rOneLagBudget X :=
    rOneLagBudget_pos (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hHone : (1 : ℝ) ≤ rOneLagBudget X := by exact_mod_cast hHpos
  have hbasePos : 0 < (X : ℝ) ^ (1 / 16 : ℝ) := by positivity
  have hneg : (-1 / 4 : ℝ) ≤ 0 := by norm_num
  have hpowMono : ((rOneLagBudget X : ℕ) : ℝ) ^ (-1 / 4 : ℝ) ≤
      ((X : ℝ) ^ (1 / 16 : ℝ)) ^ (-1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hbasePos (rpow_le_rOneLagBudget X) hneg
  have hcollapse : ((X : ℝ) ^ (1 / 16 : ℝ)) ^ (-1 / 4 : ℝ) =
      (X : ℝ) ^ (-1 / 64 : ℝ) := by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ X)]
    norm_num
  calc
    Real.sqrt
        (38 * (1 + Real.log (rOneLagBudget X : ℝ)) /
          (rOneLagBudget X : ℝ)) ≤
        9 * (rOneLagBudget X : ℝ) ^ (-1 / 4 : ℝ) :=
      sqrt_log_div_le_nine_mul_rpow_neg hHone
    _ ≤ 9 * (((X : ℝ) ^ (1 / 16 : ℝ)) ^ (-1 / 4 : ℝ)) := by
      gcongr
    _ = 9 * (X : ℝ) ^ (-1 / 64 : ℝ) := by rw [hcollapse]

/-- The chosen lag budget is eventually at most one eighth of `X^(1/4)`. -/
theorem eventually_eight_mul_rOneLagBudget_le :
    ∀ᶠ X : ℕ in atTop,
      (8 : ℝ) * rOneLagBudget X ≤ (X : ℝ) ^ (1 / 4 : ℝ) := by
  have ht : Tendsto (fun X : ℕ ↦ (X : ℝ) ^ (3 / 16 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 16)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_ge_atTop (1 : ℕ),
      ht.eventually (eventually_ge_atTop (16 : ℝ))] with X hX hrootLarge
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hsmallOne : (1 : ℝ) ≤ (X : ℝ) ^ (1 / 16 : ℝ) :=
    Real.one_le_rpow hXone (by norm_num)
  have hceil : ((rOneLagBudget X : ℕ) : ℝ) ≤
      2 * (X : ℝ) ^ (1 / 16 : ℝ) := by
    unfold rOneLagBudget
    exact AnalyticParameters.natCeil_le_two_mul hsmallOne
  calc
    (8 : ℝ) * rOneLagBudget X ≤
        16 * (X : ℝ) ^ (1 / 16 : ℝ) := by nlinarith
    _ ≤ (X : ℝ) ^ (3 / 16 : ℝ) *
        (X : ℝ) ^ (1 / 16 : ℝ) := by
      gcongr
    _ = (X : ℝ) ^ ((3 / 16 : ℝ) + 1 / 16) := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < X)]
    _ = (X : ℝ) ^ (1 / 4 : ℝ) := by norm_num

/-- The separated one-step region and the depth-two robust Weyl region
cover every positive height.  This is the precise transition dichotomy
used by the global block decomposition. -/
theorem secondDerivative_or_rawStepScale_two
    {X H : ℕ} {a U : ℝ}
    (hX : 1 ≤ X) (ha : 0 < a) (hXU : (X : ℝ) ≤ U)
    (hHX : (8 : ℝ) * H ≤ (X : ℝ) ^ (1 / 4 : ℝ)) :
    8 * (H : ℝ) * a ≤ U ^ 2 ∨
      rawStepScale 2 X a ≤ (X : ℝ) ^ (3 / 4 : ℝ) := by
  by_cases hsecond : 8 * (H : ℝ) * a ≤ U ^ 2
  · exact Or.inl hsecond
  · right
    apply rawStepScale_two_le_of_rpow_lower hX ha
    have hXpos : (0 : ℝ) < X := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
    have hXsq : (X : ℝ) ^ (2 : ℕ) ≤ U ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hXU 2
    have hheight : (X : ℝ) ^ (2 : ℕ) <
        (X : ℝ) ^ (1 / 4 : ℝ) * a := by
      calc
        (X : ℝ) ^ (2 : ℕ) ≤ U ^ 2 := hXsq
        _ < 8 * (H : ℝ) * a := lt_of_not_ge hsecond
        _ ≤ (X : ℝ) ^ (1 / 4 : ℝ) * a := by
          exact mul_le_mul_of_nonneg_right hHX ha.le
    have hsplit : (X : ℝ) ^ (2 : ℕ) =
        (X : ℝ) ^ (1 / 4 : ℝ) *
          (X : ℝ) ^ (7 / 4 : ℝ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add hXpos]
      norm_num
    rw [hsplit] at hheight
    exact (lt_of_mul_lt_mul_left hheight
      (Real.rpow_pos_of_pos hXpos (1 / 4 : ℝ)).le).le

/-- Eventual specialization of the transition dichotomy to the canonical
growing lag budget. -/
theorem eventually_secondDerivative_or_rawStepScale_two :
    ∀ᶠ X : ℕ in atTop, ∀ {a U : ℝ},
      0 < a → (X : ℝ) ≤ U →
      8 * (rOneLagBudget X : ℝ) * a ≤ U ^ 2 ∨
        rawStepScale 2 X a ≤ (X : ℝ) ^ (3 / 4 : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_eight_mul_rOneLagBudget_le] with X hX hbudget
  intro a U ha hXU
  exact secondDerivative_or_rawStepScale_two hX ha hXU hbudget

end

end Erdos67b.LogBandCoverage
