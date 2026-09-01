/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.HigherPowerDecay

/-!
# Erdős 730: analytic higher-power envelope

This module specializes the generic Tannery theorem to the exact normalized
term in equation (26).  It also proves that the number of terminal `+1`
payments remains sublinear after replacing the branch cutoff `X` by the
uniform bound `380827 X`.

The only remaining finite-combinatorial input for the actual event ledger is
the pointwise inequality saying that each branch event count is bounded by
this envelope plus one terminal payment.
-/

open Filter Topology

namespace Erdos730

/-- Exact normalized geometric term for the index `(p,k)`, where the true
prime-power exponent is `a=k+2`. -/
noncomputable def higherPowerEnvelope (X : ℕ) (i : HigherPowerIndex) : ℝ :=
  (2 / (i.1 : ℝ) ^ (i.2 + 2)) *
    higherPowerRho i.1 ^ higherPowerDepth i.1 (i.2 + 2) X

theorem higherPowerEnvelope_nonneg (X : ℕ) (i : HigherPowerIndex) :
    0 ≤ higherPowerEnvelope X i := by
  unfold higherPowerEnvelope
  exact mul_nonneg (by positivity)
    (pow_nonneg (higherPowerRho_nonneg (i.1 : ℕ)) _)

theorem higherPowerEnvelope_le_majorant (X : ℕ) (i : HigherPowerIndex) :
    higherPowerEnvelope X i ≤ higherPowerMajorant i := by
  rw [higherPowerMajorant_eq]
  unfold higherPowerEnvelope
  have hρ0 := higherPowerRho_nonneg (i.1 : ℕ)
  have hρ1 := (higherPowerRho_lt_one i.1.prop.one_lt).le
  have hpow : higherPowerRho (i.1 : ℕ) ^
      higherPowerDepth (i.1 : ℕ) (i.2 + 2) X ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hρ0 hρ1
      (higherPowerDepth (i.1 : ℕ) (i.2 + 2) X)
  have hcoef : 0 ≤ 2 / ((i.1 : ℝ) ^ (i.2 + 2)) := by positivity
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hcoef

theorem tendsto_higherPowerEnvelope_zero (i : HigherPowerIndex) :
    Tendsto (fun X ↦ higherPowerEnvelope X i) atTop (𝓝 0) := by
  simpa only [higherPowerEnvelope] using
    tendsto_higherPower_normalizedTerm_zero i.1.prop (i.2 + 2)

/-- The complete normalized sum of all geometric higher-power payments tends
to zero. -/
theorem tendsto_tsum_higherPowerEnvelope_zero :
    Tendsto (fun X ↦ ∑' i : HigherPowerIndex, higherPowerEnvelope X i)
      atTop (𝓝 0) :=
  tendsto_tsum_higherPower_of_dominated higherPowerEnvelope
    tendsto_higherPowerEnvelope_zero higherPowerEnvelope_nonneg
    higherPowerEnvelope_le_majorant

/-- Uniform linear height bound used for terminal prime powers in all four
branches. -/
def higherPowerBranchHeight : ℕ := 380827

theorem higherPowerBranchHeight_pos : 0 < higherPowerBranchHeight := by
  norm_num [higherPowerBranchHeight]

theorem tendsto_higherPower_scaledCutoff :
    Tendsto (fun X : ℕ ↦ higherPowerBranchHeight * X) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (Eventually.of_forall fun X : ℕ ↦ ?_) tendsto_id
  unfold higherPowerBranchHeight
  simpa only [id_eq, one_mul] using
    Nat.mul_le_mul_right X (show 1 ≤ 380827 by norm_num)

/-- The finite number of `(p,a)` terminal payments is still `o(X)` at the
actual uniform branch cutoff. -/
theorem tendsto_higherPrimePowerPairs_scaled_card_div :
    Tendsto (fun X : ℕ ↦
      ((higherPrimePowerPairs (higherPowerBranchHeight * X)).card : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  have hbase := tendsto_higherPrimePowerPairs_card_div.comp
    tendsto_higherPower_scaledCutoff
  have hscaled := hbase.const_mul (higherPowerBranchHeight : ℝ)
  have hscaled0 : Tendsto (fun X : ℕ ↦
      (higherPowerBranchHeight : ℝ) *
        (((higherPrimePowerPairs (higherPowerBranchHeight * X)).card : ℝ) /
          ((higherPowerBranchHeight * X : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using hscaled
  apply hscaled0.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  have hC : (higherPowerBranchHeight : ℝ) ≠ 0 := by
    exact_mod_cast higherPowerBranchHeight_pos.ne'
  simp only [Nat.cast_mul]
  field_simp

/-- Four branches do not change either vanishing assertion. -/
theorem tendsto_four_mul_higherPowerEnvelope_and_terminal_zero :
    Tendsto (fun X : ℕ ↦
      4 * ((∑' i : HigherPowerIndex, higherPowerEnvelope X i) +
        ((higherPrimePowerPairs (higherPowerBranchHeight * X)).card : ℝ) /
          (X : ℝ))) atTop (𝓝 0) := by
  simpa only [zero_add, mul_zero] using
    (tendsto_tsum_higherPowerEnvelope_zero.add
      tendsto_higherPrimePowerPairs_scaled_card_div).const_mul 4

#print axioms tendsto_tsum_higherPowerEnvelope_zero
#print axioms tendsto_higherPrimePowerPairs_scaled_card_div
#print axioms tendsto_four_mul_higherPowerEnvelope_and_terminal_zero

end Erdos730
