/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.HigherPowerCount
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Erdős 730: dominated limits for the higher-prime-power range

This file supplies the unconditional analytic limit layer behind the finite
higher-power estimates in `Erdos730HigherPowerCount`.

The exponent coordinate in `HigherPowerIndex` is shifted: `(p, k)` represents
the prime power `p^(k+2)`.  The majorant is therefore exactly
`2 / p^(k+2)`.  We prove that this majorant is summable and apply Tannery's
theorem to any nonnegative family converging pointwise to zero.

No claim is made here that a particular event count satisfies these hypotheses;
that specialization still has to instantiate the finite block estimate and its
depth parameter.
-/

open Filter Topology

namespace Erdos730

/-- A prime together with a shifted exponent.  `(p,k)` denotes exponent
`a = k+2`, so every represented exponent is at least two. -/
abbrev HigherPowerIndex := Nat.Primes × ℕ

/-- The summable majorant `2 / p^(k+2)`, written in factored form so its
summability is transparent. -/
noncomputable def higherPowerMajorant (i : HigherPowerIndex) : ℝ :=
  (2 * (i.1 : ℝ)⁻¹ ^ 2) * (i.1 : ℝ)⁻¹ ^ i.2

theorem higherPowerMajorant_eq (i : HigherPowerIndex) :
    higherPowerMajorant i = 2 / (i.1 : ℝ) ^ (i.2 + 2) := by
  rw [higherPowerMajorant, div_eq_mul_inv, inv_pow, pow_add]
  ring

theorem higherPowerMajorant_nonneg (i : HigherPowerIndex) :
    0 ≤ higherPowerMajorant i := by
  unfold higherPowerMajorant
  positivity

private theorem primeInv_le_half (p : Nat.Primes) :
    (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
  rw [inv_le_inv₀ (by exact_mod_cast p.prop.pos) (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast p.prop.two_le

/-- The double series `sum_p sum_(a>=2) 2/p^a` converges. -/
theorem higherPowerMajorant_summable : Summable higherPowerMajorant := by
  have hpNat : Summable (fun n : ℕ ↦ 2 * ((n : ℝ) ^ 2)⁻¹) := by
    exact (Real.summable_nat_pow_inv.mpr (by omega)).mul_left 2
  have hp : Summable (fun p : Nat.Primes ↦ 2 * (p : ℝ)⁻¹ ^ 2) := by
    have h := hpNat.comp_injective (i := fun p : Nat.Primes ↦ (p : ℕ))
      Subtype.val_injective
    simpa [inv_pow] using! h
  have ha : Summable (fun k : ℕ ↦ ((2 : ℝ)⁻¹) ^ k) := by
    exact summable_geometric_of_lt_one (by positivity) (by norm_num)
  have hprod : Summable (fun i : HigherPowerIndex ↦
      (2 * (i.1 : ℝ)⁻¹ ^ 2) * ((2 : ℝ)⁻¹) ^ i.2) :=
    hp.mul_of_nonneg ha (fun _ ↦ by positivity) (fun _ ↦ by positivity)
  refine hprod.of_nonneg_of_le higherPowerMajorant_nonneg ?_
  intro i
  unfold higherPowerMajorant
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (primeInv_le_half i.1) i.2)
    (by positivity)

/-- Tannery/dominated convergence for the exact higher-power majorant.

This is the countable analytic passage needed after the finite bound has been
normalized: each fixed prime/exponent contribution tends to zero, and every
contribution is bounded by `2/p^a`. -/
theorem tendsto_tsum_higherPower_of_dominated
    (f : ℕ → HigherPowerIndex → ℝ)
    (hpoint : ∀ i, Tendsto (fun X ↦ f X i) atTop (𝓝 0))
    (hnonneg : ∀ X i, 0 ≤ f X i)
    (hbound : ∀ X i, f X i ≤ higherPowerMajorant i) :
    Tendsto (fun X ↦ ∑' i, f X i) atTop (𝓝 0) := by
  have hdom : ∀ᶠ X in atTop, ∀ i, ‖f X i‖ ≤ higherPowerMajorant i :=
    Eventually.of_forall fun X i ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg X i)]
      exact hbound X i
  simpa using tendsto_tsum_of_dominated_convergence
    higherPowerMajorant_summable hpoint hdom

/-- Iterated-sum form of `tendsto_tsum_higherPower_of_dominated`. -/
theorem tendsto_iterated_tsum_higherPower_of_dominated
    (f : ℕ → Nat.Primes → ℕ → ℝ)
    (hpoint : ∀ p k, Tendsto (fun X ↦ f X p k) atTop (𝓝 0))
    (hnonneg : ∀ X p k, 0 ≤ f X p k)
    (hbound : ∀ X p k,
      f X p k ≤ higherPowerMajorant (p, k)) :
    Tendsto (fun X ↦ ∑' p : Nat.Primes, ∑' k : ℕ, f X p k)
      atTop (𝓝 0) := by
  let F : ℕ → HigherPowerIndex → ℝ := fun X i ↦ f X i.1 i.2
  have hFsum (X : ℕ) : Summable (F X) := by
    refine higherPowerMajorant_summable.of_nonneg_of_le ?_ ?_
    · intro i
      exact hnonneg X i.1 i.2
    · intro i
      exact hbound X i.1 i.2
  have hlim : Tendsto (fun X ↦ ∑' i, F X i) atTop (𝓝 0) :=
    tendsto_tsum_higherPower_of_dominated F
      (fun i ↦ hpoint i.1 i.2)
      (fun X i ↦ hnonneg X i.1 i.2)
      (fun X i ↦ hbound X i.1 i.2)
  convert hlim using 1
  ext X
  simpa [F] using (hFsum X).tsum_prod.symm

/-! ## The finite box-count error is sublinear -/

/-- The real comparison function for the cube-root/logarithm term tends to
zero after division by its argument. -/
theorem tendsto_rpow_third_mul_logb_div_atTop :
    Tendsto (fun x : ℝ ↦ x ^ (1 / 3 : ℝ) * Real.logb 2 x / x)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ ↦ Real.log x / x ^ (2 / 3 : ℝ))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).tendsto_div_nhds_zero
  have hscaled := hlog.const_mul ((Real.log 2)⁻¹)
  simpa only [mul_zero] using hscaled.congr' (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hrpow : x ^ (1 / 3 : ℝ) / x = 1 / x ^ (2 / 3 : ℝ) := by
      calc
        x ^ (1 / 3 : ℝ) / x =
            x ^ (1 / 3 : ℝ) / x ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = x ^ ((1 / 3 : ℝ) - 1) := (Real.rpow_sub hx _ _).symm
        _ = x ^ (-(2 / 3 : ℝ)) := by norm_num
        _ = 1 / x ^ (2 / 3 : ℝ) := by
          rw [Real.rpow_neg hx.le]
          simp [one_div]
    rw [Real.logb]
    calc
      (Real.log 2)⁻¹ * (Real.log x / x ^ (2 / 3 : ℝ)) =
          (Real.log x / Real.log 2) * (1 / x ^ (2 / 3 : ℝ)) := by ring
      _ = (Real.log x / Real.log 2) * (x ^ (1 / 3 : ℝ) / x) := by rw [hrpow]
      _ = x ^ (1 / 3 : ℝ) * (Real.log x / Real.log 2) / x := by ring)

/-- The exact natural floor cube root is bounded by the corresponding real
power. -/
theorem cubeRootFloor_cast_le_rpow (Z : ℕ) :
    (cubeRootFloor Z : ℝ) ≤ (Z : ℝ) ^ (1 / 3 : ℝ) := by
  rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num,
    Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by norm_num : (0 : ℝ) < 3)]
  exact_mod_cast cubeRootFloor_pow_le Z

/-- The natural square/cube-root/logarithm box bound from (27), divided by
`Z`, tends to zero.  This turns the finite cardinality estimate into the
precise `o(Z)` assertion needed for the `+1` and terminal-prime-power terms. -/
theorem tendsto_higherPrimePower_boxBound_div :
    Tendsto (fun Z : ℕ ↦
      ((Nat.sqrt Z + cubeRootFloor Z * Nat.log 2 Z : ℕ) : ℝ) / (Z : ℝ))
      atTop (𝓝 0) := by
  let comparison : ℕ → ℝ := fun Z ↦
    Real.sqrt (Z : ℝ) / (Z : ℝ) +
      ((Z : ℝ) ^ (1 / 3 : ℝ) * Real.logb 2 (Z : ℝ)) / (Z : ℝ)
  have hsqrt : Tendsto (fun Z : ℕ ↦ Real.sqrt (Z : ℝ) / (Z : ℝ))
      atTop (𝓝 0) := by
    have htop : Tendsto (fun Z : ℕ ↦ Real.sqrt (Z : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa only [Real.sqrt_div_self] using! htop.inv_tendsto_atTop
  have hcubelog : Tendsto (fun Z : ℕ ↦
      ((Z : ℝ) ^ (1 / 3 : ℝ) * Real.logb 2 (Z : ℝ)) / (Z : ℝ))
      atTop (𝓝 0) :=
    tendsto_rpow_third_mul_logb_div_atTop.comp tendsto_natCast_atTop_atTop
  have hcomparison : Tendsto comparison atTop (𝓝 0) := by
    simpa only [comparison, zero_add] using hsqrt.add hcubelog
  apply squeeze_zero' (Eventually.of_forall fun Z ↦ by positivity)
    (Eventually.of_forall fun Z ↦ ?_) hcomparison
  have hsqrtLe : (Nat.sqrt Z : ℝ) ≤ Real.sqrt (Z : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hcubeLe : (cubeRootFloor Z : ℝ) ≤ (Z : ℝ) ^ (1 / 3 : ℝ) :=
    cubeRootFloor_cast_le_rpow Z
  have hlogLe : (Nat.log 2 Z : ℝ) ≤ Real.logb 2 (Z : ℝ) :=
    Real.natLog_le_logb Z 2
  have hcubeLogLe :
      (cubeRootFloor Z : ℝ) * (Nat.log 2 Z : ℝ) ≤
        (Z : ℝ) ^ (1 / 3 : ℝ) * Real.logb 2 (Z : ℝ) := by
    exact mul_le_mul hcubeLe hlogLe (Nat.cast_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hnum :
      (Nat.sqrt Z : ℝ) + (cubeRootFloor Z : ℝ) * (Nat.log 2 Z : ℝ) ≤
        Real.sqrt (Z : ℝ) +
          (Z : ℝ) ^ (1 / 3 : ℝ) * Real.logb 2 (Z : ℝ) :=
    add_le_add hsqrtLe hcubeLogLe
  simpa only [comparison, Nat.cast_add, Nat.cast_mul, add_div] using
    div_le_div_of_nonneg_right hnum (Nat.cast_nonneg Z)

/-- Direct consequence for the actual finite set `M(Z)`. -/
theorem tendsto_higherPrimePowerPairs_card_div :
    Tendsto (fun Z : ℕ ↦ ((higherPrimePowerPairs Z).card : ℝ) / (Z : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun Z ↦ by positivity)
    (Eventually.of_forall fun Z ↦ ?_)
    tendsto_higherPrimePower_boxBound_div
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast higherPrimePowerPairs_card_le Z) (Nat.cast_nonneg Z)

end Erdos730
