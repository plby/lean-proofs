/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.ResidualDyadicAbsorption

/-!
# Absorption of the residual-fibre distribution error

The endpoint loss left by `ResidualDyadicAbsorption` is killed by choosing
the logarithmic saving exponent `100`.  On the exact dyadic ray, the proof
reduces to the elementary comparison

`constant * 2^(3r) <= 2^(97r) * (log 2 / 2)^100`.

All statements in this file are unconditional finite inequalities or
ordinary eventual consequences of powers tending to infinity.
-/

namespace Erdos4b
namespace SmoothParameters

noncomputable section

open Filter Real
open scoped BigOperators Topology

/-- Twice the ray parameter is no larger than the primary exponent. -/
theorem two_mul_self_le_primaryExponent (a r : ℕ) :
    2 * r ≤ primaryExponent a r := by
  have hpow : 2 * r ≤ 2 ^ (2 * r) :=
    Nat.le_of_lt (2 * r).lt_two_pow_self
  have ha : 2 * r ≤ a + 2 * r := by omega
  have hpow' : 2 ^ (2 * r) ≤ 2 ^ (a + 2 * r) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) ha
  have hfactor : 1 ≤ core r := Nat.one_le_iff_ne_zero.mpr (core_pos r).ne'
  calc
    2 * r ≤ 2 ^ (2 * r) := hpow
    _ ≤ 2 ^ (a + 2 * r) := hpow'
    _ ≤ 2 ^ (a + 2 * r) * core r :=
      Nat.le_mul_of_pos_right _ (core_pos r)
    _ = primaryExponent a r := by rw [primaryExponent]

/-- The logarithm of the residual-prime frontier retains at least half of
the full primary exponent. -/
theorem half_primaryExponent_mul_log_two_le_log_residualPrimeFrontier
    (a r : ℕ) :
    ((primaryExponent a r : ℝ) / 2) * Real.log 2 ≤
      Real.log (residualPrimeFrontier a r : ℝ) := by
  rw [log_residualPrimeFrontier]
  have hrK : r ≤ primaryExponent a r := by
    have htwo := two_mul_self_le_primaryExponent a r
    omega
  have htwo : (2 : ℝ) * r ≤ primaryExponent a r := by
    exact_mod_cast two_mul_self_le_primaryExponent a r
  have hsub :
      (primaryExponent a r : ℝ) / 2 ≤
        ((primaryExponent a r - r : ℕ) : ℝ) := by
    rw [Nat.cast_sub hrK]
    linarith
  exact mul_le_mul_of_nonneg_right hsub (Real.log_nonneg (by norm_num))

/-- The elementary fixed-constant comparison used to absorb the
Bombieri--Vinogradov endpoints. -/
theorem eventually_residualError_constant_comparison
    (CBV : ℝ) (hCBV : 0 ≤ CBV) :
    ∀ᶠ r : ℕ in atTop,
      2 * CBV * (2 : ℝ) ^ r * (r : ℝ) ^ 2 ≤
        (core r : ℝ) ^ 97 * (Real.log 2 / 2) ^ 100 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let c : ℝ := 2 * CBV / (Real.log 2 / 2) ^ 100
  have hbase : (1 : ℝ) < (2 : ℝ) ^ 94 := by norm_num
  have hgrow : Tendsto (fun r : ℕ ↦ ((2 : ℝ) ^ 94) ^ r)
      atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hbase
  have hconst : ∀ᶠ r : ℕ in atTop,
      c ≤ ((2 : ℝ) ^ 94) ^ r :=
    hgrow.eventually_ge_atTop c
  filter_upwards [hconst, eventually_ge_atTop 1] with r hcr hr
  have hrpow : (r : ℝ) ≤ (2 : ℝ) ^ r := by
    exact_mod_cast Nat.le_of_lt r.lt_two_pow_self
  have hcore : (2 : ℝ) ^ r ≤ core r := by
    exact_mod_cast pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ))
      (Nat.le_of_lt r.lt_two_pow_self)
  have hlogpow : 0 < (Real.log 2 / 2) ^ (100 : ℕ) := by positivity
  have hcform :
      2 * CBV ≤ ((2 : ℝ) ^ 94) ^ r *
          (Real.log 2 / 2) ^ 100 := by
    dsimp [c] at hcr
    exact (div_le_iff₀ hlogpow).mp hcr
  have hthree :
      (2 : ℝ) ^ r * ((2 : ℝ) ^ r) ^ 2 = ((2 : ℝ) ^ 3) ^ r := by
    rw [← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    omega
  have hninetySeven :
      ((2 : ℝ) ^ 94) ^ r * ((2 : ℝ) ^ 3) ^ r =
        ((2 : ℝ) ^ r) ^ 97 := by
    simp only [← pow_mul, ← pow_add]
    congr 1
    omega
  calc
    2 * CBV * (2 : ℝ) ^ r * (r : ℝ) ^ 2 ≤
        2 * CBV * (2 : ℝ) ^ r * ((2 : ℝ) ^ r) ^ 2 := by
      gcongr
    _ = 2 * CBV * ((2 : ℝ) ^ 3) ^ r := by
      rw [show 2 * CBV * (2 : ℝ) ^ r * ((2 : ℝ) ^ r) ^ 2 =
          2 * CBV * ((2 : ℝ) ^ r * ((2 : ℝ) ^ r) ^ 2) by ring]
      rw [hthree]
    _ ≤ (((2 : ℝ) ^ 94) ^ r *
          (Real.log 2 / 2) ^ 100) * ((2 : ℝ) ^ 3) ^ r := by
      exact mul_le_mul_of_nonneg_right hcform (by positivity)
    _ = ((2 : ℝ) ^ r) ^ 97 * (Real.log 2 / 2) ^ 100 := by
      rw [show ((2 : ℝ) ^ 94) ^ r * (Real.log 2 / 2) ^ 100 *
          ((2 : ℝ) ^ 3) ^ r =
          (((2 : ℝ) ^ 94) ^ r * ((2 : ℝ) ^ 3) ^ r) *
            (Real.log 2 / 2) ^ 100 by ring]
      rw [hninetySeven]
    _ ≤ (core r : ℝ) ^ 97 * (Real.log 2 / 2) ^ 100 := by
      gcongr

/-- With saving exponent `100`, the complete residual-fibre distribution
error is eventually no larger than the canonical `X / K` fresh-prime
budget. -/
theorem eventually_residualPrimeFiber_bvError_le_primary_div
    (a : ℕ) (CBV : ℝ) (hCBV : 0 ≤ CBV) :
    ∀ᶠ r : ℕ in atTop,
      (fullResidualCofactorCutoff r : ℝ) *
          (CBV * (intervalLength a r : ℝ) /
              Real.rpow (Real.log (residualPrimeFrontier a r : ℝ)) 100 +
            CBV * (residualPrimeFrontier a r : ℝ) /
              Real.rpow (Real.log (residualPrimeFrontier a r : ℝ)) 100) ≤
        (primaryFrontier a r : ℝ) / primaryExponent a r := by
  filter_upwards
    [eventually_residualError_constant_comparison CBV hCBV,
      eventually_ge_atTop 1]
    with r hconstant hr
  let K : ℕ := primaryExponent a r
  let X : ℕ := primaryFrontier a r
  let V : ℕ := core r
  let U : ℕ := intervalLength a r
  let z : ℕ := residualPrimeFrontier a r
  let Bco : ℕ := fullResidualCofactorCutoff r
  let L : ℝ := Real.log (z : ℝ)
  have hK : 0 < K := by simpa [K] using primaryExponent_pos a r
  have hX : 0 < X := by simpa [X] using primaryFrontier_pos a r
  have hV : 0 < V := by simpa [V] using core_pos r
  have hU : 0 < U := by simpa [U] using intervalLength_pos hr
  have hz : 0 < z := by simpa [z] using residualPrimeFrontier_pos a r
  have hBco : 0 < Bco := by
    dsimp [Bco, fullResidualCofactorCutoff]
    positivity
  have hL : 0 < L := by
    dsimp [L, z]
    exact Real.log_pos (by exact_mod_cast residualPrimeFrontier_one_lt a r)
  have hzU : z ≤ U := by
    dsimp [z, U]
    rw [intervalLength_eq_residualPrimeFrontier_mul_cutoff]
    exact Nat.le_mul_of_pos_right _ (by
      dsimp [fullResidualCofactorCutoff]
      positivity)
  have hLlower : ((K : ℝ) / 2) * Real.log 2 ≤ L := by
    simpa [K, L, z] using
      half_primaryExponent_mul_log_two_le_log_residualPrimeFrontier a r
  have hbaseNonneg : 0 ≤ ((K : ℝ) / 2) * Real.log 2 := by positivity
  have hpowLower :
      (((K : ℝ) / 2) * Real.log 2) ^ 100 ≤ L ^ 100 :=
    pow_le_pow_left₀ hbaseNonneg hLlower 100
  have hrpow : Real.rpow L 100 = L ^ (100 : ℕ) := by
    rw [← Real.rpow_natCast]
    norm_num
  have hden : 0 < L ^ (100 : ℕ) := pow_pos hL _
  have hdenLower : 0 < (((K : ℝ) / 2) * Real.log 2) ^ (100 : ℕ) := by
    positivity
  have hUeq : (U : ℝ) = (X : ℝ) * (V : ℝ) * r := by
    simp [U, X, V, intervalLength]
  have hBcoEq : (Bco : ℝ) = (2 : ℝ) ^ r * (V : ℝ) * r := by
    simp [Bco, V, fullResidualCofactorCutoff]
  have hKEq : (K : ℝ) = (2 : ℝ) ^ (a + 2 * r) * (V : ℝ) := by
    simp [K, V, primaryExponent]
  have hVleK : (V : ℝ) ≤ K := by
    rw [hKEq]
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (a + 2 * r) := by
      exact one_le_pow₀ (by norm_num)
    nlinarith [show (0 : ℝ) < V by exact_mod_cast hV]
  have hnumeric :
      2 * CBV * (Bco : ℝ) * (V : ℝ) * r * (K : ℝ) ≤
        (((K : ℝ) / 2) * Real.log 2) ^ 100 := by
    have hconstant' :
        2 * CBV * (2 : ℝ) ^ r * (r : ℝ) ^ 2 ≤
          (V : ℝ) ^ 97 * (Real.log 2 / 2) ^ 100 := by
      simpa [V] using hconstant
    have hmul := mul_le_mul_of_nonneg_right hconstant'
      (show 0 ≤ (V : ℝ) * (K : ℝ) by positivity)
    calc
      2 * CBV * (Bco : ℝ) * (V : ℝ) * r * (K : ℝ) =
          (2 * CBV * (2 : ℝ) ^ r * (r : ℝ) ^ 2) *
            ((V : ℝ) ^ 2 * (K : ℝ)) := by rw [hBcoEq]; ring
      _ ≤ ((V : ℝ) ^ 97 * (Real.log 2 / 2) ^ 100) *
          ((V : ℝ) ^ 2 * (K : ℝ)) := by gcongr
      _ ≤ (K : ℝ) ^ 100 * (Real.log 2 / 2) ^ 100 := by
        have hVK : (V : ℝ) ^ 99 * (K : ℝ) ≤ (K : ℝ) ^ 100 := by
          calc
            (V : ℝ) ^ 99 * (K : ℝ) ≤
                (K : ℝ) ^ 99 * (K : ℝ) := by gcongr
            _ = (K : ℝ) ^ 100 := by ring
        calc
          ((V : ℝ) ^ 97 * (Real.log 2 / 2) ^ 100) *
              ((V : ℝ) ^ 2 * (K : ℝ)) =
              ((V : ℝ) ^ 99 * (K : ℝ)) *
                (Real.log 2 / 2) ^ 100 := by ring
          _ ≤ (K : ℝ) ^ 100 * (Real.log 2 / 2) ^ 100 := by gcongr
      _ = (((K : ℝ) / 2) * Real.log 2) ^ 100 := by ring
  have hscaled :
      2 * (Bco : ℝ) * CBV * (U : ℝ) * (K : ℝ) ≤
        (X : ℝ) * L ^ 100 := by
    rw [hUeq]
    calc
      2 * (Bco : ℝ) * CBV * ((X : ℝ) * (V : ℝ) * r) *
          (K : ℝ) =
          (X : ℝ) *
            (2 * CBV * (Bco : ℝ) * (V : ℝ) * r * (K : ℝ)) := by
        ring
      _ ≤ (X : ℝ) *
          (((K : ℝ) / 2) * Real.log 2) ^ 100 := by gcongr
      _ ≤ (X : ℝ) * L ^ 100 := by gcongr
  rw [show Real.rpow (Real.log (residualPrimeFrontier a r : ℝ)) 100 =
      L ^ (100 : ℕ) by simpa [L, z] using hrpow]
  have hzUR : (z : ℝ) ≤ U := by exact_mod_cast hzU
  have hsum :
      CBV * (U : ℝ) / L ^ 100 + CBV * (z : ℝ) / L ^ 100 ≤
        2 * CBV * (U : ℝ) / L ^ 100 := by
    have hzterm : CBV * (z : ℝ) ≤ CBV * (U : ℝ) :=
      mul_le_mul_of_nonneg_left hzUR hCBV
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hden.le
    nlinarith
  calc
    (Bco : ℝ) *
        (CBV * (U : ℝ) / L ^ 100 + CBV * (z : ℝ) / L ^ 100) ≤
        (Bco : ℝ) * (2 * CBV * (U : ℝ) / L ^ 100) := by
      gcongr
    _ ≤ (X : ℝ) / K := by
      rw [show (Bco : ℝ) * (2 * CBV * (U : ℝ) / L ^ 100) =
          (2 * (Bco : ℝ) * CBV * (U : ℝ)) / L ^ 100 by ring]
      rw [div_le_div_iff₀ hden (by exact_mod_cast hK)]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
    _ = (primaryFrontier a r : ℝ) / primaryExponent a r := rfl

end

end SmoothParameters
end Erdos4b
