/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.ShiftedSmoothBadRoots
import ErdosProblems.Erdos48.PowerSieveParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Prime-chain assembly at the integer power-sieve scale

This file inserts any fixed positive `A / sqrt n` prefix-density estimate
for the literal shifted-smooth bad roots into the weighted
Ford--Konyagin--Luca closure bound.  The small positive FKL exponent and the
fixed coefficient `A` are absorbed by the gap between the power-sieve
endpoint and its smoothness cutoff.
-/

namespace Erdos48

open Filter
open scoped Topology BigOperators

noncomputable section

/-- A fixed FKL exponent small enough for the integer power-sieve scale. -/
noncomputable def powerSievePrimeChainEpsilon (L : ℕ) : ℝ :=
  1 / (480 * (L : ℝ))

/-- The target harmonic mass.  The normalization matches the raw lower
bound delivered by the progression budget and good-root argument. -/
noncomputable def powerSievePrimeChainBudget (n L : ℕ) : ℝ :=
  1 / (960000000000 * (L : ℝ) ^ 4 *
    Real.log (powerSieveX n L : ℝ))

/-- A canonical raw lower function of order `x / (q log x poly(L))`. -/
noncomputable def powerSieveRawLower (n L q : ℕ) : ℝ :=
  (powerSieveX n L : ℝ) /
    (240000000000 * (L : ℝ) ^ 4 * (q : ℝ) *
      Real.log (powerSieveX n L : ℝ))

private theorem eventually_const_mul_log_sq_le_rpow_quarter (D : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      D * Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
  by_cases hD : D ≤ 0
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (mul_nonpos_of_nonpos_of_nonneg hD (sq_nonneg _)).trans
      (Real.rpow_nonneg (by positivity) _)
  · have hDpos : 0 < D := lt_of_not_ge hD
    have hbound :=
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 4)).bound
          (show 0 < (1 / D : ℝ) by positivity)
    have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hbound
    filter_upwards [hnat, eventually_ge_atTop 1] with n hn hn1
    have hlog0 : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn1)
    have hn0 : (0 : ℝ) ≤ n := by positivity
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg
      (Real.rpow_nonneg hn0 _)] at hn
    have := mul_le_mul_of_nonneg_left hn hDpos.le
    field_simp [hDpos.ne'] at this
    simpa [Real.rpow_natCast] using this

private theorem powerSieveSmoothBound_rpow_epsilon_le
    {n L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) :
    (powerSieveSmoothBound n L : ℝ) ^
        powerSievePrimeChainEpsilon L ≤
      (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hexp :
      ((120 * L - 6 : ℕ) : ℝ) * powerSievePrimeChainEpsilon L ≤
        (1 / 4 : ℝ) := by
    have hnat : 120 * L - 6 ≤ 120 * L := Nat.sub_le _ _
    have hcast : (((120 * L - 6 : ℕ) : ℝ)) ≤ 120 * (L : ℝ) := by
      exact_mod_cast hnat
    unfold powerSievePrimeChainEpsilon
    rw [div_eq_mul_inv]
    calc
      ((120 * L - 6 : ℕ) : ℝ) * (1 * (480 * (L : ℝ))⁻¹) ≤
          (120 * (L : ℝ)) * (480 * (L : ℝ))⁻¹ := by
        simp only [one_mul]
        gcongr
      _ = 1 / 4 := by field_simp; ring
  rw [powerSieveSmoothBound, Nat.cast_pow]
  calc
    ((n : ℝ) ^ (120 * L - 6)) ^ powerSievePrimeChainEpsilon L =
        ((n : ℝ) ^ (((120 * L - 6 : ℕ) : ℝ))) ^
          powerSievePrimeChainEpsilon L := by
      rw [Real.rpow_natCast]
    _ = (n : ℝ) ^
        ((((120 * L - 6 : ℕ) : ℝ)) *
          powerSievePrimeChainEpsilon L) := by
      rw [Real.rpow_mul (by positivity)]
    _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnR hexp

private theorem natLog_smoothBound_le
    {n L : ℕ} (hn : 2 ≤ n) :
    (Nat.log 2 (powerSieveSmoothBound n L) : ℝ) ≤
      (((120 * L - 6 : ℕ) : ℝ) * Real.log (n : ℝ)) /
        Real.log 2 := by
  have huPos : (0 : ℝ) < powerSieveSmoothBound n L := by
    exact_mod_cast (pow_pos (by omega : 0 < n) _)
  calc
    (Nat.log 2 (powerSieveSmoothBound n L) : ℝ) ≤
        Real.logb 2 (powerSieveSmoothBound n L : ℝ) :=
      Real.natLog_le_logb _ _
    _ = Real.log (powerSieveSmoothBound n L : ℝ) / Real.log 2 := rfl
    _ = _ := by
      rw [powerSieveSmoothBound, Nat.cast_pow, Real.log_pow]

private theorem log_powerSieveX_eq
    {n L : ℕ} :
    Real.log (powerSieveX n L : ℝ) =
      ((240 * L : ℕ) : ℝ) * Real.log (n : ℝ) := by
  rw [powerSieveX, Nat.cast_pow, Real.log_pow]

/-- Prefix sparsity `A / sqrt n`, for any fixed positive coefficient `A`,
forces the entire bounded prime-chain
closure to have reciprocal mass at most
`1 / (960000000000 L⁴ log(powerSieveX n L))` for all sufficiently
large `n`.

The returned `Q` is the fixed FKL cutoff.  The two eventual hypotheses are
exactly the prefix estimate and the assertion that all literal bad roots
lie above that cutoff. -/
theorem exists_powerSievePrimeChainClosure_eventually_le
    (L : ℕ) (hL : 1 ≤ L) (A : ℝ) (hA : 0 < A)
    (rawLower : ℕ → ℕ → ℝ) :
    ∃ Q : ℕ, ∃ C : ℝ, 0 < C ∧ (
      (∀ᶠ n : ℕ in atTop,
        ∀ q ∈ shiftedSmoothBadRoots (powerSieveX n L)
          (powerSieveSmoothBound n L) (rawLower n), Q < q) →
      (∀ᶠ n : ℕ in atTop, ∀ y : ℕ,
        ((((shiftedSmoothBadRoots (powerSieveX n L)
          (powerSieveSmoothBound n L) (rawLower n)).filter
            fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
          (A / Real.sqrt (n : ℝ)) * y) →
      ∀ᶠ n : ℕ in atTop,
        (∑ t ∈ primeChainClosureTargets (powerSieveSmoothBound n L)
          (shiftedSmoothBadRoots (powerSieveX n L)
            (powerSieveSmoothBound n L) (rawLower n)), (t : ℝ)⁻¹) ≤
          powerSievePrimeChainBudget n L) := by
  have heps : 0 < powerSievePrimeChainEpsilon L := by
    unfold powerSievePrimeChainEpsilon
    positivity
  obtain ⟨Q, C, hC, hclosure⟩ :=
    exists_primeChainClosureTargets_harmonic_bound_of_prefix_sparse heps
  refine ⟨Q, C, hC, ?_⟩
  intro hlarge hprefix
  let D : ℝ :=
    2 * A * C * (120 * (L : ℝ)) * (240 * (L : ℝ)) *
      (Real.log 2)⁻¹ * (960000000000 * (L : ℝ) ^ 4)
  have hdecay := eventually_const_mul_log_sq_le_rpow_quarter D
  filter_upwards [hlarge, hprefix, hdecay, eventually_ge_atTop 2]
      with n hnLarge hnPrefix hnDecay hn
  let x := powerSieveX n L
  let u := powerSieveSmoothBound n L
  let E := shiftedSmoothBadRoots x u (rawLower n)
  let eps := powerSievePrimeChainEpsilon L
  have hraw := hclosure E u (A / Real.sqrt (n : ℝ))
    (fun q hq ↦ ⟨(shiftedSmoothBadRoots_prime_bound hq).1,
      hnLarge q hq, (shiftedSmoothBadRoots_prime_bound hq).2⟩)
    hnPrefix
  have huEps : (u : ℝ) ^ eps ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    simpa only [u, eps] using
      powerSieveSmoothBound_rpow_epsilon_le (by omega : 1 ≤ n) hL
  have hlogu := natLog_smoothBound_le (L := L) hn
  have hlogx : Real.log (x : ℝ) =
      (240 * (L : ℝ)) * Real.log (n : ℝ) := by
    simpa only [x, Nat.cast_mul, Nat.cast_ofNat] using
      log_powerSieveX_eq (n := n) (L := L)
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogxPos : 0 < Real.log (x : ℝ) := by
    rw [hlogx]
    positivity
  have hsqrt : Real.sqrt (n : ℝ) =
      (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hquarterPos : 0 < (n : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hsqrtEq : Real.sqrt (n : ℝ) =
      ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
    calc
      Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := hsqrt
      _ = (n : ℝ) ^ ((1 / 4 : ℝ) * (2 : ℝ)) := by norm_num
      _ = ((n : ℝ) ^ (1 / 4 : ℝ)) ^ (2 : ℝ) := by
        rw [Real.rpow_mul (by positivity)]
      _ = ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 :=
        Real.rpow_natCast _ 2
  have hbudget :
      C * (u : ℝ) ^ eps *
          ((Nat.log 2 u : ℝ) * (2 * (A / Real.sqrt (n : ℝ)))) ≤
        powerSievePrimeChainBudget n L := by
    rw [powerSievePrimeChainBudget]
    rw [show Real.log (powerSieveX n L : ℝ) = Real.log (x : ℝ) by rfl]
    have hscalePos : 0 < 960000000000 * (L : ℝ) ^ 4 := by positivity
    rw [show 1 / (960000000000 * (L : ℝ) ^ 4 * Real.log (x : ℝ)) =
        (1 / (960000000000 * (L : ℝ) ^ 4)) / Real.log (x : ℝ) by
      field_simp [hscalePos.ne', hlogxPos.ne']]
    rw [le_div_iff₀ hlogxPos]
    calc
      C * (u : ℝ) ^ eps *
            ((Nat.log 2 u : ℝ) * (2 * (A / Real.sqrt (n : ℝ)))) *
          Real.log (x : ℝ) ≤
        C * (n : ℝ) ^ (1 / 4 : ℝ) *
            ((((120 * L - 6 : ℕ) : ℝ) * Real.log (n : ℝ)) /
              Real.log 2 * (2 * (A / Real.sqrt (n : ℝ)))) *
          ((240 * (L : ℝ)) * Real.log (n : ℝ)) := by
        rw [hlogx]
        gcongr
      _ ≤
          D * Real.log (n : ℝ) ^ 2 *
            ((n : ℝ) ^ (1 / 4 : ℝ) *
              (Real.sqrt (n : ℝ))⁻¹) /
                (960000000000 * (L : ℝ) ^ 4) := by
        have hk : (((120 * L - 6 : ℕ) : ℝ)) ≤
            120 * (L : ℝ) := by
          exact_mod_cast (Nat.sub_le (120 * L) 6)
        let F : ℝ :=
          2 * A * C * (240 * (L : ℝ)) * (Real.log 2)⁻¹ *
            Real.log (n : ℝ) ^ 2 * (n : ℝ) ^ (1 / 4 : ℝ) *
              (Real.sqrt (n : ℝ))⁻¹
        calc
          C * (n : ℝ) ^ (1 / 4 : ℝ) *
                ((((120 * L - 6 : ℕ) : ℝ) * Real.log (n : ℝ)) /
                  Real.log 2 * (2 * (A / Real.sqrt (n : ℝ)))) *
              ((240 * (L : ℝ)) * Real.log (n : ℝ)) =
              (((120 * L - 6 : ℕ) : ℝ)) * F := by
            dsimp [F]
            rw [div_eq_mul_inv]
            ring
          _ ≤ (120 * (L : ℝ)) * F := by
            apply mul_le_mul_of_nonneg_right hk
            dsimp [F]
            positivity
          _ = D * Real.log (n : ℝ) ^ 2 *
                ((n : ℝ) ^ (1 / 4 : ℝ) *
                  (Real.sqrt (n : ℝ))⁻¹) /
                    (960000000000 * (L : ℝ) ^ 4) := by
            dsimp [F, D]
            field_simp [hscalePos.ne']
      _ = D * Real.log (n : ℝ) ^ 2 *
            ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹ /
              (960000000000 * (L : ℝ) ^ 4) := by
        rw [hsqrtEq, pow_two]
        field_simp [hquarterPos.ne']
      _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) *
            ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹ /
              (960000000000 * (L : ℝ) ^ 4) := by gcongr
      _ = 1 / (960000000000 * (L : ℝ) ^ 4) := by
        rw [mul_inv_cancel₀ hquarterPos.ne']
  exact hraw.trans hbudget

/-- Final finite constructor.  The two numerical hypotheses are the
elementary root-`2` and uniform-root inequalities, written against the
canonical raw lower function.  A larger application-specific raw lower
function may be supplied through `hraw`. -/
noncomputable def FLPAnalyticScale.of_powerSievePrimeChainAssembly
    {K n L : ℕ} {rawLower : ℕ → ℝ}
    (hL : 1 ≤ L)
    (hu : 2 ≤ powerSieveSmoothBound n L)
    (htwo : 2 ∉ shiftedSmoothBadRoots (powerSieveX n L)
      (powerSieveSmoothBound n L) rawLower)
    (hmass :
      (∑ t ∈ primeChainClosureTargets (powerSieveSmoothBound n L)
        (shiftedSmoothBadRoots (powerSieveX n L)
          (powerSieveSmoothBound n L) rawLower), (t : ℝ)⁻¹) ≤
        powerSievePrimeChainBudget n L)
    (hraw : ∀ q : ℕ, q.Prime → q ≤ powerSieveSmoothBound n L →
      powerSieveRawLower n L q ≤ rawLower q)
    (hcard :
      (K : ℝ) + ((powerSieveX n L + 1 : ℕ) : ℝ) / 2 *
          powerSievePrimeChainBudget n L ≤
        powerSieveRawLower n L 2)
    (hcounts : ∀ q : ℕ, q.Prime →
      q ∉ primeChainClosure
        (shiftedSmoothBadRoots (powerSieveX n L)
          (powerSieveSmoothBound n L) rawLower : Set ℕ) →
      q ≤ powerSieveSmoothBound n L →
      (((powerSieveSmoothBound n L) / (q - 1) + 1 : ℕ) : ℝ) +
          ((powerSieveX n L + 1 : ℕ) : ℝ) / q *
            powerSievePrimeChainBudget n L ≤
        powerSieveRawLower n L q) :
    FLPAnalyticScale K := by
  apply FLPAnalyticScale.of_badRoot_harmonic_bound hu htwo hmass
  · exact hcard.trans (hraw 2 Nat.prime_two (by omega))
  · intro q hq hqClosure hqu
    exact (hcounts q hq hqClosure hqu).trans (hraw q hq hqu)

end

end Erdos48
