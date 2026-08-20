/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveParameters

/-!
# The good-root output of the integer-power sieve

This file specializes the finite auxiliary-prime argument to the integer-power
parameters in `PowerSieveParameters`.  The represented-large-factor estimate is
kept behind an explicit pointwise majorant: this is the exact analytic estimate
which remains to be discharged when the beta-sieve constants are chosen.
-/

namespace Erdos48

open Filter
open scoped Topology BigOperators

noncomputable section

/-- At the power-sieve endpoint, the main scale is the `(240*L)`-th power of
the basic auxiliary scale. -/
theorem powerSieveX_eq_auxScale_pow (n L : ℕ) :
    powerSieveX n L = (powerSieveAuxScale n L) ^ (240 * L) := by
  rfl

/-- The lower endpoint of the auxiliary interval is large enough that a
shifted prime at most `powerSieveX` has at most `240*L` auxiliary divisors.
This is the numerical multiplicity inequality consumed by
`AuxiliaryCounting`. -/
theorem powerSieveX_add_one_lt_auxLower_pow
    {n L Q : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L) :
    powerSieveX n L + 1 <
      (powerSieveAuxLower n L Q + 1) ^ (240 * L + 1) := by
  let A := powerSieveAuxScale n L
  let R := powerSieveAuxLower n L Q + 1
  have hA : 2 ≤ A := by
    dsimp [A, powerSieveAuxScale]
    exact hn
  have hcoreA : A ≤ powerSieveAuxCore n L Q := by
    exact le_max_right _ _
  have hAR : A ≤ R := by
    dsimp [R, powerSieveAuxLower]
    omega
  have htwoR : 2 ≤ R := hA.trans hAR
  have hpowPos : 1 < A ^ (240 * L) := by
    exact one_lt_pow₀ (by omega) (by omega)
  have hpowLe : A ^ (240 * L) ≤ R ^ (240 * L) :=
    Nat.pow_le_pow_left hAR (240 * L)
  have hdouble : A ^ (240 * L) + 1 < 2 * A ^ (240 * L) := by omega
  have hscale : 2 * A ^ (240 * L) ≤ R * R ^ (240 * L) :=
    Nat.mul_le_mul htwoR hpowLe
  rw [powerSieveX_eq_auxScale_pow]
  change A ^ (240 * L) + 1 < R ^ (240 * L + 1)
  calc
    A ^ (240 * L) + 1 < 2 * A ^ (240 * L) := hdouble
    _ ≤ R * R ^ (240 * L) := hscale
    _ = R ^ (240 * L + 1) := by
      simpa only [Nat.succ_eq_add_one] using
        (Nat.pow_succ' (m := R) (n := 240 * L)).symm

/-- The endpoint expression which lower-bounds the cardinality of primes in
the progression `-1 mod q*r` after the three endpoint masses are controlled.
-/
def powerSieveProgressionBudget (x q r : ℕ) : ℝ :=
  (Chebyshev.theta (x : ℝ) / ((q * r).totient : ℝ) -
      (Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 +
        ((q * r).totient : ℝ)⁻¹ * (4 * ((x : ℝ) / 10)) +
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)))) /
        Real.log (x : ℝ)

/-- A pointwise majorant for the represented-large-factor exceptional set,
together with the remaining numerical room in the progression, supplies the
exact numerical premise of the finite good-root argument. -/
theorem represented_add_weight_le_powerSieveProgressionBudget
    {n L Q q B : ℕ} {W : ℝ} {E : ℕ → ℝ}
    (hrepresented : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) ≤ E r)
    (hroom : ∀ r ∈ powerSieveAuxPrimes n L Q,
      E r + W * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r) :
    ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
          W * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r := by
  intro r hr
  exact (add_le_add_left (hrepresented r hr) _).trans (hroom r hr)

/-- Version of the endpoint-good auxiliary bridge in which distinctness of
the root and auxiliary prime is stated directly.  The older range hypothesis
`q ≤ R0 < r` was only used to establish this distinctness; stating it directly
allows the same argument when root and auxiliary ranges overlap. -/
theorem mul_sum_inv_le_mul_card_smoothShiftedFiber_of_endpoint_good_of_ne
    {x u q B D R0 : ℕ} {R : Finset ℕ} {W : ℝ}
    (hx : 2 ≤ x) (hW : 0 ≤ W)
    (hq : q.Prime)
    (hprime : ∀ r ∈ R, r.Prime)
    (hqu : q ≤ u)
    (hru : ∀ r ∈ R, r ≤ u)
    (hlower : ∀ r ∈ R, R0 < r)
    (hpow : x + 1 < (R0 + 1) ^ (D + 1))
    (hqNe : ∀ r ∈ R, q ≠ r)
    (hqGood : primitiveEndpointMass x q ≤ (x : ℝ) / 10)
    (hrGood : ∀ r ∈ R,
      primitiveEndpointMass x r ≤ (x : ℝ) / 10)
    (hqrGood : ∀ r ∈ R,
      primitiveEndpointMass x (q * r) ≤ (x : ℝ) / 10)
    (hcofactor : ∀ r ∈ R,
      ∀ p ∈ primesInProgression x (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → u < s → s ∣ p + 1 →
          (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ r ∈ R,
      ((representedLargeFactorPrimes x u q r B).card : ℝ) +
          W * (r : ℝ)⁻¹ ≤
        (Chebyshev.theta (x : ℝ) / ((q * r).totient : ℝ) -
          (Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 +
            ((q * r).totient : ℝ)⁻¹ * (4 * ((x : ℝ) / 10)) +
              (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)))) /
            Real.log (x : ℝ)) :
    W * ∑ r ∈ R, (r : ℝ)⁻¹ ≤
      (D : ℝ) *
        (((smoothShiftedPrimes x u).filter
          fun p ↦ q ∣ p + 1).card : ℝ) := by
  apply mul_sum_inv_le_mul_card_smoothShiftedFiber_of_progression
    hW hq hprime hqu hru hlower hpow hcofactor
  intro r hr
  exact represented_add_weight_le_progression_card_of_endpoint_good
    hx hq (hprime r hr) (hqNe r hr) hqGood
      (hrGood r hr) (hqrGood r hr) (hnumeric r hr)

/-- Remove the root itself from the auxiliary-prime set.  This is the natural
auxiliary family when the dyadic root block overlaps the auxiliary interval.
-/
def powerSieveAuxPrimesAway (n L Q q : ℕ) : Finset ℕ :=
  (powerSieveAuxPrimes n L Q).erase q

@[simp] theorem mem_powerSieveAuxPrimesAway
    {n L Q q r : ℕ} :
    r ∈ powerSieveAuxPrimesAway n L Q q ↔
      r ∈ powerSieveAuxPrimes n L Q ∧ r ≠ q := by
  simp only [powerSieveAuxPrimesAway, Finset.mem_erase]
  tauto

/-- Erasing one root costs at most its reciprocal from the auxiliary mass. -/
theorem sum_inv_powerSieveAuxPrimes_le_root_add_away
    (n L Q q : ℕ) :
    (∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹) ≤
      (q : ℝ)⁻¹ +
        ∑ r ∈ powerSieveAuxPrimesAway n L Q q, (r : ℝ)⁻¹ := by
  classical
  by_cases hq : q ∈ powerSieveAuxPrimes n L Q
  · rw [powerSieveAuxPrimesAway,
      ← Finset.sum_erase_add _ _ hq]
    exact le_of_eq (add_comm _ _)
  · simp only [powerSieveAuxPrimesAway, Finset.erase_eq_of_notMem hq,
      le_add_iff_nonneg_left]
    positivity

/-- If `q ≥ 1000L`, erasing the root leaves half of the uniform
`1/(500L)` auxiliary reciprocal mass. -/
theorem one_div_thousand_le_sum_inv_powerSieveAuxPrimesAway
    {n L Q q : ℕ} (hL : 1 ≤ L) (hq : 1000 * L ≤ q)
    (hmass : (1 / (500 * (L : ℝ)) : ℝ) ≤
      ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹) :
    (1 / (1000 * (L : ℝ)) : ℝ) ≤
      ∑ r ∈ powerSieveAuxPrimesAway n L Q q, (r : ℝ)⁻¹ := by
  have hqInv : (q : ℝ)⁻¹ ≤ (1 / (1000 * (L : ℝ)) : ℝ) := by
    have hcast : (1000 : ℝ) * (L : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hq
    calc
      (q : ℝ)⁻¹ ≤ ((1000 : ℝ) * (L : ℝ))⁻¹ :=
        inv_anti₀ (by positivity) hcast
      _ = 1 / (1000 * (L : ℝ)) := by rw [one_div]
  have hsplit := sum_inv_powerSieveAuxPrimes_le_root_add_away n L Q q
  have hscale :
      (1 / (500 * (L : ℝ)) : ℝ) =
        2 * (1 / (1000 * (L : ℝ)) : ℝ) := by
    have hL0 : (L : ℝ) ≠ 0 := by positivity
    field_simp
    norm_num
  linarith

/-- Exact reciprocal-mass form, with no lower bound on the root: removing the
root costs at most `1/q`. -/
theorem sub_inv_le_sum_inv_powerSieveAuxPrimesAway
    {n L Q q : ℕ}
    (hmass : (1 / (500 * (L : ℝ)) : ℝ) ≤
      ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹) :
    (1 / (500 * (L : ℝ)) : ℝ) - (q : ℝ)⁻¹ ≤
      ∑ r ∈ powerSieveAuxPrimesAway n L Q q, (r : ℝ)⁻¹ := by
  have hsplit := sum_inv_powerSieveAuxPrimes_le_root_add_away n L Q q
  linarith

/-- Eventual reciprocal mass after deleting a root `q ≥ 1000L`, uniformly
in the block parameter. -/
theorem eventually_one_div_thousand_le_sum_inv_powerSieveAuxPrimesAway
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q → ∀ q : ℕ,
      1000 * L ≤ q →
      (1 / (1000 * (L : ℝ)) : ℝ) ≤
        ∑ r ∈ powerSieveAuxPrimesAway n L Q q, (r : ℝ)⁻¹ := by
  filter_upwards [eventually_powerSieveAuxPrimes_reciprocal_lower L hL]
    with n hmass Q hQ q hq
  exact one_div_thousand_le_sum_inv_powerSieveAuxPrimesAway
    hL hq (hmass Q hQ)

/-- The power-parameter specialization of the finite auxiliary-prime bridge.
The endpoint hypotheses are precisely those needed for the divisors `q`, `r`,
and `q*r`; `hnumeric` is the remaining represented-large-factor budget. -/
theorem mul_sum_inv_powerSieveAuxPrimesAway_le_mul_card_goodRoot
    {n L Q q B : ℕ} {W : ℝ}
    (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hW : 0 ≤ W)
    (hq : q.Prime)
    (hqu : q ≤ powerSieveSmoothBound n L)
    (hqGood : primitiveEndpointMass (powerSieveX n L) q ≤
      (powerSieveX n L : ℝ) / 10)
    (hrGood : ∀ r ∈ powerSieveAuxPrimes n L Q,
      primitiveEndpointMass (powerSieveX n L) r ≤
        (powerSieveX n L : ℝ) / 10)
    (hqrGood : ∀ r ∈ powerSieveAuxPrimes n L Q,
      primitiveEndpointMass (powerSieveX n L) (q * r) ≤
        (powerSieveX n L : ℝ) / 10)
    (hcofactor : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ∀ p ∈ primesInProgression
        (powerSieveX n L) (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
          s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
          W * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r) :
    W * ∑ r ∈ powerSieveAuxPrimesAway n L Q q, (r : ℝ)⁻¹ ≤
      ((240 * L : ℕ) : ℝ) *
        (((smoothShiftedPrimes
          (powerSieveX n L) (powerSieveSmoothBound n L)).filter
            fun p ↦ q ∣ p + 1).card : ℝ) := by
  apply mul_sum_inv_le_mul_card_smoothShiftedFiber_of_endpoint_good_of_ne
    (x := powerSieveX n L) (u := powerSieveSmoothBound n L)
    (q := q) (B := B) (D := 240 * L)
    (R0 := powerSieveAuxLower n L Q)
    (R := powerSieveAuxPrimesAway n L Q q) (W := W)
  · rw [powerSieveX_eq_auxScale_pow]
    have hscale : 2 ≤ powerSieveAuxScale n L := by
      dsimp [powerSieveAuxScale]
      exact hn
    exact hscale.trans (Nat.le_pow (by omega : 0 < 240 * L))
  · exact hW
  · exact hq
  · intro r hr
    exact (mem_powerSieveAuxPrimes.mp
      (mem_powerSieveAuxPrimesAway.mp hr).1).2.2
  · exact hqu
  · intro r hr
    exact (mem_powerSieveAuxPrimes.mp
      (mem_powerSieveAuxPrimesAway.mp hr).1).2.1.trans
      (powerSieveAuxUpper_le_smoothBound
        (show 1 ≤ n by omega) hL hQ)
  · intro r hr
    exact (mem_powerSieveAuxPrimes.mp
      (mem_powerSieveAuxPrimesAway.mp hr).1).1
  · simpa only using
      (powerSieveX_add_one_lt_auxLower_pow (Q := Q) hn hL)
  · intro r hr
    exact (mem_powerSieveAuxPrimesAway.mp hr).2.symm
  · exact hqGood
  · intro r hr
    exact hrGood r (mem_powerSieveAuxPrimesAway.mp hr).1
  · intro r hr
    exact hqrGood r (mem_powerSieveAuxPrimesAway.mp hr).1
  · intro r hr
    exact hcofactor r (mem_powerSieveAuxPrimesAway.mp hr).1
  · intro r hr
    simpa only [powerSieveProgressionBudget] using
      hnumeric r (mem_powerSieveAuxPrimesAway.mp hr).1

/-- Exact good-root cardinality lower bound.  It records the possible loss of
the single auxiliary prime equal to the root rather than imposing artificial
separation between the root and auxiliary ranges. -/
theorem mul_sub_inv_div_le_card_goodRoot_of_reciprocal_lower
    {n L Q q B : ℕ} {W : ℝ}
    (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hW : 0 ≤ W)
    (hmass : (1 / (500 * (L : ℝ)) : ℝ) ≤
      ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹)
    (hq : q.Prime)
    (hqu : q ≤ powerSieveSmoothBound n L)
    (hqGood : primitiveEndpointMass (powerSieveX n L) q ≤
      (powerSieveX n L : ℝ) / 10)
    (hrGood : ∀ r ∈ powerSieveAuxPrimes n L Q,
      primitiveEndpointMass (powerSieveX n L) r ≤
        (powerSieveX n L : ℝ) / 10)
    (hqrGood : ∀ r ∈ powerSieveAuxPrimes n L Q,
      primitiveEndpointMass (powerSieveX n L) (q * r) ≤
        (powerSieveX n L : ℝ) / 10)
    (hcofactor : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ∀ p ∈ primesInProgression
        (powerSieveX n L) (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
          s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
          W * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r) :
    W * ((1 / (500 * (L : ℝ)) : ℝ) - (q : ℝ)⁻¹) /
        ((240 * L : ℕ) : ℝ) ≤
      (((smoothShiftedPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L)).filter
          fun p ↦ q ∣ p + 1).card : ℝ) := by
  have hbridge :=
    mul_sum_inv_powerSieveAuxPrimesAway_le_mul_card_goodRoot
      hn hL hQ hW hq hqu hqGood hrGood hqrGood hcofactor hnumeric
  have hmassAway :=
    sub_inv_le_sum_inv_powerSieveAuxPrimesAway (q := q) hmass
  have hmassMul : W *
      ((1 / (500 * (L : ℝ)) : ℝ) - (q : ℝ)⁻¹) ≤
      W * ∑ r ∈ powerSieveAuxPrimesAway n L Q q, (r : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_left hmassAway hW
  calc
    W * ((1 / (500 * (L : ℝ)) : ℝ) - (q : ℝ)⁻¹) /
        ((240 * L : ℕ) : ℝ) ≤
        (((240 * L : ℕ) : ℝ) *
          (((smoothShiftedPrimes
            (powerSieveX n L) (powerSieveSmoothBound n L)).filter
              fun p ↦ q ∣ p + 1).card : ℝ)) /
          ((240 * L : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_right (hmassMul.trans hbridge) (by positivity)
    _ = (((smoothShiftedPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L)).filter
          fun p ↦ q ∣ p + 1).card : ℝ) := by
      have hne : (((240 * L : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp

/-- Once the auxiliary interval has reciprocal mass at least `1/(500L)`, a good
root has the explicit cardinality lower bound produced by the power sieve. -/
theorem div_le_card_goodRoot_of_powerSieveAuxPrimes_reciprocal_lower
    {n L Q q B : ℕ} {W : ℝ}
    (hn : 2 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hW : 0 ≤ W)
    (hmass : (1 / (500 * (L : ℝ)) : ℝ) ≤
      ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹)
    (hq : q.Prime)
    (hqLarge : 1000 * L ≤ q)
    (hqu : q ≤ powerSieveSmoothBound n L)
    (hqGood : primitiveEndpointMass (powerSieveX n L) q ≤
      (powerSieveX n L : ℝ) / 10)
    (hrGood : ∀ r ∈ powerSieveAuxPrimes n L Q,
      primitiveEndpointMass (powerSieveX n L) r ≤
        (powerSieveX n L : ℝ) / 10)
    (hqrGood : ∀ r ∈ powerSieveAuxPrimes n L Q,
      primitiveEndpointMass (powerSieveX n L) (q * r) ≤
        (powerSieveX n L : ℝ) / 10)
    (hcofactor : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ∀ p ∈ primesInProgression
        (powerSieveX n L) (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
          s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ r ∈ powerSieveAuxPrimes n L Q,
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
          W * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r) :
    W / (240000 * (L : ℝ) ^ 2) ≤
      (((smoothShiftedPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L)).filter
          fun p ↦ q ∣ p + 1).card : ℝ) := by
  have hbridge :=
    mul_sum_inv_powerSieveAuxPrimesAway_le_mul_card_goodRoot
      hn hL hQ hW hq hqu hqGood hrGood hqrGood hcofactor hnumeric
  have hmassAway := one_div_thousand_le_sum_inv_powerSieveAuxPrimesAway
    hL hqLarge hmass
  have hmassMul : W * (1 / (1000 * (L : ℝ)) : ℝ) ≤
      W * ∑ r ∈ powerSieveAuxPrimesAway n L Q q, (r : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_left hmassAway hW
  calc
    W / (240000 * (L : ℝ) ^ 2) =
        (W * (1 / (1000 * (L : ℝ)) : ℝ)) /
          ((240 * L : ℕ) : ℝ) := by
      push_cast
      ring
    _ ≤ (((240 * L : ℕ) : ℝ) *
        (((smoothShiftedPrimes
          (powerSieveX n L) (powerSieveSmoothBound n L)).filter
            fun p ↦ q ∣ p + 1).card : ℝ)) /
          ((240 * L : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_right (hmassMul.trans hbridge) (by positivity)
    _ = (((smoothShiftedPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L)).filter
          fun p ↦ q ∣ p + 1).card : ℝ) := by
      have hne : (((240 * L : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp

/-- Eventual form: the prime reciprocal-mass theorem supplies the mass
hypothesis uniformly for every block parameter `Q`. -/
theorem eventually_div_le_card_goodRoot (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q → ∀ q B : ℕ, ∀ W : ℝ,
      0 ≤ W → q.Prime →
      1000 * L ≤ q →
      q ≤ powerSieveSmoothBound n L →
      primitiveEndpointMass (powerSieveX n L) q ≤
        (powerSieveX n L : ℝ) / 10 →
      (∀ r ∈ powerSieveAuxPrimes n L Q,
        primitiveEndpointMass (powerSieveX n L) r ≤
          (powerSieveX n L : ℝ) / 10) →
      (∀ r ∈ powerSieveAuxPrimes n L Q,
        primitiveEndpointMass (powerSieveX n L) (q * r) ≤
          (powerSieveX n L : ℝ) / 10) →
      (∀ r ∈ powerSieveAuxPrimes n L Q,
        ∀ p ∈ primesInProgression
          (powerSieveX n L) (q * r) (q * r - 1),
          ∀ s : ℕ, s.Prime → powerSieveSmoothBound n L < s →
            s ∣ p + 1 → (p + 1) / (q * r * s) ≤ B) →
      (∀ r ∈ powerSieveAuxPrimes n L Q,
        ((representedLargeFactorPrimes
          (powerSieveX n L) (powerSieveSmoothBound n L) q r B).card : ℝ) +
            W * (r : ℝ)⁻¹ ≤
          powerSieveProgressionBudget (powerSieveX n L) q r) →
      W / (240000 * (L : ℝ) ^ 2) ≤
        (((smoothShiftedPrimes
          (powerSieveX n L) (powerSieveSmoothBound n L)).filter
            fun p ↦ q ∣ p + 1).card : ℝ) := by
  filter_upwards [eventually_powerSieveAuxPrimes_reciprocal_lower L hL,
    eventually_ge_atTop 2] with n hmass hn Q hQ q B W hW hq hqLarge hqu
      hqGood hrGood hqrGood hcofactor hnumeric
  exact div_le_card_goodRoot_of_powerSieveAuxPrimes_reciprocal_lower
    hn hL hQ hW (hmass Q hQ) hq hqLarge hqu hqGood hrGood hqrGood
      hcofactor hnumeric

end

end Erdos48
