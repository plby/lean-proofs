import ErdosProblems.Erdos980.ElliottTail.Definitions
import ErdosProblems.Erdos980.ElliottTail.LargeTailApplication
import ErdosProblems.Erdos980.ElliottTail.SmoothAmplifier

/-!
# Applying the smooth amplifier to the exact weighted tail

This file connects the closed finite large-sieve estimate in
`SmoothAmplifier` to the strict prime cutoff used by `normalizedWeightedTail`.
The exponent is left as a parameter: an amplifier of size at least
`x ^ (2 - a)` gives at most `2 * x ^ a` exceptional primes.  Consequently,
any choice of smooth-amplifier parameters with `a + 3/4 < 1` makes the
Pólya--Vinogradov large tail vanish.
-/

namespace Erdos980.ElliottTail

open Filter
open scoped Topology

noncomputable section

/-- The exceptional set with strict cutoff `p < x` is contained in the
finite large-sieve exceptional set with cutoff `p ≤ x`. -/
theorem exceptionalPrimes_subset_largeLeastKthPowerNonresiduePrimes
    {k y x : ℕ} (hk : 2 ≤ k) :
    exceptionalPrimes k y x ⊆
      largeLeastKthPowerNonresiduePrimes k x y := by
  intro p hp
  have hmem := mem_exceptionalPrimes.mp hp
  exact mem_largeLeastKthPowerNonresiduePrimes.mpr
    ⟨hmem.2.1.pos, hmem.1.le, eligible_of_mem_exceptionalPrimes hk hp,
      hmem.2.2⟩

/-- Exponent-parametric form of the finite smooth-amplifier estimate. -/
theorem largeLeastKthPowerNonresiduePrimes_card_le_two_mul_rpow
    (k x y r : ℕ) (a : ℝ) (hk : 2 ≤ k) (hx : 0 < x)
    (hr : r ≤ Nat.primeCounting y) (hpow : y ^ r ≤ x ^ 2)
    (hcard : (x : ℝ) ^ (2 - a) ≤
      ((Nat.primeCounting y).choose r : ℝ)) :
    ((largeLeastKthPowerNonresiduePrimes k x y).card : ℝ) ≤
      2 * (x : ℝ) ^ a := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hLpos : 0 < (x : ℝ) ^ (2 - a) :=
    Real.rpow_pos_of_pos hxR _
  have hmain := largeLeastKthPowerNonresiduePrimes_card_le_of_parameters
    k x y r (x ^ 2) ((x : ℝ) ^ (2 - a))
    hk hr hpow hLpos hcard
  refine hmain.trans_eq ?_
  rw [div_eq_iff hLpos.ne']
  have hrpow :
      (x : ℝ) ^ a * (x : ℝ) ^ (2 - a) = (x : ℝ) ^ 2 := by
    calc
      (x : ℝ) ^ a * (x : ℝ) ^ (2 - a) =
          (x : ℝ) ^ (a + (2 - a)) :=
        (Real.rpow_add hxR a (2 - a)).symm
      _ = (x : ℝ) ^ 2 := by
        rw [show a + (2 - a) = (2 : ℝ) by ring,
          Real.rpow_two]
  push_cast
  nlinarith

/-- The same finite estimate for the literal strict-cutoff exceptional set
appearing in the weighted tail. -/
theorem exceptionalPrimes_card_le_two_mul_rpow_of_smoothAmplifier
    (k x y r : ℕ) (a : ℝ) (hk : 2 ≤ k) (hx : 0 < x)
    (hr : r ≤ Nat.primeCounting y) (hpow : y ^ r ≤ x ^ 2)
    (hcard : (x : ℝ) ^ (2 - a) ≤
      ((Nat.primeCounting y).choose r : ℝ)) :
    ((exceptionalPrimes k y x).card : ℝ) ≤ 2 * (x : ℝ) ^ a := by
  have hcardNat :
      (exceptionalPrimes k y x).card ≤
        (largeLeastKthPowerNonresiduePrimes k x y).card :=
    Finset.card_le_card
      (exceptionalPrimes_subset_largeLeastKthPowerNonresiduePrimes hk)
  exact (by exact_mod_cast hcardNat :
      ((exceptionalPrimes k y x).card : ℝ) ≤
        ((largeLeastKthPowerNonresiduePrimes k x y).card : ℝ)).trans
    (largeLeastKthPowerNonresiduePrimes_card_le_two_mul_rpow
      k x y r a hk hx hr hpow hcard)

/-- Closed large-tail theorem.  The only remaining parameter work is to
choose a moving smoothness cutoff and product length satisfying the three
displayed eventual inequalities. -/
theorem normalizedWeightedTail_tendsto_zero_of_smoothAmplifier_parameters
    (k : ℕ) (hk : 2 ≤ k) (cutoff rank : ℕ → ℕ) (a : ℝ)
    (ha : a + 3 / 4 < 1)
    (hcutoff : Tendsto cutoff atTop atTop)
    (hr : ∀ᶠ x : ℕ in atTop,
      rank x ≤ Nat.primeCounting (cutoff x))
    (hpow : ∀ᶠ x : ℕ in atTop,
      cutoff x ^ rank x ≤ x ^ 2)
    (hcard : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (2 - a) ≤
        ((Nat.primeCounting (cutoff x)).choose (rank x) : ℝ)) :
    Tendsto (fun x ↦ normalizedWeightedTail k (cutoff x) x)
      atTop (nhds 0) := by
  apply normalizedWeightedTail_tendsto_zero_of_eventually_card_rpow
    k hk cutoff 2 a ha hcutoff
  filter_upwards [eventually_ge_atTop 1, hr, hpow, hcard]
    with x hx hxrank hxpow hxcard
  exact exceptionalPrimes_card_le_two_mul_rpow_of_smoothAmplifier
    k x (cutoff x) (rank x) a hk (by omega) hxrank hxpow hxcard

/-- Flexible pointwise-exponent version.  In particular, an amplifier of
size `x^(7/4)` gives `a = 1/4`; choosing any `β` strictly between `1/2` and
`3/4` then closes the large tail. -/
theorem normalizedWeightedTail_tendsto_zero_of_smoothAmplifier_parameters_beta
    (k : ℕ) (hk : 2 ≤ k) (cutoff rank : ℕ → ℕ) (a β : ℝ)
    (hβ : 1 / 2 < β) (haβ : a + β < 1)
    (hcutoff : Tendsto cutoff atTop atTop)
    (hr : ∀ᶠ x : ℕ in atTop,
      rank x ≤ Nat.primeCounting (cutoff x))
    (hpow : ∀ᶠ x : ℕ in atTop,
      cutoff x ^ rank x ≤ x ^ 2)
    (hcard : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (2 - a) ≤
        ((Nat.primeCounting (cutoff x)).choose (rank x) : ℝ)) :
    Tendsto (fun x ↦ normalizedWeightedTail k (cutoff x) x)
      atTop (nhds 0) := by
  apply normalizedWeightedTail_tendsto_zero_of_eventually_card_rpow_and_beta
    k hk cutoff 2 a β hβ haβ hcutoff
  filter_upwards [eventually_ge_atTop 1, hr, hpow, hcard]
    with x hx hxrank hxpow hxcard
  exact exceptionalPrimes_card_le_two_mul_rpow_of_smoothAmplifier
    k x (cutoff x) (rank x) a hk (by omega) hxrank hxpow hxcard

/-- The explicit logarithmic smooth-amplifier parameters close the large
tail without any remaining analytic hypothesis. -/
theorem normalizedWeightedTail_smoothParameter_tendsto_zero
    (k : ℕ) (hk : 2 ≤ k) :
    Tendsto
      (fun x ↦ normalizedWeightedTail k (smoothParameterY x) x)
      atTop (nhds 0) := by
  apply normalizedWeightedTail_tendsto_zero_of_smoothAmplifier_parameters_beta
    k hk smoothParameterY smoothParameterR (1 / 5) (2 / 3)
      (by norm_num) (by norm_num) tendsto_smoothParameterY_atTop
  · exact eventually_smooth_parameters.mono fun _ h ↦ h.1
  · exact eventually_smooth_parameters.mono fun _ h ↦ h.2.1
  · filter_upwards [eventually_smooth_parameters] with x hx
    norm_num at hx ⊢
    exact hx.2.2

end

end Erdos980.ElliottTail
