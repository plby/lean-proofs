import ErdosProblems.Erdos4.PlainSmoothBound
import ErdosProblems.Erdos4.ZeroSieveResidual

/-!
# Integer outer parameters

The sparse ray reuses the checked Rankin parameters. Source and reserve
endpoints are integer multiples of `t⁵⁰`; all logarithmic cutoffs are
integer powers. The length multiplier remains free after the fixed
Rankin loss parameter has been chosen.
-/

open scoped BigOperators

namespace Erdos4.OuterRay

open SmoothParameters ChebyshevIntervals

def base (a r : ℕ) : ℕ := primaryFrontier a r ^ 50
def frontier (a r : ℕ) : ℕ := 256 * base a r
def length (a D r : ℕ) : ℕ := D * frontier a r * core r * r
def smallCutoff (a r : ℕ) : ℕ := primaryExponent a r ^ 4
def sourcePrimes (a r : ℕ) : Finset ℕ := primeInterval (16 * base a r) (frontier a r)
def reservePrimes (a r : ℕ) : Finset ℕ := primeInterval (base a r) (16 * base a r)
def randomPrimes (a r : ℕ) : Finset ℕ := primeInterval (smallCutoff a r) (smoothFrontier r)

instance primeInterval_factPrime (a b : ℕ) (p : primeInterval a b) : Fact (p : ℕ).Prime :=
  ⟨(mem_primeInterval.mp p.property).1⟩

theorem primary_two_le (a r : ℕ) : 2 ≤ primaryFrontier a r := by
  exact Nat.le_pow (primaryExponent_pos a r)

theorem base_pos (a r : ℕ) : 0 < base a r := pow_pos (primaryFrontier_pos a r) 50
theorem frontier_pos (a r : ℕ) : 0 < frontier a r := Nat.mul_pos (by norm_num) (base_pos a r)
theorem primary_le_base (a r : ℕ) : primaryFrontier a r ≤ base a r := Nat.le_pow (by norm_num)
theorem base_le_frontier (a r : ℕ) : base a r ≤ frontier a r := by
  unfold frontier
  omega

theorem frontier_le_length (a : ℕ) {D r : ℕ} (hD : 1 ≤ D) (hr : 1 ≤ r) :
    frontier a r ≤ length a D r := by
  have hV : 1 ≤ core r := (core_pos r)
  have hh := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_right (frontier a r) hD) hV) hr
  simpa only [one_mul, mul_one, length] using hh

theorem primary_le_length (a : ℕ) {D r : ℕ} (hD : 1 ≤ D) (hr : 1 ≤ r) :
    primaryFrontier a r ≤ length a D r :=
  (primary_le_base a r).trans ((base_le_frontier a r).trans (frontier_le_length a hD hr))

theorem length_le_core_square (a D r : ℕ) :
    length a D r ≤ (256 * D) * primaryFrontier a r ^ 50 * core r ^ 2 := by
  have hh := Nat.mul_le_mul_left (D * frontier a r * core r) (self_le_core r)
  unfold length frontier base
  calc
    _ ≤ D * (256 * primaryFrontier a r ^ 50) * core r * core r := hh
    _ = _ := by ring

theorem smooth_le_primary (a r : ℕ) : smoothFrontier r ≤ primaryFrontier a r := by
  have hr : r ≤ 2 ^ r := (show r < 2 ^ r from Nat.lt_two_pow_self).le
  have hmul := Nat.mul_le_mul_right (2 ^ r * core r) hr
  have hscale := Nat.mul_le_mul_right (2 ^ r * (2 ^ r * core r))
    (show 1 ≤ 2 ^ a from Nat.one_le_two_pow)
  have hE : smoothExponent r ≤ primaryExponent a r := by
    unfold smoothExponent rankinDenominator primaryExponent
    rw [show a + 2 * r = a + r + r by omega, pow_add, pow_add]
    exact hmul.trans (by simpa only [one_mul, mul_assoc] using hscale)
  exact Nat.pow_le_pow_right (by norm_num) hE

theorem smooth_le_base (a r : ℕ) : smoothFrontier r ≤ base a r :=
  (smooth_le_primary a r).trans (primary_le_base a r)

theorem eventually_small_le_smooth (a : ℕ) :
    ∀ᶠ r : ℕ in Filter.atTop, smallCutoff a r ≤ smoothFrontier r := by
  filter_upwards [Filter.eventually_ge_atTop (max a 8)] with r hr
  have hra : a ≤ r := (le_max_left a 8).trans hr
  have hr8 : 8 ≤ r := (le_max_right a 8).trans hr
  have hE : primaryExponent a r ≤ core r ^ 2 :=
    primaryExponent_le_core_sq_of (stable_exponent_comparison hra (by omega))
  have h8 : 8 ≤ r * core r := by
    have hh := Nat.mul_le_mul_left r (show 1 ≤ core r from core_pos r)
    omega
  have hexp : 2 ^ r * 8 ≤ r * (2 ^ r * core r) := by
    have hh := Nat.mul_le_mul_left (2 ^ r) h8
    nlinarith
  calc
    smallCutoff a r ≤ (core r ^ 2) ^ 4 := Nat.pow_le_pow_left hE 4
    _ = 2 ^ (2 ^ r * 8) := by rw [← pow_mul, core, ← pow_mul]
    _ ≤ 2 ^ (r * (2 ^ r * core r)) := Nat.pow_le_pow_right (by norm_num) hexp
    _ = smoothFrontier r := rfl

end Erdos4.OuterRay
