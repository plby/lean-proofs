import ErdosProblems.Erdos980.ElliottTail.ModelBridge

/-!
# Reduction from a composite exponent to a divisor

If `ell ∣ k`, then every `k`-th power is an `ell`-th power.  Consequently an
`ell`-th-power nonresidue is a `k`-th-power nonresidue, and the least
`k`-th-power nonresidue is at most the least `ell`-th-power nonresidue.

The total normalization in `Basic` needs a little care here.  At a modulus
which is not eligible for `k`, the left side is zero.  At a modulus eligible
for `k`, divisibility makes the modulus eligible for `ell`, so both minima
have their genuine number-theoretic meanings.  The last results transfer a
uniform weighted-tail estimate for one divisor exponent to `k`; in
particular one may take a prime divisor such as `Nat.minFac k`.
-/

namespace Erdos980.ElliottTail

open Filter

/-- A `k`-th power is an `ell`-th power whenever `ell ∣ k`. -/
theorem exists_pow_eq_of_dvd_exponent
    {M : Type*} [Monoid M] {ell k : ℕ} (hellk : ell ∣ k) {a : M}
    (ha : ∃ b : M, b ^ k = a) :
    ∃ c : M, c ^ ell = a := by
  obtain ⟨d, rfl⟩ := hellk
  obtain ⟨b, hb⟩ := ha
  refine ⟨b ^ d, ?_⟩
  rw [← pow_mul]
  simpa [Nat.mul_comm] using hb

/-- An `ell`-th-power nonresidue is a `k`-th-power nonresidue when
`ell ∣ k`.  This algebraic implication does not require primality or
eligibility. -/
theorem isKthPowerNonresidue_of_dvd_exponent
    {ell k p a : ℕ} (hellk : ell ∣ k)
    (ha : IsKthPowerNonresidue ell p a) :
    IsKthPowerNonresidue k p a := by
  refine ⟨ha.1, ?_⟩
  intro hkpow
  exact ha.2 (exists_pow_eq_of_dvd_exponent hellk hkpow)

/-- Eligibility descends from an exponent to each of its divisors. -/
theorem eligible_of_dvd_exponent
    {ell k p : ℕ} (hellk : ell ∣ k) (hp : Eligible k p) :
    Eligible ell p := by
  exact ⟨hp.1, hp.2.of_dvd hellk⟩

/-- At a modulus eligible for `k`, the least `k`-th-power nonresidue is no
larger than the least nonresidue for any nontrivial divisor exponent. -/
theorem leastKthPowerNonresidue_le_of_eligible_of_dvd_exponent
    {ell k p : ℕ} (hell : 2 ≤ ell) (hk : 2 ≤ k) (hellk : ell ∣ k)
    (hp : Eligible k p) :
    leastKthPowerNonresidue k p ≤ leastKthPowerNonresidue ell p := by
  have hpell : Eligible ell p := eligible_of_dvd_exponent hellk hp
  apply leastKthPowerNonresidue_minimal hk hp
  exact isKthPowerNonresidue_of_dvd_exponent hellk
    (leastKthPowerNonresidue_spec hell hpell)

/-- The least-nonresidue comparison holds at every modulus under the total
normalization.  The ineligible case is exactly where the left side is zero. -/
theorem leastKthPowerNonresidue_le_of_dvd_exponent
    {ell k : ℕ} (hell : 2 ≤ ell) (hk : 2 ≤ k) (hellk : ell ∣ k)
    (p : ℕ) :
    leastKthPowerNonresidue k p ≤ leastKthPowerNonresidue ell p := by
  by_cases hp : Eligible k p
  · exact leastKthPowerNonresidue_le_of_eligible_of_dvd_exponent
      hell hk hellk hp
  · rw [leastKthPowerNonresidue_eq_zero_of_not_eligible
      (k := k) (p := p) (by tauto)]
    exact Nat.zero_le _

/-- A prime exceptional for `k` above a fixed cutoff is also exceptional for
any nontrivial divisor exponent. -/
theorem exceptionalPrimes_subset_of_dvd_exponent
    {ell k : ℕ} (hell : 2 ≤ ell) (hk : 2 ≤ k) (hellk : ell ∣ k)
    (y x : ℕ) :
    exceptionalPrimes k y x ⊆ exceptionalPrimes ell y x := by
  intro p hp
  have hp' := mem_exceptionalPrimes.mp hp
  apply mem_exceptionalPrimes.mpr
  exact ⟨hp'.1, hp'.2.1,
    hp'.2.2.trans_le
      (leastKthPowerNonresidue_le_of_dvd_exponent hell hk hellk p)⟩

/-- The unnormalized weighted tail for `k` is bounded by the corresponding
tail for every nontrivial divisor exponent. -/
theorem weightedTailSum_le_of_dvd_exponent
    {ell k : ℕ} (hell : 2 ≤ ell) (hk : 2 ≤ k) (hellk : ell ∣ k)
    (y x : ℕ) :
    weightedTailSum k y x ≤ weightedTailSum ell y x := by
  classical
  unfold weightedTailSum
  calc
    (∑ p ∈ exceptionalPrimes k y x,
        (leastKthPowerNonresidue k p : ℝ)) ≤
        ∑ p ∈ exceptionalPrimes k y x,
          (leastKthPowerNonresidue ell p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact_mod_cast
        leastKthPowerNonresidue_le_of_dvd_exponent hell hk hellk p
    _ ≤ ∑ p ∈ exceptionalPrimes ell y x,
          (leastKthPowerNonresidue ell p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact exceptionalPrimes_subset_of_dvd_exponent hell hk hellk y x
      · intro p _ _
        positivity

/-- The normalized weighted-tail comparison.  The lower bound on `x` merely
ensures that the factor `log x / x` is nonnegative. -/
theorem normalizedWeightedTail_le_of_dvd_exponent
    {ell k : ℕ} (hell : 2 ≤ ell) (hk : 2 ≤ k) (hellk : ell ∣ k)
    (y x : ℕ) (hx : 2 ≤ x) :
    normalizedWeightedTail k y x ≤ normalizedWeightedTail ell y x := by
  unfold normalizedWeightedTail
  apply mul_le_mul_of_nonneg_left
    (weightedTailSum_le_of_dvd_exponent hell hk hellk y x)
  apply div_nonneg
  · apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ x by omega)
  · positivity

/-- Any literal uniform estimate for Elliott's normalized tails transfers
from a nontrivial divisor exponent `ell` to `k`, with the same cutoff and
eventual threshold. -/
theorem normalizedWeightedTail_uniform_of_dvd_exponent
    {ell k : ℕ} (hell : 2 ≤ ell) (hk : 2 ≤ k) (hellk : ell ∣ k)
    (cutoff : ℕ → ℕ)
    (hsmall : ∀ ε > 0, ∃ M₀, ∀ M ≥ M₀,
      ∀ᶠ x : ℕ in atTop,
        normalizedWeightedTail ell (cutoff M) x < ε) :
    ∀ ε > 0, ∃ M₀, ∀ M ≥ M₀,
      ∀ᶠ x : ℕ in atTop,
        normalizedWeightedTail k (cutoff M) x < ε := by
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := hsmall ε hε
  refine ⟨M₀, fun M hM ↦ ?_⟩
  filter_upwards [hM₀ M hM, eventually_ge_atTop 2] with x hxsmall hx
  exact (normalizedWeightedTail_le_of_dvd_exponent
    hell hk hellk (cutoff M) x hx).trans_lt hxsmall

/-- Uniform integrability of the exact prime-value tail transfers from a
nontrivial divisor exponent to `k`.  This is the reusable exponent-reduction
interface for the final analytic argument. -/
theorem uniformlyNegligibleTail_leastNonresidueModel_of_dvd_exponent
    {ell k : ℕ} (hell : 2 ≤ ell) (hk : 2 ≤ k) (hellk : ell ∣ k)
    (hui : UniformlyNegligibleTail
      (primeValueTail (leastKthPowerNonresidueModel ell)) erdos980Scale) :
    UniformlyNegligibleTail
      (primeValueTail (leastKthPowerNonresidueModel k)) erdos980Scale := by
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := hui ε hε
  refine ⟨M₀, fun M hM ↦ ?_⟩
  filter_upwards [hM₀ M hM, eventually_ge_atTop 2] with x hxell hx
  rw [primeValueTail_div_erdos980Scale_eq_normalizedWeightedTail hk]
  rw [abs_of_nonneg (normalizedWeightedTail_nonneg k
    (rationalPrime M - 1) x hx)]
  calc
    normalizedWeightedTail k (rationalPrime M - 1) x ≤
        normalizedWeightedTail ell (rationalPrime M - 1) x :=
      normalizedWeightedTail_le_of_dvd_exponent
        hell hk hellk (rationalPrime M - 1) x hx
    _ = primeValueTail (leastKthPowerNonresidueModel ell) M x /
          erdos980Scale x := by
      rw [primeValueTail_div_erdos980Scale_eq_normalizedWeightedTail hell]
    _ ≤ |primeValueTail (leastKthPowerNonresidueModel ell) M x /
          erdos980Scale x| := le_abs_self _
    _ < ε := hxell

/-- Every exponent `k ≥ 2` can be reduced to its least prime divisor. -/
theorem uniformlyNegligibleTail_leastNonresidueModel_of_minFac
    (k : ℕ) (hk : 2 ≤ k)
    (hui : UniformlyNegligibleTail
      (primeValueTail (leastKthPowerNonresidueModel k.minFac))
      erdos980Scale) :
    UniformlyNegligibleTail
      (primeValueTail (leastKthPowerNonresidueModel k)) erdos980Scale := by
  have hk1 : k ≠ 1 := by omega
  have hprime : k.minFac.Prime := Nat.minFac_prime hk1
  exact uniformlyNegligibleTail_leastNonresidueModel_of_dvd_exponent
    hprime.two_le hk (Nat.minFac_dvd k) hui

end Erdos980.ElliottTail
