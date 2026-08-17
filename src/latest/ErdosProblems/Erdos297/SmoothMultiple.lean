/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.PrimeIntervals
import ErdosProblems.Erdos297.Parameters

/-!
# Smooth multiples in the Liu--Sawhney minor-arc argument

At the arithmetic step on line 400 of the first arXiv version of
Liu--Sawhney, a divisor `d` is extended by one prime to a denominator in
`[N / 2, N]`.  The prime must not divide `d`: this both preserves exact
prime-power smoothness and increases `Omega` by exactly one.

The source obtains the prime from its preceding auxiliary-prime construction.
Here that supply is stated by the exact, finite cardinal inequality saying
that the dyadic multiplier interval contains more primes than `d` has prime
divisors.  Keeping this finite hypothesis visible is important: the much
weaker hypotheses `Omega(d) = O(log log N)` and `d <= N / 2000` alone do not
imply that a prime in this particular interval is coprime to `d`.
-/

namespace Erdos297.SmoothMultiple

open Filter Finset
open scoped ArithmeticFunction.Omega

noncomputable section

open Erdos285.PrimePowers
open GoodFactorization PrimeIntervals

attribute [local instance] Classical.propDecidable

/-- Multipliers strictly above `N / (2d)` and at most `N / d` produce a
multiple of `d` in `[N/2,N]`. -/
def multiplierPrimes (N d : ℕ) : Finset ℕ :=
  primesBetween (N / (2 * d) + 1) (N / d)

@[simp] lemma mem_multiplierPrimes {N d p : ℕ} :
    p ∈ multiplierPrimes N d ↔
      N / (2 * d) < p ∧ p ≤ N / d ∧ p.Prime := by
  simp only [multiplierPrimes, primesBetween, Finset.mem_filter,
    Finset.mem_Icc, Nat.lt_iff_add_one_le]
  tauto

lemma multiplierPrimes_eq_Ioc_filter (N d : ℕ) :
    multiplierPrimes N d =
      (Ioc ((N / d) / 2) (N / d)).filter Nat.Prime := by
  ext p
  simp only [mem_multiplierPrimes, Finset.mem_filter, Finset.mem_Ioc]
  have hlower : N / (2 * d) = (N / d) / 2 := by
    rw [Nat.mul_comm 2 d, Nat.div_div_eq_div_mul]
  rw [hlower]
  tauto

/-- If the quotient `N / d(N)` tends to infinity, the multiplier interval
eventually contains at least six primes.  This is the analytic supply needed
after replacing the source scale by `KSafe`. -/
theorem eventually_six_le_card_multiplierPrimes_of_quotient
    (d : ℕ → ℕ)
    (hquot : Tendsto (fun N ↦ N / d N) atTop atTop) :
    ∀ᶠ N : ℕ in atTop, 6 ≤ (multiplierPrimes N (d N)).card := by
  have hhalf : Tendsto (fun N ↦ (N / d N) / 2) atTop atTop :=
    (Nat.tendsto_div_const_atTop (by norm_num : 2 ≠ 0)).comp hquot
  have hP := hhalf.eventually eventually_six_le_card_primesBetween_dyadic
  filter_upwards [hP] with N hP
  apply hP.trans
  apply Finset.card_le_card
  intro p hp
  rw [mem_primesBetween] at hp
  rw [mem_multiplierPrimes]
  have hlower : N / (2 * d N) = (N / d N) / 2 := by
    rw [Nat.mul_comm 2 (d N), Nat.div_div_eq_div_mul]
  refine ⟨?_, hp.2.1.trans (Nat.mul_div_le (N / d N) 2), hp.2.2⟩
  rw [hlower]
  omega

/-- A prime in the multiplier interval produces a multiple in the required
closed interval. -/
lemma mul_mem_half_interval {N d p : ℕ} (hd : d ≠ 0)
    (hpLower : N / (2 * d) < p) (hpUpper : p ≤ N / d) :
    N / 2 ≤ d * p ∧ d * p ≤ N := by
  have htwoD : 0 < 2 * d := by positivity
  have hNlt : N < 2 * d * p := by
    exact (Nat.lt_mul_div_succ N htwoD).trans_le
      (Nat.mul_le_mul_left (2 * d) (Nat.succ_le_iff.mpr hpLower))
  rw [show 2 * d * p = 2 * (d * p) by ring] at hNlt
  have hlower : N / 2 ≤ d * p := by omega
  have hupper : d * p ≤ N := by
    exact (Nat.mul_le_mul_left d hpUpper).trans (Nat.mul_div_le N d)
  exact ⟨hlower, hupper⟩

/-- Multiplication by a new prime preserves exact prime-power smoothness.
This is the exact-prime-power version of the familiar smooth-number fact. -/
lemma primePowerSmooth_mul_prime_of_not_dvd {S d p : ℕ}
    (hd : d ≠ 0) (hp : p.Prime) (hpd : ¬p ∣ d)
    (hdSmooth : PrimePowerSmooth S d) (hpS : p ≤ S) :
    PrimePowerSmooth S (d * p) := by
  intro q hq
  have hdp : d * p ≠ 0 := mul_ne_zero hd hp.ne_zero
  rcases (mem_primePowerParts hdp).mp hq with ⟨hqpp, hqdiv, hqcop⟩
  obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hqpp
  have hfactor : (d * p).factorization r = k :=
    (UnitFractions.factorization_eq_iff hr hk.ne').mp ⟨hqdiv, hqcop⟩
  by_cases hrp : r = p
  · subst r
    have hdfactor : d.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hpd
    rw [Nat.factorization_mul hd hp.ne_zero, Finsupp.add_apply,
      hdfactor, hp.factorization_self] at hfactor
    have : k = 1 := by omega
    simpa [this] using hpS
  · have hpfactor : p.factorization r = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      exact fun hrdiv ↦ hrp ((hp.dvd_iff_eq hr.ne_one).mp hrdiv).symm
    rw [Nat.factorization_mul hd hp.ne_zero, Finsupp.add_apply,
      hpfactor, add_zero] at hfactor
    apply hdSmooth
    apply (mem_primePowerParts hd).mpr
    refine ⟨(isPrimePow_nat_iff _).mpr ⟨r, k, hr, hk, rfl⟩, ?_⟩
    exact (UnitFractions.factorization_eq_iff hr hk.ne').mpr hfactor

/-- Multiplication by a prime not dividing `d` does not increase any old
prime exponent and introduces the new exponent `1`. -/
lemma maxPrimeExponent_mul_prime_of_not_dvd {d p E : ℕ}
    (hd : d ≠ 0) (hp : p.Prime) (hpd : ¬p ∣ d)
    (hE : 1 ≤ E) (hdExp : maxPrimeExponent d ≤ E) :
    maxPrimeExponent (d * p) ≤ E := by
  rw [maxPrimeExponent, Finset.sup_le_iff]
  intro r hrSupport
  have hrPrime : r.Prime := by
    rw [Nat.support_factorization] at hrSupport
    exact Nat.prime_of_mem_primeFactors hrSupport
  by_cases hrp : r = p
  · subst r
    rw [Nat.factorization_mul hd hp.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpd, hp.factorization_self]
    simpa using hE
  · have hpfactor : p.factorization r = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      exact fun hrdiv ↦ hrp ((hp.dvd_iff_eq hrPrime.ne_one).mp hrdiv).symm
    rw [Nat.factorization_mul hd hp.ne_zero, Finsupp.add_apply,
      hpfactor, add_zero]
    by_cases hr0 : d.factorization r = 0
    · simp [hr0]
    · have hrMem : r ∈ d.factorization.support :=
        Finsupp.mem_support_iff.mpr hr0
      exact (Finset.le_sup (f := fun s ↦ d.factorization s) hrMem).trans hdExp

/-- A finite prime-cardinality condition supplies a prime multiplier not
dividing `d`. -/
lemma exists_coprime_multiplier_prime {N d : ℕ} (hd : d ≠ 0)
    (hcard : d.primeFactors.card < (multiplierPrimes N d).card) :
    ∃ p : ℕ, p.Prime ∧ N / (2 * d) < p ∧ p ≤ N / d ∧ ¬p ∣ d := by
  obtain ⟨p, hp, hpLower, hpUpper, hpd⟩ :=
    exists_prime_in_interval_not_dvd hd (by
      simpa [multiplierPrimes] using hcard)
  exact ⟨p, hp, by simpa [multiplierPrimes] using hpLower,
    by simpa [multiplierPrimes] using hpUpper, hpd⟩

/-- Exact finite smooth-multiple supply used by the minor arcs.

The hypotheses after `hcard` are precisely the properties that make the
chosen product a member of `goodDenominators`; no asymptotic or analytic
claim is hidden in this theorem. -/
theorem exists_goodDenominator_multiple {N M S d : ℕ}
    (hd : d ≠ 0) (hM : M ≤ N / 2)
    (hcard : d.primeFactors.card < (multiplierPrimes N d).card)
    (hquotS : N / d ≤ S)
    (hdSmooth : PrimePowerSmooth S d)
    (hdExp : maxPrimeExponent d ≤ exponentBound N)
    (hExpPos : 1 ≤ exponentBound N)
    (hdOmega : Ω d + 1 ≤ factorBound N) :
    ∃ n ∈ goodDenominators N M S,
      N / 2 ≤ n ∧ n ≤ N ∧ d ∣ n := by
  obtain ⟨p, hp, hpLower, hpUpper, hpd⟩ :=
    exists_coprime_multiplier_prime hd hcard
  refine ⟨d * p, ?_, ?_⟩
  · rw [mem_goodDenominators]
    have hrange := mul_mem_half_interval hd hpLower hpUpper
    refine ⟨hM.trans hrange.1, hrange.2, ?_, ?_, ?_⟩
    · exact primePowerSmooth_mul_prime_of_not_dvd hd hp hpd hdSmooth
        (hpUpper.trans hquotS)
    · exact maxPrimeExponent_mul_prime_of_not_dvd hd hp hpd hExpPos hdExp
    · rw [ArithmeticFunction.cardFactors_mul hd hp.ne_zero,
        ArithmeticFunction.cardFactors_apply_prime hp]
      exact hdOmega
  · exact ⟨(mul_mem_half_interval hd hpLower hpUpper).1,
      (mul_mem_half_interval hd hpLower hpUpper).2, dvd_mul_right d p⟩

/-- The same conclusion in the `divisiblePart` form consumed by the
minor-arc incidence argument. -/
theorem divisiblePart_goodDenominators_nonempty {N M S d : ℕ}
    (hd : d ≠ 0) (hM : M ≤ N / 2)
    (hcard : d.primeFactors.card < (multiplierPrimes N d).card)
    (hquotS : N / d ≤ S)
    (hdSmooth : PrimePowerSmooth S d)
    (hdExp : maxPrimeExponent d ≤ exponentBound N)
    (hExpPos : 1 ≤ exponentBound N)
    (hdOmega : Ω d + 1 ≤ factorBound N) :
    (divisiblePart (goodDenominators N M S) d).Nonempty := by
  obtain ⟨n, hnGood, -, -, hdn⟩ :=
    exists_goodDenominator_multiple hd hM hcard hquotS hdSmooth hdExp
      hExpPos hdOmega
  exact ⟨n, mem_divisiblePart.mpr ⟨hnGood, hdn⟩⟩

/-! ## The repaired `KSafe` specialization -/

/-- The concrete, certificate-free smooth-multiple supply at the repaired
`KSafe` scale.  The five-prime-factor hypothesis is exactly what is available
for the product `q p' r p` in the minor-arc construction. -/
theorem eventually_exists_goodDenominator_multiple_KSafe :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      KSafe N ≤ d →
      (d : ℝ) ≤ 4000 * (KSafe N : ℝ) * logScale N →
      d.primeFactors.card ≤ 5 →
      PrimePowerSmooth (S N) d →
      maxPrimeExponent d ≤ exponentBound N →
      Ω d + 1 ≤ factorBound N →
      ∃ n ∈ goodDenominators N (M N) (S N),
        N / 2 ≤ n ∧ n ≤ N ∧ d ∣ n := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1
    eventually_six_le_card_primesBetween_dyadic
  have hExp : ∀ᶠ N : ℕ in atTop, 1 ≤ exponentBound N := by
    filter_upwards [tendsto_logLogScale.eventually_ge_atTop 1] with N hLL
    rw [exponentBound]
    apply Nat.le_floor
    have hLL' : (1 : ℝ) ≤ Real.log (Real.log (N : ℝ)) := by
      simpa [logLogScale, logScale] using hLL
    norm_num only [Nat.cast_one]
    linarith
  filter_upwards [eventually_nat_safe_scale_chain,
      eventually_almostOnePower_le_natS, eventually_KSafeReal_ge_two,
      tendsto_dyadicMultiplierScale.eventually_ge_atTop (2 * T : ℝ),
      eventually_N_div_KSafe_le_S, eventually_pos_scales, hExp]
    with N hchain hNS hsafe hdyadic hNKS hpos hExpPos
  intro d hKd hdUpper hdCard hdSmooth hdExp hdOmega
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hKpos : 0 < KSafe N := by
    have hhalf := half_le_floor hsafe
    have hhalfpos : (0 : ℝ) < KSafeReal N / 2 := by nlinarith
    have hcast : (0 : ℝ) < (⌊KSafeReal N⌋₊ : ℝ) := hhalfpos.trans_le hhalf
    change 0 < ⌊KSafeReal N⌋₊
    exact_mod_cast hcast
  have hd0 : d ≠ 0 := (hKpos.trans_le hKd).ne'
  have hMhalf : M N ≤ N / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    have hreal : ((M N * 2 : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      nlinarith [hchain.2.2]
    exact_mod_cast hreal
  have hquotS : N / d ≤ S N := by
    exact (Nat.div_le_div_left hKd hKpos).trans hNKS
  have hDpos : 0 < 4000 * (KSafe N : ℝ) * logScale N := by
    exact mul_pos (mul_pos (by norm_num) (by exact_mod_cast hKpos))
      (zero_lt_one.trans hL)
  have hTlower : T ≤ N / (2 * d) := by
    have hclearedD :
        (2 * (T : ℝ)) *
            (4000 * (KSafe N : ℝ) * logScale N) ≤ (N : ℝ) := by
      exact (le_div_iff₀ hDpos).mp (by
        simpa [dyadicMultiplierScale] using hdyadic)
    have hcleared : ((T * (2 * d) : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      calc
        (T : ℝ) * (2 * (d : ℝ)) = (2 * (T : ℝ)) * (d : ℝ) := by ring
        _ ≤ (2 * (T : ℝ)) *
            (4000 * (KSafe N : ℝ) * logScale N) := by gcongr
        _ ≤ (N : ℝ) := hclearedD
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * d)).2
    exact_mod_cast hcleared
  have hcardSix : 6 ≤ (multiplierPrimes N d).card := by
    apply (hT _ hTlower).trans
    apply Finset.card_le_card
    intro p hp
    rw [mem_primesBetween] at hp
    rw [mem_multiplierPrimes]
    have hlower : N / (2 * d) = (N / d) / 2 := by
      rw [Nat.mul_comm 2 d, Nat.div_div_eq_div_mul]
    rw [hlower] at hp ⊢
    exact ⟨by omega, hp.2.1.trans (Nat.mul_div_le (N / d) 2), hp.2.2⟩
  have hcard : d.primeFactors.card < (multiplierPrimes N d).card := by omega
  exact exists_goodDenominator_multiple hd0 hMhalf hcard hquotS hdSmooth
    hdExp hExpPos hdOmega

end

end Erdos297.SmoothMultiple
