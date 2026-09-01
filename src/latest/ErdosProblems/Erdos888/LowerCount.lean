import ErdosProblems.Erdos888.LowerRigidity
import ErdosProblems.Erdos469
import PrimeNumberTheoremAnd.Consequences

/-!
# Erdős 888: cardinality of the lower-bound construction

We count a canonical subfamily of the squarefree semiprimes.  Put
`y = sqrt (sqrt n)`.  For every prime `p ≤ y`, use the primes
`y < q ≤ n / p`.  The products `p*q` are distinct and belong to
`lowerBoundSet n`.  The prime number theorem supplies uniformly

`#{q : y < q ≤ n/p} ≫ n / (p log n) - y`.

Summing over `p` and using the reciprocal-prime Mertens estimate already
proved in `ErdosProblems.Erdos469` gives the required
`n * log(log n) / log n` lower bound.  All constants below are deliberately
very conservative.
-/

open Filter Finset Asymptotics
open scoped BigOperators Topology

namespace Erdos888

/-- The prime-counting function is bounded by its endpoint. -/
lemma primeCounting_le_self (x : ℕ) : Nat.primeCounting x ≤ x := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  calc
    x.primesLE.card ≤ (Finset.Icc 1 x).card := by
      apply Finset.card_le_card
      intro p hp
      have hp' := Nat.mem_primesLE.mp hp
      exact Finset.mem_Icc.mpr ⟨hp'.2.one_le, hp'.1⟩
    _ = x := by simp

/-- The natural fourth-root cutoff used in the semiprime count. -/
def fourthRoot (n : ℕ) : ℕ := n.sqrt.sqrt

/-- Small prime factors in the counting subfamily. -/
def countSmallPrimes (n : ℕ) : Finset ℕ :=
  Erdos469.primesThrough (fourthRoot n)

/-- For a fixed small prime `p`, the permitted large prime factors. -/
def countPartnerPrimes (n p : ℕ) : Finset ℕ :=
  (Finset.Ioc (fourthRoot n) (n / p)).filter Nat.Prime

/-- Pairs whose products form the counted subfamily. -/
def countPairs (n : ℕ) : Finset ((_ : ℕ) × ℕ) :=
  (countSmallPrimes n).sigma (countPartnerPrimes n)

@[simp] lemma mem_countSmallPrimes {n p : ℕ} :
    p ∈ countSmallPrimes n ↔ p.Prime ∧ p ≤ fourthRoot n := by
  simp [countSmallPrimes, Erdos469.mem_primesThrough]

@[simp] lemma mem_countPartnerPrimes {n p q : ℕ} :
    q ∈ countPartnerPrimes n p ↔
      fourthRoot n < q ∧ q ≤ n / p ∧ q.Prime := by
  simp [countPartnerPrimes, and_assoc]

/-- Ordered products of two distinct primes have unique coordinates. -/
lemma ordered_prime_product_unique {p q r s : ℕ}
    (hp : p.Prime) (_hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hrs : r < s) (hprod : p * q = r * s) :
    p = r ∧ q = s := by
  have hpdvd : p ∣ r * s := by
    rw [← hprod]
    exact dvd_mul_right p q
  rcases hp.dvd_mul.mp hpdvd with hpr | hps
  · have hpr' : p = r :=
      ((Nat.dvd_prime hr).mp hpr).resolve_left hp.ne_one
    subst r
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos hprod⟩
  · have hps' : p = s :=
      ((Nat.dvd_prime hs).mp hps).resolve_left hp.ne_one
    subst s
    have hqr : q = r := by
      apply Nat.eq_of_mul_eq_mul_right hp.pos
      simpa [mul_comm] using hprod
    subst r
    omega

/-- Multiplication is injective on the counted prime pairs. -/
lemma countPairs_product_injective (n : ℕ) :
    Set.InjOn (fun z : (_ : ℕ) × ℕ => z.1 * z.2) (countPairs n : Set _) := by
  rintro ⟨p, q⟩ hpq ⟨r, s⟩ hrs heq
  simp only [countPairs, Finset.mem_coe, Finset.mem_sigma,
    mem_countSmallPrimes, mem_countPartnerPrimes] at hpq hrs
  obtain ⟨hpr, hqs⟩ := ordered_prime_product_unique
    hpq.1.1 hpq.2.2.2 hrs.1.1 hrs.2.2.2
    (hpq.1.2.trans_lt hpq.2.1) (hrs.1.2.trans_lt hrs.2.1) heq
  simp [hpr, hqs]

/-- Products in `countPairs` lie in the prime-plus-squarefree-semiprime
construction. -/
lemma countPairs_product_mem_lowerBoundSet {n : ℕ} {z : (_ : ℕ) × ℕ}
    (hz : z ∈ countPairs n) : z.1 * z.2 ∈ lowerBoundSet n := by
  rcases z with ⟨p, q⟩
  simp only [countPairs, Finset.mem_sigma, mem_countSmallPrimes,
    mem_countPartnerPrimes] at hz
  have hpq : p < q := hz.1.2.trans_lt hz.2.1
  have hcop : p.Coprime q :=
    (Nat.coprime_primes hz.1.1 hz.2.2.2).mpr (ne_of_lt hpq)
  have hprod : p * q ≤ n := by
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le hz.1.1.pos).mp hz.2.2.1
  have hsqfree : Squarefree (p * q) :=
    (Nat.squarefree_mul hcop).mpr ⟨hz.1.1.squarefree, hz.2.2.2.squarefree⟩
  have hcard : (p * q).primeFactors.card = 2 := by
    rw [hcop.primeFactors_mul, hz.1.1.primeFactors, hz.2.2.2.primeFactors]
    simp [ne_of_lt hpq]
  exact mem_lowerBoundSet.mpr
    ⟨Nat.mul_pos hz.1.1.pos hz.2.2.2.pos, hprod, hsqfree, Or.inr hcard⟩

/-- The pair count is a lower bound for the construction's cardinality. -/
lemma countPairs_card_le_lowerBoundSet_card (n : ℕ) :
    (countPairs n).card ≤ (lowerBoundSet n).card := by
  let f : (_ : ℕ) × ℕ → ℕ := fun z => z.1 * z.2
  have himage : (countPairs n).image f ⊆ lowerBoundSet n := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨z, hz, rfl⟩
    exact countPairs_product_mem_lowerBoundSet hz
  calc
    (countPairs n).card = ((countPairs n).image f).card := by
      symm
      exact Finset.card_image_iff.mpr (countPairs_product_injective n)
    _ ≤ (lowerBoundSet n).card := Finset.card_le_card himage

/-- The number of primes in a natural interval is a difference of prime
counting functions. -/
lemma card_partnerPrimes (n p : ℕ)
    (hcut : fourthRoot n ≤ n / p) :
    (countPartnerPrimes n p).card =
      Nat.primeCounting (n / p) - Nat.primeCounting (fourthRoot n) := by
  let y := fourthRoot n
  let m := n / p
  have hset : countPartnerPrimes n p = m.primesLE \ y.primesLE := by
    ext q
    simp only [countPartnerPrimes, Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hyq, hqm⟩, hq⟩
      exact ⟨⟨hqm, hq⟩, fun hqy => (not_le_of_gt hyq) hqy.1⟩
    · rintro ⟨⟨hqm, hq⟩, hnot⟩
      exact ⟨⟨lt_of_not_ge fun hqy => hnot ⟨hqy, hq⟩, hqm⟩, hq⟩
  rw [hset, Finset.card_sdiff_of_subset (Nat.primesLE_mono hcut)]
  simp

/-- A floor-free lower estimate for natural-number division. -/
lemma half_real_div_le_nat_div {n p : ℕ} (hp : 0 < p) (h2p : 2 * p ≤ n) :
    (n : ℝ) / (2 * p) ≤ (n / p : ℕ) := by
  have htwo : 2 ≤ n / p := (Nat.le_div_iff_mul_le hp).mpr (by simpa using h2p)
  have hltNat : n < p * (n / p + 1) := by
    calc
      n = n % p + p * (n / p) := (Nat.mod_add_div n p).symm
      _ < p + p * (n / p) := Nat.add_lt_add_right (Nat.mod_lt n hp) _
      _ = p * (n / p + 1) := by ring
  have hlt : (n : ℝ) < (p : ℝ) * ((n / p : ℕ) + 1) := by
    exact_mod_cast hltNat
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have htwoR : (2 : ℝ) ≤ (n / p : ℕ) := by exact_mod_cast htwo
  rw [div_le_iff₀ (mul_pos (by norm_num) hpR)]
  nlinarith

/-- A convenient explicit lower half of the prime number theorem. -/
lemma eventually_primeCounting_lower :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ) / (2 * Real.log m) ≤ (Nat.primeCounting m : ℝ) := by
  obtain ⟨e, he, hpi⟩ := pi_alt
  have herr := tendsto_natCast_atTop_atTop.eventually
    (he.bound (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [herr, eventually_ge_atTop 3] with m hm hm3
  have hlog : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have heLower : (1 / 2 : ℝ) ≤ 1 + e (m : ℝ) := by
    have habs : |e (m : ℝ)| ≤ (1 / 2 : ℝ) := by simpa using hm
    linarith [neg_le_abs (e (m : ℝ))]
  have hformula := hpi (m : ℝ)
  norm_num at hformula
  rw [hformula]
  rw [show (m : ℝ) / (2 * Real.log m) =
      ((1 / 2 : ℝ) * m) / Real.log m by ring]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right heLower (Nat.cast_nonneg m)) hlog.le

/-- The fourth-root cutoff tends to infinity. -/
lemma tendsto_fourthRoot_atTop : Tendsto fourthRoot atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b ^ 4, fun n hn => ?_⟩
  have hb1 : b ^ 2 ≤ n.sqrt := by
    rw [Nat.le_sqrt]
    calc
      b ^ 2 * b ^ 2 = b ^ 4 := by ring
      _ ≤ n := hn
  exact Nat.le_sqrt.mpr (by simpa [pow_two] using hb1)

/-- The reciprocal mass of the small primes has the expected iterated-log
lower bound. -/
lemma eventually_smallPrimeMass_lower :
    ∀ᶠ n : ℕ in atTop,
      (1 / 8 : ℝ) * Real.log (Real.log (n : ℝ)) ≤
        ∑ p ∈ countSmallPrimes n, (p : ℝ)⁻¹ := by
  let C := Erdos469.reciprocalPrimeMertensConstant
  have hyTop : Tendsto fourthRoot atTop atTop := tendsto_fourthRoot_atTop
  have hsTop : Tendsto (fun n : ℕ => n.sqrt) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b ^ 2, fun n hn => Nat.le_sqrt.mpr (by simpa [pow_two] using hn)⟩
  have hloglogTop : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hsloglogTop :
      Tendsto (fun n : ℕ => Real.log (Real.log (n.sqrt : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_iff.mpr hsTop))
  filter_upwards
      [eventually_ge_atTop 256,
       hloglogTop.eventually (eventually_ge_atTop (8 * C)),
       hloglogTop.eventually (eventually_ge_atTop (2 * Real.log 3)),
       hsloglogTop.eventually (eventually_ge_atTop (2 * Real.log 3)),
       hyTop.eventually (eventually_ge_atTop 2)]
      with n hn hC hlog3 hslog3 hy2
  let s := n.sqrt
  let y := fourthRoot n
  have hs16 : 16 ≤ s := Nat.le_sqrt.mpr (by simpa [s] using hn)
  have hy4 : 4 ≤ y := by
    exact Nat.le_sqrt.mpr (by simpa [s, y, fourthRoot] using hs16)
  have hlog_n_sqrt :
      Real.log (n : ℝ) ≤ 3 * Real.log (s : ℝ) := by
    have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsquare : n ≤ 4 * (s * s) := by
      have hlt : n < (s + 1) * (s + 1) := by
        simpa [s, pow_two] using Nat.lt_succ_sqrt n
      nlinarith
    calc
      Real.log (n : ℝ) ≤ Real.log (4 * ((s : ℝ) * s)) := by
        apply Real.log_le_log hnpos
        exact_mod_cast hsquare
      _ = Real.log 4 + 2 * Real.log (s : ℝ) := by
        rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
          (mul_ne_zero hspos.ne' hspos.ne'), Real.log_mul hspos.ne' hspos.ne']
        ring
      _ ≤ 3 * Real.log (s : ℝ) := by
        have : Real.log (4 : ℝ) ≤ Real.log (s : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hs16.trans' (by omega))
        linarith
  have hhalf1 :
      (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) ≤
        Real.log (Real.log (s : ℝ)) := by
    have hlogn : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hlogs : 0 < Real.log (s : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < s by omega))
    have h := Real.log_le_log hlogn hlog_n_sqrt
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hlogs.ne'] at h
    have hlog3' : 2 * Real.log 3 ≤ Real.log (Real.log (n : ℝ)) := by
      simpa using hlog3
    linarith
  have hlog_s_y :
      Real.log (s : ℝ) ≤ 3 * Real.log (y : ℝ) := by
    have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
    have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    have hySquare : s ≤ 4 * (y * y) := by
      have hlt : s < (y + 1) * (y + 1) := by
        simpa [s, y, fourthRoot, pow_two] using Nat.lt_succ_sqrt s
      nlinarith
    calc
      Real.log (s : ℝ) ≤ Real.log (4 * ((y : ℝ) * y)) := by
        apply Real.log_le_log hspos
        exact_mod_cast hySquare
      _ = Real.log 4 + 2 * Real.log (y : ℝ) := by
        rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
          (mul_ne_zero hypos.ne' hypos.ne'), Real.log_mul hypos.ne' hypos.ne']
        ring
      _ ≤ 3 * Real.log (y : ℝ) := by
        have : Real.log (4 : ℝ) ≤ Real.log (y : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hy4)
        linarith
  have hhalf2 :
      (1 / 2 : ℝ) * Real.log (Real.log (s : ℝ)) ≤
        Real.log (Real.log (y : ℝ)) := by
    have hlogs : 0 < Real.log (s : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < s by omega))
    have hlogy : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have h := Real.log_le_log hlogs hlog_s_y
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hlogy.ne'] at h
    have hslog3' : 2 * Real.log 3 ≤ Real.log (Real.log (s : ℝ)) := by
      simpa [s] using hslog3
    linarith
  have hmertens := Erdos469.abs_primeReciprocalSum_sub_logLog_le hy2
  change (1 / 8 : ℝ) * Real.log (Real.log (n : ℝ)) ≤
    Erdos469.primeReciprocalSum y
  rw [abs_le] at hmertens
  have hquarter :
      (1 / 4 : ℝ) * Real.log (Real.log (n : ℝ)) ≤
        Real.log (Real.log (y : ℝ)) := by linarith
  dsimp [C] at hC
  linarith

/-- The fourth-root error is negligible compared with the target scale. -/
lemma eventually_fourthRoot_sq_le_scale :
    ∀ᶠ n : ℕ in atTop,
      ((fourthRoot n : ℝ) ^ 2) ≤ (1 / 64 : ℝ) * scale n := by
  have hsmall := (isLittleO_sqrt_mul_log.natCast_atTop).bound
    (by norm_num : (0 : ℝ) < 1 / 128)
  have hloglog := (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hsmall, hloglog, eventually_ge_atTop 3] with n hn hll hn3
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hroot : ((fourthRoot n : ℝ) ^ 2) ≤ Real.sqrt (n : ℝ) := by
    have hnat : (fourthRoot n) ^ 2 ≤ n.sqrt := Nat.sqrt_le' n.sqrt
    have hcast : ((fourthRoot n : ℝ) ^ 2) ≤ (n.sqrt : ℝ) := by exact_mod_cast hnat
    exact hcast.trans Real.nat_sqrt_le_real_sqrt
  have hsqrtlog : Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ (1 / 128 : ℝ) * n := by
    simpa [Real.norm_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ) * Real.log (n : ℝ)),
      Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ))] using hn
  rw [scale]
  calc
    ((fourthRoot n : ℝ) ^ 2) ≤ Real.sqrt (n : ℝ) := hroot
    _ ≤ (1 / 128 : ℝ) * (n : ℝ) / Real.log (n : ℝ) := by
      rw [le_div_iff₀ hlog]
      exact hsqrtlog
    _ ≤ (1 / 64 : ℝ) * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := by
      change 1 ≤ Real.log (Real.log (n : ℝ)) at hll
      have hcoef : (1 / 128 : ℝ) ≤
          (1 / 64 : ℝ) * Real.log (Real.log (n : ℝ)) := by
        nlinarith
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hh := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg n))
          (inv_nonneg.mpr hlog.le)
      calc
        1 / 128 * (n : ℝ) * (Real.log (n : ℝ))⁻¹ =
            (1 / 128 : ℝ) * n * (Real.log (n : ℝ))⁻¹ := by norm_num
        _ ≤ (1 / 64 : ℝ) * Real.log (Real.log (n : ℝ)) * n *
            (Real.log (n : ℝ))⁻¹ := hh
        _ = 1 / 64 * ((n : ℝ) * Real.log (Real.log (n : ℝ)) *
            (Real.log (n : ℝ))⁻¹) := by ring

/-- Quantitative cardinality lower bound for the construction. -/
theorem eventually_lowerBoundSet_card_lower :
    ∀ᶠ n : ℕ in atTop,
      (1 / 64 : ℝ) * scale n ≤ (lowerBoundSet n).card := by
  rcases eventually_atTop.1 eventually_primeCounting_lower with ⟨M, hM⟩
  have hcutTop := tendsto_fourthRoot_atTop.eventually (eventually_ge_atTop (max M 3))
  filter_upwards [hcutTop, eventually_smallPrimeMass_lower,
      eventually_fourthRoot_sq_le_scale, eventually_scale_pos,
      eventually_ge_atTop 256]
      with n hy hmass herr hscale hn
  let y := fourthRoot n
  have hyM : M ≤ y := (le_max_left M 3).trans hy
  have hy3 : 3 ≤ y := (le_max_right M 3).trans hy
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hsqrty : y ^ 2 ≤ n.sqrt := Nat.sqrt_le' n.sqrt
  have hsqrtn : n.sqrt ^ 2 ≤ n := Nat.sqrt_le' n
  have hpTerm : ∀ p ∈ countSmallPrimes n,
      (n : ℝ) / (4 * (p : ℝ) * Real.log n) - (y : ℝ) ≤
        ((countPartnerPrimes n p).card : ℝ) := by
    intro p hp
    have hpdata := mem_countSmallPrimes.mp hp
    have hp0 : 0 < p := hpdata.1.pos
    have hp_le_sqrt : p ≤ n.sqrt :=
      hpdata.2.trans (Nat.sqrt_le_sqrt (Nat.sqrt_le_self n))
    have h2p : 2 * p ≤ n := by
      have hy_le_sqrt : y ≤ n.sqrt := by
        simpa [y, fourthRoot] using Nat.sqrt_le_self n.sqrt
      have h2y : 2 ≤ n.sqrt := (show 2 ≤ y by omega).trans hy_le_sqrt
      calc
        2 * p ≤ n.sqrt * n.sqrt := Nat.mul_le_mul h2y hp_le_sqrt
        _ ≤ n := Nat.sqrt_le n
    let m := n / p
    have hym : y ≤ m := by
      rw [Nat.le_div_iff_mul_le hp0]
      calc
        y * p ≤ y * y := Nat.mul_le_mul_left y hpdata.2
        _ ≤ n.sqrt := by simpa [pow_two] using hsqrty
        _ ≤ n := Nat.sqrt_le_self n
    have hmM : M ≤ m := hyM.trans hym
    have hm2 : 2 ≤ m := (show 2 ≤ y by omega).trans hym
    have hmle : m ≤ n := Nat.div_le_self n p
    have hlogm : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    have hlogmn : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hmle)
    have hfloor := half_real_div_le_nat_div hp0 h2p
    have hratio :
        (n : ℝ) / (2 * (p : ℝ) * Real.log n) ≤
          (m : ℝ) / Real.log m := by
      calc
        (n : ℝ) / (2 * (p : ℝ) * Real.log n) =
            ((n : ℝ) / (2 * p)) / Real.log n := by ring
        _ ≤ (m : ℝ) / Real.log n :=
          div_le_div_of_nonneg_right hfloor hlogn.le
        _ ≤ (m : ℝ) / Real.log m :=
          div_le_div_of_nonneg_left (by positivity) hlogm hlogmn
    have hpnt := hM m hmM
    have hpiLower :
        (n : ℝ) / (4 * (p : ℝ) * Real.log n) ≤
          (Nat.primeCounting m : ℝ) := by
      calc
        (n : ℝ) / (4 * (p : ℝ) * Real.log n) =
            (1 / 2 : ℝ) * ((n : ℝ) / (2 * p * Real.log n)) := by ring
        _ ≤ (1 / 2 : ℝ) * ((m : ℝ) / Real.log m) := by gcongr
        _ = (m : ℝ) / (2 * Real.log m) := by ring
        _ ≤ (Nat.primeCounting m : ℝ) := hpnt
    have hpiy : (Nat.primeCounting y : ℝ) ≤ (y : ℝ) := by
      exact_mod_cast (primeCounting_le_self y)
    rw [card_partnerPrimes n p hym, Nat.cast_sub
      (Nat.monotone_primeCounting hym)]
    linarith
  have hpCard : (countSmallPrimes n).card ≤ y := by
    calc
      (countSmallPrimes n).card = Nat.primeCounting y := by
        simpa [countSmallPrimes, Erdos469.primesThrough, Nat.primesLE,
          Nat.primesBelow] using Nat.primesLE_card_eq_primeCounting y
      _ ≤ y := primeCounting_le_self y
  have hpairSum :
      (n : ℝ) / (4 * Real.log n) *
            (∑ p ∈ countSmallPrimes n, (p : ℝ)⁻¹) - (y : ℝ) ^ 2 ≤
        ((countPairs n).card : ℝ) := by
    rw [countPairs, Finset.card_sigma]
    push_cast
    calc
      (n : ℝ) / (4 * Real.log n) *
              (∑ p ∈ countSmallPrimes n, (p : ℝ)⁻¹) - (y : ℝ) ^ 2
          ≤ (n : ℝ) / (4 * Real.log n) *
              (∑ p ∈ countSmallPrimes n, (p : ℝ)⁻¹) -
                ((countSmallPrimes n).card : ℝ) * y := by
            have : (((countSmallPrimes n).card : ℝ) * y) ≤ (y : ℝ) ^ 2 := by
              rw [pow_two]
              exact_mod_cast Nat.mul_le_mul_right y hpCard
            linarith
      _ = ∑ p ∈ countSmallPrimes n,
            ((n : ℝ) / (4 * (p : ℝ) * Real.log n) - y) := by
          rw [Finset.sum_sub_distrib]
          simp_rw [Finset.sum_const, nsmul_eq_mul]
          rw [Finset.mul_sum]
          apply congrArg₂ (· - ·) ?_ rfl
          apply Finset.sum_congr rfl
          intro p hp
          have hp0 : (p : ℝ) ≠ 0 := by
            exact_mod_cast (mem_countSmallPrimes.mp hp).1.ne_zero
          field_simp
      _ ≤ ∑ p ∈ countSmallPrimes n, ((countPartnerPrimes n p).card : ℝ) :=
        Finset.sum_le_sum hpTerm
  have hmain :
      (1 / 32 : ℝ) * scale n - (y : ℝ) ^ 2 ≤
        ((countPairs n).card : ℝ) := by
    refine le_trans ?_ hpairSum
    apply sub_le_sub_right
    rw [scale]
    calc
      (1 / 32 : ℝ) * ((n : ℝ) * Real.log (Real.log n) / Real.log n) =
          (n : ℝ) / (4 * Real.log n) *
            ((1 / 8 : ℝ) * Real.log (Real.log n)) := by ring
      _ ≤ (n : ℝ) / (4 * Real.log n) *
          (∑ p ∈ countSmallPrimes n, (p : ℝ)⁻¹) := by
        gcongr
  have hcount : (1 / 64 : ℝ) * scale n ≤ (countPairs n).card := by
    have hhalf : (1 / 64 : ℝ) * scale n + (1 / 64 : ℝ) * scale n =
        (1 / 32 : ℝ) * scale n := by ring
    rw [← hhalf] at hmain
    linarith
  exact hcount.trans (by exact_mod_cast countPairs_card_le_lowerBoundSet_card n)

/-- Landau `Ω` form of the lower construction count. -/
theorem lowerBoundSet_isOmega_scale :
    Asymptotics.IsBigO atTop scale
      (fun n : ℕ => ((lowerBoundSet n).card : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 64
  filter_upwards [eventually_lowerBoundSet_card_lower,
    eventually_scale_pos] with n hn hs
  rw [Real.norm_of_nonneg hs.le, Real.norm_of_nonneg (by positivity)]
  linarith

/-- The lower construction transfers the same `Ω` bound to the extremal
cardinality itself. -/
theorem extremalSize_isOmega_scale :
    Asymptotics.IsBigO atTop scale
      (fun n : ℕ => (extremalSize n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 64
  filter_upwards [eventually_lowerBoundSet_card_lower,
    eventually_scale_pos] with n hn hs
  have hcard : ((lowerBoundSet n).card : ℝ) ≤ extremalSize n := by
    exact_mod_cast card_lowerBoundSet_le_extremalSize n
  rw [Real.norm_of_nonneg hs.le, Real.norm_of_nonneg (by positivity)]
  linarith

end Erdos888
