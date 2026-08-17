import ErdosProblems.Erdos220.Basic

/-!
# Finite Fourier lemmas for Erdős 220

This file contains the elementary finite Fourier input used in the
Montgomery--Vaughan moment calculation.  We use the grid
`exp (2 * pi * I / q)` and intervals `0, ..., h - 1`; translating the
interval to `1, ..., h` only multiplies its Fourier transform by a unit.
-/

open scoped BigOperators
open Finset

namespace Erdos220

noncomputable section

/-! ## Roots of unity and orthogonality -/

/-- The standard primitive `q`-th root of unity. -/
def fourierRoot (q : ℕ) : ℂ :=
  Complex.exp (2 * (↑Real.pi : ℂ) * Complex.I / q)

@[simp] theorem fourierRoot_ne_zero (q : ℕ) : fourierRoot q ≠ 0 := by
  exact Complex.exp_ne_zero _

/-- A complete nontrivial geometric sum on a root-of-unity grid vanishes. -/
theorem fourierRoot_sum_zero (q : ℕ) (hq : 2 ≤ q) (k : ℕ)
    (hk0 : 0 < k) (hkq : k < q) :
    ∑ a ∈ range q, fourierRoot q ^ (k * a) = 0 := by
  norm_num [pow_mul]
  rw [geom_sum_eq] <;> norm_num [fourierRoot]
  · rw [← pow_mul, Nat.mul_comm, pow_mul, ← Complex.exp_nat_mul, mul_comm,
      div_mul_cancel₀] <;>
      norm_num [show q ≠ 0 by positivity]
  · rw [← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_one_iff]
    norm_num [Complex.ext_iff, div_mul_eq_mul_div]
    intro x hx
    rw [div_eq_iff (by positivity)] at hx
    exact False.elim <|
      absurd hx <| by
        exact fun hx' => by
          exact absurd
            (Int.le_of_dvd (by positivity) <|
              show (q : ℤ) ∣ k from
                ⟨x, by
                  rw [← @Int.cast_inj ℝ]
                  push_cast
                  nlinarith [Real.pi_pos]⟩)
            (by
              norm_cast
              linarith)

/-- Orthogonality of additive characters on `Z/qZ`, in divisibility form. -/
theorem fourierRoot_orthogonality (q : ℕ) (hq : 0 < q) (k : ℤ) :
    ∑ a ∈ range q, fourierRoot q ^ (k * ↑a) =
      if (q : ℤ) ∣ k then q else 0 := by
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    norm_num [zpow_mul, fourierRoot]
    norm_num [← Complex.exp_nat_mul, mul_div_cancel₀, hq.ne']
  · obtain ⟨u, r, hr⟩ : ∃ u r : ℤ, 0 < r ∧ r < q ∧ k = q * u + r := by
      exact
        ⟨k / q, k % q,
          lt_of_le_of_ne (Int.emod_nonneg _ (by positivity)) (Ne.symm (by aesop)),
          Int.emod_lt_of_pos _ (by positivity),
          by rw [Int.mul_ediv_add_emod]⟩
    have h_exp : ∀ a : ℕ,
        fourierRoot q ^ (k * a) = fourierRoot q ^ (r * a) := by
      intro a
      simp [hr, fourierRoot]
      norm_num [zpow_add₀ (Complex.exp_ne_zero _), zpow_mul]
      norm_num [← Complex.exp_nat_mul, mul_div_cancel₀, hq.ne']
    convert fourierRoot_sum_zero q (by omega) r.natAbs (by omega) (by omega) using 1
    cases r <;> aesop
    all_goals exact Nat.cast_zero

/-! ## The Fourier transform of an interval -/

/-- The unnormalised Fourier transform of the interval `0, ..., h - 1`. -/
def intervalExponentialSum (q h a : ℕ) : ℂ :=
  ∑ t ∈ range h, fourierRoot q ^ (a * t)

/-- Ordered pairs in the interval which are congruent modulo `q`. -/
def congruentIntervalPairs (q h : ℕ) : Finset (ℕ × ℕ) :=
  (range h ×ˢ range h).filter fun tu => Nat.ModEq q tu.1 tu.2

/-- Exact finite Parseval identity for an interval on the `q`-point grid. -/
theorem interval_parseval (q h : ℕ) (hq : 0 < q) :
    ∑ a ∈ range q, ‖intervalExponentialSum q h a‖ ^ 2 =
      (q : ℝ) * (congruentIntervalPairs q h).card := by
  classical
  have norm_sq_expand : ∀ a ∈ range q,
      ‖intervalExponentialSum q h a‖ ^ 2 =
        ∑ t ∈ range h, ∑ u ∈ range h,
          fourierRoot q ^ (((t : ℤ) - u) * a) := by
    intro a _ha
    have norm_sq_mul_conj : ∀ z : ℂ, ‖z‖ ^ 2 = z * starRingEnd ℂ z := by
      simp +decide [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [norm_sq_mul_conj, intervalExponentialSum, map_sum, Finset.sum_mul]
    simp +decide [sub_mul, zpow_sub₀,
      show fourierRoot q ≠ 0 from Complex.exp_ne_zero _]
    norm_cast
    simp +decide [div_eq_mul_inv, Finset.mul_sum _ _ _]
    norm_num [fourierRoot, Complex.inv_def, Complex.normSq_eq_norm_sq,
      Complex.norm_exp]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro u hu
    congr 1
    ring
    all_goals simp only [Nat.mul_comm]
  have swap_to_orthog :
      ∑ a ∈ range q, ‖intervalExponentialSum q h a‖ ^ 2 =
        ∑ t ∈ range h, ∑ u ∈ range h,
          ∑ a ∈ range q, fourierRoot q ^ (((t : ℤ) - u) * a) := by
    push_cast [Finset.sum_congr rfl norm_sq_expand]
    exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)
  apply Complex.ofReal_injective
  rw [swap_to_orthog]
  simp_rw [fourierRoot_orthogonality q hq]
  push_cast
  have hmod : ∀ t u : ℕ,
      ((q : ℤ) ∣ (t : ℤ) - u) ↔ Nat.ModEq q t u := by
    intro t u
    rw [Nat.modEq_iff_dvd]
    constructor <;> intro h
    · rcases h with ⟨c, hc⟩
      exact ⟨-c, by linarith⟩
    · rcases h with ⟨c, hc⟩
      exact ⟨-c, by linarith⟩
  simp_rw [hmod]
  rw [← Finset.sum_product']
  change (∑ tu ∈ range h ×ˢ range h,
      if Nat.ModEq q tu.1 tu.2 then (q : ℂ) else 0) =
    (q : ℂ) * ((congruentIntervalPairs q h).card : ℂ)
  calc
    _ = (q : ℂ) * (∑ tu ∈ range h ×ˢ range h,
        if Nat.ModEq q tu.1 tu.2 then 1 else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tu htu
      split_ifs <;> simp
    _ = _ := by simp [congruentIntervalPairs, Finset.sum_boole]

/-- Below the modulus, congruence of two interval points is equality. -/
theorem congruentIntervalPairs_card_of_le (q h : ℕ) (hh : h ≤ q) :
    (congruentIntervalPairs q h).card = h := by
  classical
  have hpairs : congruentIntervalPairs q h =
      (range h).image fun t => (t, t) := by
    ext tu
    rcases tu with ⟨t, u⟩
    simp only [congruentIntervalPairs, mem_filter, mem_product, mem_range,
      mem_image]
    constructor
    · rintro ⟨⟨ht, hu⟩, htu⟩
      have heq : t = u := htu.eq_of_lt_of_lt (lt_of_lt_of_le ht hh)
        (lt_of_lt_of_le hu hh)
      subst u
      exact ⟨t, ht, rfl⟩
    · rintro ⟨v, hv, htu⟩
      cases htu
      exact ⟨⟨hv, hv⟩, Nat.ModEq.refl t⟩
  rw [hpairs, card_image_of_injective]
  · simp
  · intro t u htu
    exact congrArg Prod.fst htu

/-- The interval Parseval sum is at most the trivial diagonal-pair bound. -/
theorem interval_parseval_le (q h : ℕ) (hq : 0 < q) :
    ∑ a ∈ range q, ‖intervalExponentialSum q h a‖ ^ 2 ≤
      (q : ℝ) * h ^ 2 := by
  rw [interval_parseval q h hq]
  gcongr
  have hc := Finset.card_filter_le (range h ×ˢ range h)
    (p := fun tu => Nat.ModEq q tu.1 tu.2)
  norm_cast
  simpa only [congruentIntervalPairs, Finset.card_product, card_range, pow_two] using hc

/-- The spectrum after complete `q`-blocks have been removed. -/
def centeredIntervalExponentialSum (q h a : ℕ) : ℂ :=
  intervalExponentialSum q (h % q) a

/-- Exact Parseval for the residual interval of length `h % q`. -/
theorem centered_interval_parseval (q h : ℕ) (hq : 0 < q) :
    ∑ a ∈ range q, ‖centeredIntervalExponentialSum q h a‖ ^ 2 =
      (q : ℝ) * ((h % q : ℕ) : ℝ) := by
  simp only [centeredIntervalExponentialSum]
  rw [interval_parseval q (h % q) hq,
    congruentIntervalPairs_card_of_le]
  exact (Nat.mod_lt h hq).le

/-- The residual-interval `L²` bound used in the centered divisor expansion. -/
theorem centered_interval_parseval_le (q h : ℕ) (hq : 0 < q) :
    ∑ a ∈ range q, ‖centeredIntervalExponentialSum q h a‖ ^ 2 ≤
      (q : ℝ) * ((min q h : ℕ) : ℝ) := by
  rw [centered_interval_parseval q h hq]
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast le_min (Nat.mod_lt h hq).le (Nat.mod_le h q)
  · positivity

/-- Restricting to primitive frequencies can only decrease the residual `L²` mass. -/
theorem centered_interval_primitive_parseval_le (q h : ℕ) (hq : 0 < q) :
    ∑ a ∈ (range q).filter (fun a => a.Coprime q),
        ‖centeredIntervalExponentialSum q h a‖ ^ 2 ≤
      (q : ℝ) * ((min q h : ℕ) : ℝ) := by
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ => sq_nonneg _).trans ?_
  exact centered_interval_parseval_le q h hq

/-! ## Ramanujan sums -/

/-- The exponential definition of the Ramanujan sum `c_q(m)`. -/
def ramanujanSum (q m : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter fun a => a.Coprime q, fourierRoot q ^ (a * m)

/-- Evaluation of a Ramanujan sum at a prime modulus. -/
theorem ramanujanSum_prime (p m : ℕ) (hp : p.Prime) :
    ramanujanSum p m = if p ∣ m then ((p - 1 : ℕ) : ℂ) else (-1 : ℂ) := by
  have hp0 : 0 < p := hp.pos
  have hfilter : (range p).filter (fun a => a.Coprime p) = (range p).erase 0 := by
    ext a
    simp only [mem_filter, mem_range, mem_erase, ne_eq]
    constructor
    · rintro ⟨ha, hcop⟩
      exact ⟨by
        intro ha0
        subst a
        have hp1 : p = 1 := by simpa using hcop
        exact hp.ne_one hp1, ha⟩
    · rintro ⟨ha0, ha⟩
      exact ⟨ha, (hp.coprime_iff_not_dvd.mpr fun hpa => by
        exact ha0 (Nat.eq_zero_of_dvd_of_lt hpa ha)).symm⟩
  rw [ramanujanSum, hfilter]
  have herase :
      (∑ a ∈ (range p).erase 0, fourierRoot p ^ (a * m)) =
        (∑ a ∈ range p, fourierRoot p ^ (a * m)) - 1 := by
    rw [eq_sub_iff_add_eq]
    simpa only [zero_mul, pow_zero] using
      (Finset.sum_erase_add (s := range p)
        (f := fun a => fourierRoot p ^ (a * m)) (mem_range.mpr hp0))
  rw [herase]
  have hortho := fourierRoot_orthogonality p hp0 (m : ℤ)
  norm_cast at hortho
  simp only [Nat.cast_ite, Nat.cast_zero] at hortho
  have hortho' :
      (∑ a ∈ range p, fourierRoot p ^ (a * m)) =
        if p ∣ m then (p : ℂ) else 0 := by
    simpa only [Nat.mul_comm] using hortho
  by_cases hpm : p ∣ m
  · simp only [if_pos hpm] at hortho' ⊢
    rw [hortho', Nat.cast_sub hp.one_le]
    ring
  · simp only [if_neg hpm] at hortho' ⊢
    rw [hortho']
    ring

/-- The prime factor occurring in the squarefree Ramanujan expansion. -/
def primeRamanujanFactor (p m : ℕ) : ℂ :=
  ((p - 1 : ℕ) : ℂ) / p * (1 - ramanujanSum p m / (p - 1 : ℕ))

/-- At a prime, the Ramanujan factor is exactly the coprimality indicator. -/
theorem primeRamanujanFactor_eq_indicator (p m : ℕ) (hp : p.Prime) :
    primeRamanujanFactor p m = if m.Coprime p then 1 else 0 := by
  have hp1 : (p - 1 : ℕ) ≠ 0 := by have := hp.two_le; omega
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1c : ((p - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hp1
  rw [primeRamanujanFactor, ramanujanSum_prime p m hp]
  by_cases hpm : p ∣ m
  · have hnc : ¬ m.Coprime p := by
      simpa [Nat.coprime_comm, hp.coprime_iff_not_dvd] using hpm
    rw [if_pos hpm, if_neg hnc]
    simp only [div_self hp1c, sub_self, mul_zero]
  · have hc : m.Coprime p := by
      simpa [Nat.coprime_comm, hp.coprime_iff_not_dvd] using hpm
    rw [if_neg hpm, if_pos hc]
    field_simp [hp0, hp1c]
    rw [Nat.cast_sub hp.one_le]
    ring

/-- Product form of the squarefree Ramanujan expansion. -/
def squarefreeRamanujanExpansion (s m : ℕ) : ℂ :=
  ∏ p ∈ s.primeFactors, primeRamanujanFactor p m

/-- The squarefree Ramanujan product is the coprimality indicator. -/
theorem squarefreeRamanujanExpansion_eq_indicator (s m : ℕ) (hs : Squarefree s) :
    squarefreeRamanujanExpansion s m = if m.Coprime s then 1 else 0 := by
  rw [squarefreeRamanujanExpansion]
  rw [Finset.prod_congr rfl fun p hp =>
    primeRamanujanFactor_eq_indicator p m (Nat.prime_of_mem_primeFactors hp)]
  rw [Finset.prod_boole]
  congr 1
  rw [← Nat.coprime_prod_right_iff, Nat.prod_primeFactors_of_squarefree hs]

/-! ## The subset (squarefree-divisor) expansion -/

/-- The product of the prime densities. -/
def fourierDensity (s : ℕ) : ℂ :=
  ∏ p ∈ s.primeFactors, (((p - 1 : ℕ) : ℂ) / p)

/-- The nonconstant part of the prime Ramanujan factor. -/
def ramanujanCorrection (p m : ℕ) : ℂ :=
  -ramanujanSum p m / (p - 1 : ℕ)

/-- The term indexed by a squarefree divisor, represented by its set of primes. -/
def ramanujanSubsetTerm (T : Finset ℕ) (m : ℕ) : ℂ :=
  ∏ p ∈ T, ramanujanCorrection p m

/-- Prime products give the usual density `φ(s)/s`. -/
theorem fourierDensity_eq_density (s : ℕ) (hs : 0 < s) :
    fourierDensity s = (density s : ℂ) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hPnat : ∏ p ∈ s.primeFactors, p ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hPC : ((∏ p ∈ s.primeFactors, p : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hPnat
  have htot := Nat.totient_mul_prod_primeFactors s
  rw [fourierDensity, density]
  push_cast
  change (∏ p ∈ s.primeFactors, (((p - 1 : ℕ) : ℂ) / p)) =
    (s.totient : ℂ) / s
  rw [Finset.prod_div_distrib]
  have hPC' : (∏ p ∈ s.primeFactors, (p : ℂ)) ≠ 0 := by
    simpa only [Nat.cast_prod] using hPC
  apply (div_eq_div_iff hPC' hsC).2
  convert congrArg (fun n : ℕ => (n : ℂ)) htot.symm using 1 <;>
    push_cast <;> ring

/-- Expanding the product over primes gives the sum over squarefree divisors. -/
theorem squarefreeRamanujanExpansion_eq_subsetSum (s m : ℕ) :
    squarefreeRamanujanExpansion s m =
      fourierDensity s *
        ∑ T ∈ s.primeFactors.powerset, ramanujanSubsetTerm T m := by
  simp only [squarefreeRamanujanExpansion, fourierDensity, ramanujanSubsetTerm]
  calc
    ∏ p ∈ s.primeFactors, primeRamanujanFactor p m =
        ∏ p ∈ s.primeFactors,
          ((((p - 1 : ℕ) : ℂ) / p) * (1 + ramanujanCorrection p m)) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [primeRamanujanFactor, ramanujanCorrection]
      ring
    _ = (∏ p ∈ s.primeFactors, (((p - 1 : ℕ) : ℂ) / p)) *
        ∏ p ∈ s.primeFactors, (1 + ramanujanCorrection p m) := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by rw [Finset.prod_one_add]

/-- Coprimality in squarefree modulus, in divisor/Ramanujan expansion form. -/
theorem coprimeIndicator_eq_ramanujanSubsetSum (s m : ℕ) (hs : Squarefree s) :
    (if s.Coprime m then (1 : ℂ) else 0) =
      fourierDensity s *
        ∑ T ∈ s.primeFactors.powerset, ramanujanSubsetTerm T m := by
  rw [← squarefreeRamanujanExpansion_eq_subsetSum]
  simpa [Nat.coprime_comm] using
    (squarefreeRamanujanExpansion_eq_indicator s m hs).symm

/-! ## Translated interval counts -/

/-- The natural unit count is the sum of the squarefree Fourier indicator. -/
theorem unitCount_cast_eq_squarefreeRamanujanExpansion
    (s h u : ℕ) (hs : Squarefree s) :
    (unitCount s h u : ℂ) =
      ∑ t ∈ Finset.Icc 1 h, squarefreeRamanujanExpansion s (u + t) := by
  rw [unitCount]
  simp_rw [squarefreeRamanujanExpansion_eq_indicator _ _ hs]
  simp [Nat.coprime_comm, Finset.sum_boole]

/-- Exact divisor-sum expansion of a translated interval count. -/
theorem unitCount_cast_eq_ramanujanSubsetSum
    (s h u : ℕ) (hs : Squarefree s) :
    (unitCount s h u : ℂ) =
      fourierDensity s * ∑ t ∈ Finset.Icc 1 h,
        ∑ T ∈ s.primeFactors.powerset, ramanujanSubsetTerm T (u + t) := by
  rw [unitCount_cast_eq_squarefreeRamanujanExpansion s h u hs]
  simp_rw [squarefreeRamanujanExpansion_eq_subsetSum]
  rw [Finset.mul_sum]

/-- Nonempty subsets are precisely the nonconstant terms in the expansion. -/
def nonconstantRamanujanSubsets (s : ℕ) : Finset (Finset ℕ) :=
  s.primeFactors.powerset.erase ∅

/-- The centered interval count is exactly the sum of the nonconstant
squarefree-divisor terms. -/
theorem unitCount_centered_eq_ramanujanSubsetSum
    (s h u : ℕ) (hs : Squarefree s) :
    (unitCount s h u : ℂ) - h * fourierDensity s =
      fourierDensity s *
        ∑ T ∈ nonconstantRamanujanSubsets s,
          ∑ t ∈ Finset.Icc 1 h, ramanujanSubsetTerm T (u + t) := by
  rw [unitCount_cast_eq_ramanujanSubsetSum s h u hs]
  rw [Finset.sum_comm]
  have hempty : ∅ ∈ s.primeFactors.powerset := Finset.empty_mem_powerset _
  rw [← Finset.add_sum_erase _ _ hempty]
  simp only [ramanujanSubsetTerm, Finset.prod_empty, Finset.sum_const,
    Nat.card_Icc, nsmul_eq_mul,
    nonconstantRamanujanSubsets]
  simp only [Nat.add_sub_cancel]
  ring

/-! ## Expansion into prime-frequency tuples -/

/-- A primitive frequency modulo `p`, represented by its least natural residue. -/
def PrimitiveFrequency (p : ℕ) :=
  {a : ℕ // a ∈ (Finset.range p).filter fun a => a.Coprime p}

instance primitiveFrequencyFintype (p : ℕ) : Fintype (PrimitiveFrequency p) :=
  Fintype.ofFinset ((Finset.range p).filter fun a => a.Coprime p) (fun _ => Iff.rfl)

/-- One primitive frequency for every prime in `T`. -/
abbrev PrimitiveFrequencyTuple (T : Finset ℕ) :=
  ∀ p : T, PrimitiveFrequency p.1

/-- The product character attached to a tuple of prime frequencies. -/
def primitiveTupleCharacter {T : Finset ℕ}
    (a : PrimitiveFrequencyTuple T) (m : ℕ) : ℂ :=
  ∏ p : T, fourierRoot p.1 ^ ((a p).1 * m)

/-- The exponential Ramanujan product is a sum over primitive frequency tuples. -/
theorem ramanujanSubsetTerm_eq_frequencySum (T : Finset ℕ) (m : ℕ) :
    ramanujanSubsetTerm T m =
      (∏ p ∈ T, (-(1 : ℂ) / (p - 1 : ℕ))) *
        ∑ a : PrimitiveFrequencyTuple T, primitiveTupleCharacter a m := by
  classical
  rw [ramanujanSubsetTerm]
  have hprime (p : ℕ) :
      ramanujanCorrection p m =
        (-(1 : ℂ) / (p - 1 : ℕ)) *
          ∑ a : PrimitiveFrequency p, fourierRoot p ^ (a.1 * m) := by
    rw [ramanujanCorrection, ramanujanSum]
    rw [Finset.sum_subtype (F := primitiveFrequencyFintype p)
      ((Finset.range p).filter fun a => a.Coprime p)
      (fun _ => Iff.rfl) (fun a => fourierRoot p ^ (a * m))]
    simp only [Nat.mul_comm]
    simp only [div_eq_mul_inv, neg_mul, one_mul]
    congr 1
    exact mul_comm _ _
  simp_rw [hprime]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_attach T]
  have hatt : T.attach = (Finset.univ : Finset T) := by ext p; simp
  rw [hatt]
  simpa only [primitiveTupleCharacter] using
    (Fintype.prod_sum (R := ℂ)
      (f := fun p : T => fun a : PrimitiveFrequency p.1 =>
        fourierRoot p.1 ^ (a.1 * m)))

/-- Summing a squarefree-divisor term over a translated interval exposes
the combined interval character estimated by product Parseval. -/
theorem sum_ramanujanSubsetTerm_eq_frequencySum (T : Finset ℕ) (h u : ℕ) :
    ∑ t ∈ Finset.Icc 1 h, ramanujanSubsetTerm T (u + t) =
      (∏ p ∈ T, (-(1 : ℂ) / (p - 1 : ℕ))) *
        ∑ a : PrimitiveFrequencyTuple T,
          ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t) := by
  simp_rw [ramanujanSubsetTerm_eq_frequencySum]
  rw [← Finset.mul_sum]
  congr 1
  change (∑ t ∈ Finset.Icc 1 h,
      ∑ a ∈ (Finset.univ : Finset (PrimitiveFrequencyTuple T)),
        primitiveTupleCharacter a (u + t)) =
    ∑ a ∈ (Finset.univ : Finset (PrimitiveFrequencyTuple T)),
      ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t)
  exact Finset.sum_comm

end

/-! ### Complete-period orthogonality for six frequency tuples -/

private theorem complex_exp_pow_nat (z : ℂ) (n : ℕ) :
    Complex.exp z ^ n = Complex.exp ((n : ℂ) * z) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, Complex.exp_add]

theorem fourierRoot_pow_of_dvd {p s k : ℕ} (hs : 0 < s) (hp : 0 < p) (hps : p ∣ s) :
    fourierRoot p ^ k = fourierRoot s ^ (k * (s / p)) := by
  have hsp : 0 < s / p := Nat.div_pos (Nat.le_of_dvd hs hps) hp
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  have hspC : ((s / p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hsp)
  have hfactor : (s : ℂ) = (p : ℂ) * (s / p : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hps).symm
  simp only [fourierRoot, complex_exp_pow_nat, Nat.cast_mul]
  congr 1
  rw [hfactor]
  field_simp [hpC, hspC]

private theorem finset_prod_pow_eq_pow_sum {α : Type*} (S : Finset α)
    (f : α → ℕ) (z : ℂ) :
    ∏ x ∈ S, z ^ f x = z ^ (∑ x ∈ S, f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih => simp [hx, ih, pow_add]

def sixFrequencyNumerator (s : ℕ) (U : Fin 6 → Finset ℕ)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) : ℕ :=
  ∑ i : Fin 6, ∑ p : U i, (a i p).1 * (s / p.1)

def sixLocalFrequencyNat {U : Fin 6 → Finset ℕ}
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) (p : ℕ) : ℕ :=
  ∑ i : Fin 6, if hp : p ∈ U i then (a i ⟨p, hp⟩).1 else 0

def sixLocalFrequency {U : Fin 6 → Finset ℕ}
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) (p : ℕ) : ZMod p :=
  (sixLocalFrequencyNat a p : ZMod p)

def sixPrimeCompatible (s : ℕ) {U : Fin 6 → Finset ℕ}
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) : Prop :=
  ∀ p ∈ s.primeFactors, sixLocalFrequency a p = 0

noncomputable instance instDecidableSixPrimeCompatible
    (s : ℕ) {U : Fin 6 → Finset ℕ}
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) :
    Decidable (sixPrimeCompatible s a) :=
  Classical.propDecidable _

theorem sixLocalFrequency_eq_zero_iff {U : Fin 6 → Finset ℕ}
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) (p : ℕ) :
    sixLocalFrequency a p = 0 ↔ p ∣ sixLocalFrequencyNat a p := by
  simp [sixLocalFrequency, ZMod.natCast_eq_zero_iff]

def sixPrimeWeightedNumerator (s : ℕ) {U : Fin 6 → Finset ℕ}
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) : ℕ :=
  ∑ p ∈ s.primeFactors, sixLocalFrequencyNat a p * (s / p)

theorem sixFrequencyNumerator_eq_primeWeighted
    (s : ℕ) {U : Fin 6 → Finset ℕ}
    (hU : ∀ i, U i ⊆ s.primeFactors)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) :
    sixFrequencyNumerator s U a = sixPrimeWeightedNumerator s a := by
  classical
  unfold sixFrequencyNumerator sixPrimeWeightedNumerator sixLocalFrequencyNat
  calc
    ∑ i : Fin 6, ∑ p : U i, (a i p).1 * (s / p.1) =
        ∑ i : Fin 6, ∑ p ∈ s.primeFactors,
          if hp : p ∈ U i then (a i ⟨p, hp⟩).1 * (s / p) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        ∑ p : U i, (a i p).1 * (s / p.1) =
            ∑ p : U i, if hp : p.1 ∈ U i then
              (a i ⟨p.1, hp⟩).1 * (s / p.1) else 0 := by simp
        _ = ∑ p ∈ U i, if hp : p ∈ U i then
              (a i ⟨p, hp⟩).1 * (s / p) else 0 := by
          symm
          apply Finset.sum_subtype (U i)
          intro p
          rfl
        _ = ∑ p ∈ s.primeFactors, if hp : p ∈ U i then
              (a i ⟨p, hp⟩).1 * (s / p) else 0 := by
          apply Finset.sum_subset (hU i)
          intro p hp hpn
          simp [hpn]
    _ = ∑ p ∈ s.primeFactors, ∑ i : Fin 6,
          (if hp : p ∈ U i then (a i ⟨p, hp⟩).1 else 0) * (s / p) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro i hi
      split <;> simp_all
    _ = ∑ p ∈ s.primeFactors,
          (∑ i : Fin 6, if hp : p ∈ U i then (a i ⟨p, hp⟩).1 else 0) *
            (s / p) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_mul]

theorem sixPrimeWeightedNumerator_dvd_iff
    {s : ℕ} (hsq : Squarefree s) {U : Fin 6 → Finset ℕ}
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) :
    s ∣ sixPrimeWeightedNumerator s a ↔ sixPrimeCompatible s a := by
  classical
  constructor
  · intro htotal p hp
    apply (sixLocalFrequency_eq_zero_iff a p).2
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hps : p ∣ s := Nat.dvd_of_mem_primeFactors hp
    have hpTotal : p ∣ sixPrimeWeightedNumerator s a := hps.trans htotal
    have hrest : p ∣ ∑ q ∈ s.primeFactors.erase p,
        sixLocalFrequencyNat a q * (s / q) := by
      apply Finset.dvd_sum
      intro q hq
      have hq' := Finset.mem_erase.mp hq
      have hqPrime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq'.2
      have hqs : q ∣ s := Nat.dvd_of_mem_primeFactors hq'.2
      have hpProd : p ∣ q * (s / q) := by
        simpa [Nat.mul_div_cancel' hqs] using hps
      have hpQuot : p ∣ s / q := by
        rcases hpPrime.dvd_mul.mp hpProd with hpq | hpQuot
        · have hpqeq : q = p := (hqPrime.dvd_iff_eq hpPrime.ne_one).mp hpq
          exact (hq'.1 hpqeq).elim
        · exact hpQuot
      exact dvd_mul_of_dvd_right hpQuot _
    have hpTerm : p ∣ sixLocalFrequencyNat a p * (s / p) := by
      apply (Nat.dvd_add_iff_right hrest).mpr
      rw [Finset.sum_erase_add s.primeFactors
        (fun q ↦ sixLocalFrequencyNat a q * (s / q)) hp]
      exact hpTotal
    rcases hpPrime.dvd_mul.mp hpTerm with hpLocal | hpQuot
    · exact hpLocal
    · have hcop : p.Coprime (s / p) := by
        apply Nat.coprime_of_squarefree_mul
        simpa [Nat.mul_div_cancel' hps] using hsq
      exact ((hpPrime.coprime_iff_not_dvd).mp hcop hpQuot).elim
  · intro hcompat
    unfold sixPrimeWeightedNumerator
    apply Finset.dvd_sum
    intro p hp
    have hps : p ∣ s := Nat.dvd_of_mem_primeFactors hp
    have hpLocal : p ∣ sixLocalFrequencyNat a p :=
      (sixLocalFrequency_eq_zero_iff a p).1 (hcompat p hp)
    rcases hpLocal with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    calc
      p * k * (s / p) = p * (s / p) * k := by ac_rfl
      _ = s * k := by rw [Nat.mul_div_cancel' hps]

theorem sixFrequencyNumerator_dvd_iff_primeCompatible
    {s : ℕ} (hsq : Squarefree s) {U : Fin 6 → Finset ℕ}
    (hU : ∀ i, U i ⊆ s.primeFactors)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) :
    s ∣ sixFrequencyNumerator s U a ↔ sixPrimeCompatible s a := by
  rw [sixFrequencyNumerator_eq_primeWeighted s hU a]
  exact sixPrimeWeightedNumerator_dvd_iff hsq a

theorem primitiveTupleCharacter_eq_fourierRoot_pow
    {s : ℕ} (hs : 0 < s) {T : Finset ℕ} (hT : T ⊆ s.primeFactors)
    (a : PrimitiveFrequencyTuple T) (u : ℕ) :
    primitiveTupleCharacter a u =
      fourierRoot s ^ ((∑ p : T, (a p).1 * (s / p.1)) * u) := by
  classical
  unfold primitiveTupleCharacter
  have hterm (p : T) :
      fourierRoot p.1 ^ ((a p).1 * u) =
        fourierRoot s ^ (((a p).1 * (s / p.1)) * u) := by
    have hp_mem : p.1 ∈ s.primeFactors := hT p.2
    have hp_prime : Nat.Prime p.1 := Nat.prime_of_mem_primeFactors hp_mem
    have hp_dvd : p.1 ∣ s := Nat.dvd_of_mem_primeFactors hp_mem
    convert fourierRoot_pow_of_dvd hs hp_prime.pos hp_dvd (k := (a p).1 * u) using 1
    all_goals ring
  simp_rw [hterm]
  rw [finset_prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.sum_mul]

theorem six_primitiveTupleCharacter_eq_fourierRoot_pow
    {s : ℕ} (hs : 0 < s) {U : Fin 6 → Finset ℕ}
    (hU : ∀ i, U i ⊆ s.primeFactors)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) (u : ℕ) :
    ∏ i : Fin 6, primitiveTupleCharacter (a i) u =
      fourierRoot s ^ (sixFrequencyNumerator s U a * u) := by
  classical
  simp_rw [primitiveTupleCharacter_eq_fourierRoot_pow hs (hU _)]
  rw [finset_prod_pow_eq_pow_sum]
  congr 1
  unfold sixFrequencyNumerator
  rw [Finset.sum_mul]

theorem six_primitiveTupleCharacter_orthogonality_global
    {s : ℕ} (hs : 0 < s) {U : Fin 6 → Finset ℕ}
    (hU : ∀ i, U i ⊆ s.primeFactors)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) :
    ∑ u ∈ Finset.range s, ∏ i : Fin 6, primitiveTupleCharacter (a i) u =
      if s ∣ sixFrequencyNumerator s U a then (s : ℂ) else 0 := by
  classical
  simp_rw [six_primitiveTupleCharacter_eq_fourierRoot_pow hs hU a]
  simpa only [← Int.natCast_mul, zpow_natCast, Int.natCast_dvd_natCast,
    Nat.cast_ite, Nat.cast_zero] using
    fourierRoot_orthogonality s hs (sixFrequencyNumerator s U a : ℤ)

theorem six_primitiveTupleCharacter_orthogonality
    {s : ℕ} (hs : 0 < s) (hsq : Squarefree s)
    {U : Fin 6 → Finset ℕ} (hU : ∀ i, U i ⊆ s.primeFactors)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) :
    ∑ u ∈ Finset.range s, ∏ i : Fin 6, primitiveTupleCharacter (a i) u =
      if sixPrimeCompatible s a then (s : ℂ) else 0 := by
  classical
  rw [six_primitiveTupleCharacter_orthogonality_global hs hU a]
  by_cases h : sixPrimeCompatible s a
  · rw [if_pos h, if_pos ((sixFrequencyNumerator_dvd_iff_primeCompatible hsq hU a).2 h)]
  · rw [if_neg h, if_neg]
    intro hd
    exact h ((sixFrequencyNumerator_dvd_iff_primeCompatible hsq hU a).1 hd)

end Erdos220
