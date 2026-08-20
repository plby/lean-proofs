/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.PrimeReciprocal
import ErdosProblems.Erdos980.External.Erdos822.PrimeIntervals
import ErdosProblems.Erdos980.External.Erdos822.StructuredInputs
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The three cofactor layers in Erdős Problem 822

At a perfect-sixtieth-power scale `x = N^60`, the GIL cofactors have the
shape `k*r*q` with `k ≤ N`, `N^4 < r ≤ N^5`, and
`N^21 < q ≤ N^22`.  This file first formalizes the raw finite product and
its unique factorization.  The later good-set filters are subfinsets of this
raw layer.
-/

namespace Erdos822

open scoped BigOperators Finset

/-- The unrestricted small-factor layer. -/
def smallFactors (N : ℕ) : Finset ℕ := Finset.Icc 1 N

/-- The middle prime layer, corresponding to `(x^(1/15),x^(1/12)]` at
`x=N^60`.  The lower endpoint is written closed; for `N ≥ 2`, `N^4` is
composite, so this agrees with the paper's open endpoint. -/
def middlePrimes (N : ℕ) : Finset ℕ :=
  (Finset.Icc (N ^ 4) (N ^ 5)).filter Nat.Prime

/-- The large prime layer, corresponding to `(x^(7/20),x^(11/30)]` at
`x=N^60`. -/
def largePrimes (N : ℕ) : Finset ℕ :=
  (Finset.Icc (N ^ 21) (N ^ 22)).filter Nat.Prime

/-- Raw triples `(k,r,q)` before the GIL normal-order filters are imposed. -/
def rawCofactorTriples (N : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (smallFactors N).product ((middlePrimes N).product (largePrimes N))

/-- The cofactor represented by a raw triple. -/
def cofactorProduct (t : ℕ × (ℕ × ℕ)) : ℕ := t.1 * t.2.1 * t.2.2

/-- The raw cofactor layer as a finset of integers. -/
def rawCofactors (N : ℕ) : Finset ℕ :=
  (rawCofactorTriples N).image cofactorProduct

/-- Reciprocal mass of the raw cofactor layer. -/
noncomputable def reciprocalRawCofactorSum (N : ℕ) : ℝ :=
  ∑ m ∈ rawCofactors N, (1 : ℝ) / m

@[simp]
theorem mem_smallFactors_iff {N k : ℕ} :
    k ∈ smallFactors N ↔ 1 ≤ k ∧ k ≤ N := by
  simp [smallFactors]

@[simp]
theorem mem_middlePrimes_iff {N r : ℕ} :
    r ∈ middlePrimes N ↔ N ^ 4 ≤ r ∧ r ≤ N ^ 5 ∧ r.Prime := by
  simp [middlePrimes, and_assoc]

@[simp]
theorem mem_largePrimes_iff {N q : ℕ} :
    q ∈ largePrimes N ↔ N ^ 21 ≤ q ∧ q ≤ N ^ 22 ∧ q.Prime := by
  simp [largePrimes, and_assoc]

@[simp]
theorem mem_rawCofactorTriples_iff {N k r q : ℕ} :
    (k, r, q) ∈ rawCofactorTriples N ↔
      k ∈ smallFactors N ∧ r ∈ middlePrimes N ∧ q ∈ largePrimes N := by
  simp [rawCofactorTriples, and_assoc]

/-- For `N ≥ 2`, the three layers are strictly separated: `k < r < q` and
even the product `k*r` is smaller than `q`. -/
theorem rawCofactorTriples_separated {N k r q : ℕ} (hN : 2 ≤ N)
    (h : (k, r, q) ∈ rawCofactorTriples N) :
    0 < k ∧ k < r ∧ k * r < q := by
  rw [mem_rawCofactorTriples_iff] at h
  have hk := mem_smallFactors_iff.mp h.1
  have hr := mem_middlePrimes_iff.mp h.2.1
  have hq := mem_largePrimes_iff.mp h.2.2
  have hNpos : 0 < N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNltN4 : N < N ^ 4 := by
    simpa using Nat.pow_lt_pow_right (by omega : 1 < N) (by omega : 1 < 4)
  have hN6ltN21 : N ^ 6 < N ^ 21 := by
    exact Nat.pow_lt_pow_right (by omega : 1 < N) (by omega)
  have hkrle : k * r ≤ N ^ 6 := by
    calc
      k * r ≤ N * (N ^ 5) := Nat.mul_le_mul hk.2 hr.2.1
      _ = N ^ 6 := by ring
  constructor
  · omega
  constructor
  · exact hk.2.trans_lt (hNltN4.trans_le hr.1)
  · exact hkrle.trans_lt (hN6ltN21.trans_le hq.1)

/-- The map `(k,r,q) ↦ k*r*q` is injective on the raw layer.  First the
largest prime `q` is recovered, then the middle prime `r`, and finally `k`.
-/
theorem cofactorProduct_injOn_rawCofactorTriples {N : ℕ} (hN : 2 ≤ N) :
    Set.InjOn cofactorProduct (rawCofactorTriples N) := by
  intro a ha b hb hab
  rcases a with ⟨k, r, q⟩
  rcases b with ⟨k', r', q'⟩
  have ha' : (k, r, q) ∈ rawCofactorTriples N := ha
  have hb' : (k', r', q') ∈ rawCofactorTriples N := hb
  have hsep := rawCofactorTriples_separated hN ha'
  have hsep' := rawCofactorTriples_separated hN hb'
  rw [mem_rawCofactorTriples_iff] at ha' hb'
  have hr : r.Prime := (mem_middlePrimes_iff.mp ha'.2.1).2.2
  have hr' : r'.Prime := (mem_middlePrimes_iff.mp hb'.2.1).2.2
  have hq : q.Prime := (mem_largePrimes_iff.mp ha'.2.2).2.2
  have hq' : q'.Prime := (mem_largePrimes_iff.mp hb'.2.2).2.2
  change k * r * q = k' * r' * q' at hab
  have houter := eq_of_mul_eq_mul_of_large_primes hq hq'
    (Nat.mul_pos hsep.1 hr.pos) (Nat.mul_pos hsep'.1 hr'.pos)
    hsep.2.2 hsep'.2.2 hab
  rcases houter with ⟨hkr, hqq⟩
  have hinner := eq_of_mul_eq_mul_of_large_primes hr hr'
    hsep.1 hsep'.1 hsep.2.1 hsep'.2.1 hkr
  rcases hinner with ⟨hkk, hrr⟩
  subst k'
  subst r'
  subst q'
  rfl

/-- Therefore the raw cofactor finset has exactly as many elements as the
cartesian product of the three layers. -/
theorem rawCofactors_card_eq_product {N : ℕ} (hN : 2 ≤ N) :
    (rawCofactors N).card =
      (smallFactors N).card * (middlePrimes N).card * (largePrimes N).card := by
  rw [rawCofactors, Finset.card_image_of_injOn
    (cofactorProduct_injOn_rawCofactorTriples hN)]
  simp [rawCofactorTriples, Nat.mul_assoc]

/-- Every raw cofactor is positive. -/
theorem rawCofactors_pos {N m : ℕ} (hm : m ∈ rawCofactors N) : 0 < m := by
  rw [rawCofactors] at hm
  simp only [Finset.mem_image] at hm
  obtain ⟨⟨k, r, q⟩, ht, rfl⟩ := hm
  rw [mem_rawCofactorTriples_iff] at ht
  have hk : 0 < k := by
    have := (mem_smallFactors_iff.mp ht.1).1
    omega
  have hr : 0 < r := (mem_middlePrimes_iff.mp ht.2.1).2.2.pos
  have hq : 0 < q := (mem_largePrimes_iff.mp ht.2.2).2.2.pos
  exact Nat.mul_pos (Nat.mul_pos hk hr) hq

/-- At scale `N^60`, every raw cofactor is at most `N^28`, the integral
form of the paper's `x^(7/15)` bound. -/
theorem rawCofactors_le_pow_twenty_eight {N m : ℕ}
    (hm : m ∈ rawCofactors N) : m ≤ N ^ 28 := by
  rw [rawCofactors] at hm
  simp only [Finset.mem_image] at hm
  obtain ⟨⟨k, r, q⟩, ht, rfl⟩ := hm
  rw [mem_rawCofactorTriples_iff] at ht
  have hk := (mem_smallFactors_iff.mp ht.1).2
  have hr := (mem_middlePrimes_iff.mp ht.2.1).2.1
  have hq := (mem_largePrimes_iff.mp ht.2.2).2.1
  calc
    k * r * q ≤ N * (N ^ 5) * (N ^ 22) :=
      Nat.mul_le_mul (Nat.mul_le_mul hk hr) hq
    _ = N ^ 28 := by ring

/-- For sufficiently large integral scale, every outer prime attached to a
raw cofactor is larger than that cofactor. -/
theorem outerPrime_large_of_mem_rawCofactors {N m p : ℕ} (hN : 2 ≤ N)
    (hm : m ∈ rawCofactors N) (hp : p ∈ outerPrimes (N ^ 60) m) :
    m < p := by
  have hmpos := rawCofactors_pos hm
  have hmle := rawCofactors_le_pow_twenty_eight hm
  have hpow4 : 2 ≤ N ^ 4 :=
    (by norm_num : 2 ≤ 2 ^ 4).trans (Nat.pow_le_pow_left hN 4)
  have hpow : 2 * N ^ 56 ≤ N ^ 60 := by
    calc
      2 * N ^ 56 ≤ N ^ 4 * N ^ 56 := Nat.mul_le_mul_right _ hpow4
      _ = N ^ 60 := by ring
  have hmm : m * m ≤ N ^ 56 := by
    calc
      m * m ≤ N ^ 28 * N ^ 28 := Nat.mul_le_mul hmle hmle
      _ = N ^ 56 := by ring
  have htwomm : 2 * m * m ≤ N ^ 60 := by
    calc
      2 * m * m ≤ 2 * N ^ 56 := by
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hmm
      _ ≤ N ^ 60 := hpow
  have hdenom : 0 < 2 * m := by positivity
  have hmdiv : m ≤ N ^ 60 / (2 * m) :=
    (Nat.le_div_iff_mul_le hdenom).2 (by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using htwomm)
  exact hmdiv.trans_lt (mem_outerPrimes_iff.mp hp).1

/-- Hence the raw outer layer has the expected sum-of-prime-intervals
cardinality. -/
theorem rawOuterInputs_card_eq_sum (N : ℕ) (hN : 2 ≤ N) :
    (outerInputs (fun _ => rawCofactors N) (N ^ 60)).card =
      ∑ m ∈ rawCofactors N, (outerPrimes (N ^ 60) m).card := by
  have hpos : ∀ m ∈ rawCofactors N, 0 < m := by
    intro m hm
    exact rawCofactors_pos hm
  have hlarge : ∀ m ∈ rawCofactors N,
      ∀ p ∈ outerPrimes (N ^ 60) m, m < p := by
    intro m hm p hp
    exact outerPrime_large_of_mem_rawCofactors hN hm hp
  exact outerInputs_card_eq_sum_outerPrimes_card (fun _ => rawCofactors N) (N ^ 60)
    hpos hlarge

/-- Uniform PNT lower bound for the outer prime interval attached to every
raw cofactor.  The constant absorbs the floor in `N^60 / m` and the bound
`log (N^60/m) ≤ 60 log N`. -/
theorem eventually_outerPrimes_card_lower_raw :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ m ∈ rawCofactors N,
      ((N ^ 60 : ℕ) : ℝ) / (1200 * (m : ℝ) * Real.log N) ≤
        ((outerPrimes (N ^ 60) m).card : ℝ) := by
  obtain ⟨T, hT⟩ := exists_card_filter_Ioc_prime_half_interval_lower_threshold
  filter_upwards [Filter.eventually_ge_atTop (max 2 T)] with N hNmax
  intro m hm
  have hN : 2 ≤ N := le_trans (le_max_left 2 T) hNmax
  have hTN : T ≤ N := le_trans (le_max_right 2 T) hNmax
  have hmpos : 0 < m := rawCofactors_pos hm
  have hmle : m ≤ N ^ 28 := rawCofactors_le_pow_twenty_eight hm
  have hNleN32 : N ≤ N ^ 32 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ N) (by omega : 1 ≤ 32)
  have hmul : N ^ 32 * m ≤ N ^ 60 := by
    calc
      N ^ 32 * m ≤ N ^ 32 * N ^ 28 := Nat.mul_le_mul_left _ hmle
      _ = N ^ 60 := by ring
  have hquotlower : N ^ 32 ≤ N ^ 60 / m :=
    (Nat.le_div_iff_mul_le hmpos).2 hmul
  have hTquot : T ≤ N ^ 60 / m :=
    hTN.trans (hNleN32.trans hquotlower)
  have hprime := hT (N ^ 60 / m) hTquot
  have hquotone : 1 ≤ N ^ 60 / m := by
    have : 1 ≤ N ^ 32 := (by omega : 1 ≤ N).trans hNleN32
    exact this.trans hquotlower
  have hquotpos : 0 < N ^ 60 / m := by omega
  have hN60pos : 0 < N ^ 60 := Nat.pow_pos (by omega)
  have hdecomp := Nat.div_add_mod (N ^ 60) m
  have hxlt : N ^ 60 < m * (N ^ 60 / m + 1) := by
    calc
      N ^ 60 = m * (N ^ 60 / m) + N ^ 60 % m := hdecomp.symm
      _ < m * (N ^ 60 / m) + m :=
        Nat.add_lt_add_left (Nat.mod_lt _ hmpos) _
      _ = m * (N ^ 60 / m + 1) := by ring
  have hmleprod : m ≤ m * (N ^ 60 / m) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left m hquotone
  have hxfloorNat : N ^ 60 ≤ 2 * m * (N ^ 60 / m) := by
    have hmiddle : m * (N ^ 60 / m + 1) ≤ 2 * m * (N ^ 60 / m) := by
      nlinarith
    exact hxlt.le.trans hmiddle
  have hxfloor : ((N ^ 60 : ℕ) : ℝ) / (2 * (m : ℝ)) ≤
      (N ^ 60 / m : ℕ) := by
    apply (div_le_iff₀ (by positivity)).2
    exact_mod_cast (by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hxfloorNat)
  have hquotle : N ^ 60 / m ≤ N ^ 60 := Nat.div_le_self _ _
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogquotpos : 0 < Real.log ((N ^ 60 / m : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N ^ 60 / m))
  have hlogle : Real.log ((N ^ 60 / m : ℕ) : ℝ) ≤
      60 * Real.log (N : ℝ) := by
    calc
      Real.log ((N ^ 60 / m : ℕ) : ℝ) ≤ Real.log ((N ^ 60 : ℕ) : ℝ) := by
        apply Real.strictMonoOn_log.monotoneOn
        · simp only [Set.mem_Ioi]
          exact_mod_cast hquotpos
        · simp only [Set.mem_Ioi]
          exact_mod_cast hN60pos
        · exact_mod_cast hquotle
      _ = 60 * Real.log (N : ℝ) := by
        push_cast
        rw [Real.log_pow]
        norm_num
  have hscaled :
      ((N ^ 60 : ℕ) : ℝ) / (1200 * (m : ℝ) * Real.log N) ≤
        ((N ^ 60 / m : ℕ) : ℝ) /
          (10 * Real.log (N ^ 60 / m : ℕ)) := by
    calc
      ((N ^ 60 : ℕ) : ℝ) / (1200 * (m : ℝ) * Real.log N) =
          (((N ^ 60 : ℕ) : ℝ) / (2 * (m : ℝ))) /
            (10 * (60 * Real.log N)) := by ring
      _ ≤ ((N ^ 60 / m : ℕ) : ℝ) /
            (10 * (60 * Real.log N)) := by
        exact div_le_div_of_nonneg_right hxfloor (by positivity)
      _ ≤ ((N ^ 60 / m : ℕ) : ℝ) /
            (10 * Real.log (N ^ 60 / m : ℕ)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith
  rw [outerPrimes]
  have hlower : N ^ 60 / (2 * m) = (N ^ 60 / m) / 2 := by
    calc
      N ^ 60 / (2 * m) = N ^ 60 / (m * 2) := by rw [Nat.mul_comm 2 m]
      _ = (N ^ 60 / m) / 2 := (Nat.div_div_eq_div_mul _ _ _).symm
  rw [hlower]
  exact hscaled.trans hprime

/-- The middle layer is the standard prime interval from the Mertens helper.
-/
theorem middlePrimes_eq_primesLE_sdiff (N : ℕ) :
    middlePrimes N = Nat.primesLE (N ^ 5) \ Nat.primesLE (N ^ 4 - 1) := by
  ext p
  simp only [middlePrimes, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hp⟩
    exact ⟨⟨hhi, hp⟩, fun hle => by
      have hp2 : 2 ≤ p := hp.two_le
      omega⟩
  · rintro ⟨⟨hhi, hp⟩, hnot⟩
    have hnle : ¬ p ≤ N ^ 4 - 1 := fun hle => hnot ⟨hle, hp⟩
    exact ⟨⟨by
      have hp2 : 2 ≤ p := hp.two_le
      omega, hhi⟩, hp⟩

/-- The large layer is likewise a standard prime interval. -/
theorem largePrimes_eq_primesLE_sdiff (N : ℕ) :
    largePrimes N = Nat.primesLE (N ^ 22) \ Nat.primesLE (N ^ 21 - 1) := by
  ext p
  simp only [largePrimes, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hp⟩
    exact ⟨⟨hhi, hp⟩, fun hle => by
      have hp2 : 2 ≤ p := hp.two_le
      omega⟩
  · rintro ⟨⟨hhi, hp⟩, hnot⟩
    have hnle : ¬ p ≤ N ^ 21 - 1 := fun hle => hnot ⟨hle, hp⟩
    exact ⟨⟨by
      have hp2 : 2 ≤ p := hp.two_le
      omega, hhi⟩, hp⟩

/-- The reciprocal mass of the raw cofactor layer factorizes exactly into
the harmonic `k` mass and the two reciprocal prime masses. -/
theorem reciprocalRawCofactorSum_eq_product {N : ℕ} (hN : 2 ≤ N) :
    reciprocalRawCofactorSum N =
      (∑ k ∈ smallFactors N, (1 : ℝ) / k) *
        reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) *
          reciprocalPrimeIntervalSum (N ^ 21) (N ^ 22) := by
  rw [reciprocalRawCofactorSum, rawCofactors,
    Finset.sum_image (cofactorProduct_injOn_rawCofactorTriples hN)]
  rw [rawCofactorTriples]
  change (∑ x ∈ smallFactors N ×ˢ (middlePrimes N ×ˢ largePrimes N),
      (1 : ℝ) / cofactorProduct x) = _
  rw [Finset.sum_product]
  simp_rw [Finset.sum_product]
  rw [middlePrimes_eq_primesLE_sdiff, largePrimes_eq_primesLE_sdiff]
  unfold reciprocalPrimeIntervalSum cofactorProduct
  simp only [Nat.cast_mul]
  calc
    (∑ x ∈ smallFactors N,
        ∑ y ∈ Nat.primesLE (N ^ 5) \ Nat.primesLE (N ^ 4 - 1),
          ∑ y_1 ∈ Nat.primesLE (N ^ 22) \ Nat.primesLE (N ^ 21 - 1),
            (1 : ℝ) / (x * y * y_1)) =
        ∑ x ∈ smallFactors N,
          ∑ y ∈ Nat.primesLE (N ^ 5) \ Nat.primesLE (N ^ 4 - 1),
            ∑ y_1 ∈ Nat.primesLE (N ^ 22) \ Nat.primesLE (N ^ 21 - 1),
              ((1 : ℝ) / x) * ((1 : ℝ) / y) * ((1 : ℝ) / y_1) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = (∑ k ∈ smallFactors N, (1 : ℝ) / k) *
        (∑ p ∈ Nat.primesLE (N ^ 5) \ Nat.primesLE (N ^ 4 - 1), (1 : ℝ) / p) *
          (∑ p ∈ Nat.primesLE (N ^ 22) \ Nat.primesLE (N ^ 21 - 1), (1 : ℝ) / p) := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

/-- The unrestricted three-layer family has logarithmic reciprocal mass.
This is the exact finite counterpart of the first, pre-exceptional part of
GIL equation (4.1). -/
theorem eventually_log_le_mul_reciprocalRawCofactorSum :
    ∀ᶠ N : ℕ in Filter.atTop,
      (1 / 500 : ℝ) * Real.log N ≤ reciprocalRawCofactorSum N := by
  filter_upwards [eventually_reciprocalPrimeIntervalSum_four_five_lower,
      eventually_reciprocalPrimeIntervalSum_twentyone_twentytwo_lower,
      Filter.eventually_ge_atTop 2] with N hr hq hN
  have hK : Real.log (N : ℝ) ≤
      ∑ k ∈ smallFactors N, (1 : ℝ) / k := by
    have hharm := log_add_one_le_harmonic N
    have hlogmono : Real.log (N : ℝ) ≤ Real.log (N + 1 : ℕ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · simp only [Set.mem_Ioi]
        exact_mod_cast (by omega : 0 < N)
      · simp only [Set.mem_Ioi]
        exact_mod_cast (by omega : 0 < N + 1)
      · exact_mod_cast (by omega : N ≤ N + 1)
    calc
      Real.log (N : ℝ) ≤ Real.log (N + 1 : ℕ) := hlogmono
      _ ≤ (harmonic N : ℝ) := hharm
      _ = ∑ k ∈ smallFactors N, (1 : ℝ) / k := by
        simp [smallFactors, harmonic_eq_sum_Icc, one_div]
  have hlognonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hKnonneg : 0 ≤ ∑ k ∈ smallFactors N, (1 : ℝ) / k := by
    exact Finset.sum_nonneg fun k hk => by positivity
  have hrnonneg : 0 ≤ reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1 / 10) hr
  rw [reciprocalRawCofactorSum_eq_product hN]
  calc
    (1 / 500 : ℝ) * Real.log N =
        Real.log N * (1 / 10 : ℝ) * (1 / 50 : ℝ) := by ring
    _ ≤ (∑ k ∈ smallFactors N, (1 : ℝ) / k) *
        (1 / 10 : ℝ) * (1 / 50 : ℝ) := by
      gcongr
    _ ≤ (∑ k ∈ smallFactors N, (1 : ℝ) / k) *
        reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) * (1 / 50 : ℝ) := by
      gcongr
    _ ≤ (∑ k ∈ smallFactors N, (1 : ℝ) / k) *
        reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) *
          reciprocalPrimeIntervalSum (N ^ 21) (N ^ 22) := by
      gcongr

/-- Summing the uniform outer-prime lower bound against the logarithmic
cofactor mass produces linearly many raw inputs at the perfect-power scale.
-/
theorem eventually_rawOuterInputs_card_linear :
    ∀ᶠ N : ℕ in Filter.atTop,
      (1 / 600000 : ℝ) * ((N ^ 60 : ℕ) : ℝ) ≤
        ((outerInputs (fun _ => rawCofactors N) (N ^ 60)).card : ℝ) := by
  filter_upwards [eventually_outerPrimes_card_lower_raw,
      eventually_log_le_mul_reciprocalRawCofactorSum,
      Filter.eventually_ge_atTop 2] with N houter hmass hN
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hfactor_nonneg :
      0 ≤ ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) := by positivity
  have hmassmul :
      ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          ((1 / 500 : ℝ) * Real.log N) ≤
        ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          reciprocalRawCofactorSum N :=
    mul_le_mul_of_nonneg_left hmass hfactor_nonneg
  have hsum :
      ∑ m ∈ rawCofactors N,
          ((N ^ 60 : ℕ) : ℝ) / (1200 * (m : ℝ) * Real.log N) ≤
        ∑ m ∈ rawCofactors N, ((outerPrimes (N ^ 60) m).card : ℝ) := by
    apply Finset.sum_le_sum
    intro m hm
    exact houter m hm
  have hleft :
      ∑ m ∈ rawCofactors N,
          ((N ^ 60 : ℕ) : ℝ) / (1200 * (m : ℝ) * Real.log N) =
        ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          reciprocalRawCofactorSum N := by
    unfold reciprocalRawCofactorSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  have hcardcast :
      ((outerInputs (fun _ => rawCofactors N) (N ^ 60)).card : ℝ) =
        ∑ m ∈ rawCofactors N, ((outerPrimes (N ^ 60) m).card : ℝ) := by
    rw [rawOuterInputs_card_eq_sum N hN]
    norm_cast
  calc
    (1 / 600000 : ℝ) * ((N ^ 60 : ℕ) : ℝ) =
        ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          ((1 / 500 : ℝ) * Real.log N) := by
      field_simp
      ring
    _ ≤ ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          reciprocalRawCofactorSum N := hmassmul
    _ = ∑ m ∈ rawCofactors N,
          ((N ^ 60 : ℕ) : ℝ) / (1200 * (m : ℝ) * Real.log N) := hleft.symm
    _ ≤ ∑ m ∈ rawCofactors N, ((outerPrimes (N ^ 60) m).card : ℝ) := hsum
    _ = ((outerInputs (fun _ => rawCofactors N) (N ^ 60)).card : ℝ) := hcardcast.symm

end Erdos822
