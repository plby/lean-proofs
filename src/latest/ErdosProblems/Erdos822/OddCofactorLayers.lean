/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.CofactorLayers
import ErdosProblems.Erdos822.OddSmooth
import ErdosProblems.Erdos822.NthRootScale

/-!
# Odd raw cofactor layers

For the fixed cutoff-two smooth class we keep only odd small factors.  They
are represented as 2*j-1 rather than as a filtered interval, so the
reciprocal mass is directly comparable to a harmonic sum.
-/

namespace Erdos822

open scoped BigOperators Finset

/-- Odd positive small factors, parameterized without a parity filter. -/
def oddSmallFactors (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N / 2)).image fun j ↦ 2 * j - 1

/-- Raw odd triples. -/
def oddCofactorTriples (N : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (oddSmallFactors N).product ((middlePrimes N).product (largePrimes N))

/-- Odd raw cofactor layer. -/
def oddRawCofactors (N : ℕ) : Finset ℕ :=
  (oddCofactorTriples N).image cofactorProduct

/-- Reciprocal mass of the odd raw cofactor layer. -/
noncomputable def reciprocalOddRawCofactorSum (N : ℕ) : ℝ :=
  ∑ m ∈ oddRawCofactors N, (1 : ℝ) / m

@[simp]
theorem mem_oddSmallFactors_iff {N k : ℕ} :
    k ∈ oddSmallFactors N ↔
      ∃ j ∈ Finset.Icc 1 (N / 2), k = 2 * j - 1 := by
  simp [oddSmallFactors, eq_comm]

theorem oddSmallFactors_pos {N k : ℕ} (hk : k ∈ oddSmallFactors N) :
    0 < k := by
  rw [mem_oddSmallFactors_iff] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  omega

theorem oddSmallFactors_le {N k : ℕ} (hk : k ∈ oddSmallFactors N) :
    k ≤ N := by
  rw [mem_oddSmallFactors_iff] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hjN : j ≤ N / 2 := (Finset.mem_Icc.mp hj).2
  have htwo : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
  omega

theorem oddSmallFactors_odd {N k : ℕ} (hk : k ∈ oddSmallFactors N) :
    Odd k := by
  rw [mem_oddSmallFactors_iff] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hj1
  refine ⟨u, ?_⟩
  omega

@[simp]
theorem mem_oddCofactorTriples_iff {N k r q : ℕ} :
    (k, r, q) ∈ oddCofactorTriples N ↔
      k ∈ oddSmallFactors N ∧ r ∈ middlePrimes N ∧ q ∈ largePrimes N := by
  simp [oddCofactorTriples, and_assoc]

theorem oddCofactorTriples_subset_raw (N : ℕ) :
    oddCofactorTriples N ⊆ rawCofactorTriples N := by
  rintro ⟨k, r, q⟩ hk
  rw [mem_oddCofactorTriples_iff] at hk
  rw [mem_rawCofactorTriples_iff]
  refine ⟨?_, hk.2.1, hk.2.2⟩
  rw [mem_smallFactors_iff]
  have hkpos := oddSmallFactors_pos hk.1
  exact ⟨by omega, oddSmallFactors_le hk.1⟩

theorem oddCofactorTriples_separated {N k r q : ℕ} (hN : 2 ≤ N)
    (h : (k, r, q) ∈ oddCofactorTriples N) :
    0 < k ∧ k < r ∧ k * r < q :=
  rawCofactorTriples_separated hN
    (oddCofactorTriples_subset_raw N h)

theorem cofactorProduct_injOn_oddCofactorTriples {N : ℕ} (hN : 2 ≤ N) :
    Set.InjOn cofactorProduct (oddCofactorTriples N) := by
  exact (cofactorProduct_injOn_rawCofactorTriples hN).mono
    (oddCofactorTriples_subset_raw N)

theorem oddRawCofactors_card_eq_product {N : ℕ} (hN : 2 ≤ N) :
    (oddRawCofactors N).card =
      (oddSmallFactors N).card * (middlePrimes N).card *
        (largePrimes N).card := by
  rw [oddRawCofactors, Finset.card_image_of_injOn
    (cofactorProduct_injOn_oddCofactorTriples hN)]
  simp [oddCofactorTriples, Nat.mul_assoc]

theorem oddRawCofactors_subset_raw (N : ℕ) :
    oddRawCofactors N ⊆ rawCofactors N := by
  intro m hm
  rw [oddRawCofactors] at hm
  simp only [Finset.mem_image] at hm
  obtain ⟨u, hu, rfl⟩ := hm
  rw [rawCofactors]
  exact Finset.mem_image.mpr
    ⟨u, oddCofactorTriples_subset_raw N hu, rfl⟩

theorem oddRawCofactors_pos {N m : ℕ} (hm : m ∈ oddRawCofactors N) :
    0 < m :=
  rawCofactors_pos (oddRawCofactors_subset_raw N hm)

theorem oddRawCofactors_le_pow_twenty_eight {N m : ℕ}
    (hm : m ∈ oddRawCofactors N) : m ≤ N ^ 28 :=
  rawCofactors_le_pow_twenty_eight (oddRawCofactors_subset_raw N hm)

/-- The two prime layers force every odd raw cofactor to lie well above
the base scale.  This is useful when the later sieve endpoint is chosen as
a natural root of that scale. -/
theorem oddRawCofactors_ge_pow_twenty_five {N m : ℕ} (hN : 2 ≤ N)
    (hm : m ∈ oddRawCofactors N) : N ^ 25 ≤ m := by
  rw [oddRawCofactors] at hm
  simp only [Finset.mem_image] at hm
  obtain ⟨⟨k, r, q⟩, ht, rfl⟩ := hm
  rw [mem_oddCofactorTriples_iff] at ht
  have hk : 1 ≤ k := by
    rw [mem_oddSmallFactors_iff] at ht
    obtain ⟨j, hj, hkj⟩ := ht.1
    have hj1 := (Finset.mem_Icc.mp hj).1
    omega
  have hr : N ^ 4 ≤ r := (mem_middlePrimes_iff.mp ht.2.1).1
  have hq : N ^ 21 ≤ q := (mem_largePrimes_iff.mp ht.2.2).1
  calc
    N ^ 25 = 1 * (N ^ 4) * (N ^ 21) := by ring
    _ ≤ k * r * q := Nat.mul_le_mul (Nat.mul_le_mul hk hr) hq

theorem oddRawCofactors_odd {N m : ℕ}
    (hm : m ∈ oddRawCofactors N) : Odd m := by
  rw [oddRawCofactors] at hm
  simp only [Finset.mem_image] at hm
  obtain ⟨⟨k, r, q⟩, ht, rfl⟩ := hm
  rw [mem_oddCofactorTriples_iff] at ht
  have hkOdd := oddSmallFactors_odd ht.1
  have hrPrime := (mem_middlePrimes_iff.mp ht.2.1).2.2
  have hqPrime := (mem_largePrimes_iff.mp ht.2.2).2.2
  have hN : 2 ≤ N := by
    by_contra hN
    have hNle : N ≤ 1 := by omega
    interval_cases N <;> simp [middlePrimes] at ht
  have hrOdd : Odd r := hrPrime.odd_of_ne_two (by
    have hrge := (mem_middlePrimes_iff.mp ht.2.1).1
    have hpow : 2 ^ 4 ≤ N ^ 4 := Nat.pow_le_pow_left hN 4
    norm_num at hpow
    omega)
  have hqOdd : Odd q := hqPrime.odd_of_ne_two (by
    have hqge := (mem_largePrimes_iff.mp ht.2.2).1
    have hpow : 2 ^ 21 ≤ N ^ 21 := Nat.pow_le_pow_left hN 21
    norm_num at hpow
    omega)
  exact (hkOdd.mul hrOdd).mul hqOdd

theorem oddOuterPrime_large_of_mem {N m p : ℕ} (hN : 2 ≤ N)
    (hm : m ∈ oddRawCofactors N) (hp : p ∈ outerPrimes (N ^ 60) m) :
    m < p :=
  outerPrime_large_of_mem_rawCofactors hN
    (oddRawCofactors_subset_raw N hm) hp

theorem oddRawOuterInputs_card_eq_sum (N : ℕ) (hN : 2 ≤ N) :
    (outerInputs (fun _ => oddRawCofactors N) (N ^ 60)).card =
      ∑ m ∈ oddRawCofactors N, (outerPrimes (N ^ 60) m).card := by
  have hpos : ∀ m ∈ oddRawCofactors N, 0 < m := by
    intro m hm
    exact oddRawCofactors_pos hm
  have hlarge : ∀ m ∈ oddRawCofactors N,
      ∀ p ∈ outerPrimes (N ^ 60) m, m < p := by
    intro m hm p hp
    exact oddOuterPrime_large_of_mem hN hm hp
  exact outerInputs_card_eq_sum_outerPrimes_card
    (fun _ => oddRawCofactors N) (N ^ 60) hpos hlarge

/-- The odd small-factor reciprocal sum retains a fixed fraction of the
ordinary harmonic sum. -/
theorem half_harmonic_le_sum_inv_oddSmallFactors (N : ℕ) :
    ((harmonic (N / 2) : ℚ) : ℝ) / 2 ≤
      ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k := by
  have hinj : Set.InjOn (fun j : ℕ ↦ 2 * j - 1)
      (Finset.Icc 1 (N / 2)) := by
    intro i hi j hj hij
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hj1 := (Finset.mem_Icc.mp hj).1
    change 2 * i - 1 = 2 * j - 1 at hij
    omega
  rw [oddSmallFactors, Finset.sum_image hinj]
  rw [harmonic_eq_sum_Icc, Rat.cast_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hpos : (0 : ℝ) < (2 * j - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < 2 * j - 1)
  have hle : ((2 * j - 1 : ℕ) : ℝ) ≤ (2 * j : ℕ) := by
    exact_mod_cast (by omega : 2 * j - 1 ≤ 2 * j)
  simp only [Rat.cast_inv, Rat.cast_natCast]
  have hleft : ((j : ℝ)⁻¹) / 2 = (1 : ℝ) / ((2 * j : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hleft]
  exact one_div_le_one_div_of_le hpos hle

/-- For large N, odd small factors still supply logarithmic reciprocal
mass. -/
theorem eventually_log_quarter_le_sum_inv_oddSmallFactors :
    ∀ᶠ N : ℕ in Filter.atTop,
      (1 / 4 : ℝ) * Real.log N ≤
        ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k := by
  filter_upwards [Filter.eventually_ge_atTop 4] with N hN
  have hhalf : ((harmonic (N / 2) : ℚ) : ℝ) / 2 ≤
      ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k :=
    half_harmonic_le_sum_inv_oddSmallFactors N
  have hbaseNat : N ≤ (N / 2 + 1) ^ 2 := by
    have hlin : N ≤ 2 * (N / 2 + 1) := by omega
    have htwo : 2 ≤ N / 2 + 1 := by omega
    nlinarith
  have hlogmono :
      Real.log (N : ℝ) ≤ Real.log (((N / 2 + 1) ^ 2 : ℕ) : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · simp only [Set.mem_Ioi]
      exact_mod_cast (by omega : 0 < N)
    · simp only [Set.mem_Ioi]
      exact_mod_cast (by positivity : 0 < (N / 2 + 1) ^ 2)
    · exact_mod_cast hbaseNat
  have hlog :
      Real.log (N : ℝ) ≤ 2 * Real.log ((N / 2 + 1 : ℕ) : ℝ) := by
    calc
      Real.log (N : ℝ) ≤ Real.log (((N / 2 + 1) ^ 2 : ℕ) : ℝ) :=
        hlogmono
      _ = 2 * Real.log ((N / 2 + 1 : ℕ) : ℝ) := by
        push_cast
        rw [Real.log_pow]
        norm_num
  have hharm : Real.log ((N / 2 + 1 : ℕ) : ℝ) ≤
      (harmonic (N / 2) : ℝ) :=
    log_add_one_le_harmonic (N / 2)
  calc
    (1 / 4 : ℝ) * Real.log N ≤
        ((harmonic (N / 2) : ℚ) : ℝ) / 2 := by
      have : Real.log (N : ℝ) ≤ 2 * (harmonic (N / 2) : ℝ) :=
        hlog.trans (mul_le_mul_of_nonneg_left hharm (by norm_num))
      norm_num at this ⊢
      linarith
    _ ≤ ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k := hhalf

/-- The reciprocal mass of the odd layer factorizes into its odd harmonic
factor and the same two prime factors as the raw layer. -/
theorem reciprocalOddRawCofactorSum_eq_product {N : ℕ} (hN : 2 ≤ N) :
    reciprocalOddRawCofactorSum N =
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) *
          reciprocalPrimeIntervalSum (N ^ 21) (N ^ 22) := by
  rw [reciprocalOddRawCofactorSum, oddRawCofactors,
    Finset.sum_image (cofactorProduct_injOn_oddCofactorTriples hN)]
  rw [oddCofactorTriples]
  change (∑ x ∈ oddSmallFactors N ×ˢ (middlePrimes N ×ˢ largePrimes N),
      (1 : ℝ) / cofactorProduct x) = _
  rw [Finset.sum_product]
  simp_rw [Finset.sum_product]
  rw [middlePrimes_eq_primesLE_sdiff, largePrimes_eq_primesLE_sdiff]
  unfold reciprocalPrimeIntervalSum cofactorProduct
  simp only [Nat.cast_mul]
  calc
    (∑ x ∈ oddSmallFactors N,
        ∑ y ∈ Nat.primesLE (N ^ 5) \
            Nat.primesLE (N ^ 4 - 1),
          ∑ y_1 ∈ Nat.primesLE (N ^ 22) \
              Nat.primesLE (N ^ 21 - 1),
            (1 : ℝ) / (x * y * y_1)) =
        ∑ x ∈ oddSmallFactors N,
          ∑ y ∈ Nat.primesLE (N ^ 5) \
              Nat.primesLE (N ^ 4 - 1),
            ∑ y_1 ∈ Nat.primesLE (N ^ 22) \
                Nat.primesLE (N ^ 21 - 1),
              ((1 : ℝ) / x) * ((1 : ℝ) / y) * ((1 : ℝ) / y_1) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ p ∈ Nat.primesLE (N ^ 5) \
            Nat.primesLE (N ^ 4 - 1), (1 : ℝ) / p) *
          (∑ p ∈ Nat.primesLE (N ^ 22) \
              Nat.primesLE (N ^ 21 - 1), (1 : ℝ) / p) := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

theorem eventually_log_le_mul_reciprocalOddRawCofactorSum :
    ∀ᶠ N : ℕ in Filter.atTop,
      (1 / 2000 : ℝ) * Real.log N ≤ reciprocalOddRawCofactorSum N := by
  filter_upwards [eventually_reciprocalPrimeIntervalSum_four_five_lower,
      eventually_reciprocalPrimeIntervalSum_twentyone_twentytwo_lower,
      eventually_log_quarter_le_sum_inv_oddSmallFactors,
      Filter.eventually_ge_atTop 2] with N hr hq hK hN
  have hlognonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hKnonneg : 0 ≤ ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k := by
    exact Finset.sum_nonneg fun k hk => by positivity
  have hrnonneg : 0 ≤ reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1 / 10) hr
  rw [reciprocalOddRawCofactorSum_eq_product hN]
  calc
    (1 / 2000 : ℝ) * Real.log N =
        ((1 / 4 : ℝ) * Real.log N) * (1 / 10 : ℝ) * (1 / 50 : ℝ) := by ring
    _ ≤ (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (1 / 10 : ℝ) * (1 / 50 : ℝ) := by gcongr
    _ ≤ (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) * (1 / 50 : ℝ) := by
      gcongr
    _ ≤ (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) *
          reciprocalPrimeIntervalSum (N ^ 21) (N ^ 22) := by
      gcongr

theorem eventually_oddRawOuterInputs_card_linear :
    ∀ᶠ N : ℕ in Filter.atTop,
      (1 / 2400000 : ℝ) * ((N ^ 60 : ℕ) : ℝ) ≤
        ((outerInputs (fun _ => oddRawCofactors N) (N ^ 60)).card : ℝ) := by
  filter_upwards [eventually_outerPrimes_card_lower_raw,
      eventually_log_le_mul_reciprocalOddRawCofactorSum,
      Filter.eventually_ge_atTop 2] with N houter hmass hN
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hfactor_nonneg :
      0 ≤ ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) := by positivity
  have hmassmul :
      ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          ((1 / 2000 : ℝ) * Real.log N) ≤
        ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          reciprocalOddRawCofactorSum N :=
    mul_le_mul_of_nonneg_left hmass hfactor_nonneg
  have hsum :
      ∑ m ∈ oddRawCofactors N,
          ((N ^ 60 : ℕ) : ℝ) / (1200 * (m : ℝ) * Real.log N) ≤
        ∑ m ∈ oddRawCofactors N, ((outerPrimes (N ^ 60) m).card : ℝ) := by
    apply Finset.sum_le_sum
    intro m hm
    exact houter m (oddRawCofactors_subset_raw N hm)
  have hleft :
      ∑ m ∈ oddRawCofactors N,
          ((N ^ 60 : ℕ) : ℝ) / (1200 * (m : ℝ) * Real.log N) =
        ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          reciprocalOddRawCofactorSum N := by
    unfold reciprocalOddRawCofactorSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  have hcardcast :
      ((outerInputs (fun _ => oddRawCofactors N) (N ^ 60)).card : ℝ) =
        ∑ m ∈ oddRawCofactors N, ((outerPrimes (N ^ 60) m).card : ℝ) := by
    rw [oddRawOuterInputs_card_eq_sum N hN]
    norm_cast
  calc
    (1 / 2400000 : ℝ) * ((N ^ 60 : ℕ) : ℝ) =
        ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          ((1 / 2000 : ℝ) * Real.log N) := by
      field_simp
      ring
    _ ≤ ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          reciprocalOddRawCofactorSum N := hmassmul
    _ = ∑ m ∈ oddRawCofactors N,
          ((N ^ 60 : ℕ) : ℝ) / (1200 * (m : ℝ) * Real.log N) := hleft.symm
    _ ≤ ∑ m ∈ oddRawCofactors N, ((outerPrimes (N ^ 60) m).card : ℝ) := hsum
    _ = ((outerInputs (fun _ => oddRawCofactors N) (N ^ 60)).card : ℝ) := hcardcast.symm

end Erdos822
