import ErdosProblems.Erdos538.Truncation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

open scoped Nat.Prime
open Chebyshev

/-- The prime set used in the finite arithmetic development is Mathlib's
standard set of primes at most `N`. -/
theorem primeIntegers_eq_primesLE (N : ℕ) :
    primeIntegers N = Nat.primesLE N := by
  simpa [primeIntegers, positiveIntegers] using
    (Nat.primesLE_eq_filter_Icc_one N).symm

/-- Primes at most `N` whose binary logarithm is exactly `j`. -/
def dyadicPrimeBlock (N j : ℕ) : Finset ℕ :=
  (primeIntegers N).filter fun p => Nat.log 2 p = j

/-- Every prime at most `N` lies in the dyadic block indexed by its binary
logarithm, and that index is between one and `log₂ N`. -/
theorem prime_mem_dyadicPrimeBlock {N p : ℕ} (hp : p ∈ primeIntegers N) :
    p ∈ dyadicPrimeBlock N (Nat.log 2 p) ∧
      1 ≤ Nat.log 2 p ∧ Nat.log 2 p ≤ Nat.log 2 N := by
  have hpPrime : p.Prime := by
    simpa [primeIntegers, positiveIntegers] using (Finset.mem_filter.mp hp).2
  have hpN : p ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
  refine ⟨Finset.mem_filter.mpr ⟨hp, rfl⟩, ?_, Nat.log_mono_right hpN⟩
  rw [Nat.le_log_iff_pow_le Nat.one_lt_two hpPrime.ne_zero]
  simpa using hpPrime.two_le

/-- A binary-logarithmic prime block is contained in all primes below the next
power of two. -/
theorem dyadicPrimeBlock_subset_primesLE_pow (N j : ℕ) :
    dyadicPrimeBlock N j ⊆ Nat.primesLE (2 ^ (j + 1)) := by
  intro p hp
  have hlog : Nat.log 2 p = j := (Finset.mem_filter.mp hp).2
  apply Nat.mem_primesLE.mpr
  refine ⟨?_, ?_⟩
  · have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two p
    rw [hlog] at hlt
    exact hlt.le
  · have hpN := (Finset.mem_filter.mp hp).1
    exact (Finset.mem_filter.mp hpN).2

/-- Chebyshev's theta bound controls the cardinality of each binary-logarithmic
prime block. -/
theorem dyadicPrimeBlock_card_bound (N j : ℕ) (hj : 0 < j) :
    ((dyadicPrimeBlock N j).card : ℝ) * j ≤ 4 * (2 : ℝ) ^ j := by
  let B := dyadicPrimeBlock N j
  have hlogLower : ∀ p ∈ B, (j : ℝ) * Real.log 2 ≤ Real.log p := by
    intro p hp
    have hpPrime : p.Prime := by
      have hpN := (Finset.mem_filter.mp hp).1
      exact (Finset.mem_filter.mp hpN).2
    have hlog : Nat.log 2 p = j := (Finset.mem_filter.mp hp).2
    have hpowNat : 2 ^ j ≤ p := by
      rw [← hlog]
      exact Nat.pow_log_le_self 2 hpPrime.ne_zero
    calc
      (j : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ j) := by
        rw [Real.log_pow]
      _ ≤ Real.log p := by
        exact Real.log_le_log (by positivity) (by exact_mod_cast hpowNat)
  have hsumLower : (B.card : ℝ) * ((j : ℝ) * Real.log 2) ≤
      ∑ p ∈ B, Real.log p := by
    calc
      (B.card : ℝ) * ((j : ℝ) * Real.log 2) =
          ∑ p ∈ B, ((j : ℝ) * Real.log 2) := by simp
      _ ≤ ∑ p ∈ B, Real.log p := by
        exact Finset.sum_le_sum fun p hp => hlogLower p hp
  have hsubset : B ⊆ Nat.primesLE (2 ^ (j + 1)) := by
    simpa [B] using dyadicPrimeBlock_subset_primesLE_pow N j
  have hsumTheta : (∑ p ∈ B, Real.log p) ≤
      Chebyshev.theta (2 ^ (j + 1) : ℕ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun p hp hnot => Real.log_natCast_nonneg p)
  have htheta : Chebyshev.theta (2 ^ (j + 1) : ℕ) ≤
      Real.log 4 * (2 ^ (j + 1) : ℕ) :=
    Chebyshev.theta_le_log4_mul_x (by positivity)
  have hbound : (B.card : ℝ) * ((j : ℝ) * Real.log 2) ≤
      Real.log 4 * (2 ^ (j + 1) : ℕ) :=
    hsumLower.trans (hsumTheta.trans htheta)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    convert Real.log_pow (x := (2 : ℝ)) 2 using 1 <;> norm_num
  rw [hlog4] at hbound
  push_cast at hbound ⊢
  rw [pow_succ] at hbound
  nlinarith

/-- The reciprocal mass of one positive binary-logarithmic prime block is at
most `4/j`. -/
theorem dyadicPrimeBlock_reciprocal_bound (N j : ℕ) (hj : 0 < j) :
    (∑ p ∈ dyadicPrimeBlock N j, (p : ℝ)⁻¹) ≤ 4 / j := by
  let B := dyadicPrimeBlock N j
  have hterm : ∀ p ∈ B, (p : ℝ)⁻¹ ≤ ((2 : ℝ) ^ j)⁻¹ := by
    intro p hp
    have hpPrime : p.Prime := by
      have hpN := (Finset.mem_filter.mp hp).1
      exact (Finset.mem_filter.mp hpN).2
    have hlog : Nat.log 2 p = j := (Finset.mem_filter.mp hp).2
    have hpowNat : 2 ^ j ≤ p := by
      rw [← hlog]
      exact Nat.pow_log_le_self 2 hpPrime.ne_zero
    exact inv_anti₀ (by positivity) (by exact_mod_cast hpowNat)
  have hsum : (∑ p ∈ B, (p : ℝ)⁻¹) ≤
      (B.card : ℝ) * ((2 : ℝ) ^ j)⁻¹ := by
    calc
      (∑ p ∈ B, (p : ℝ)⁻¹) ≤ ∑ p ∈ B, ((2 : ℝ) ^ j)⁻¹ := by
        exact Finset.sum_le_sum fun p hp => hterm p hp
      _ = (B.card : ℝ) * ((2 : ℝ) ^ j)⁻¹ := by simp
  have hcard := dyadicPrimeBlock_card_bound N j hj
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hpow : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  rw [inv_eq_one_div] at hsum
  calc
    (∑ p ∈ dyadicPrimeBlock N j, (p : ℝ)⁻¹) =
        ∑ p ∈ B, (p : ℝ)⁻¹ := by rfl
    _ ≤ (B.card : ℝ) * (1 / (2 : ℝ) ^ j) := hsum
    _ ≤ 4 / j := by
      apply (le_div_iff₀ hjR).2
      have hcard' : (B.card : ℝ) * j ≤ 4 * (2 : ℝ) ^ j := by
        simpa [B] using hcard
      calc
        (B.card : ℝ) * (1 / (2 : ℝ) ^ j) * j =
            ((B.card : ℝ) * j) * ((2 : ℝ) ^ j)⁻¹ := by
              field_simp
              <;> ring
        _ ≤ (4 * (2 : ℝ) ^ j) * ((2 : ℝ) ^ j)⁻¹ :=
          mul_le_mul_of_nonneg_right hcard' (inv_nonneg.mpr hpow.le)
        _ = 4 := by field_simp

/-- The dyadic prime blocks with positive indices through `log₂ N` partition
all primes at most `N`. -/
theorem biUnion_dyadicPrimeBlock (N : ℕ) :
    (Finset.Icc 1 (Nat.log 2 N)).biUnion (dyadicPrimeBlock N) =
      primeIntegers N := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hpj).1
  · intro hp
    obtain ⟨hpBlock, hj1, hjN⟩ := prime_mem_dyadicPrimeBlock hp
    exact Finset.mem_biUnion.mpr
      ⟨Nat.log 2 p, Finset.mem_Icc.mpr ⟨hj1, hjN⟩, hpBlock⟩

/-- Distinct binary-logarithmic prime blocks are disjoint. -/
theorem pairwiseDisjoint_dyadicPrimeBlock (N : ℕ) :
    ((Finset.Icc 1 (Nat.log 2 N) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (dyadicPrimeBlock N) := by
  intro i hi j hj hij
  change Disjoint (dyadicPrimeBlock N i) (dyadicPrimeBlock N j)
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hli : Nat.log 2 p = i := (Finset.mem_filter.mp hpi).2
  have hlj : Nat.log 2 p = j := (Finset.mem_filter.mp hpj).2
  exact hij (hli.symm.trans hlj)

/-- The real-valued reciprocal prime sum has the elementary dyadic bound
`4 H_{⌊log₂ N⌋}`. -/
theorem prime_reciprocal_sum_le_four_harmonic_log (N : ℕ) :
    (∑ p ∈ primeIntegers N, (p : ℝ)⁻¹) ≤
      4 * (harmonic (Nat.log 2 N) : ℝ) := by
  classical
  let L := Nat.log 2 N
  let ks := Finset.Icc 1 L
  have hdisj : (ks : Set ℕ).PairwiseDisjoint (dyadicPrimeBlock N) := by
    simpa [ks, L] using pairwiseDisjoint_dyadicPrimeBlock N
  have hunion : ks.biUnion (dyadicPrimeBlock N) = primeIntegers N := by
    simpa [ks, L] using biUnion_dyadicPrimeBlock N
  have hharm : (harmonic L : ℝ) =
      ∑ j ∈ ks, (j : ℝ)⁻¹ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, ks]
  calc
    (∑ p ∈ primeIntegers N, (p : ℝ)⁻¹) =
        ∑ j ∈ ks, ∑ p ∈ dyadicPrimeBlock N j, (p : ℝ)⁻¹ := by
          rw [← hunion, Finset.sum_biUnion hdisj]
    _ ≤ ∑ j ∈ ks, 4 / (j : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact dyadicPrimeBlock_reciprocal_bound N j
        (Finset.mem_Icc.mp hj).1
    _ = 4 * (harmonic L : ℝ) := by
      rw [hharm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_eq_mul_inv]
    _ = 4 * (harmonic (Nat.log 2 N) : ℝ) := by rfl

/-- Exact nonnegative-rational form of the elementary Mertens upper bound used
by the baseline construction. -/
theorem primeHarmonicNN_le_four_harmonic_log (N : ℕ) :
    primeHarmonicNN N ≤ 4 * harmonicMassNN (Nat.log 2 N) := by
  apply (NNRat.cast_le (K := ℝ)).mp
  change (primeHarmonicNN N : ℝ) ≤
    ((4 * harmonicMassNN (Nat.log 2 N) : ℚ≥0) : ℝ)
  have h := prime_reciprocal_sum_le_four_harmonic_log N
  simp only [primeHarmonicNN, harmonicMassNN, reciprocalMassNN]
  push_cast
  simpa [positiveIntegers, harmonic_eq_sum_Icc] using h

end Erdos538
