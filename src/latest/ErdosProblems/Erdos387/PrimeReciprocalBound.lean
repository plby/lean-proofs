/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.ParameterScale
import ErdosProblems.Erdos387.QualitativeSieve
import ErdosProblems.Erdos387.RoughIntervalEstimate

/-!
# A uniform Chebyshev bound and prime reciprocal shells

This module develops the sharper logarithmic-depth Brun truncation needed
when the roughness threshold grows.  The first step upgrades the eventual
Chebyshev estimate to every natural endpoint at least two.
-/

namespace Erdos387

open scoped BigOperators
open Finset Nat Real

namespace PrimeReciprocal

/-- The number of primes at most `t` never exceeds `t`. -/
theorem primeCounting_le_self (t : ℕ) : Nat.primeCounting t ≤ t := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  calc
    (Nat.primesLE t).card ≤ (Finset.Icc 1 t).card := by
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_Icc.mpr
        ⟨(Nat.prime_of_mem_primesLE hp).one_lt.le,
          (Nat.mem_primesLE.mp hp).1⟩
    _ ≤ t := by simp

/-- Uniform `π(t) ≪ t / log t` for every natural `t ≥ 2`, including the
finite initial segment omitted by the asymptotic Chebyshev theorem. -/
theorem exists_uniform_primeCounting_le_div_log_all :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t := by
  obtain ⟨C, hC, N, hcheb⟩ :=
    RoughHarmonic.exists_uniform_primeCounting_le_div_log
  let C' := C + Real.log (N + 1 : ℕ) + 1
  have hC' : 0 < C' := by
    dsimp [C']
    have hlog : 0 ≤ Real.log (N + 1 : ℕ) :=
      Real.log_natCast_nonneg (N + 1)
    linarith
  refine ⟨C', hC', ?_⟩
  intro t ht
  have hlogt : 0 < Real.log (t : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  by_cases hNt : N ≤ t
  · have hbase := hcheb t hNt
    have hCC' : C ≤ C' := by
      dsimp [C']
      have hlog : 0 ≤ Real.log (N + 1 : ℕ) :=
        Real.log_natCast_nonneg (N + 1)
      linarith
    exact hbase.trans (by
      apply (div_le_div_iff_of_pos_right hlogt).2
      exact mul_le_mul_of_nonneg_right hCC' (by positivity))
  · have htN : t ≤ N := by omega
    have hlogLe : Real.log (t : ℝ) ≤ Real.log (N + 1 : ℕ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact_mod_cast (show t ≤ N + 1 by omega)
    have hlogC : Real.log (t : ℝ) ≤ C' := by
      dsimp [C']
      linarith
    have hcount : (Nat.primeCounting t : ℝ) ≤ t := by
      exact_mod_cast primeCounting_le_self t
    refine hcount.trans ?_
    apply (le_div_iff₀ hlogt).2
    nlinarith

/-- Reciprocal mass of the primes at most `z`. -/
noncomputable def primeReciprocalSum (z : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE z, (1 : ℝ) / p

/-- The primes at most `z` whose dyadic logarithm is exactly `j`. -/
noncomputable def primeLogShell (z j : ℕ) : Finset ℕ := by
  classical
  exact (Nat.primesLE z).filter fun p => Nat.log 2 p = j

theorem pairwiseDisjoint_primeLogShell (z J : ℕ) :
    ((Finset.Icc 1 J : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (primeLogShell z) := by
  classical
  intro i hi j hj hij
  change Disjoint (primeLogShell z i) (primeLogShell z j)
  rw [Finset.disjoint_left]
  intro p hpi hpj
  rw [primeLogShell, Finset.mem_filter] at hpi hpj
  exact hij (hpi.2.symm.trans hpj.2)

/-- Dyadic logarithm partitions all primes at most `z`.  The lower shell
index is one because every prime is at least two. -/
theorem biUnion_primeLogShell (z : ℕ) :
    (Finset.Icc 1 (Nat.log 2 z)).biUnion (primeLogShell z) =
      Nat.primesLE z := by
  classical
  ext p
  constructor
  · intro hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨j, hj, hpj⟩ := hp
    exact (Finset.mem_filter.mp hpj).1
  · intro hp
    have hpPrime := Nat.prime_of_mem_primesLE hp
    have hpTwo : 2 ≤ p := hpPrime.two_le
    have hpz : p ≤ z := (Nat.mem_primesLE.mp hp).1
    have hlogPos : 1 ≤ Nat.log 2 p := Nat.log_pos (by omega) hpTwo
    have hlogLe : Nat.log 2 p ≤ Nat.log 2 z := Nat.log_mono_right hpz
    rw [Finset.mem_biUnion]
    refine ⟨Nat.log 2 p, Finset.mem_Icc.mpr ⟨hlogPos, hlogLe⟩, ?_⟩
    rw [primeLogShell, Finset.mem_filter]
    exact ⟨hp, rfl⟩

/-- The reciprocal prime sum is the sum of its dyadic shells. -/
theorem primeReciprocalSum_eq_shells (z : ℕ) :
    primeReciprocalSum z =
      ∑ j ∈ Finset.Icc 1 (Nat.log 2 z),
        ∑ p ∈ primeLogShell z j, (1 : ℝ) / p := by
  classical
  rw [primeReciprocalSum, ← biUnion_primeLogShell z,
    Finset.sum_biUnion (pairwiseDisjoint_primeLogShell z (Nat.log 2 z))]

/-- Each prime reciprocal in shell `j` is at most `2^{-j}`. -/
theorem sum_primeLogShell_le_card_div_pow (z j : ℕ) :
    (∑ p ∈ primeLogShell z j, (1 : ℝ) / p) ≤
      (primeLogShell z j).card / (2 : ℝ) ^ j := by
  classical
  calc
    (∑ p ∈ primeLogShell z j, (1 : ℝ) / p) ≤
        ∑ _p ∈ primeLogShell z j, (1 : ℝ) / (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro p hp
      have hpData := Finset.mem_filter.mp (show p ∈
        (Nat.primesLE z).filter (fun q => Nat.log 2 q = j) by
          simpa [primeLogShell] using hp)
      have hpPos : p ≠ 0 := (Nat.prime_of_mem_primesLE hpData.1).ne_zero
      have hpowNat : 2 ^ j ≤ p := by
        rw [← hpData.2]
        exact Nat.pow_log_le_self 2 hpPos
      have hpow : (2 : ℝ) ^ j ≤ p := by exact_mod_cast hpowNat
      exact one_div_le_one_div_of_le (by positivity) hpow
    _ = (primeLogShell z j).card / (2 : ℝ) ^ j := by
      simp [div_eq_mul_inv]

/-- A dyadic shell has at most `π(2^(j+1))` members. -/
theorem card_primeLogShell_le_primeCounting (z j : ℕ) :
    (primeLogShell z j).card ≤ Nat.primeCounting (2 ^ (j + 1)) := by
  classical
  rw [← Nat.primesLE_card_eq_primeCounting]
  apply Finset.card_le_card
  intro p hp
  rw [primeLogShell, Finset.mem_filter] at hp
  rw [Nat.mem_primesLE]
  refine ⟨?_, Nat.prime_of_mem_primesLE hp.1⟩
  have hlt : p < 2 ^ (Nat.log 2 p).succ :=
    Nat.lt_pow_succ_log_self (by omega) p
  rw [hp.2, Nat.succ_eq_add_one] at hlt
  exact hlt.le

/-- A shell reciprocal sum is bounded by a prime-counting quotient. -/
theorem sum_primeLogShell_le_primeCounting_div_pow (z j : ℕ) :
    (∑ p ∈ primeLogShell z j, (1 : ℝ) / p) ≤
      (Nat.primeCounting (2 ^ (j + 1)) : ℝ) / (2 : ℝ) ^ j := by
  refine (sum_primeLogShell_le_card_div_pow z j).trans ?_
  apply div_le_div_of_nonneg_right
  · exact_mod_cast card_primeLogShell_le_primeCounting z j
  · positivity

/-- Chebyshev's estimate turns the `j`-th shell into a harmonic summand. -/
theorem primeCounting_pow_div_pow_le_harmonicSummand
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    {j : ℕ} (hj : 1 ≤ j) :
    (Nat.primeCounting (2 ^ (j + 1)) : ℝ) / (2 : ℝ) ^ j ≤
      (2 * C / Real.log 2) * (j : ℝ)⁻¹ := by
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hjPos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hjOnePos : (0 : ℝ) < j + 1 := by positivity
  have htTwo : 2 ≤ 2 ^ (j + 1) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hbase := hcheb (2 ^ (j + 1)) htTwo
  calc
    (Nat.primeCounting (2 ^ (j + 1)) : ℝ) / (2 : ℝ) ^ j ≤
        (C * (2 ^ (j + 1) : ℕ) / Real.log (2 ^ (j + 1) : ℕ)) /
          (2 : ℝ) ^ j := by
      apply div_le_div_of_nonneg_right hbase
      positivity
    _ = (2 * C / Real.log 2) * ((j + 1 : ℕ) : ℝ)⁻¹ := by
      rw [show ((2 ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) by norm_cast,
        Real.log_pow, pow_succ]
      push_cast
      field_simp
    _ ≤ (2 * C / Real.log 2) * (j : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left
      · exact inv_anti₀ hjPos (by norm_num)
      · positivity

/-- The prime reciprocal mass is bounded by a constant multiple of a
harmonic number at the dyadic logarithm. -/
theorem primeReciprocalSum_le_harmonic
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (z : ℕ) :
    primeReciprocalSum z ≤
      (2 * C / Real.log 2) * (harmonic (Nat.log 2 z) : ℝ) := by
  classical
  rw [primeReciprocalSum_eq_shells]
  calc
    (∑ j ∈ Finset.Icc 1 (Nat.log 2 z),
        ∑ p ∈ primeLogShell z j, (1 : ℝ) / p) ≤
        ∑ j ∈ Finset.Icc 1 (Nat.log 2 z),
          (2 * C / Real.log 2) * (j : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjOne : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      exact (sum_primeLogShell_le_primeCounting_div_pow z j).trans
        (primeCounting_pow_div_pow_le_harmonicSummand hC hcheb hjOne)
    _ = (2 * C / Real.log 2) * (harmonic (Nat.log 2 z) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        Finset.mul_sum]

/-- The ordinary logarithm of a natural is bounded by its binary logarithm,
up to the harmless additive constant used below. -/
theorem one_add_log_nat_le_two_add_log_two (J : ℕ) :
    1 + Real.log (J : ℝ) ≤ Nat.log 2 J + 2 := by
  by_cases hJ : J = 0
  · simp [hJ]
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (Nat.pos_of_ne_zero hJ)
  have hpowNat : J < 2 ^ (Nat.log 2 J + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) J
  have hpow : (J : ℝ) < (2 : ℝ) ^ (Nat.log 2 J + 1) := by
    exact_mod_cast hpowNat
  have hlogJ : Real.log (J : ℝ) < Nat.log 2 J + 1 := by
    have hlogMono := Real.strictMonoOn_log hJpos
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 J + 1)) hpow
    rw [Real.log_pow] at hlogMono
    have hlogTwoLe : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at this ⊢
      exact this
    calc
      Real.log (J : ℝ) <
          ((Nat.log 2 J + 1 : ℕ) : ℝ) * Real.log 2 := hlogMono
      _ ≤ ((Nat.log 2 J + 1 : ℕ) : ℝ) * 1 := by gcongr
      _ = Nat.log 2 J + 1 := by push_cast; ring
  linarith

/-- A fully discrete logarithmic bound for harmonic numbers.  It is weaker
than the standard real-log estimate by only an additive constant, and is
particularly convenient for choosing an integral Brun depth. -/
theorem harmonic_le_two_add_log_two (J : ℕ) :
    (harmonic J : ℝ) ≤ Nat.log 2 J + 2 := by
  exact (harmonic_le_one_add_log J).trans
    (one_add_log_nat_le_two_add_log_two J)

/-- Discrete `O(log log z)` form of the prime reciprocal bound. -/
theorem primeReciprocalSum_le_log_log_two
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (z : ℕ) :
    primeReciprocalSum z ≤
      (2 * C / Real.log 2) * (Nat.log 2 (Nat.log 2 z) + 2) := by
  refine (primeReciprocalSum_le_harmonic hC hcheb z).trans ?_
  apply mul_le_mul_of_nonneg_left (harmonic_le_two_add_log_two (Nat.log 2 z))
  positivity

/-- In particular the prime reciprocal mass is `O(log log z)`, stated
with the natural dyadic logarithm to avoid any rounding convention. -/
theorem primeReciprocalSum_le_one_add_log_log
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (z : ℕ) :
    primeReciprocalSum z ≤
      (2 * C / Real.log 2) *
        (1 + Real.log (Nat.log 2 z : ℕ)) := by
  refine (primeReciprocalSum_le_harmonic hC hcheb z).trans ?_
  apply mul_le_mul_of_nonneg_left (harmonic_le_one_add_log (Nat.log 2 z))
  positivity

/-- The elementary moment majorant from `QualitativeSieve` grows only
polylogarithmically in `z`.  The finitely many primes at most `2k` are
absorbed into the first factor. -/
theorem prod_binomialMomentMajorant_le_exp_log_log
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    {k z : ℕ} (hk : 0 < k) :
    (∏ p ∈ (sievePrimeProduct k z).primeFactors,
        binomialMomentMajorant k p) ≤
      (4 * k : ℝ) ^ (2 * k + 1) *
        Real.exp ((6 * k : ℝ) * (2 * C / Real.log 2) *
          (1 + Real.log (Nat.log 2 z : ℕ))) := by
  classical
  let P := (sievePrimeProduct k z).primeFactors
  let S := P.filter fun p => p ≤ 2 * k
  let G := P.filter fun p => ¬p ≤ 2 * k
  have hsplit :
      (∏ p ∈ P, binomialMomentMajorant k p) =
        (∏ _p ∈ S, (4 * k : ℝ)) *
          ∏ p ∈ G, (1 + (6 * k : ℝ) / p) := by
    simpa [binomialMomentMajorant, S, G] using
      (Finset.prod_ite (s := P) (p := fun p => p ≤ 2 * k)
        (fun _p => (4 * k : ℝ))
        (fun p => 1 + (6 * k : ℝ) / p))
  have hSsub : S ⊆ Finset.range (2 * k + 1) := by
    intro p hp
    have hp' : p ∈ P ∧ p ≤ 2 * k := by simpa [S] using hp
    rw [Finset.mem_range]
    omega
  have hScard : S.card ≤ 2 * k + 1 := by
    simpa using Finset.card_le_card hSsub
  have hsmall :
      (∏ _p ∈ S, (4 * k : ℝ)) ≤ (4 * k : ℝ) ^ (2 * k + 1) := by
    simp only [Finset.prod_const]
    apply pow_le_pow_right₀
    · exact_mod_cast (by omega : 1 ≤ 4 * k)
    · exact hScard
  have hGsub : G ⊆ Nat.primesLE z := by
    intro p hpG
    have hpP := (Finset.mem_filter.mp hpG).1
    have hpPrime := Nat.prime_of_mem_primeFactors hpP
    have hpProd := Nat.dvd_of_mem_primeFactors hpP
    have hmem := mem_sievePrimes.mp
      (prime_mem_sievePrimes_of_dvd_product hpPrime hpProd)
    exact Nat.mem_primesLE.mpr ⟨hmem.2.2.le, hpPrime⟩
  have hrecipG :
      (∑ p ∈ G, (1 : ℝ) / p) ≤ primeReciprocalSum z := by
    unfold primeReciprocalSum
    apply Finset.sum_le_sum_of_subset_of_nonneg hGsub
    intro p hp _hpG
    positivity
  have hrecip := primeReciprocalSum_le_one_add_log_log hC hcheb z
  have hlarge :
      (∏ p ∈ G, (1 + (6 * k : ℝ) / p)) ≤
        Real.exp ((6 * k : ℝ) * (2 * C / Real.log 2) *
          (1 + Real.log (Nat.log 2 z : ℕ))) := by
    calc
      (∏ p ∈ G, (1 + (6 * k : ℝ) / p)) ≤
          Real.exp (∑ p ∈ G, (6 * k : ℝ) / p) := by
        apply Real.prod_one_add_le_exp_sum
        intro p
        positivity
      _ = Real.exp ((6 * k : ℝ) *
          ∑ p ∈ G, (1 : ℝ) / p) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ ≤ Real.exp ((6 * k : ℝ) * (2 * C / Real.log 2) *
          (1 + Real.log (Nat.log 2 z : ℕ))) := by
        apply Real.exp_le_exp.mpr
        calc
          (6 * k : ℝ) * (∑ p ∈ G, (1 : ℝ) / p) ≤
              (6 * k : ℝ) * primeReciprocalSum z := by gcongr
          _ ≤ (6 * k : ℝ) *
              ((2 * C / Real.log 2) *
                (1 + Real.log (Nat.log 2 z : ℕ))) := by gcongr
          _ = (6 * k : ℝ) * (2 * C / Real.log 2) *
              (1 + Real.log (Nat.log 2 z : ℕ)) := by ring
  rw [show (sievePrimeProduct k z).primeFactors = P by rfl, hsplit]
  exact mul_le_mul hsmall hlarge
    (Finset.prod_nonneg fun p hp => by
      exact add_nonneg (by norm_num) (div_nonneg (by positivity) (by positivity)))
    (by positivity)

/-- Discrete version of the preceding moment bound. -/
theorem prod_binomialMomentMajorant_le_exp_log_log_two
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    {k z : ℕ} (hk : 0 < k) :
    (∏ p ∈ (sievePrimeProduct k z).primeFactors,
        binomialMomentMajorant k p) ≤
      (4 * k : ℝ) ^ (2 * k + 1) *
        Real.exp ((6 * k : ℝ) * (2 * C / Real.log 2) *
          (Nat.log 2 (Nat.log 2 z) + 2)) := by
  refine (prod_binomialMomentMajorant_le_exp_log_log hC hcheb hk).trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left
    · exact one_add_log_nat_le_two_add_log_two (Nat.log 2 z)
    · positivity
  · positivity

/-- The discrete bound applies to every subfamily of primes in `(k,z)`. -/
theorem prod_binomialMomentMajorant_le_exp_log_log_two_of_prime_bounds
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    {k z : ℕ} (hk : 0 < k) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ k < p ∧ p < z) :
    (∏ p ∈ P, binomialMomentMajorant k p) ≤
      (4 * k : ℝ) ^ (2 * k + 1) *
        Real.exp ((6 * k : ℝ) * (2 * C / Real.log 2) *
          (Nat.log 2 (Nat.log 2 z) + 2)) := by
  classical
  let P₀ := (sievePrimeProduct k z).primeFactors
  have hsub : P ⊆ P₀ := by
    intro p hp
    have hpData := hP p hp
    have hpMem : p ∈ sievePrimes k z :=
      mem_sievePrimes.mpr hpData
    have hpDvd : p ∣ sievePrimeProduct k z := by
      exact Finset.dvd_prod_of_mem id hpMem
    exact Nat.mem_primeFactors.mpr
      ⟨hpData.1, hpDvd, (sievePrimeProduct_pos k z).ne'⟩
  have hfactorOne : ∀ p ∈ P₀, 1 ≤ binomialMomentMajorant k p := by
    intro p hp
    unfold binomialMomentMajorant
    split_ifs
    · exact_mod_cast (by omega : 1 ≤ 4 * k)
    · exact le_add_of_nonneg_right (by positivity)
  calc
    (∏ p ∈ P, binomialMomentMajorant k p) ≤
        ∏ p ∈ P₀, binomialMomentMajorant k p := by
      apply Finset.prod_le_prod_of_subset_of_one_le hsub
      · intro p hp
        exact (hfactorOne p (hsub hp)).trans' zero_le_one
      · intro p hp _hpP
        exact hfactorOne p hp
    _ ≤ (4 * k : ℝ) ^ (2 * k + 1) *
        Real.exp ((6 * k : ℝ) * (2 * C / Real.log 2) *
          (Nat.log 2 (Nat.log 2 z) + 2)) := by
      simpa [P₀] using
        (prod_binomialMomentMajorant_le_exp_log_log_two hC hcheb hk
          (z := z))

/-- Generic moment/Euler comparison for a finite family of primes in
`(k,z)`. -/
theorem binomialMomentProduct_le_exp_log_log_two_mul_euler
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    {k z : ℕ} (hk : 0 < k) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ k < p ∧ p < z) :
    (∏ p ∈ P, (1 + 2 * binomialSieveNu k p)) ≤
      ((4 * k : ℝ) ^ (2 * k + 1) *
        Real.exp ((6 * k : ℝ) * (2 * C / Real.log 2) *
          (Nat.log 2 (Nat.log 2 z) + 2))) *
        finiteEulerProduct P (fun p => binomialSieveNu k p) := by
  have hlocal : ∀ p ∈ P,
      1 + 2 * binomialSieveNu k p ≤
        binomialMomentMajorant k p * (1 - binomialSieveNu k p) := by
    intro p hpP
    exact binomial_moment_le_majorant hk (hP p hpP).1 (hP p hpP).2.1
  have hmajorant :=
    prod_binomialMomentMajorant_le_exp_log_log_two_of_prime_bounds
      hC hcheb hk P hP
  have hEulerNonneg :
      0 ≤ finiteEulerProduct P (fun p => binomialSieveNu k p) := by
    unfold finiteEulerProduct
    apply Finset.prod_nonneg
    intro p hp
    change 0 ≤ 1 - binomialSieveNu k p
    rw [binomialSieveNu_prime (hP p hp).1]
    have hpPos : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
    exact sub_nonneg.mpr ((div_le_one hpPos).mpr
      (by exact_mod_cast (hP p hp).2.1.le))
  calc
    (∏ p ∈ P, (1 + 2 * binomialSieveNu k p)) ≤
        ∏ p ∈ P, (binomialMomentMajorant k p *
          (1 - binomialSieveNu k p)) := by
      apply Finset.prod_le_prod
      · intro p hp
        rw [binomialSieveNu_prime (hP p hp).1]
        positivity
      · exact hlocal
    _ = (∏ p ∈ P, binomialMomentMajorant k p) *
          finiteEulerProduct P (fun p => binomialSieveNu k p) := by
      rw [Finset.prod_mul_distrib]
      rfl
    _ ≤ ((4 * k : ℝ) ^ (2 * k + 1) *
          Real.exp ((6 * k : ℝ) * (2 * C / Real.log 2) *
            (Nat.log 2 (Nat.log 2 z) + 2))) *
        finiteEulerProduct P (fun p => binomialSieveNu k p) :=
      mul_le_mul_of_nonneg_right hmajorant hEulerNonneg

/-- Generic powers-of-two tail criterion for the binomial local density. -/
theorem binomial_brunTail_le_half_of_exp_log_log_two_bound
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    {k z L : ℕ} (hk : 0 < k) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ k < p ∧ p < z)
    (hpow :
      2 * ((4 * k : ℝ) ^ (2 * k + 1) *
        Real.exp ((6 * k : ℝ) * (2 * C / Real.log 2) *
          (Nat.log 2 (Nat.log 2 z) + 2))) ≤
        (2 : ℝ) ^ (L + 1)) :
    2 * brunSubsetTail P (fun p => binomialSieveNu k p) L ≤
      finiteEulerProduct P (fun p => binomialSieveNu k p) := by
  apply two_mul_brunSubsetTail_le_of_moment
  · intro p hp
    rw [binomialSieveNu_prime (hP p hp).1]
    positivity
  · have hmoment := binomialMomentProduct_le_exp_log_log_two_mul_euler
      hC hcheb hk P hP
    have hEulerNonneg :
        0 ≤ finiteEulerProduct P (fun p => binomialSieveNu k p) := by
      unfold finiteEulerProduct
      apply Finset.prod_nonneg
      intro p hp
      change 0 ≤ 1 - binomialSieveNu k p
      rw [binomialSieveNu_prime (hP p hp).1]
      have hpPos : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
      exact sub_nonneg.mpr ((div_le_one hpPos).mpr
        (by exact_mod_cast (hP p hp).2.1.le))
    calc
      2 * (∏ p ∈ P, (1 + 2 * binomialSieveNu k p)) ≤
          2 * (((4 * k : ℝ) ^ (2 * k + 1) *
            Real.exp ((6 * k : ℝ) * (2 * C / Real.log 2) *
              (Nat.log 2 (Nat.log 2 z) + 2))) *
                finiteEulerProduct P (fun p => binomialSieveNu k p)) := by
        gcongr
      _ = (2 * ((4 * k : ℝ) ^ (2 * k + 1) *
            Real.exp ((6 * k : ℝ) * (2 * C / Real.log 2) *
              (Nat.log 2 (Nat.log 2 z) + 2)))) *
                finiteEulerProduct P (fun p => binomialSieveNu k p) := by ring
      _ ≤ (2 : ℝ) ^ (L + 1) *
          finiteEulerProduct P (fun p => binomialSieveNu k p) :=
        mul_le_mul_of_nonneg_right hpow hEulerNonneg

/-- Any fixed real exponential base is dominated by an integral power of
two; consequently its `r`-th power is dominated uniformly in `r`. -/
theorem exists_exp_mul_nat_le_pow_two (A : ℝ) :
    ∃ a : ℕ, ∀ r : ℕ,
      Real.exp (A * r) ≤ (2 : ℝ) ^ (a * r) := by
  have hevent :=
    (tendsto_pow_atTop_atTop_of_one_lt
      (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop (Real.exp A)
  obtain ⟨a, ha⟩ := hevent.exists
  refine ⟨a, ?_⟩
  intro r
  calc
    Real.exp (A * r) = Real.exp A ^ r := by
      rw [mul_comm, Real.exp_nat_mul]
    _ ≤ ((2 : ℝ) ^ a) ^ r :=
      pow_le_pow_left₀ (Real.exp_nonneg A) ha r
    _ = (2 : ℝ) ^ (a * r) := by rw [pow_mul]

/-- Odd depth used after choosing the two fixed power-of-two constants. -/
def logarithmicBrunDepth (a b z : ℕ) : ℕ :=
  2 * (b + a * (Nat.log 2 (Nat.log 2 z) + 2)) + 1

theorem logarithmicBrunDepth_odd (a b z : ℕ) :
    Odd (logarithmicBrunDepth a b z) := by
  refine ⟨b + a * (Nat.log 2 (Nat.log 2 z) + 2), ?_⟩
  simp [logarithmicBrunDepth]

/-- Fixed integral constants make the discrete moment coefficient fit below
the powers-of-two depth for every endpoint `z`. -/
theorem exists_logarithmicBrunDepth_parameters
    (C : ℝ) (k : ℕ) :
    ∃ a b : ℕ, ∀ z : ℕ,
      2 * ((4 * k : ℝ) ^ (2 * k + 1) *
        Real.exp ((6 * k : ℝ) * (2 * C / Real.log 2) *
          (Nat.log 2 (Nat.log 2 z) + 2))) ≤
        (2 : ℝ) ^ (logarithmicBrunDepth a b z + 1) := by
  let A : ℝ := (6 * k : ℝ) * (2 * C / Real.log 2)
  let K₀ : ℝ := 2 * (4 * k : ℝ) ^ (2 * k + 1)
  obtain ⟨a, ha⟩ := exists_exp_mul_nat_le_pow_two A
  have hevent :=
    (tendsto_pow_atTop_atTop_of_one_lt
      (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop K₀
  obtain ⟨b, hb⟩ := hevent.exists
  refine ⟨a, b, ?_⟩
  intro z
  let r := Nat.log 2 (Nat.log 2 z) + 2
  have hExp := ha r
  have hprod :
      K₀ * Real.exp (A * r) ≤ (2 : ℝ) ^ (b + a * r) := by
    calc
      K₀ * Real.exp (A * r) ≤
          (2 : ℝ) ^ b * (2 : ℝ) ^ (a * r) :=
        mul_le_mul hb hExp (Real.exp_nonneg _) (by positivity)
      _ = (2 : ℝ) ^ (b + a * r) := (pow_add _ _ _).symm
  have hexp : b + a * r ≤ logarithmicBrunDepth a b z + 1 := by
    simp [logarithmicBrunDepth, r]
    omega
  have hpowMono :
      (2 : ℝ) ^ (b + a * r) ≤
        (2 : ℝ) ^ (logarithmicBrunDepth a b z + 1) := by
    exact pow_le_pow_right₀ (by norm_num) hexp
  simpa [K₀, A, r, Nat.cast_add, Nat.cast_ofNat, mul_assoc] using
    hprod.trans hpowMono

/-- The complete powers-of-two moment is bounded by the polylogarithmic
majorant times the absorber sieve's Euler product. -/
theorem absorberMomentProduct_le_exp_log_log_mul_euler
    {Cπ : ℝ} (hCπ : 0 < Cπ)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ Cπ * t / Real.log t)
    {m k z : ℕ} (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k) :
    (∏ p ∈ (sievePrimeProduct k z).primeFactors,
        (1 + 2 * binomialSieveNu k p)) ≤
      ((4 * k : ℝ) ^ (2 * k + 1) *
        Real.exp ((6 * k : ℝ) * (2 * Cπ / Real.log 2) *
          (1 + Real.log (Nat.log 2 z : ℕ)))) *
        absorberEulerProduct k z := by
  let P := (sievePrimeProduct k z).primeFactors
  have hlocal : ∀ p ∈ P,
      1 + 2 * binomialSieveNu k p ≤
        binomialMomentMajorant k p * (1 - binomialSieveNu k p) := by
    intro p hpP
    have hpPrime := Nat.prime_of_mem_primeFactors hpP
    have hpProd := Nat.dvd_of_mem_primeFactors hpP
    have hmem := mem_sievePrimes.mp
      (prime_mem_sievePrimes_of_dvd_product hpPrime hpProd)
    exact binomial_moment_le_majorant hk hpPrime hmem.2.1
  have hmajorant := prod_binomialMomentMajorant_le_exp_log_log
    hCπ hcheb (z := z) hk
  have hV := (absorberEulerProduct_pos C hk (z := z)).le
  calc
    (∏ p ∈ (sievePrimeProduct k z).primeFactors,
        (1 + 2 * binomialSieveNu k p)) ≤
        ∏ p ∈ P, (binomialMomentMajorant k p *
          (1 - binomialSieveNu k p)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpPrime := Nat.prime_of_mem_primeFactors hp
        rw [binomialSieveNu_prime hpPrime]
        positivity
      · exact hlocal
    _ = (∏ p ∈ P, binomialMomentMajorant k p) *
          absorberEulerProduct k z := by
      rw [Finset.prod_mul_distrib]
      rfl
    _ ≤ ((4 * k : ℝ) ^ (2 * k + 1) *
          Real.exp ((6 * k : ℝ) * (2 * Cπ / Real.log 2) *
            (1 + Real.log (Nat.log 2 z : ℕ)))) *
        absorberEulerProduct k z := by
      exact mul_le_mul_of_nonneg_right (by simpa [P] using hmajorant) hV

/-- A logarithmic-depth numerical condition now suffices for the half-Euler
Brun-tail estimate. -/
theorem absorber_brunTail_le_half_of_exp_log_log_bound
    {Cπ : ℝ} (hCπ : 0 < Cπ)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ Cπ * t / Real.log t)
    {m k z L : ℕ} (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k)
    (hpow :
      2 * ((4 * k : ℝ) ^ (2 * k + 1) *
        Real.exp ((6 * k : ℝ) * (2 * Cπ / Real.log 2) *
          (1 + Real.log (Nat.log 2 z : ℕ)))) ≤
        (2 : ℝ) ^ (L + 1)) :
    2 * brunSubsetTail (sievePrimeProduct k z).primeFactors
          (fun p => binomialSieveNu k p) L ≤
      absorberEulerProduct k z := by
  apply two_mul_brunSubsetTail_le_of_moment
  · intro p hpP
    have hpPrime := Nat.prime_of_mem_primeFactors hpP
    rw [binomialSieveNu_prime hpPrime]
    positivity
  · have hmoment := absorberMomentProduct_le_exp_log_log_mul_euler
      hCπ hcheb C hk (z := z)
    have hV := (absorberEulerProduct_pos C hk (z := z)).le
    calc
      2 * (∏ p ∈ (sievePrimeProduct k z).primeFactors,
          (1 + 2 * binomialSieveNu k p)) ≤
          2 * (((4 * k : ℝ) ^ (2 * k + 1) *
            Real.exp ((6 * k : ℝ) * (2 * Cπ / Real.log 2) *
              (1 + Real.log (Nat.log 2 z : ℕ)))) *
                absorberEulerProduct k z) := by gcongr
      _ = (2 * ((4 * k : ℝ) ^ (2 * k + 1) *
            Real.exp ((6 * k : ℝ) * (2 * Cπ / Real.log 2) *
              (1 + Real.log (Nat.log 2 z : ℕ))))) *
                absorberEulerProduct k z := by ring
      _ ≤ (2 : ℝ) ^ (L + 1) * absorberEulerProduct k z :=
        mul_le_mul_of_nonneg_right hpow hV
      _ = (2 : ℝ) ^ (L + 1) *
          finiteEulerProduct (sievePrimeProduct k z).primeFactors
            (fun p => binomialSieveNu k p) := by rfl

/-- The discrete double-log coefficient also implies the half-Euler tail
bound. -/
theorem absorber_brunTail_le_half_of_exp_log_log_two_bound
    {Cπ : ℝ} (hCπ : 0 < Cπ)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ Cπ * t / Real.log t)
    {m k z L : ℕ} (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k)
    (hpow :
      2 * ((4 * k : ℝ) ^ (2 * k + 1) *
        Real.exp ((6 * k : ℝ) * (2 * Cπ / Real.log 2) *
          (Nat.log 2 (Nat.log 2 z) + 2))) ≤
        (2 : ℝ) ^ (L + 1)) :
    2 * brunSubsetTail (sievePrimeProduct k z).primeFactors
          (fun p => binomialSieveNu k p) L ≤
      absorberEulerProduct k z := by
  apply absorber_brunTail_le_half_of_exp_log_log_bound hCπ hcheb C hk
  refine (mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)).trans hpow
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left
    · exact one_add_log_nat_le_two_add_log_two (Nat.log 2 z)
    · positivity
  · positivity

/-- For fixed `k`, two fixed natural constants give a valid odd
logarithmic Brun depth simultaneously for every `z`. -/
theorem exists_absorber_brunTail_le_half_logarithmicDepth
    {Cπ : ℝ} (hCπ : 0 < Cπ)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ Cπ * t / Real.log t)
    {m k : ℕ} (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k) :
    ∃ a b : ℕ, ∀ z : ℕ,
      2 * brunSubsetTail (sievePrimeProduct k z).primeFactors
            (fun p => binomialSieveNu k p)
            (logarithmicBrunDepth a b z) ≤
        absorberEulerProduct k z := by
  obtain ⟨a, b, hab⟩ := exists_logarithmicBrunDepth_parameters Cπ k
  refine ⟨a, b, ?_⟩
  intro z
  exact absorber_brunTail_le_half_of_exp_log_log_two_bound
    hCπ hcheb C hk (hab z)

end PrimeReciprocal

end Erdos387
