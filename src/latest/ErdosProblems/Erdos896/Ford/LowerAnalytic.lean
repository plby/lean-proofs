/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.LowerBridge
import ErdosProblems.Erdos896.Ford.H1Count
import ErdosProblems.Erdos896.Ford.StirlingScale

/-!
# Analytic aggregation for the Ford lower bound

This file packages the last analytic summation in the lower bound for
Erdős Problem 896.  A logarithmic stack of disjoint factor-four prime
blocks is placed strictly inside the candidate-prime band.  The generous
integer margins in the exponents absorb every quotient endpoint occurring
in the exact scaled divisor window.
-/

namespace Erdos896

open Filter Asymptotics
open scoped BigOperators

namespace Ford

/-- The coarse logarithmic parameter used to place the prime blocks. -/
def lowerAnalyticIndex (N : ℕ) : ℕ := Nat.log 2 N / 24

/-- The number of factor-four blocks used in the prime aggregation. -/
def lowerAnalyticBlockCount (N : ℕ) : ℕ :=
  (lowerAnalyticIndex N - 20) / 2

/-- The base of the `j`-th factor-four block. -/
def lowerAnalyticBlockBase (N j : ℕ) : ℕ :=
  2 ^ (16 * lowerAnalyticIndex N + 17 + 2 * j)

/-- A disjoint logarithmic stack of factor-four prime blocks. -/
def lowerAnalyticPrimeCore (N : ℕ) : Finset ℕ :=
  (Finset.range (lowerAnalyticBlockCount N)).biUnion fun j ↦
    Erdos896.primeBlock (lowerAnalyticBlockBase N j)

private theorem lowerAnalytic_exponent_bounds
    {N j : ℕ} (hj : j < lowerAnalyticBlockCount N) :
    2 * (Nat.log 2 N + 1) ≤
        3 * (16 * lowerAnalyticIndex N + 17 + 2 * j) ∧
      24 * (16 * lowerAnalyticIndex N + 17 + 2 * j + 3) ≤
        17 * Nat.log 2 N ∧
      16 * lowerAnalyticIndex N + 17 + 2 * j + 2 ≤ Nat.log 2 N := by
  let L := Nat.log 2 N
  let k := lowerAnalyticIndex N
  have hk : k = L / 24 := by simp [k, L, lowerAnalyticIndex]
  have hLlow : 24 * k ≤ L := by
    rw [hk, mul_comm]
    exact Nat.div_mul_le_self L 24
  have hLhigh : L < 24 * (k + 1) := by
    rw [hk]
    have h := Nat.lt_div_mul_add (a := L) (by omega : 0 < 24)
    omega
  have hj' : j < (k - 20) / 2 := by
    simpa [lowerAnalyticBlockCount, k] using hj
  have htwom : 2 * ((k - 20) / 2) ≤ k - 20 := by
    simpa [mul_comm] using Nat.div_mul_le_self (k - 20) 2
  have hjbound : 2 * (j + 1) ≤ k - 20 := by omega
  have hklarge : 22 ≤ k := by omega
  constructor
  · omega
  constructor <;> omega

/-- Every prime in the logarithmic core belongs to the candidate pool.
The strengthened middle inequality is also recorded: it is the margin
needed after replacing `N/(2p)` by its natural quotient. -/
theorem mem_lowerAnalyticPrimeCore_data {N p : ℕ} (hN : 1 ≤ N)
    (hp : p ∈ lowerAnalyticPrimeCore N) :
    p ∈ candidatePrimePool N ∧ 2 ^ 24 * p ^ 24 ≤ N ^ 17 := by
  classical
  rw [lowerAnalyticPrimeCore, Finset.mem_biUnion] at hp
  obtain ⟨j, hj, hpblock⟩ := hp
  have hjlt : j < lowerAnalyticBlockCount N := Finset.mem_range.mp hj
  have hb := Erdos896.mem_primeBlock.mp hpblock
  let L := Nat.log 2 N
  let e := 16 * lowerAnalyticIndex N + 17 + 2 * j
  have hexp := lowerAnalytic_exponent_bounds hjlt
  have hN0 : N ≠ 0 := by omega
  have hpowL : 2 ^ L ≤ N := by
    simpa [L] using Nat.pow_log_le_self 2 hN0
  have hNupper : N < 2 ^ (L + 1) := by
    simpa [L] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) N
  have hbase : lowerAnalyticBlockBase N j = 2 ^ e := rfl
  have hfour : 4 * lowerAnalyticBlockBase N j = 2 ^ (e + 2) := by
    rw [hbase]
    simp only [show 4 = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have hpN : p ≤ N := by
    calc
      p ≤ 4 * lowerAnalyticBlockBase N j := hb.2.1
      _ = 2 ^ (e + 2) := hfour
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hexp.2.2
      _ ≤ N := hpowL
  have hNcube : N ^ 2 < p ^ 3 := by
    have hpowExp : 2 ^ (2 * (L + 1)) ≤ 2 ^ (3 * e) :=
      Nat.pow_le_pow_right (by omega) hexp.1
    have hbasep : (2 ^ e) ^ 3 < p ^ 3 :=
      Nat.pow_lt_pow_left hb.1 (by omega)
    calc
      N ^ 2 < (2 ^ (L + 1)) ^ 2 := Nat.pow_lt_pow_left hNupper (by omega)
      _ = 2 ^ (2 * (L + 1)) := by
        rw [show 2 * (L + 1) = (L + 1) * 2 by omega, Nat.pow_mul]
      _ ≤ 2 ^ (3 * e) := hpowExp
      _ = (2 ^ e) ^ 3 := by
        rw [show 3 * e = e * 3 by omega, Nat.pow_mul]
      _ < p ^ 3 := hbasep
  have hsafety : 2 ^ 24 * p ^ 24 ≤ N ^ 17 := by
    have hpupper : p ≤ 2 ^ (e + 2) := by simpa [hfour] using hb.2.1
    have hppow : p ^ 24 ≤ (2 ^ (e + 2)) ^ 24 :=
      Nat.pow_le_pow_left hpupper 24
    calc
      2 ^ 24 * p ^ 24 ≤ 2 ^ 24 * (2 ^ (e + 2)) ^ 24 :=
        Nat.mul_le_mul_left _ hppow
      _ = 2 ^ (24 * (e + 3)) := by
        rw [← Nat.pow_mul]
        rw [← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ (17 * L) := Nat.pow_le_pow_right (by omega) hexp.2.1
      _ = (2 ^ L) ^ 17 := by
        rw [show 17 * L = L * 17 by omega, Nat.pow_mul]
      _ ≤ N ^ 17 := Nat.pow_le_pow_left hpowL 17
  refine ⟨mem_candidatePrimePool.mpr ⟨by omega, hpN, hb.2.2,
    hNcube, ?_⟩, hsafety⟩
  exact (Nat.le_mul_of_pos_left (p ^ 24) (by positivity : 0 < 2 ^ 24)).trans hsafety

theorem lowerAnalyticPrimeCore_subset_candidatePrimePool {N : ℕ}
    (hN : 1 ≤ N) :
    lowerAnalyticPrimeCore N ⊆ candidatePrimePool N := by
  intro p hp
  exact (mem_lowerAnalyticPrimeCore_data hN hp).1

private theorem lowerAnalyticPrimeBlocks_pairwise (N : ℕ) :
    ((Finset.range (lowerAnalyticBlockCount N) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun j ↦ Erdos896.primeBlock (lowerAnalyticBlockBase N j)) := by
  intro i hi j hj hij
  change Disjoint (Erdos896.primeBlock (lowerAnalyticBlockBase N i))
    (Erdos896.primeBlock (lowerAnalyticBlockBase N j))
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hi' := Erdos896.mem_primeBlock.mp hpi
  have hj' := Erdos896.mem_primeBlock.mp hpj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hbase : 4 * lowerAnalyticBlockBase N i ≤
        lowerAnalyticBlockBase N j := by
      unfold lowerAnalyticBlockBase
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
      apply Nat.pow_le_pow_right (by omega)
      omega
    exact (not_lt_of_ge (hi'.2.1.trans hbase)) hj'.1
  · have hbase : 4 * lowerAnalyticBlockBase N j ≤
        lowerAnalyticBlockBase N i := by
      unfold lowerAnalyticBlockBase
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
      apply Nat.pow_le_pow_right (by omega)
      omega
    exact (not_lt_of_ge (hj'.2.1.trans hbase)) hi'.1

theorem sum_lowerAnalyticPrimeCore (N : ℕ) :
    (∑ p ∈ lowerAnalyticPrimeCore N, (1 : ℝ) / p) =
      ∑ j ∈ Finset.range (lowerAnalyticBlockCount N),
        ∑ p ∈ Erdos896.primeBlock (lowerAnalyticBlockBase N j),
          (1 : ℝ) / p := by
  exact Finset.sum_biUnion (lowerAnalyticPrimeBlocks_pairwise N)

/-- The logarithmic stack has a uniformly positive reciprocal-prime mass.
This is where the factor `log N` lost by a single Chebyshev block is
recovered by summing `asymp log N` disjoint blocks. -/
theorem eventually_lowerAnalyticPrimeCore_harmonic_lower :
    ∀ᶠ N : ℕ in atTop,
      (1 / 4096 : ℝ) ≤
        ∑ p ∈ lowerAnalyticPrimeCore N, (1 : ℝ) / p := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    Erdos896.eventually_primeBlock_harmonic_lower
  let K := max 100 (Nat.log 2 (max B 2) + 1)
  filter_upwards [eventually_ge_atTop (2 ^ (24 * K))] with N hN
  have hNpos : 0 < N :=
    (Nat.pow_pos (by omega : 0 < 2)).trans_le hN
  have hN0 : N ≠ 0 := Nat.ne_of_gt hNpos
  let L := Nat.log 2 N
  let k := lowerAnalyticIndex N
  let m := lowerAnalyticBlockCount N
  have hlogLower : 24 * K ≤ L := by
    dsimp [L]
    exact Nat.le_log_of_pow_le (by omega : 1 < 2) hN
  have hK100 : 100 ≤ K := le_max_left _ _
  have hLlarge : 2400 ≤ L := by nlinarith
  have hk : k = L / 24 := by simp [k, L, lowerAnalyticIndex]
  have hm : m = (k - 20) / 2 := by
    simp [m, k, lowerAnalyticBlockCount]
  have hLlow : 24 * k ≤ L := by
    rw [hk, mul_comm]
    exact Nat.div_mul_le_self L 24
  have hLhigh : L < 24 * (k + 1) := by
    rw [hk]
    have h := Nat.lt_div_mul_add (a := L) (by omega : 0 < 24)
    omega
  have hmLower : L + 1 ≤ 100 * m := by
    rw [hm]
    have hdiv : 2 * ((k - 20) / 2) + 1 ≥ k - 20 := by
      have h := Nat.lt_div_mul_add (a := k - 20) (by omega : 0 < 2)
      omega
    omega
  have hpowL : 2 ^ L ≤ N := by
    simpa [L] using Nat.pow_log_le_self 2 hN0
  have hNupper : N < 2 ^ (L + 1) := by
    simpa [L] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) N
  have hlogNpos : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by
      exact (Nat.one_lt_two_pow (by nlinarith [hK100])).trans_le hN)
  have hlogNupper : Real.log (N : ℝ) ≤
      (L + 1 : ℕ) * Real.log 2 := by
    have hlog := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by exact_mod_cast hNpos : (0 : ℝ) < (N : ℝ)))
      (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < ((2 ^ (L + 1) : ℕ) : ℝ)))
      (by exact_mod_cast hNupper.le : (N : ℝ) ≤ ((2 ^ (L + 1) : ℕ) : ℝ))
    rw [Nat.cast_pow, Real.log_pow] at hlog
    simpa using hlog
  have hblock : ∀ j ∈ Finset.range m,
      Real.log 2 / (24 * Real.log (N : ℝ)) ≤
        ∑ p ∈ Erdos896.primeBlock (lowerAnalyticBlockBase N j),
          (1 : ℝ) / p := by
    intro j hj
    have hjlt : j < m := Finset.mem_range.mp hj
    have hbaseLeN : lowerAnalyticBlockBase N j ≤ N := by
      have hexp := (lowerAnalytic_exponent_bounds (N := N) (j := j) (by
        simpa [m] using hjlt)).2.2
      calc
        lowerAnalyticBlockBase N j ≤
            4 * lowerAnalyticBlockBase N j := by
              exact Nat.le_mul_of_pos_left _ (by omega)
        _ = 2 ^ (16 * lowerAnalyticIndex N + 17 + 2 * j + 2) := by
          unfold lowerAnalyticBlockBase
          rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
          congr 1
          omega
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by simpa [L] using hexp)
        _ ≤ N := hpowL
    have hbaseB : B ≤ lowerAnalyticBlockBase N j := by
      have hKB : Nat.log 2 (max B 2) + 1 ≤ K := le_max_right _ _
      have hBpow : max B 2 < 2 ^ K := by
        exact (Nat.lt_pow_succ_log_self (by omega : 1 < 2) (max B 2)).trans_le
          (Nat.pow_le_pow_right (by omega) hKB)
      have hKexp : K ≤ 16 * lowerAnalyticIndex N + 17 + 2 * j := by
        change K ≤ 16 * k + 17 + 2 * j
        rw [hk]
        omega
      exact (le_max_left B 2).trans (hBpow.le.trans
        (Nat.pow_le_pow_right (by omega) hKexp))
    have hbasePos : 0 < lowerAnalyticBlockBase N j := by
      unfold lowerAnalyticBlockBase
      positivity
    have hlogbasePos : 0 < Real.log (lowerAnalyticBlockBase N j : ℝ) := by
      apply Real.log_pos
      have : 2 ≤ lowerAnalyticBlockBase N j := by
        unfold lowerAnalyticBlockBase
        exact Nat.one_lt_two_pow (by omega)
      exact_mod_cast this
    have hlogbaseN : Real.log (lowerAnalyticBlockBase N j : ℝ) ≤
        Real.log (N : ℝ) := by
      exact Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by exact_mod_cast hbasePos))
        (Set.mem_Ioi.mpr (by exact_mod_cast hNpos))
        (by exact_mod_cast hbaseLeN)
    calc
      Real.log 2 / (24 * Real.log (N : ℝ)) ≤
          Real.log 2 / (24 * Real.log (lowerAnalyticBlockBase N j : ℝ)) := by
        exact div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num))
          (mul_pos (by norm_num) hlogbasePos) (by gcongr)
      _ ≤ ∑ p ∈ Erdos896.primeBlock (lowerAnalyticBlockBase N j),
          (1 : ℝ) / p := hB _ hbaseB
  have hcount : (1 / 4096 : ℝ) ≤
      (m : ℝ) * (Real.log 2 / (24 * Real.log (N : ℝ))) := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hmpos : 0 < m := by omega
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hmLowerR : (L + 1 : ℕ) ≤ 100 * m := hmLower
    have hratio : Real.log (N : ℝ) ≤ 100 * (m : ℝ) * Real.log 2 := by
      calc
        Real.log (N : ℝ) ≤ (L + 1 : ℕ) * Real.log 2 := hlogNupper
        _ ≤ (100 * m : ℕ) * Real.log 2 := by gcongr
        _ = 100 * (m : ℝ) * Real.log 2 := by push_cast; ring
    have : Real.log (N : ℝ) ≤ 4096 / 24 * (m : ℝ) * Real.log 2 := by
      calc
        Real.log (N : ℝ) ≤ 100 * (m : ℝ) * Real.log 2 := hratio
        _ ≤ 4096 / 24 * (m : ℝ) * Real.log 2 := by gcongr <;> norm_num
    calc
      (1 / 4096 : ℝ) ≤
          ((m : ℝ) * Real.log 2) / (24 * Real.log (N : ℝ)) := by
        apply (le_div_iff₀ (mul_pos (by norm_num) hlogNpos)).2
        nlinarith
      _ = (m : ℝ) * (Real.log 2 / (24 * Real.log (N : ℝ))) := by ring
  rw [sum_lowerAnalyticPrimeCore]
  calc
    (1 / 4096 : ℝ) ≤
        (m : ℝ) * (Real.log 2 / (24 * Real.log (N : ℝ))) := hcount
    _ = ∑ _j ∈ Finset.range m,
        Real.log 2 / (24 * Real.log (N : ℝ)) := by simp
    _ ≤ ∑ j ∈ Finset.range m,
        ∑ p ∈ Erdos896.primeBlock (lowerAnalyticBlockBase N j),
          (1 : ℝ) / p := Finset.sum_le_sum hblock

theorem eventually_candidatePrimePool_harmonic_lower :
    ∀ᶠ N : ℕ in atTop,
      (1 / 4096 : ℝ) ≤
        ∑ p ∈ candidatePrimePool N, (1 : ℝ) / p := by
  filter_upwards [eventually_lowerAnalyticPrimeCore_harmonic_lower,
    eventually_ge_atTop 1] with N hcore hN
  exact hcore.trans (Finset.sum_le_sum_of_subset_of_nonneg
    (lowerAnalyticPrimeCore_subset_candidatePrimePool hN)
    (fun p _ _ ↦ by positivity))

/-! ## The exact quotient window -/

/-- The dyadic prime interval based at `y = N/(2p)` lies in the literal
cross-multiplied window.  The strict lower endpoint follows from the
defining remainder inequality for natural division. -/
theorem quotientDyadicPrimeInterval_subset_scaledWindowPrimes
    {N p y a d : ℕ} (hp : 0 < p) (hy : y = N / (2 * p))
    (ha : a ^ 2 ≤ y) (hd : IsolatedDivisor a d dyadicSigma) :
    h1PrimeInterval (y / d + 1) (2 * (y / d)) ⊆
      scaledWindowPrimes N p a d := by
  intro q hqmem
  rw [mem_h1PrimeInterval] at hqmem
  rcases hqmem with ⟨hqlower, hqupper, hq⟩
  have ha0 := isolatedDivisor_ne_zero hd
  have hapos : 0 < a := Nat.pos_of_ne_zero ha0
  have hdvd := isolatedDivisor_dvd hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hapos
  have hda : d ≤ a := Nat.le_of_dvd hapos hdvd
  have had : a * d ≤ y := by
    calc
      a * d ≤ a * a := Nat.mul_le_mul_left a hda
      _ = a ^ 2 := by ring
      _ ≤ y := ha
  have hau : a ≤ y / d := (Nat.le_div_iff_mul_le hdpos).2 had
  have hyqd : y < q * d := by
    apply (Nat.div_lt_iff_lt_mul hdpos).1
    omega
  have hqdy : q * d ≤ 2 * y := by
    calc
      q * d ≤ (2 * (y / d)) * d := Nat.mul_le_mul_right d hqupper
      _ = 2 * ((y / d) * d) := by ring
      _ ≤ 2 * y := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self y d)
  have h2p : 0 < 2 * p := by positivity
  have hquotUpper : (2 * p) * y ≤ N := by
    rw [hy]
    exact Nat.mul_div_le N (2 * p)
  have hquotStrict : N < (2 * p) * (y + 1) := by
    have h := Nat.lt_div_mul_add (a := N) h2p
    simpa [hy, mul_add, mul_comm, mul_left_comm, mul_assoc] using h
  have hqtop : q ≤ N / p := by
    apply (Nat.le_div_iff_mul_le hp).2
    have hqle : q ≤ q * d := by
      simpa using Nat.le_mul_of_pos_right q hdpos
    calc
      q * p = p * q := by ring
      _ ≤ p * (q * d) := Nat.mul_le_mul_left p hqle
      _ ≤ p * (2 * y) := Nat.mul_le_mul_left p hqdy
      _ = (2 * p) * y := by ring
      _ ≤ N := hquotUpper
  rw [mem_scaledWindowPrimes]
  refine ⟨by omega, hqtop, hq, ?_⟩
  constructor
  · exact hquotStrict.trans_le (by
      have hmul := Nat.mul_le_mul_left (2 * p) (Nat.add_one_le_iff.mpr hyqd)
      simpa [mul_assoc] using hmul)
  · calc
      p * (q * d) ≤ p * (2 * y) := Nat.mul_le_mul_left p hqdy
      _ = (2 * p) * y := by ring
      _ ≤ N := hquotUpper

/-- The second-prime base lies above the exact scaled window once `p` is
larger than the small part by the harmless factor eight. -/
theorem quotient_secondPrime_base_ge
    {N p a q : ℕ} (hp : 0 < p) (ha : 0 < a) (hq : 0 < q)
    (hqtop : q ≤ N / p) (hap : 8 * a ≤ p) :
    N / p ≤ X N p / (4 * (a * q)) := by
  have haq : 0 < a * q := Nat.mul_pos ha hq
  have hden : 0 < 4 * (a * q) := by positivity
  apply (Nat.le_div_iff_mul_le hden).2
  unfold X
  have h2p : 0 < 2 * p := by positivity
  apply (Nat.le_div_iff_mul_le h2p).2
  have hpq : p * q ≤ N := by
    simpa [mul_comm] using (Nat.le_div_iff_mul_le hp).1 hqtop
  have hpt : p * (N / p) ≤ N := Nat.mul_div_le N p
  have hat : 8 * a * (N / p) ≤ N := by
    calc
      8 * a * (N / p) ≤ p * (N / p) :=
        Nat.mul_le_mul_right (N / p) hap
      _ ≤ N := hpt
  calc
    (N / p) * (4 * (a * q)) * (2 * p) =
        (p * q) * (8 * a * (N / p)) := by ring
    _ ≤ N * N := Nat.mul_le_mul hpq hat

/-- On the quotient application band, the exact cutoff `X N p` has a
logarithm bounded by nine times the divisor-window logarithm. -/
theorem log_X_le_nine_log_of_quotient_band
    {N p y : ℕ} (hp : 0 < p) (hy : y = N / (2 * p))
    (hy2 : 2 ≤ y) (hNlow : 8 * y ^ 3 ≤ N)
    (hNhigh : N ^ 7 ≤ (2 * y) ^ 24) :
    Real.log (X N p) ≤ 9 * Real.log y := by
  have hNpos : 0 < N := (by positivity : 0 < 8 * y ^ 3).trans_le hNlow
  have hypos : 0 < y := by omega
  have h2p : 0 < 2 * p := by positivity
  have hquotStrict : N < (2 * p) * (y + 1) := by
    have h := Nat.lt_div_mul_add (a := N) h2p
    simpa [hy, mul_add, mul_comm, mul_left_comm, mul_assoc] using h
  have hXlt : X N p < N * (y + 1) := by
    unfold X
    apply (Nat.div_lt_iff_lt_mul h2p).2
    have hmul := (Nat.mul_lt_mul_left hNpos).2 hquotStrict
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hmul
  have hXle : X N p ≤ 2 * (N * y) := by
    have : y + 1 ≤ 2 * y := by omega
    exact hXlt.le.trans (by
      have hmul := Nat.mul_le_mul_left N this
      simpa [mul_assoc, mul_comm, mul_left_comm] using hmul)
  have hNypos : 0 < N * y := Nat.mul_pos hNpos hypos
  have hlogmono : Real.log (X N p) ≤ Real.log (2 * (N * y) : ℕ) := by
    by_cases hX0 : X N p = 0
    · simp only [Nat.cast_mul, Nat.cast_ofNat]
      have hone : 1 ≤ 2 * (N * y) :=
        Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero hNpos.ne' hypos.ne'))
      exact Real.log_nonneg (by exact_mod_cast hone)
    · exact Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by exact_mod_cast (Nat.pos_of_ne_zero hX0)))
        (Set.mem_Ioi.mpr (by
          exact_mod_cast (Nat.mul_pos (by omega : 0 < 2) hNypos) :
            (0 : ℝ) < ((2 * (N * y) : ℕ) : ℝ)))
        (by exact_mod_cast hXle)
  have hlogNy := log_mul_le_eight_log_of_dyadic_band hy2 hNlow hNhigh
  have hlog2le : Real.log 2 ≤ Real.log y := by
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (by exact_mod_cast hypos)) (by exact_mod_cast hy2)
  calc
    Real.log (X N p) ≤ Real.log (2 * (N * y) : ℕ) := hlogmono
    _ = Real.log 2 + Real.log (N * y) := by
      push_cast
      rw [Real.log_mul (by norm_num) (by exact_mod_cast hNypos.ne')]
    _ ≤ 9 * Real.log y := by linarith

/-- Ford's `r=1` lower bound directly in the quotient-scaled window used
by `G N p`.  Unlike the fixed-dyadic statement, this theorem has no
endpoint comparison: its conclusion is literally `scaledH1 N p (X N p)`.
-/
theorem exists_quotientBand_weightedIsolatedSum_le_scaledH1 :
    ∃ c : ℝ, 0 < c ∧ ∃ Y₀ : ℕ, ∀ (N p y : ℕ) (A : Finset ℕ),
      0 < p → y = N / (2 * p) → Y₀ ≤ y →
      8 * y ^ 3 ≤ N → N ^ 7 ≤ (2 * y) ^ 24 →
      (∀ a ∈ A, a ^ 2 ≤ y) → (∀ a ∈ A, 8 * a ≤ p) →
      c * (X N p : ℕ) / Real.log y ^ 2 *
          weightedIsolatedSum A dyadicSigma ≤
        (scaledH1 N p (X N p) : ℝ) := by
  obtain ⟨Uq₀, hqmass⟩ :=
    eventually_one_sixteenth_div_log_le_primeReciprocalIntervalSum
  obtain ⟨Ub₀, hbcard⟩ :=
    eventually_one_eighth_mul_div_log_le_primeIntervalCard
  let T := max 4 (max Uq₀ Ub₀)
  refine ⟨1 / 9216, by norm_num, max 2 (T ^ 2), ?_⟩
  intro N p y A hp hy hY hNlow hNhigh haSq haP
  have hy2 : 2 ≤ y := (le_max_left 2 (T ^ 2)).trans hY
  have hTsq : T ^ 2 ≤ y := (le_max_right 2 (T ^ 2)).trans hY
  have hypos : 0 < y := by omega
  have hNpos : 0 < N := (by positivity : 0 < 8 * y ^ 3).trans_le hNlow
  have hXpos : 0 < X N p := by
    have h2py : (2 * p) * y ≤ N := by
      rw [hy]
      exact Nat.mul_div_le N (2 * p)
    have hNyX : N * y ≤ X N p := by
      unfold X
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * p)).2
      calc
        N * y * (2 * p) = N * ((2 * p) * y) := by ring
        _ ≤ N * N := Nat.mul_le_mul_left N h2py
    exact (Nat.mul_pos hNpos hypos).trans_le hNyX
  have hlogy : 0 < Real.log y :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogX : 0 < Real.log (X N p) := by
    apply Real.log_pos
    have hNy : 1 < N * y := by
      have : y ≤ N * y := Nat.le_mul_of_pos_left y hNpos
      omega
    have h2py : (2 * p) * y ≤ N := by
      rw [hy]
      exact Nat.mul_div_le N (2 * p)
    have hNyX : N * y ≤ X N p := by
      unfold X
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * p)).2
      calc
        N * y * (2 * p) = N * ((2 * p) * y) := by ring
        _ ≤ N * N := Nat.mul_le_mul_left N h2py
    exact_mod_cast hNy.trans_le hNyX
  have hlogCompare := log_X_le_nine_log_of_quotient_band hp hy hy2 hNlow hNhigh
  let C : ℝ := (X N p : ℕ) / (9216 * Real.log y ^ 2)
  have haSmall : ∀ a ∈ A, 2 * p * a ≤ N := by
    intro a ha
    have ha2 := haSq a ha
    have hay : a ≤ y := by nlinarith [sq_nonneg (a : ℝ)]
    have hquot : (2 * p) * y ≤ N := by
      rw [hy]
      exact Nat.mul_div_le N (2 * p)
    nlinarith
  have hprime : ∀ a ∈ A, ∀ d ∈ isolatedDivisors a dyadicSigma,
      C / (a : ℝ) ≤
        ((∑ q ∈ scaledWindowPrimes N p a d,
          (h1SecondPrimeInterval N p (X N p) a q).card : ℕ) : ℝ) := by
    intro a ha d hdmem
    have hd := mem_isolatedDivisors.mp hdmem
    have ha0 := isolatedDivisor_ne_zero hd
    have hapos : 0 < a := Nat.pos_of_ne_zero ha0
    have hdvd := isolatedDivisor_dvd hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hapos
    have hda : d ≤ a := Nat.le_of_dvd hapos hdvd
    have ha2 := haSq a ha
    have hd2 : d ^ 2 ≤ y := (Nat.pow_le_pow_left hda 2).trans ha2
    have hTd : T * d ≤ y := by nlinarith [sq_nonneg ((T : ℝ) - d)]
    have hTU : T ≤ y / d := (Nat.le_div_iff_mul_le hdpos).2 hTd
    have hUq₀ : Uq₀ ≤ y / d :=
      (le_max_left Uq₀ Ub₀).trans ((le_max_right 4 (max Uq₀ Ub₀)).trans hTU)
    have hUpos : 0 < y / d := Nat.div_pos (hda.trans (by
      have hay : a ≤ y := by nlinarith [sq_nonneg (a : ℝ)]
      exact hay)) hdpos
    have hlogU : 0 < Real.log ((y / d : ℕ) : ℝ) := by
      have hU4 : 4 ≤ y / d := (le_max_left 4 (max Uq₀ Ub₀)).trans hTU
      exact Real.log_pos (by exact_mod_cast (show 1 < y / d by omega))
    let Q := h1PrimeInterval (y / d + 1) (2 * (y / d))
    have hQsub : Q ⊆ scaledWindowPrimes N p a d :=
      quotientDyadicPrimeInterval_subset_scaledWindowPrimes hp hy ha2 hd
    have hmassQ : (1 / 16 : ℝ) / Real.log y ≤
        ∑ q ∈ Q, (1 : ℝ) / q := by
      have hrec := hqmass (y / d) hUq₀
      have hUle : y / d ≤ y := Nat.div_le_self y d
      have hlogUle : Real.log ((y / d : ℕ) : ℝ) ≤ Real.log y := by
        exact Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr (by exact_mod_cast hUpos))
          (Set.mem_Ioi.mpr (by exact_mod_cast hypos)) (by exact_mod_cast hUle)
      calc
        (1 / 16 : ℝ) / Real.log y ≤
            (1 / 16 : ℝ) / Real.log ((y / d : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_left (by norm_num) hlogU hlogUle
        _ ≤ primeReciprocalIntervalSum (y / d) (2 * (y / d)) := hrec
        _ = ∑ q ∈ Q, (1 : ℝ) / q := by
          unfold primeReciprocalIntervalSum
          rw [primesLE_sdiff_eq_h1PrimeInterval]
    have hqTerm : ∀ q ∈ Q,
        (X N p : ℕ) /
            (64 * (a : ℝ) * q * Real.log (X N p)) ≤
          ((h1SecondPrimeInterval N p (X N p) a q).card : ℝ) := by
      intro q hqQ
      have hqdata := mem_h1PrimeInterval.mp hqQ
      have hqprime := hqdata.2.2
      have haqpos : 0 < a * q := Nat.mul_pos hapos hqprime.pos
      have hqsubmem := hQsub hqQ
      have hqtop := (mem_scaledWindowPrimes.mp hqsubmem).2.1
      let V := X N p / (4 * (a * q))
      have hbase : N / p ≤ V := by
        simpa [V] using quotient_secondPrime_base_ge hp hapos hqprime.pos hqtop (haP a ha)
      have h2yNp : 2 * y ≤ N / p := by
        apply (Nat.le_div_iff_mul_le hp).2
        have hquot : (2 * p) * y ≤ N := by
          rw [hy]
          exact Nat.mul_div_le N (2 * p)
        nlinarith
      have hTy : T ≤ y := by nlinarith
      have hUb₀ : Ub₀ ≤ V :=
        (le_max_right Uq₀ Ub₀).trans
          ((le_max_right 4 (max Uq₀ Ub₀)).trans
            (hTy.trans ((Nat.le_mul_of_pos_left y (by omega : 0 < 2)).trans
              (h2yNp.trans hbase))))
      have hVpos : 0 < V := by omega
      have hlogV : 0 < Real.log V :=
        Real.log_pos (by exact_mod_cast (show 1 < V by omega))
      have hVleX : V ≤ X N p := Nat.div_le_self (X N p) (4 * (a * q))
      have hlogVle : Real.log V ≤ Real.log (X N p) := by
        exact Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr (by exact_mod_cast hVpos))
          (Set.mem_Ioi.mpr (by exact_mod_cast hXpos)) (by exact_mod_cast hVleX)
      have h8aq : 8 * (a * q) ≤ X N p := by
        have h4aq : 0 < 4 * (a * q) := by positivity
        have hV2 : 2 ≤ V := (by omega : 2 ≤ 2 * y).trans (h2yNp.trans hbase)
        have hmul := (Nat.le_div_iff_mul_le h4aq).1 hV2
        simpa [V, mul_assoc, mul_comm, mul_left_comm] using hmul
      have hVfloor : (((X N p : ℕ) : ℝ) /
          (8 * (a : ℝ) * (q : ℝ))) ≤ (V : ℝ) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
          (cast_div_eight_le_cast_div_four haqpos h8aq)
      have hbstd := hbcard V hUb₀
      rw [primesLE_sdiff_eq_h1PrimeInterval] at hbstd
      have hbsub := doublePrimeInterval_subset_secondPrimeInterval
        (N := N) (p := p) (X := X N p) haqpos (by simpa [V] using hbase)
      calc
        (X N p : ℕ) / (64 * (a : ℝ) * q * Real.log (X N p)) =
            (1 / 8 : ℝ) * ((X N p : ℕ) / (8 * (a * q))) /
              Real.log (X N p) := by ring
        _ ≤ (1 / 8 : ℝ) * V / Real.log (X N p) := by
          apply div_le_div_of_nonneg_right _ hlogX.le
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          simpa only [mul_assoc] using hVfloor
        _ ≤ (1 / 8 : ℝ) * V / Real.log V := by
          exact div_le_div_of_nonneg_left (by positivity) hlogV hlogVle
        _ ≤ ((h1PrimeInterval (V + 1) (2 * V)).card : ℝ) := hbstd
        _ ≤ ((h1SecondPrimeInterval N p (X N p) a q).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hbsub
    have hsumQ :
        (X N p : ℕ) /
            (64 * (a : ℝ) * Real.log (X N p)) *
              ((1 / 16 : ℝ) / Real.log y) ≤
          ∑ q ∈ Q,
            ((h1SecondPrimeInterval N p (X N p) a q).card : ℝ) := by
      calc
        (X N p : ℕ) / (64 * (a : ℝ) * Real.log (X N p)) *
              ((1 / 16 : ℝ) / Real.log y) ≤
            (X N p : ℕ) / (64 * (a : ℝ) * Real.log (X N p)) *
              (∑ q ∈ Q, (1 : ℝ) / q) := by gcongr
        _ = ∑ q ∈ Q,
            (X N p : ℕ) /
              (64 * (a : ℝ) * q * Real.log (X N p)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring
        _ ≤ ∑ q ∈ Q,
            ((h1SecondPrimeInterval N p (X N p) a q).card : ℝ) := by
          exact Finset.sum_le_sum fun q hq ↦ hqTerm q hq
    calc
      C / (a : ℝ) ≤
          (X N p : ℕ) /
            (64 * (a : ℝ) * Real.log (X N p)) *
              ((1 / 16 : ℝ) / Real.log y) := by
        dsimp [C]
        have hdena : (0 : ℝ) < a := by exact_mod_cast hapos
        field_simp
        nlinarith
      _ ≤ ∑ q ∈ Q,
          ((h1SecondPrimeInterval N p (X N p) a q).card : ℝ) := hsumQ
      _ ≤ ∑ q ∈ scaledWindowPrimes N p a d,
          ((h1SecondPrimeInterval N p (X N p) a q).card : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hQsub
        intro q hq hnot
        positivity
      _ = ((∑ q ∈ scaledWindowPrimes N p a d,
          (h1SecondPrimeInterval N p (X N p) a q).card : ℕ) : ℝ) := by
        push_cast
        rfl
  have h := mul_weightedIsolatedSum_le_scaledH1_of_primeFibers
    (N := N) (p := p) (X := X N p) A hp C haSmall hprime
  dsimp [C] at h
  convert h using 1
  ring

/-! ## Uniform arithmetic on the prime core -/

theorem candidatePrime_quotient_band_low {N p : ℕ}
    (hN : 0 < N) (hp : p ∈ candidatePrimePool N) :
    8 * (N / (2 * p)) ^ 3 ≤ N := by
  have hpdata := mem_candidatePrimePool.mp hp
  have hppos := hpdata.2.2.1.pos
  let y := N / (2 * p)
  by_cases hy0 : y = 0
  · change 8 * y ^ 3 ≤ N
    simp [hy0]
  have hypos : 0 < y := Nat.pos_of_ne_zero hy0
  have h2py : (2 * p) * y ≤ N := by
    dsimp [y]
    exact Nat.mul_div_le N (2 * p)
  have hcubes : ((2 * p) * y) ^ 3 ≤ N ^ 3 :=
    Nat.pow_le_pow_left h2py 3
  have hstrict : (8 * y ^ 3) * N ^ 2 < N * N ^ 2 := by
    calc
      (8 * y ^ 3) * N ^ 2 < (8 * y ^ 3) * p ^ 3 :=
        Nat.mul_lt_mul_of_pos_left hpdata.2.2.2.1 (by positivity)
      _ = ((2 * p) * y) ^ 3 := by ring
      _ ≤ N ^ 3 := hcubes
      _ = N * N ^ 2 := by ring
  have hN2 : 0 < N ^ 2 := by positivity
  have hcancel : 8 * y ^ 3 < N := (Nat.mul_lt_mul_right hN2).mp (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hstrict)
  exact hcancel.le

theorem lowerAnalyticPrime_quotient_band_high {N p : ℕ}
    (hN : 0 < N) (hp : p ∈ lowerAnalyticPrimeCore N)
    (hy : 1 ≤ N / (2 * p)) :
    N ^ 7 ≤ (2 * (N / (2 * p))) ^ 24 := by
  let y := N / (2 * p)
  have hpdata := mem_lowerAnalyticPrimeCore_data hN hp
  have hppos := (mem_candidatePrimePool.mp hpdata.1).2.2.1.pos
  have h2p : 0 < 2 * p := by positivity
  have hquotStrict : N < (2 * p) * (y + 1) := by
    have h := Nat.lt_div_mul_add (a := N) h2p
    simpa [y, mul_add, mul_comm, mul_left_comm, mul_assoc] using h
  have hy2 : y + 1 ≤ 2 * y := by omega
  have hNle : N ≤ (2 * p) * (2 * y) :=
    hquotStrict.le.trans (Nat.mul_le_mul_left (2 * p) hy2)
  have hpow := Nat.pow_le_pow_left hNle 24
  have hmain : N ^ 24 ≤ N ^ 17 * (2 * y) ^ 24 := by
    calc
      N ^ 24 ≤ ((2 * p) * (2 * y)) ^ 24 := hpow
      _ = (2 ^ 24 * p ^ 24) * (2 * y) ^ 24 := by ring
      _ ≤ N ^ 17 * (2 * y) ^ 24 :=
        Nat.mul_le_mul_right ((2 * y) ^ 24) hpdata.2
  have hN17 : 0 < N ^ 17 := by positivity
  exact Nat.le_of_mul_le_mul_left (by
    calc
      N ^ 17 * N ^ 7 = N ^ 24 := by rw [← pow_add]
      _ ≤ N ^ 17 * (2 * y) ^ 24 := hmain) hN17

theorem candidatePrime_smallPart_separated {N p y a : ℕ}
    (hy2 : 2 ≤ y) (hy : y = N / (2 * p))
    (hp : p ∈ candidatePrimePool N) (ha : a ^ 2 ≤ y) :
    8 * a ≤ p := by
  have hpdata := mem_candidatePrimePool.mp hp
  have hppos := hpdata.2.2.1.pos
  have h2py : (2 * p) * y ≤ N := by
    rw [hy]
    exact Nat.mul_div_le N (2 * p)
  have hsquare : ((2 * p) * y) ^ 2 ≤ N ^ 2 :=
    Nat.pow_le_pow_left h2py 2
  have hstrict : (p ^ 2) * (4 * y ^ 2) < (p ^ 2) * p := by
    calc
      p ^ 2 * (4 * y ^ 2) = ((2 * p) * y) ^ 2 := by ring
      _ ≤ N ^ 2 := hsquare
      _ < p ^ 3 := hpdata.2.2.2.1
      _ = p ^ 2 * p := by ring
  have hp2 : 0 < p ^ 2 := by positivity
  have hpy : 4 * y ^ 2 < p := (Nat.mul_lt_mul_left hp2).mp hstrict
  have hay : a ≤ y := by nlinarith [sq_nonneg (a : ℝ)]
  calc
    8 * a ≤ 4 * y ^ 2 := by nlinarith
    _ ≤ p := hpy.le

/-- The quotient `N/(2p)` tends uniformly to infinity over the logarithmic
prime core. -/
theorem eventually_lowerAnalyticPrimeCore_quotient_ge (Y₀ : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ p ∈ lowerAnalyticPrimeCore N, Y₀ ≤ N / (2 * p) := by
  let K := max 22 (Nat.log 2 (max (2 * Y₀) 1) + 1)
  filter_upwards [eventually_ge_atTop (2 ^ (24 * K))] with N hN
  have hNpos : 0 < N := (Nat.pow_pos (by omega : 0 < 2)).trans_le hN
  have hN0 : N ≠ 0 := hNpos.ne'
  let L := Nat.log 2 N
  let k := lowerAnalyticIndex N
  have hlogLower : 24 * K ≤ L := by
    dsimp [L]
    exact Nat.le_log_of_pow_le (by omega : 1 < 2) hN
  have hk : k = L / 24 := by simp [k, L, lowerAnalyticIndex]
  have hkLower : K ≤ k := by
    rw [hk]
    exact (Nat.le_div_iff_mul_le (by omega : 0 < 24)).2
      (by simpa [mul_comm] using hlogLower)
  have hpowL : 2 ^ L ≤ N := by
    simpa [L] using Nat.pow_log_le_self 2 hN0
  intro p hp
  rw [lowerAnalyticPrimeCore, Finset.mem_biUnion] at hp
  obtain ⟨j, hj, hpblock⟩ := hp
  have hjlt : j < lowerAnalyticBlockCount N := Finset.mem_range.mp hj
  have hb := Erdos896.mem_primeBlock.mp hpblock
  have hppos : 0 < p := hb.2.2.pos
  let e := 16 * k + 17 + 2 * j
  have hj' : j < (k - 20) / 2 := by
    simpa [lowerAnalyticBlockCount, k] using hjlt
  have htwom : 2 * ((k - 20) / 2) ≤ k - 20 := by
    simpa [mul_comm] using Nat.div_mul_le_self (k - 20) 2
  have he : e + 3 ≤ 17 * k := by
    dsimp [e]
    omega
  have hpupper : p ≤ 2 ^ (17 * k) := by
    calc
      p ≤ 4 * lowerAnalyticBlockBase N j := hb.2.1
      _ = 2 ^ (16 * k + 17 + 2 * j + 2) := by
        unfold lowerAnalyticBlockBase
        change 4 * 2 ^ (16 * k + 17 + 2 * j) = _
        rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ (17 * k) := Nat.pow_le_pow_right (by omega) (by omega)
  have hYpow : 2 * Y₀ ≤ 2 ^ (7 * k) := by
    have hKpow : max (2 * Y₀) 1 < 2 ^ K := by
      exact (Nat.lt_pow_succ_log_self (by omega : 1 < 2) _).trans_le
        (Nat.pow_le_pow_right (by omega) (le_max_right 22 _))
    exact (le_max_left (2 * Y₀) 1).trans
      (hKpow.le.trans (Nat.pow_le_pow_right (by omega) (by omega)))
  have hdenY : (2 * p) * Y₀ ≤ N := by
    calc
      (2 * p) * Y₀ = p * (2 * Y₀) := by ring
      _ ≤ 2 ^ (17 * k) * 2 ^ (7 * k) := Nat.mul_le_mul hpupper hYpow
      _ = 2 ^ (24 * k) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by
        rw [hk, mul_comm]
        exact Nat.div_mul_le_self L 24)
      _ ≤ N := hpowL
  exact (Nat.le_div_iff_mul_le (by nlinarith : 0 < 2 * p)).2
    (by simpa [mul_comm] using hdenY)

/-! ## Stirling and global mass aggregation -/

/-- The exact algebraic identity converting Ford's factorial target into
the slowly varying denominator. -/
theorem inv_log_sq_mul_stirlingTarget {y : ℕ} (hy : 3 ≤ y) :
    (1 / Real.log y ^ 2) * stirlingTarget (y : ℝ) =
      1 / Erdos896.logDenom896 y := by
  have hyR : (3 : ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < y := by positivity
  have hlogy : 1 < Real.log (y : ℝ) := by
    apply (Real.lt_log_iff_exp_lt hy0).2
    exact Real.exp_one_lt_three.trans_le hyR
  have hlogy0 : 0 < Real.log (y : ℝ) := zero_lt_one.trans hlogy
  rw [stirlingTarget, Erdos896.logDenom896, Erdos896.logDenom896R,
    Real.rpow_sub hlogy0]
  field_simp
  rw [Real.rpow_two]

/-- The precise isolated-family input consumed by the global aggregation.
It is separated as a predicate so the finite analytic summation can be
checked independently of the capped-profile construction. -/
def WeightedIsolatedFamilyLower (C : ℝ) : Prop :=
  ∃ Y₀ : ℕ, ∀ y : ℕ, Y₀ ≤ y → ∃ A : Finset ℕ,
    (∀ a ∈ A, a ^ 2 ≤ y) ∧
      C * stirlingTerm (y : ℝ) ≤ weightedIsolatedSum A dyadicSigma

/-- A quotient is at least the real half of its unfloored value once its
natural quotient is positive. -/
private theorem half_real_div_le_nat_div {u v : ℕ} (hv : 0 < v)
    (hquot : 1 ≤ u / v) :
    (u : ℝ) / (2 * v) ≤ (u / v : ℕ) := by
  have hlt := Nat.lt_div_mul_add (a := u) hv
  have huv : u ≤ 2 * (u / v) * v := by
    have hm : u < (u / v + 1) * v := by
      simpa [add_mul] using hlt
    have hs : u / v + 1 ≤ 2 * (u / v) := by omega
    exact hm.le.trans (by
      have := Nat.mul_le_mul_right v hs
      simpa [mul_comm, mul_left_comm, mul_assoc] using this)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * v)).2
  exact_mod_cast (by simpa [mul_comm, mul_left_comm, mul_assoc] using huv)

/-- The exact cutoff is at least `N²/(4p)` throughout the nonempty
quotient range. -/
theorem half_unfloored_X_le_X {N p : ℕ} (hp : 0 < p)
    (hy : 1 ≤ N / (2 * p)) :
    (N : ℝ) ^ 2 / (4 * p) ≤ (X N p : ℕ) := by
  unfold X
  have hhalf := half_real_div_le_nat_div
    (u := N * N) (v := 2 * p) (by positivity) (by
      have hN : 2 * p ≤ N := by
        simpa using (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * p)).1 hy
      have hNpos : 0 < N := (by positivity : 0 < 2 * p).trans_le hN
      have hNN : N ≤ N * N := Nat.le_mul_of_pos_right N hNpos
      exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt
        (Nat.div_pos (hN.trans hNN) (by positivity))))
  convert hhalf using 1 <;> push_cast <;> ring

/-- The generic global aggregation.  Its only input is the frozen
per-`y` isolated-family theorem; all prime-band, endpoint, and scale
comparisons are discharged here. -/
theorem exists_scaledH1MassLower_of_weightedIsolatedFamilyLower
    {Cfamily : ℝ} (hCfamily : 0 < Cfamily)
    (hfamily : WeightedIsolatedFamilyLower Cfamily) :
    ∃ c : ℝ, 0 < c ∧ ScaledH1MassLower c := by
  obtain ⟨cH, hcH, YH, hH⟩ :=
    exists_quotientBand_weightedIsolatedSum_le_scaledH1
  obtain ⟨Ys, hYs⟩ := hfamily
  obtain ⟨cS, hcS, hSreal⟩ :=
    eventually_const_mul_target_le_stirlingTerm
  have hSnat : ∀ᶠ y : ℕ in atTop,
      cS * stirlingTarget (y : ℝ) ≤ stirlingTerm (y : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hSreal
  obtain ⟨YS, hYS⟩ := eventually_atTop.mp hSnat
  let Y₀ := max 3 (max YH (max Ys YS))
  have hquotEventually := eventually_lowerAnalyticPrimeCore_quotient_ge Y₀
  let c : ℝ := cH * Cfamily * cS / (4 * 4096)
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  filter_upwards [hquotEventually,
    eventually_lowerAnalyticPrimeCore_harmonic_lower,
    eventually_ge_atTop 3] with N hquot hcore hN
  have hN1 : 1 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hper : ∀ p ∈ lowerAnalyticPrimeCore N,
      (cH * Cfamily * cS / 4) *
          ((N : ℝ) ^ 2 / Erdos896.logDenom896 N) * (1 / (p : ℝ)) ≤
        ((G N p).card : ℝ) := by
    intro p hpCore
    have hpPool := lowerAnalyticPrimeCore_subset_candidatePrimePool hN1 hpCore
    have hpPrime := (mem_candidatePrimePool.mp hpPool).2.2.1
    have hppos := hpPrime.pos
    let y := N / (2 * p)
    have hyY : Y₀ ≤ y := hquot p hpCore
    have hy3 : 3 ≤ y := (le_max_left 3 (max YH (max Ys YS))).trans hyY
    have hyH : YH ≤ y :=
      (le_max_left YH (max Ys YS)).trans
        ((le_max_right 3 (max YH (max Ys YS))).trans hyY)
    have hyFam : Ys ≤ y :=
      (le_max_left Ys YS).trans ((le_max_right YH (max Ys YS)).trans
        ((le_max_right 3 (max YH (max Ys YS))).trans hyY))
    have hyS : YS ≤ y :=
      (le_max_right Ys YS).trans ((le_max_right YH (max Ys YS)).trans
        ((le_max_right 3 (max YH (max Ys YS))).trans hyY))
    obtain ⟨A, haSq, hAfam⟩ := hYs y hyFam
    have hlow : 8 * y ^ 3 ≤ N := by
      simpa [y] using candidatePrime_quotient_band_low hNpos hpPool
    have hhigh : N ^ 7 ≤ (2 * y) ^ 24 := by
      simpa [y] using lowerAnalyticPrime_quotient_band_high hNpos hpCore
        ((by omega : 1 ≤ Y₀).trans hyY)
    have haSep : ∀ a ∈ A, 8 * a ≤ p := by
      intro a ha
      exact candidatePrime_smallPart_separated (by omega : 2 ≤ y) rfl
        hpPool (haSq a ha)
    have hcount := hH N p y A hppos rfl hyH hlow hhigh haSq haSep
    have hstir := hYS y hyS
    have htargetW : Cfamily * cS * stirlingTarget (y : ℝ) ≤
        weightedIsolatedSum A dyadicSigma := by
      calc
        Cfamily * cS * stirlingTarget (y : ℝ) =
            Cfamily * (cS * stirlingTarget (y : ℝ)) := by ring
        _ ≤ Cfamily * stirlingTerm (y : ℝ) :=
          mul_le_mul_of_nonneg_left hstir hCfamily.le
        _ ≤ weightedIsolatedSum A dyadicSigma := hAfam
    have hlogy : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have hdenY : 0 < Erdos896.logDenom896 y :=
      Erdos896.logDenom896_pos hy3
    have hdenN : 0 < Erdos896.logDenom896 N :=
      Erdos896.logDenom896_pos (hy3.trans (by
        have hyN : y ≤ N := (Nat.div_le_self N (2 * p))
        exact hyN))
    have hyN : y ≤ N := Nat.div_le_self N (2 * p)
    have hdenMono : Erdos896.logDenom896 y ≤ Erdos896.logDenom896 N :=
      Erdos896.logDenom896_mono hy3 hyN
    have hXlower := half_unfloored_X_le_X hppos
      ((by omega : 1 ≤ Y₀).trans hyY)
    have hratio : (N : ℝ) ^ 2 / (4 * p) /
          Erdos896.logDenom896 N ≤
        (X N p : ℕ) / Erdos896.logDenom896 y := by
      calc
        (N : ℝ) ^ 2 / (4 * p) / Erdos896.logDenom896 N ≤
            (N : ℝ) ^ 2 / (4 * p) / Erdos896.logDenom896 y := by
          exact div_le_div_of_nonneg_left (by positivity) hdenY hdenMono
        _ ≤ (X N p : ℕ) / Erdos896.logDenom896 y :=
          div_le_div_of_nonneg_right hXlower hdenY.le
    have hmain : cH * Cfamily * cS *
          ((X N p : ℕ) / Erdos896.logDenom896 y) ≤
        ((G N p).card : ℝ) := by
      calc
        cH * Cfamily * cS * ((X N p : ℕ) / Erdos896.logDenom896 y) =
            cH * Cfamily * cS * (X N p : ℕ) *
              ((1 / Real.log y ^ 2) * stirlingTarget (y : ℝ)) := by
          rw [inv_log_sq_mul_stirlingTarget hy3]
          ring
        _ = cH * (X N p : ℕ) / Real.log y ^ 2 *
              (Cfamily * cS * stirlingTarget (y : ℝ)) := by ring
        _ ≤ cH * (X N p : ℕ) / Real.log y ^ 2 *
              weightedIsolatedSum A dyadicSigma := by
          exact mul_le_mul_of_nonneg_left htargetW (by positivity)
        _ ≤ (scaledH1 N p (X N p) : ℝ) := hcount
        _ = ((G N p).card : ℝ) := by rfl
    calc
      (cH * Cfamily * cS / 4) *
            ((N : ℝ) ^ 2 / Erdos896.logDenom896 N) * (1 / (p : ℝ)) =
          (cH * Cfamily * cS) *
            ((N : ℝ) ^ 2 / (4 * p) / Erdos896.logDenom896 N) := by ring
      _ ≤ (cH * Cfamily * cS) *
            ((X N p : ℕ) / Erdos896.logDenom896 y) := by
        exact mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ ((G N p).card : ℝ) := hmain
  have hsumCore :
      (cH * Cfamily * cS / 4) *
          ((N : ℝ) ^ 2 / Erdos896.logDenom896 N) *
            (∑ p ∈ lowerAnalyticPrimeCore N, (1 : ℝ) / p) ≤
        ∑ p ∈ lowerAnalyticPrimeCore N, ((G N p).card : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hper
  have hsubset := lowerAnalyticPrimeCore_subset_candidatePrimePool hN1
  have hsumPool :
      ∑ p ∈ lowerAnalyticPrimeCore N, ((G N p).card : ℝ) ≤
        (scaledH1Mass N : ℝ) := by
    unfold scaledH1Mass
    have hnat :
        ∑ p ∈ lowerAnalyticPrimeCore N, (G N p).card ≤
          ∑ p ∈ candidatePrimePool N, (G N p).card :=
      Finset.sum_le_sum_of_subset hsubset
    exact_mod_cast hnat
  have hcoeff : 0 ≤ (cH * Cfamily * cS / 4) *
      ((N : ℝ) ^ 2 / Erdos896.logDenom896 N) := by
    exact mul_nonneg (by positivity)
      (div_nonneg (sq_nonneg (N : ℝ)) (Erdos896.logDenom896_pos hN).le)
  calc
    c * Erdos896.scale896 N =
        (cH * Cfamily * cS / 4) *
          ((N : ℝ) ^ 2 / Erdos896.logDenom896 N) * (1 / 4096) := by
      simp only [c, Erdos896.scale896]
      ring
    _ ≤ (cH * Cfamily * cS / 4) *
          ((N : ℝ) ^ 2 / Erdos896.logDenom896 N) *
            (∑ p ∈ lowerAnalyticPrimeCore N, (1 : ℝ) / p) := by
      exact mul_le_mul_of_nonneg_left hcore hcoeff
    _ ≤ ∑ p ∈ lowerAnalyticPrimeCore N, ((G N p).card : ℝ) := hsumCore
    _ ≤ (scaledH1Mass N : ℝ) := hsumPool

/-! ## The discarded owner multiples -/

private theorem candidatePrime_cast_le_rpow {N p : ℕ}
    (hp : p ∈ candidatePrimePool N) :
    (p : ℝ) ≤ (N : ℝ) ^ (17 / 24 : ℝ) := by
  have hpdata := mem_candidatePrimePool.mp hp
  have hR : (p : ℝ) ^ 24 ≤ (N : ℝ) ^ 17 := by
    exact_mod_cast hpdata.2.2.2.2
  have hr := Real.rpow_le_rpow
    (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 24) hR
    (by norm_num : (0 : ℝ) ≤ 1 / 24)
  rw [← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p)] at hr
  rw [← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)] at hr
  norm_num at hr ⊢
  simpa [show (17 : ℝ) * (1 / 24) = 17 / 24 by ring] using hr

private theorem X_div_owner_le_owner {N p : ℕ}
    (hp : p ∈ candidatePrimePool N) : X N p / p ≤ p := by
  have hpdata := mem_candidatePrimePool.mp hp
  have hppos := hpdata.2.2.1.pos
  have hXlt : X N p < p * p := by
    unfold X
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 * p)).2
    calc
      N * N = N ^ 2 := by ring
      _ < p ^ 3 := hpdata.2.2.2.1
      _ ≤ (p * p) * (2 * p) := by ring_nf; nlinarith
  exact ((Nat.div_lt_iff_lt_mul hppos).2 hXlt).le

/-- A global real-power upper bound for the owner-multiple loss. -/
theorem multipleLoss_le_rpow (N : ℕ) :
    (multipleLoss N : ℝ) ≤
      (N : ℝ) * (N : ℝ) ^ (17 / 24 : ℝ) := by
  have hcard : (candidatePrimePool N).card ≤ N := by
    calc
      (candidatePrimePool N).card ≤ (Finset.Icc 1 N).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ N := by simp
  unfold multipleLoss
  push_cast
  calc
    ∑ p ∈ candidatePrimePool N, ((X N p / p : ℕ) : ℝ) ≤
        ∑ p ∈ candidatePrimePool N, (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact_mod_cast X_div_owner_le_owner hp
    _ ≤ ∑ _p ∈ candidatePrimePool N,
        (N : ℝ) ^ (17 / 24 : ℝ) := by
      exact Finset.sum_le_sum fun p hp ↦ candidatePrime_cast_le_rpow hp
    _ = ((candidatePrimePool N).card : ℝ) *
        (N : ℝ) ^ (17 / 24 : ℝ) := by simp
    _ ≤ (N : ℝ) * (N : ℝ) ^ (17 / 24 : ℝ) := by
      gcongr

private theorem lowerAnalytic_logDenom_le_log_rpow {N : ℕ} (hN : 3 ≤ N) :
    Erdos896.logDenom896 N ≤ (Real.log (N : ℝ)) ^ (5 / 2 : ℝ) := by
  have hNreal : Real.exp 1 < (N : ℝ) :=
    Real.exp_one_lt_three.trans_le (by exact_mod_cast hN)
  have hNpos : (0 : ℝ) < N := (Real.exp_pos 1).trans hNreal
  have hlog_one : 1 < Real.log (N : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hNpos]
    simpa using hNreal
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_one
  have hloglog_le : Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hlog_pos]
  have hfirst :
      (Real.log (N : ℝ)) ^ Erdos896.delta896 ≤ Real.log (N : ℝ) := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hlog_one.le Erdos896.delta896_le_one)
  have hsecond :
      (Real.log (Real.log (N : ℝ))) ^ (3 / 2 : ℝ) ≤
        (Real.log (N : ℝ)) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hloglog_pos.le hloglog_le (by norm_num)
  unfold Erdos896.logDenom896 Erdos896.logDenom896R
  calc
    (Real.log (N : ℝ)) ^ Erdos896.delta896 *
          (Real.log (Real.log (N : ℝ))) ^ (3 / 2 : ℝ) ≤
        Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (3 / 2 : ℝ) := by
      exact mul_le_mul hfirst hsecond
        (Real.rpow_nonneg hloglog_pos.le _) hlog_pos.le
    _ = (Real.log (N : ℝ)) ^ (5 / 2 : ℝ) := by
      calc
        Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (3 / 2 : ℝ) =
            (Real.log (N : ℝ)) ^ (1 : ℝ) *
              (Real.log (N : ℝ)) ^ (3 / 2 : ℝ) := by rw [Real.rpow_one]
        _ = (Real.log (N : ℝ)) ^ ((1 : ℝ) + 3 / 2) := by
          rw [Real.rpow_add hlog_pos]
        _ = (Real.log (N : ℝ)) ^ (5 / 2 : ℝ) := by norm_num

private theorem lowerAnalytic_eventually_logDenom_le_eighth_rpow :
    ∀ᶠ N : ℕ in atTop,
      Erdos896.logDenom896 N ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (5 / 2 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 8)).bound one_pos
  have hsmallNat :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmallReal
  filter_upwards [hsmallNat, eventually_ge_atTop 3] with N hsmall hN
  have hlogpow_nonneg :
      0 ≤ (Real.log (N : ℝ)) ^ (5 / 2 : ℝ) := by positivity
  have hNpow_nonneg : 0 ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by positivity
  have hpow : (Real.log (N : ℝ)) ^ (5 / 2 : ℝ) ≤
      (N : ℝ) ^ (1 / 8 : ℝ) := by
    simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg hlogpow_nonneg,
      abs_of_nonneg hNpow_nonneg] using hsmall
  exact (lowerAnalytic_logDenom_le_log_rpow hN).trans hpow

/-- The owner-multiple loss is negligible compared with the Ford scale,
with any prescribed positive constant. -/
theorem multipleLossSmall_of_pos {c : ℝ} (hc : 0 < c) :
    MultipleLossSmall c := by
  have hgrowth : ∀ᶠ N : ℕ in atTop,
      2 / c ≤ (N : ℝ) ^ (1 / 6 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (2 / c)
  filter_upwards [lowerAnalytic_eventually_logDenom_le_eighth_rpow,
    hgrowth, eventually_ge_atTop 3] with N hden hgrowthN hN
  have hNR : (0 : ℝ) < N := by positivity
  have hdenpos := Erdos896.logDenom896_pos hN
  have hloss := multipleLoss_le_rpow N
  have hpow17 : 0 ≤ (N : ℝ) ^ (17 / 24 : ℝ) := by positivity
  have hpow18 : 0 ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by positivity
  have hprod : (multipleLoss N : ℝ) * Erdos896.logDenom896 N ≤
      (N : ℝ) ^ (11 / 6 : ℝ) := by
    calc
      (multipleLoss N : ℝ) * Erdos896.logDenom896 N ≤
          ((N : ℝ) * (N : ℝ) ^ (17 / 24 : ℝ)) *
            ((N : ℝ) ^ (1 / 8 : ℝ)) :=
        mul_le_mul hloss hden hdenpos.le
          (mul_nonneg (Nat.cast_nonneg N) hpow17)
      _ = (N : ℝ) ^ (11 / 6 : ℝ) := by
        calc
          ((N : ℝ) * (N : ℝ) ^ (17 / 24 : ℝ)) *
                (N : ℝ) ^ (1 / 8 : ℝ) =
              ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (17 / 24 : ℝ)) *
                (N : ℝ) ^ (1 / 8 : ℝ) := by rw [Real.rpow_one]
          _ = (N : ℝ) ^ (((1 : ℝ) + 17 / 24) + 1 / 8) := by
            rw [← Real.rpow_add hNR, ← Real.rpow_add hNR]
          _ = (N : ℝ) ^ (11 / 6 : ℝ) := by norm_num
  have hfactor : 1 ≤ (c / 2) * (N : ℝ) ^ (1 / 6 : ℝ) := by
    have hc2 : 0 < c / 2 := by positivity
    calc
      1 = (c / 2) * (2 / c) := by field_simp
      _ ≤ (c / 2) * (N : ℝ) ^ (1 / 6 : ℝ) :=
        mul_le_mul_of_nonneg_left hgrowthN hc2.le
  have hpowMain : (N : ℝ) ^ (11 / 6 : ℝ) ≤
      (c / 2) * (N : ℝ) ^ (2 : ℕ) := by
    calc
      (N : ℝ) ^ (11 / 6 : ℝ) =
          (N : ℝ) ^ (11 / 6 : ℝ) * 1 := by ring
      _ ≤ (N : ℝ) ^ (11 / 6 : ℝ) *
          ((c / 2) * (N : ℝ) ^ (1 / 6 : ℝ)) := by gcongr
      _ = (c / 2) *
          ((N : ℝ) ^ (11 / 6 : ℝ) * (N : ℝ) ^ (1 / 6 : ℝ)) := by ring
      _ = (c / 2) * (N : ℝ) ^ (2 : ℝ) := by
        rw [← Real.rpow_add hNR]
        norm_num
      _ = (c / 2) * (N : ℝ) ^ (2 : ℕ) := by rw [Real.rpow_two]
  have hquot : (multipleLoss N : ℝ) ≤
      ((c / 2) * (N : ℝ) ^ 2) / Erdos896.logDenom896 N :=
    (le_div_iff₀ hdenpos).2 (hprod.trans hpowMain)
  simpa [Erdos896.scale896] using (show
    (multipleLoss N : ℝ) ≤ (c / 2) * Erdos896.scale896 N by
      calc
        (multipleLoss N : ℝ) ≤
            ((c / 2) * (N : ℝ) ^ 2) / Erdos896.logDenom896 N := hquot
        _ = (c / 2) * Erdos896.scale896 N := by
          simp [Erdos896.scale896]
          ring)

/-- Combined conditional package consumed by the finite lower bridge. -/
theorem exists_massLower_and_multipleLossSmall_of_weightedIsolatedFamilyLower
    {Cfamily : ℝ} (hCfamily : 0 < Cfamily)
    (hfamily : WeightedIsolatedFamilyLower Cfamily) :
    ∃ c : ℝ, 0 < c ∧ ScaledH1MassLower c ∧ MultipleLossSmall c := by
  obtain ⟨c, hc, hmass⟩ :=
    exists_scaledH1MassLower_of_weightedIsolatedFamilyLower hCfamily hfamily
  exact ⟨c, hc, hmass, multipleLossSmall_of_pos hc⟩

/-- Assumption-free analytic lower package for the finite lower bridge. -/
theorem exists_massLower_and_multipleLossSmall :
    ∃ c : ℝ, 0 < c ∧ ScaledH1MassLower c ∧ MultipleLossSmall c := by
  obtain ⟨C, hC, Y₀, hfamily⟩ :=
    exists_eventually_weightedIsolatedSum_lower
  exact exists_massLower_and_multipleLossSmall_of_weightedIsolatedFamilyLower
    hC ⟨Y₀, hfamily⟩

/-- In particular, the raw exact-one-divisor mass dominates the Ford
scale with an absolute positive constant. -/
theorem exists_scaledH1MassLower :
    ∃ c : ℝ, 0 < c ∧ ScaledH1MassLower c := by
  obtain ⟨c, hc, hmass, _⟩ := exists_massLower_and_multipleLossSmall
  exact ⟨c, hc, hmass⟩

end Ford

end Erdos896
