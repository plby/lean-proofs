/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RefinedLogarithmicSieve

/-!
# Sieve weights with a genuine level of distribution

Brun's truncation by the number of prime factors is supported only on
`d < z ^ L`.  This is unsuitable when the roughness cutoff `z` is a fixed
power of the ambient parameter and the depth `L` grows.  Combinatorial
beta-sieve weights instead have a prescribed *level*: their nonzero
coefficients satisfy `d ≤ G`.

This file isolates the exact finite interface needed to exploit such a
level restriction.  It also records what the `lambdaSquared` construction
from Mathlib's Selberg-sieve file does provide: weights supported on
`d ≤ H` produce an upper-Moebius weight supported on `d ≤ H ^ 2`.
-/

open scoped BigOperators
open Finset Nat

namespace BoundingSieve

variable {s : BoundingSieve}

/-- A sieve coefficient is level-supported on the divisors which occur in
the given sieve problem. -/
def IsLevelSupportedOnProdPrimes (G : ℕ) (mu : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, d ∣ s.prodPrimes → G < d → mu d = 0

/-- Level support restricts the abstract remainder sum to divisors at most
the level. -/
theorem errSum_eq_levelSum_of_isLevelSupportedOnProdPrimes
    {G : ℕ} {mu : ℕ → ℝ}
    (hmu : s.IsLevelSupportedOnProdPrimes G mu) :
    s.errSum mu =
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d ↦ d ≤ G),
        |mu d| * |s.rem d| := by
  rw [errSum]
  calc
    (∑ d ∈ s.prodPrimes.divisors, |mu d| * |s.rem d|) =
        ∑ d ∈ s.prodPrimes.divisors,
          if d ≤ G then |mu d| * |s.rem d| else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdG : d ≤ G
      · simp [hdG]
      · have hdDiv : d ∣ s.prodPrimes := (Nat.mem_divisors.mp hd).1
        have hzero := hmu d hdDiv (Nat.lt_of_not_ge hdG)
        simp [hdG, hzero]
    _ = ∑ d ∈ s.prodPrimes.divisors.filter (fun d ↦ d ≤ G),
          |mu d| * |s.rem d| := by
      rw [← Finset.sum_filter]

/-- If the coefficients have absolute value at most one, a level-supported
remainder is bounded by a plain sum over `d ≤ G`.  This is the finite
bridge used with beta-sieve weights. -/
theorem errSum_le_sum_range_of_isLevelSupportedOnProdPrimes
    {G : ℕ} {mu : ℕ → ℝ} {R : ℕ → ℝ}
    (hmu : s.IsLevelSupportedOnProdPrimes G mu)
    (hmuone : ∀ d : ℕ, d ∣ s.prodPrimes → |mu d| ≤ 1)
    (hrem : ∀ d : ℕ, d ∣ s.prodPrimes → |s.rem d| ≤ R d)
    (hR : ∀ d : ℕ, 0 ≤ R d) :
    s.errSum mu ≤ ∑ d ∈ Finset.range (G + 1), R d := by
  rw [errSum_eq_levelSum_of_isLevelSupportedOnProdPrimes hmu]
  calc
    (∑ d ∈ s.prodPrimes.divisors.filter (fun d ↦ d ≤ G),
        |mu d| * |s.rem d|) ≤
        ∑ d ∈ s.prodPrimes.divisors.filter (fun d ↦ d ≤ G), R d := by
      apply Finset.sum_le_sum
      intro d hd
      have hdDiv : d ∣ s.prodPrimes :=
        (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
      calc
        |mu d| * |s.rem d| ≤ 1 * R d :=
          mul_le_mul (hmuone d hdDiv) (hrem d hdDiv)
            (abs_nonneg _) zero_le_one
        _ = R d := one_mul _
    _ ≤ ∑ d ∈ Finset.range (G + 1), R d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        have hdG := (Finset.mem_filter.mp hd).2
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hdG)
      · intro d _ _
        exact hR d

/-- Globally level-supported base weights give level-supported Selberg
`lambdaSquared` coefficients, with the level squared. -/
theorem lambdaSquared_isLevelSupportedOnProdPrimes
    {H : ℕ} {w : ℕ → ℝ}
    (hw : ∀ d : ℕ, H < d → w d = 0) :
    s.IsLevelSupportedOnProdPrimes (H ^ 2) (lambdaSquared w) := by
  intro d _ hd
  unfold lambdaSquared
  apply Finset.sum_eq_zero
  intro d₁ hd₁
  apply Finset.sum_eq_zero
  intro d₂ hd₂
  by_cases heq : d = Nat.lcm d₁ d₂
  · rw [if_pos heq]
    by_cases h₁ : d₁ ≤ H
    · by_cases h₂ : d₂ ≤ H
      · have hd₁pos : 0 < d₁ := Nat.pos_of_dvd_of_pos
            (Nat.dvd_of_mem_divisors hd₁) (by omega)
        have hd₂pos : 0 < d₂ := Nat.pos_of_dvd_of_pos
            (Nat.dvd_of_mem_divisors hd₂) (by omega)
        have hlcm : Nat.lcm d₁ d₂ ≤ d₁ * d₂ :=
          Nat.le_of_dvd (Nat.mul_pos hd₁pos hd₂pos) (Nat.lcm_dvd_mul d₁ d₂)
        have : d ≤ H ^ 2 := by
          rw [heq]
          exact hlcm.trans (by simpa [pow_two] using Nat.mul_le_mul h₁ h₂)
        omega
      · rw [hw d₂ (Nat.lt_of_not_ge h₂), mul_zero]
    · rw [hw d₁ (Nat.lt_of_not_ge h₁), zero_mul]
  · rw [if_neg heq]

/-- The exact upper Selberg inequality with its error term visibly
restricted to the squared support of the base weights. -/
theorem siftedSum_le_lambdaSquared_main_add_levelError
    {H : ℕ} {w : ℕ → ℝ}
    (hwOne : w 1 = 1)
    (hw : ∀ d : ℕ, H < d → w d = 0) :
    s.siftedSum ≤
      s.totalMass * s.mainSum (lambdaSquared w) +
        ∑ d ∈ s.prodPrimes.divisors.filter (fun d ↦ d ≤ H ^ 2),
          |lambdaSquared w d| * |s.rem d| := by
  have hsieve := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (lambdaSquared w) (upperMoebius_lambdaSquared w hwOne)
  rw [errSum_eq_levelSum_of_isLevelSupportedOnProdPrimes
    (lambdaSquared_isLevelSupportedOnProdPrimes (s := s) hw)] at hsieve
  exact hsieve

end BoundingSieve

namespace Erdos387

open scoped ArithmeticFunction.Omega

/-- The squarefree divisor expansion underlying the standard endpoint
estimate for level-supported sieve weights. -/
theorem sum_divisors_pow_primeFactorsCard_div_eq_prod_one_add
    {P k : ℕ} (hP : Squarefree P) :
    (∑ d ∈ P.divisors,
        (k : ℝ) ^ d.primeFactors.card / d) =
      ∏ p ∈ P.primeFactors, (1 + (k : ℝ) / p) := by
  rw [divisors_eq_image_prod_primeFactorSubsets hP,
    Finset.sum_image (prod_primeFactorSubsets_injOn P),
    Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro T hT
  obtain ⟨_, hcard⟩ := prod_primeFactorSubset_squarefree_card hT
  have hpfcard : (∏ p ∈ T, p).primeFactors.card = T.card := by
    simpa [cardDistinctFactors_eq_primeFactors_card] using hcard
  rw [hpfcard]
  push_cast
  rw [Finset.prod_div_distrib]
  simp

/-- The weighted endpoint loss for a level `G` is `G` times the full
squarefree harmonic Euler product.  This is the support estimate used in
the fixed-power version of the argument. -/
theorem refinedBinomialBoundingSieve_errSum_le_level_mul_euler
    {B K X z G : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hX : S.k ≤ X / 2) {mu : ℕ → ℝ}
    (hmusupp :
      (refinedBinomialBoundingSieve S X z).IsLevelSupportedOnProdPrimes G mu)
    (hmuone : ∀ d : ℕ,
      d ∣ CoverBPZ.refinedSievePrimeProduct S z → |mu d| ≤ 1) :
    (refinedBinomialBoundingSieve S X z).errSum mu ≤
      4 * G *
        ∏ p ∈ (CoverBPZ.refinedSievePrimeProduct S z).primeFactors,
          (1 + (S.k : ℝ) / p) := by
  let s := refinedBinomialBoundingSieve S X z
  let P := CoverBPZ.refinedSievePrimeProduct S z
  have hlevel :=
    BoundingSieve.errSum_eq_levelSum_of_isLevelSupportedOnProdPrimes hmusupp
  change s.errSum mu = _ at hlevel
  rw [hlevel]
  change (∑ d ∈ P.divisors.filter (fun d ↦ d ≤ G),
      |mu d| * |s.rem d|) ≤ _
  have hterm :
      (∑ d ∈ P.divisors.filter (fun d ↦ d ≤ G),
          |mu d| * |s.rem d|) ≤
        4 * ∑ d ∈ P.divisors.filter (fun d ↦ d ≤ G),
          (S.k : ℝ) ^ d.primeFactors.card := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hdDiv : d ∣ P :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    calc
      |mu d| * |s.rem d| ≤
          1 * (4 * (S.k : ℝ) ^ d.primeFactors.card) :=
        mul_le_mul (hmuone d hdDiv)
          (by simpa [s, P] using
            refinedBinomialBoundingSieve_abs_rem_le S hX hdDiv)
          (abs_nonneg _) zero_le_one
      _ = 4 * (S.k : ℝ) ^ d.primeFactors.card := by ring
  have hcore :
    (∑ d ∈ P.divisors.filter (fun d ↦ d ≤ G),
        (S.k : ℝ) ^ d.primeFactors.card) ≤
      (G : ℝ) *
        ∏ p ∈ P.primeFactors, (1 + (S.k : ℝ) / p) := by
    calc
      (∑ d ∈ P.divisors.filter (fun d ↦ d ≤ G),
          (S.k : ℝ) ^ d.primeFactors.card) ≤
          (G : ℝ) *
            ∑ d ∈ P.divisors.filter (fun d ↦ d ≤ G),
              (S.k : ℝ) ^ d.primeFactors.card / d := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro d hd
        have hdMem := (Finset.mem_filter.mp hd).1
        have hdG := (Finset.mem_filter.mp hd).2
        have hdDiv : d ∣ P := (Nat.mem_divisors.mp hdMem).1
        have hPpos : 0 < P := CoverBPZ.refinedSievePrimeProduct_pos S z
        have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hdDiv hPpos
        have hdGreal : (d : ℝ) ≤ G := by exact_mod_cast hdG
        have hpowNonneg : 0 ≤ (S.k : ℝ) ^ d.primeFactors.card := by positivity
        rw [show (G : ℝ) *
            ((S.k : ℝ) ^ d.primeFactors.card / d) =
            ((G : ℝ) * (S.k : ℝ) ^ d.primeFactors.card) / d by ring]
        rw [le_div_iff₀ (by exact_mod_cast hdPos)]
        calc
          (S.k : ℝ) ^ d.primeFactors.card * d ≤
              (S.k : ℝ) ^ d.primeFactors.card * G :=
            mul_le_mul_of_nonneg_left hdGreal hpowNonneg
          _ = G * (S.k : ℝ) ^ d.primeFactors.card := by ring
      _ ≤ (G : ℝ) *
          ∑ d ∈ P.divisors,
            (S.k : ℝ) ^ d.primeFactors.card / d := by
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro d hd _
            positivity
        · positivity
      _ = (G : ℝ) *
        ∏ p ∈ P.primeFactors, (1 + (S.k : ℝ) / p) := by
        rw [sum_divisors_pow_primeFactorsCard_div_eq_prod_one_add
          (CoverBPZ.refinedSievePrimeProduct_squarefree S z)]
  exact hterm.trans (by
    calc
      4 * ∑ d ∈ P.divisors.filter (fun d ↦ d ≤ G),
          (S.k : ℝ) ^ d.primeFactors.card ≤
          4 * ((G : ℝ) *
            ∏ p ∈ P.primeFactors, (1 + (S.k : ℝ) / p)) :=
        mul_le_mul_of_nonneg_left hcore (by norm_num)
      _ = 4 * G *
          ∏ p ∈ (CoverBPZ.refinedSievePrimeProduct S z).primeFactors,
            (1 + (S.k : ℝ) / p) := by
        simp [P]
        ring)

/-- Combining the level estimate with the already formalized prime
reciprocal bound expresses the endpoint loss as `G` times a
polylogarithmic envelope times the natural sieve density. -/
theorem refinedBinomialBoundingSieve_errSum_le_level_mul_densityEnvelope
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    {B K X z G : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hX : S.k ≤ X / 2) {mu : ℕ → ℝ}
    (hmusupp :
      (refinedBinomialBoundingSieve S X z).IsLevelSupportedOnProdPrimes G mu)
    (hmuone : ∀ d : ℕ,
      d ∣ CoverBPZ.refinedSievePrimeProduct S z → |mu d| ≤ 1) :
    (refinedBinomialBoundingSieve S X z).errSum mu ≤
      4 * G *
        (((4 * S.k : ℝ) ^ (2 * S.k + 1) *
          Real.exp ((6 * S.k : ℝ) * (2 * C / Real.log 2) *
            (Nat.log 2 (Nat.log 2 z) + 2))) *
          finiteEulerProduct
            (CoverBPZ.refinedSievePrimeProduct S z).primeFactors
            (fun p ↦ binomialSieveNu S.k p)) := by
  let P := (CoverBPZ.refinedSievePrimeProduct S z).primeFactors
  have hP : ∀ p ∈ P, p.Prime ∧ S.k < p ∧ p < z := by
    intro p hp
    exact CoverBPZ.refinedSievePrimeFactor_bounds S hp
  have hprod :
      (∏ p ∈ P, (1 + (S.k : ℝ) / p)) ≤
        ∏ p ∈ P, (1 + 2 * binomialSieveNu S.k p) := by
    apply Finset.prod_le_prod
    · intro p hp
      positivity
    · intro p hp
      rw [binomialSieveNu_prime (hP p hp).1]
      have hnonneg : 0 ≤ (S.k : ℝ) / p := by positivity
      linarith
  have hmoment :=
    PrimeReciprocal.binomialMomentProduct_le_exp_log_log_two_mul_euler
      hC hcheb (by have := S.hk3; omega) P hP
  have hbase := refinedBinomialBoundingSieve_errSum_le_level_mul_euler
    S hX hmusupp hmuone
  calc
    (refinedBinomialBoundingSieve S X z).errSum mu ≤
        4 * G * ∏ p ∈ P, (1 + (S.k : ℝ) / p) := by
      simpa [P] using hbase
    _ ≤ 4 * G * ∏ p ∈ P,
        (1 + 2 * binomialSieveNu S.k p) := by
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ 4 * G *
        (((4 * S.k : ℝ) ^ (2 * S.k + 1) *
          Real.exp ((6 * S.k : ℝ) * (2 * C / Real.log 2) *
            (Nat.log 2 (Nat.log 2 z) + 2))) *
          finiteEulerProduct P (fun p ↦ binomialSieveNu S.k p)) := by
      exact mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = _ := by rfl

/-- Ready-to-use lower-sieve interface at a prescribed level.  A
beta-sieve fundamental lemma supplies the last missing data here: the
lower-Moebius property, level support, coefficient bound, and the stated
Euler-product main-term window. -/
theorem refinedSiftedCandidates_card_lowerBound_of_levelWeights
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    {B K X z G : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hX : S.k ≤ X / 2) {mu : ℕ → ℝ}
    (hmulower :
      (refinedBinomialBoundingSieve S X z).IsLowerMoebiusOnProdPrimes mu)
    (hmusupp :
      (refinedBinomialBoundingSieve S X z).IsLevelSupportedOnProdPrimes G mu)
    (hmuone : ∀ d : ℕ,
      d ∣ CoverBPZ.refinedSievePrimeProduct S z → |mu d| ≤ 1)
    (hmain :
      finiteEulerProduct
          (CoverBPZ.refinedSievePrimeProduct S z).primeFactors
          (fun p ↦ binomialSieveNu S.k p) / 2 ≤
        (refinedBinomialBoundingSieve S X z).mainSum mu) :
    ((RefinedBaseCandidates S X).card : ℝ) *
          (finiteEulerProduct
            (CoverBPZ.refinedSievePrimeProduct S z).primeFactors
            (fun p ↦ binomialSieveNu S.k p) / 2) -
        4 * G *
          (((4 * S.k : ℝ) ^ (2 * S.k + 1) *
            Real.exp ((6 * S.k : ℝ) * (2 * C / Real.log 2) *
              (Nat.log 2 (Nat.log 2 z) + 2))) *
            finiteEulerProduct
              (CoverBPZ.refinedSievePrimeProduct S z).primeFactors
              (fun p ↦ binomialSieveNu S.k p)) ≤
      ((RefinedSiftedCandidates S X z).card : ℝ) := by
  let s := refinedBinomialBoundingSieve S X z
  let V := finiteEulerProduct
    (CoverBPZ.refinedSievePrimeProduct S z).primeFactors
    (fun p ↦ binomialSieveNu S.k p)
  let H := (4 * S.k : ℝ) ^ (2 * S.k + 1) *
    Real.exp ((6 * S.k : ℝ) * (2 * C / Real.log 2) *
      (Nat.log 2 (Nat.log 2 z) + 2))
  have herr :=
    refinedBinomialBoundingSieve_errSum_le_level_mul_densityEnvelope
      hC hcheb S hX hmusupp hmuone
  change s.errSum mu ≤ 4 * G * (H * V) at herr
  have hsieve := s.totalMass_mainSum_sub_errSum_le_siftedSum mu hmulower
  rw [refinedBinomialBoundingSieve_siftedSum S] at hsieve
  have hmass : 0 ≤ s.totalMass := by
    dsimp [s, refinedBinomialBoundingSieve]
    positivity
  have hmainmul : s.totalMass * (V / 2) ≤ s.totalMass * s.mainSum mu := by
    apply mul_le_mul_of_nonneg_left
    · simpa [V] using hmain
    · exact hmass
  change ((RefinedBaseCandidates S X).card : ℝ) * (V / 2) -
      4 * G * (H * V) ≤ _
  calc
    ((RefinedBaseCandidates S X).card : ℝ) * (V / 2) -
          4 * G * (H * V) =
        s.totalMass * (V / 2) - 4 * G * (H * V) := by rfl
    _ ≤ s.totalMass * s.mainSum mu - s.errSum mu :=
      sub_le_sub hmainmul herr
    _ ≤ ((RefinedSiftedCandidates S X z).card : ℝ) := hsieve

/-- Matching upper-sieve interface at a prescribed level. -/
theorem refinedSiftedCandidates_card_upperBound_of_levelWeights
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    {B K X z G : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hX : S.k ≤ X / 2) {mu : ℕ → ℝ}
    (hmuupper :
      (refinedBinomialBoundingSieve S X z).IsUpperMoebiusOnProdPrimes mu)
    (hmusupp :
      (refinedBinomialBoundingSieve S X z).IsLevelSupportedOnProdPrimes G mu)
    (hmuone : ∀ d : ℕ,
      d ∣ CoverBPZ.refinedSievePrimeProduct S z → |mu d| ≤ 1)
    (hmain :
      (refinedBinomialBoundingSieve S X z).mainSum mu ≤
        3 * finiteEulerProduct
          (CoverBPZ.refinedSievePrimeProduct S z).primeFactors
          (fun p ↦ binomialSieveNu S.k p) / 2) :
    ((RefinedSiftedCandidates S X z).card : ℝ) ≤
      ((RefinedBaseCandidates S X).card : ℝ) *
          (3 * finiteEulerProduct
            (CoverBPZ.refinedSievePrimeProduct S z).primeFactors
            (fun p ↦ binomialSieveNu S.k p) / 2) +
        4 * G *
          (((4 * S.k : ℝ) ^ (2 * S.k + 1) *
            Real.exp ((6 * S.k : ℝ) * (2 * C / Real.log 2) *
              (Nat.log 2 (Nat.log 2 z) + 2))) *
            finiteEulerProduct
              (CoverBPZ.refinedSievePrimeProduct S z).primeFactors
              (fun p ↦ binomialSieveNu S.k p)) := by
  let s := refinedBinomialBoundingSieve S X z
  let V := finiteEulerProduct
    (CoverBPZ.refinedSievePrimeProduct S z).primeFactors
    (fun p ↦ binomialSieveNu S.k p)
  let H := (4 * S.k : ℝ) ^ (2 * S.k + 1) *
    Real.exp ((6 * S.k : ℝ) * (2 * C / Real.log 2) *
      (Nat.log 2 (Nat.log 2 z) + 2))
  have herr :=
    refinedBinomialBoundingSieve_errSum_le_level_mul_densityEnvelope
      hC hcheb S hX hmusupp hmuone
  change s.errSum mu ≤ 4 * G * (H * V) at herr
  have hsieve := s.siftedSum_le_totalMass_mainSum_add_errSum mu hmuupper
  rw [refinedBinomialBoundingSieve_siftedSum S] at hsieve
  have hmass : 0 ≤ s.totalMass := by
    dsimp [s, refinedBinomialBoundingSieve]
    positivity
  have hmainmul : s.totalMass * s.mainSum mu ≤
      s.totalMass * (3 * V / 2) := by
    apply mul_le_mul_of_nonneg_left
    · simpa [V] using hmain
    · exact hmass
  change _ ≤ ((RefinedBaseCandidates S X).card : ℝ) * (3 * V / 2) +
      4 * G * (H * V)
  calc
    ((RefinedSiftedCandidates S X z).card : ℝ) ≤
        s.totalMass * s.mainSum mu + s.errSum mu := hsieve
    _ ≤ s.totalMass * (3 * V / 2) + 4 * G * (H * V) :=
      add_le_add hmainmul herr
    _ = ((RefinedBaseCandidates S X).card : ℝ) * (3 * V / 2) +
        4 * G * (H * V) := by rfl

/-- On the refined binomial progression, level-supported coefficients of
absolute value at most one incur only the CRT endpoint errors with
`d ≤ G`; no factor `z ^ L` is introduced. -/
theorem refinedBinomialBoundingSieve_errSum_le_levelOmegaSum
    {B K X z G : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hX : S.k ≤ X / 2) {mu : ℕ → ℝ}
    (hmusupp :
      (refinedBinomialBoundingSieve S X z).IsLevelSupportedOnProdPrimes G mu)
    (hmuone : ∀ d : ℕ,
      d ∣ CoverBPZ.refinedSievePrimeProduct S z → |mu d| ≤ 1) :
    (refinedBinomialBoundingSieve S X z).errSum mu ≤
      4 * ∑ d ∈ Finset.range (G + 1),
        (S.k : ℝ) ^ d.primeFactors.card := by
  have h := BoundingSieve.errSum_le_sum_range_of_isLevelSupportedOnProdPrimes
    (s := refinedBinomialBoundingSieve S X z)
    hmusupp hmuone
    (fun d hd ↦ refinedBinomialBoundingSieve_abs_rem_le S hX hd)
    (fun d ↦ by positivity)
  simpa [Finset.mul_sum] using h

end Erdos387
