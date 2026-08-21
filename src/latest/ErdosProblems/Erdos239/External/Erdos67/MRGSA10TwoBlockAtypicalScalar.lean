import ErdosProblems.Erdos239.External.Erdos67.MRTDensity
import ErdosProblems.Erdos239.External.Erdos67.MRFiniteHalaszTypicalSetBridge

/-!
# A source-scale atypical-set bound for two prime blocks

This file specializes the finite beta-sieve density theorem to the two
blocks used in the A.10 centered decomposition.  It also fixes a canonical
pair corresponding to the half-open source intervals

`(3, 2^K]` and `(2^K, 2^(K^2)]`.

Since `primesInBlock` uses closed natural intervals, these are encoded as
`(4, 2^K)` and `(2^K + 1, 2^(K^2))`.
-/

open scoped BigOperators
open Finset

namespace Erdos67

noncomputable section

/-- First canonical A.10 prime block, representing `(3,2^K]`. -/
def gsA10CanonicalFirstBlock (K : ℕ) : ℕ × ℕ := (4, 2 ^ K)

/-- Second canonical A.10 prime block, representing
`(2^K,2^(K^2)]`. -/
def gsA10CanonicalSecondBlock (K : ℕ) : ℕ × ℕ :=
  (2 ^ K + 1, 2 ^ (K ^ 2))

/-- Diagonal block exponent.  Its square is at most one `4S`-th of the
binary logarithm, leaving exactly enough room to absorb the squared
beta-sieve remainder. -/
def gsA10CanonicalBlockExponent (S Z : ℕ) : ℕ :=
  Nat.sqrt (Nat.log 2 Z / (4 * S))

/-- The two canonical blocks are disjoint as sets of primes. -/
theorem disjoint_primesInBlock_gsA10Canonical
    {K : ℕ} (hK : 2 ≤ K) :
    Disjoint (primesInBlock (gsA10CanonicalFirstBlock K))
      (primesInBlock (gsA10CanonicalSecondBlock K)) := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  have hp₁' := (mem_primesInBlock.mp hp₁).2.2
  have hp₂' := (mem_primesInBlock.mp hp₂).2.1
  dsimp only [gsA10CanonicalFirstBlock, gsA10CanonicalSecondBlock,
    Prod.fst, Prod.snd] at hp₁' hp₂'
  omega

/-- Both canonical upper endpoints lie below the common source cutoff
`y=2^(K^2)`. -/
theorem gsA10CanonicalBlock_uppers_le
    {K : ℕ} (hK : 2 ≤ K) :
    (gsA10CanonicalFirstBlock K).2 ≤ 2 ^ (K ^ 2) ∧
      (gsA10CanonicalSecondBlock K).2 ≤ 2 ^ (K ^ 2) := by
  dsimp only [gsA10CanonicalFirstBlock, gsA10CanonicalSecondBlock,
    Prod.snd]
  constructor
  · exact Nat.pow_le_pow_right (by omega) (by nlinarith)
  · exact le_rfl

/-- Every prime at most three is outside the two canonical A.10 blocks.
This supplies `houtside` in the high-order scheduled annulus with the
viable choice `Ylow=3`. -/
theorem mrTwoBlockOutside_gsA10Canonical_of_le_three
    {K p : ℕ} (hK : 2 ≤ K) (hp : p.Prime) (hp3 : p ≤ 3) :
    mrTwoBlockOutside (gsA10CanonicalFirstBlock K)
      (gsA10CanonicalSecondBlock K) p := by
  constructor
  · intro hp₁
    have hp₁' := (mem_primesInBlock.mp hp₁).2.1
    dsimp only [gsA10CanonicalFirstBlock, Prod.fst] at hp₁'
    omega
  · intro hp₂
    have hp₂' := (mem_primesInBlock.mp hp₂).2.1
    dsimp only [gsA10CanonicalSecondBlock, Prod.fst] at hp₂'
    have hpow : 4 ≤ 2 ^ K := by
      have := Nat.pow_le_pow_right (by omega : 0 < 2) hK
      norm_num at this ⊢
      exact this
    omega

/-- Both canonical blocks satisfy the endpoint hypotheses required by the
finite beta sieve. -/
theorem gsA10CanonicalBlocks_valid
    {K : ℕ} (hK : 2 ≤ K) :
    ∀ I ∈ ({gsA10CanonicalFirstBlock K,
        gsA10CanonicalSecondBlock K} : Finset (ℕ × ℕ)),
      3 ≤ I.1 ∧ I.1 ≤ I.2 := by
  intro I hI
  simp only [Finset.mem_insert, Finset.mem_singleton] at hI
  rcases hI with rfl | rfl
  · dsimp only [gsA10CanonicalFirstBlock, Prod.fst, Prod.snd]
    constructor
    · norm_num
    · have : 2 ^ 2 ≤ 2 ^ K := Nat.pow_le_pow_right (by omega) hK
      norm_num at this ⊢
      exact this
  · dsimp only [gsA10CanonicalSecondBlock, Prod.fst, Prod.snd]
    have hpowFour : 4 ≤ 2 ^ K := by
      have := Nat.pow_le_pow_right (by omega : 0 < 2) hK
      norm_num at this ⊢
      exact this
    constructor
    · omega
    · have hKK : K ≤ K ^ 2 := by nlinarith
      have hpow : 2 ^ K < 2 ^ (K ^ 2) := by
        exact Nat.pow_lt_pow_right (by omega) (by nlinarith)
      omega

/-- A harmless absolute constant dominating both canonical logarithmic
block ratios. -/
def gsA10CanonicalLogRatioConstant : ℝ :=
  max (Real.log 3 / Real.log 2) 1

theorem one_le_gsA10CanonicalLogRatioConstant :
    1 ≤ gsA10CanonicalLogRatioConstant := by
  exact le_max_right _ _

/-- The first canonical logarithmic block ratio is `O(1/K)`. -/
theorem gsA10CanonicalFirstBlock_logRatio_le
    {K : ℕ} (hK : 2 ≤ K) :
    Real.log (((gsA10CanonicalFirstBlock K).1 - 1 : ℕ) : ℝ) /
        Real.log ((gsA10CanonicalFirstBlock K).2 : ℝ) ≤
      gsA10CanonicalLogRatioConstant / K := by
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hconst : Real.log 3 / Real.log 2 ≤
      gsA10CanonicalLogRatioConstant := le_max_left _ _
  dsimp only [gsA10CanonicalFirstBlock, Prod.fst, Prod.snd]
  norm_num only
  rw [Nat.cast_pow, Real.log_pow]
  calc
    Real.log 3 / ((K : ℝ) * Real.log 2) =
        (Real.log 3 / Real.log 2) / K := by field_simp
    _ ≤ gsA10CanonicalLogRatioConstant / K := by
      exact div_le_div_of_nonneg_right hconst (by positivity)

/-- The second canonical logarithmic block ratio is at most `1/K`. -/
theorem gsA10CanonicalSecondBlock_logRatio_le
    {K : ℕ} (hK : 2 ≤ K) :
    Real.log (((gsA10CanonicalSecondBlock K).1 - 1 : ℕ) : ℝ) /
        Real.log ((gsA10CanonicalSecondBlock K).2 : ℝ) ≤
      gsA10CanonicalLogRatioConstant / K := by
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hKK0 : ((K : ℝ) ^ 2) ≠ 0 := pow_ne_zero 2 hK0
  have hconst := one_le_gsA10CanonicalLogRatioConstant
  dsimp only [gsA10CanonicalSecondBlock, Prod.fst, Prod.snd]
  rw [Nat.add_sub_cancel, Nat.cast_pow, Nat.cast_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  calc
    ((K : ℝ) * Real.log 2) / ((K : ℝ) ^ 2 * Real.log 2) =
        1 / (K : ℝ) := by field_simp
    _ ≤ gsA10CanonicalLogRatioConstant / K := by
      exact div_le_div_of_nonneg_right hconst (by positivity)

/-- A fixed absolute beta-sieve constant and depth turn two logarithmic
block-ratio bounds and the explicit finite remainder into a lossless
two-block atypical-density estimate. -/
theorem exists_twoBlock_atypicalFactorizationSet_le_of_logRatios :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ (I₁ I₂ : ℕ × ℕ) (Z : ℕ) (rho : ℝ),
        3 ≤ I₁.1 → I₁.1 ≤ I₁.2 →
        3 ≤ I₂.1 → I₂.1 ≤ I₂.2 →
        0 ≤ rho →
        Real.log ((I₁.1 - 1 : ℕ) : ℝ) / Real.log (I₁.2 : ℝ) ≤ rho →
        Real.log ((I₂.1 - 1 : ℕ) : ℝ) / Real.log (I₂.2 : ℝ) ≤ rho →
        (∑ I ∈ ({I₁, I₂} : Finset (ℕ × ℕ)),
            (((I.2 ^ S : ℕ) : ℝ) ^ 2)) ≤ rho * Z →
        ((atypicalFactorizationSet {I₁, I₂} Z).card : ℝ) ≤
          C * rho * Z := by
  obtain ⟨A, S, hA, hS, _hlog, hfinite⟩ :=
    exists_uniform_card_atypicalFactorizationSet_mertens_beta_bound
  let eta : ℝ := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let D : ℝ := (1 + eta) * Real.exp (2 * PrimeEstimates.mertensBound)
  let C : ℝ := 2 * D + 1
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have heta0 : 0 ≤ eta := by
    dsimp only [eta]
    positivity
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, S, hS, ?_⟩
  intro I₁ I₂ Z rho hI₁lo hI₁ hI₂lo hI₂ hrho hratio₁ hratio₂ hrem
  let blocks : Finset (ℕ × ℕ) := {I₁, I₂}
  have hblocks : ∀ I ∈ blocks, 3 ≤ I.1 ∧ I.1 ≤ I.2 := by
    intro I hmem
    simp only [blocks, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact ⟨hI₁lo, hI₁⟩
    · exact ⟨hI₂lo, hI₂⟩
  have hraw := hfinite blocks Z hblocks
  let ratio : ℕ × ℕ → ℝ := fun I ↦
    Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)
  have hratio : ∀ I ∈ blocks, ratio I ≤ rho := by
    intro I hmem
    simp only [blocks, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact hratio₁
    · exact hratio₂
  have hmain :
      (∑ I ∈ blocks,
          (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            (Real.exp (2 * PrimeEstimates.mertensBound) * ratio I)) ≤
        2 * D * rho := by
    calc
      (∑ I ∈ blocks,
          (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            (Real.exp (2 * PrimeEstimates.mertensBound) * ratio I)) =
          ∑ I ∈ blocks, D * ratio I := by
        apply Finset.sum_congr rfl
        intro I _
        dsimp only [D, eta]
        ring
      _ ≤ ∑ _I ∈ blocks, D * rho := by
        apply Finset.sum_le_sum
        intro I hmem
        exact mul_le_mul_of_nonneg_left (hratio I hmem) hD0
      _ = (blocks.card : ℝ) * (D * rho) := by simp
      _ ≤ 2 * (D * rho) := by
        have hcard : (blocks.card : ℝ) ≤ 2 := by
          exact_mod_cast (Finset.card_insert_le I₁ {I₂})
        exact mul_le_mul_of_nonneg_right hcard (mul_nonneg hD0 hrho)
      _ = 2 * D * rho := by ring
  have hrem' :
      (∑ I ∈ blocks, (((I.2 ^ S : ℕ) : ℝ) ^ 2)) ≤ rho * Z := by
    simpa only [blocks] using hrem
  change ((atypicalFactorizationSet blocks Z).card : ℝ) ≤ C * rho * Z
  calc
    ((atypicalFactorizationSet blocks Z).card : ℝ) ≤
        (Z : ℝ) *
            (∑ I ∈ blocks,
              (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                (Real.exp (2 * PrimeEstimates.mertensBound) * ratio I)) +
          ∑ I ∈ blocks, (((I.2 ^ S : ℕ) : ℝ) ^ 2) := by
      simpa only [ratio] using hraw
    _ ≤ (Z : ℝ) * (2 * D * rho) + rho * Z :=
      add_le_add (mul_le_mul_of_nonneg_left hmain (by positivity)) hrem'
    _ = C * rho * Z := by
      dsimp only [C]
      ring

/-- Canonical specialization.  The sole remaining scalar is the explicit
finite beta-sieve remainder; once it is at most the canonical `1/K`
density, the atypical set has the same power-saving density. -/
theorem exists_gsA10Canonical_atypicalFactorizationSet_le :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ (K Z : ℕ), 2 ≤ K →
        (∑ I ∈ ({gsA10CanonicalFirstBlock K,
            gsA10CanonicalSecondBlock K} : Finset (ℕ × ℕ)),
          (((I.2 ^ S : ℕ) : ℝ) ^ 2)) ≤
            (gsA10CanonicalLogRatioConstant / K) * Z →
        ((atypicalFactorizationSet
            {gsA10CanonicalFirstBlock K,
              gsA10CanonicalSecondBlock K} Z).card : ℝ) ≤
          C * (gsA10CanonicalLogRatioConstant / K) * Z := by
  obtain ⟨C, hC, S, hS, htwo⟩ :=
    exists_twoBlock_atypicalFactorizationSet_le_of_logRatios
  refine ⟨C, hC, S, hS, ?_⟩
  intro K Z hK hrem
  have hvalid := gsA10CanonicalBlocks_valid hK
  have hvalid₁ := hvalid (gsA10CanonicalFirstBlock K) (by simp)
  have hvalid₂ := hvalid (gsA10CanonicalSecondBlock K) (by simp)
  apply htwo (gsA10CanonicalFirstBlock K)
    (gsA10CanonicalSecondBlock K) Z
      (gsA10CanonicalLogRatioConstant / K)
  · exact hvalid₁.1
  · exact hvalid₁.2
  · exact hvalid₂.1
  · exact hvalid₂.2
  · exact div_nonneg
      (zero_le_one.trans one_le_gsA10CanonicalLogRatioConstant) (by positivity)
  · exact gsA10CanonicalFirstBlock_logRatio_le hK
  · exact gsA10CanonicalSecondBlock_logRatio_le hK
  · exact hrem

/-- The diagonal exponent satisfies the exact natural inequality needed
by the beta-sieve power remainder. -/
theorem four_mul_mul_canonicalBlockExponent_sq_le_log
    {S Z : ℕ} :
    4 * S * (gsA10CanonicalBlockExponent S Z) ^ 2 ≤ Nat.log 2 Z := by
  let L := Nat.log 2 Z
  let K := gsA10CanonicalBlockExponent S Z
  have hsqrt : K ^ 2 ≤ L / (4 * S) := by
    dsimp only [K, gsA10CanonicalBlockExponent]
    exact Nat.sqrt_le' _
  calc
    4 * S * K ^ 2 ≤ 4 * S * (L / (4 * S)) :=
      Nat.mul_le_mul_left (4 * S) hsqrt
    _ ≤ L := by
      simpa only [Nat.mul_comm] using Nat.mul_div_le L (4 * S)

/-- The two canonical finite-sieve power terms are bounded by twice the
larger one. -/
theorem sum_gsA10Canonical_betaRemainder_le
    {S K : ℕ} (hK : 2 ≤ K) :
    (∑ I ∈ ({gsA10CanonicalFirstBlock K,
        gsA10CanonicalSecondBlock K} : Finset (ℕ × ℕ)),
      (((I.2 ^ S : ℕ) : ℝ) ^ 2)) ≤
        2 * (((2 ^ (K ^ 2 * S) : ℕ) : ℝ) ^ 2) := by
  have hneq : gsA10CanonicalFirstBlock K ≠
      gsA10CanonicalSecondBlock K := by
    intro h
    have hfst := congrArg Prod.fst h
    dsimp only [gsA10CanonicalFirstBlock, gsA10CanonicalSecondBlock,
      Prod.fst] at hfst
    have hpow : 4 ≤ 2 ^ K := by
      have := Nat.pow_le_pow_right (by omega : 0 < 2) hK
      norm_num at this ⊢
      exact this
    omega
  have hKK : K ≤ K ^ 2 := by nlinarith
  have hexp : K * S ≤ K ^ 2 * S := Nat.mul_le_mul_right S hKK
  have hpow : 2 ^ (K * S) ≤ 2 ^ (K ^ 2 * S) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hcast : ((2 ^ (K * S) : ℕ) : ℝ) ^ 2 ≤
      ((2 ^ (K ^ 2 * S) : ℕ) : ℝ) ^ 2 := by
    have hpowR : ((2 ^ (K * S) : ℕ) : ℝ) ≤
        (2 ^ (K ^ 2 * S) : ℕ) := by exact_mod_cast hpow
    nlinarith
  rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using hneq),
    Finset.sum_singleton]
  dsimp only [gsA10CanonicalFirstBlock, gsA10CanonicalSecondBlock, Prod.snd]
  rw [← pow_mul, ← pow_mul]
  nlinarith

/-- The diagonal exponent automatically makes the explicit beta-sieve
remainder no larger than its canonical `1/K` density, once `K≥2`.
No asymptotic or desired-density premise remains. -/
theorem sum_gsA10Canonical_betaRemainder_le_density
    {S Z : ℕ} (hS : 1 ≤ S)
    (hK : 2 ≤ gsA10CanonicalBlockExponent S Z) :
    (∑ I ∈ ({gsA10CanonicalFirstBlock (gsA10CanonicalBlockExponent S Z),
        gsA10CanonicalSecondBlock (gsA10CanonicalBlockExponent S Z)} :
          Finset (ℕ × ℕ)),
      (((I.2 ^ S : ℕ) : ℝ) ^ 2)) ≤
        (gsA10CanonicalLogRatioConstant /
          gsA10CanonicalBlockExponent S Z) * Z := by
  let K := gsA10CanonicalBlockExponent S Z
  let L := Nat.log 2 Z
  let E : ℕ := (2 ^ (K ^ 2 * S)) ^ 2
  have hExp : 4 * S * K ^ 2 ≤ L := by
    simpa only [K, L] using
      (four_mul_mul_canonicalBlockExponent_sq_le_log (S := S) (Z := Z))
  have hpowLog : 2 ^ L ≤ Z := by
    by_cases hZ : Z = 0
    · subst Z
      simp [L] at hExp
      rcases hExp with hS0 | hK0 <;> omega
    · exact Nat.pow_log_le_self 2 hZ
  have hEeq : E ^ 2 = 2 ^ (4 * S * K ^ 2) := by
    dsimp only [E]
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  have hE2 : E ^ 2 ≤ Z := by
    rw [hEeq]
    exact (Nat.pow_le_pow_right (by omega) hExp).trans hpowLog
  have hKsq : 4 * K ^ 2 ≤ L := by
    calc
      4 * K ^ 2 ≤ 4 * S * K ^ 2 := by
        have hm := Nat.mul_le_mul_right (4 * K ^ 2) hS
        simpa only [one_mul, mul_assoc, mul_left_comm, mul_comm] using hm
      _ ≤ L := hExp
  have hLZ : L ≤ Z := by
    exact Nat.log_le_self 2 Z
  have htwoK2 : (2 * K) ^ 2 ≤ Z := by
    calc
      (2 * K) ^ 2 = 4 * K ^ 2 := by ring
      _ ≤ L := hKsq
      _ ≤ Z := hLZ
  have hEroot : E ≤ Nat.sqrt Z := (Nat.le_sqrt').2 hE2
  have hKroot : 2 * K ≤ Nat.sqrt Z := (Nat.le_sqrt').2 htwoK2
  have hproductNat : 2 * E * K ≤ Z := by
    calc
      2 * E * K = E * (2 * K) := by ring
      _ ≤ Nat.sqrt Z * Nat.sqrt Z := Nat.mul_le_mul hEroot hKroot
      _ ≤ Z := Nat.sqrt_le Z
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hEcast : (2 : ℝ) * E ≤ (1 / (K : ℝ)) * Z := by
    have hproductReal : (2 : ℝ) * E * K ≤ Z := by
      exact_mod_cast hproductNat
    calc
      (2 : ℝ) * E ≤ (Z : ℝ) / K :=
        (le_div_iff₀ hKpos).2 hproductReal
      _ = (1 / (K : ℝ)) * Z := by ring
  have hconst : (1 : ℝ) ≤ gsA10CanonicalLogRatioConstant :=
    one_le_gsA10CanonicalLogRatioConstant
  calc
    (∑ I ∈ ({gsA10CanonicalFirstBlock K,
        gsA10CanonicalSecondBlock K} : Finset (ℕ × ℕ)),
      (((I.2 ^ S : ℕ) : ℝ) ^ 2)) ≤ 2 * (E : ℝ) := by
      simpa only [E, Nat.cast_pow] using
        (sum_gsA10Canonical_betaRemainder_le (S := S) hK)
    _ ≤ (1 / (K : ℝ)) * Z := hEcast
    _ ≤ (gsA10CanonicalLogRatioConstant / K) * Z := by
      apply mul_le_mul_of_nonneg_right
      · exact div_le_div_of_nonneg_right hconst (by positivity)
      · positivity

/-- The diagonal block exponent is at least two beyond an explicit source
threshold. -/
theorem two_le_gsA10CanonicalBlockExponent
    {S Z : ℕ} (hS : 1 ≤ S) (hZ : 2 ^ (16 * S) ≤ Z) :
    2 ≤ gsA10CanonicalBlockExponent S Z := by
  have hlog : 16 * S ≤ Nat.log 2 Z :=
    Nat.le_log_of_pow_le (by omega) hZ
  have hden : 0 < 4 * S := by positivity
  have hdiv : 4 ≤ Nat.log 2 Z / (4 * S) := by
    rw [Nat.le_div_iff_mul_le hden]
    nlinarith
  rw [gsA10CanonicalBlockExponent, Nat.le_sqrt']
  norm_num
  exact hdiv

/-- Conversely, the binary logarithm is controlled by the square of the
diagonal exponent.  This is the floor-safe comparison which turns `1/K`
into a negative half-power of a logarithm. -/
theorem log_le_sixteen_mul_canonicalBlockExponent_sq
    {S Z : ℕ} (hS : 1 ≤ S)
    (hK : 1 ≤ gsA10CanonicalBlockExponent S Z) :
    Nat.log 2 Z ≤
      16 * S * (gsA10CanonicalBlockExponent S Z) ^ 2 := by
  let L := Nat.log 2 Z
  let d := 4 * S
  let q := L / d
  let K := gsA10CanonicalBlockExponent S Z
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdiv : L < d * (q + 1) := by
    simpa only [q] using Nat.lt_mul_div_succ L hd
  have hroot : q + 1 ≤ (K + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt' q
    have hKq : K = Nat.sqrt q := by rfl
    rw [hKq]
    exact Nat.succ_le_iff.mpr h
  have hKtwo : K + 1 ≤ 2 * K := by omega
  calc
    L ≤ d * (q + 1) := hdiv.le
    _ ≤ d * (K + 1) ^ 2 := Nat.mul_le_mul_left d hroot
    _ ≤ d * (2 * K) ^ 2 := by gcongr
    _ = 16 * S * K ^ 2 := by
      dsimp only [d]
      ring

/-- Quantitative conversion of the scheduled reciprocal exponent to a
negative half-power of the binary logarithm. -/
theorem div_canonicalBlockExponent_le_log_rpow_neg_half
    {S Z : ℕ} (hS : 1 ≤ S)
    (hK : 2 ≤ gsA10CanonicalBlockExponent S Z) :
    gsA10CanonicalLogRatioConstant /
        gsA10CanonicalBlockExponent S Z ≤
      (4 * gsA10CanonicalLogRatioConstant * Real.sqrt S) *
        ((Nat.log 2 Z : ℝ) ^ (-(1 / 2 : ℝ))) := by
  let L := Nat.log 2 Z
  let K := gsA10CanonicalBlockExponent S Z
  have hLnat : L ≤ 16 * S * K ^ 2 := by
    simpa only [L, K] using
      log_le_sixteen_mul_canonicalBlockExponent_sq (S := S) (Z := Z)
        hS (by omega)
  have hLreal : (L : ℝ) ≤ 16 * (S : ℝ) * (K : ℝ) ^ 2 := by
    exact_mod_cast hLnat
  have hLposNat : 0 < L := by
    have hExp := four_mul_mul_canonicalBlockExponent_sq_le_log
      (S := S) (Z := Z)
    change 4 * S * K ^ 2 ≤ L at hExp
    have hleft : 0 < 4 * S * K ^ 2 := by positivity
    exact hleft.trans_le hExp
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hLposNat
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hS0 : (0 : ℝ) ≤ S := by positivity
  have hsqrtLsq : (Real.sqrt (L : ℝ)) ^ 2 = L :=
    Real.sq_sqrt hLpos.le
  have hsqrtSsq : (Real.sqrt (S : ℝ)) ^ 2 = S :=
    Real.sq_sqrt hS0
  have hsqrtBound : Real.sqrt (L : ℝ) ≤
      4 * Real.sqrt (S : ℝ) * K := by
    have hright0 : 0 ≤ 4 * Real.sqrt (S : ℝ) * K := by positivity
    nlinarith [Real.sqrt_nonneg (L : ℝ), Real.sqrt_nonneg (S : ℝ)]
  have hinv : (1 : ℝ) / K ≤
      (4 * Real.sqrt (S : ℝ)) / Real.sqrt (L : ℝ) := by
    apply (div_le_div_iff₀ hKpos (Real.sqrt_pos.2 hLpos)).2
    simpa only [one_mul, mul_assoc] using hsqrtBound
  have hrpow : (1 : ℝ) / Real.sqrt (L : ℝ) =
      (L : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, show (-(1 / 2 : ℝ)) = -(1 / 2 : ℝ) by rfl,
      Real.rpow_neg hLpos.le]
    rw [div_eq_mul_inv, one_mul]
  have hconst0 : 0 ≤ gsA10CanonicalLogRatioConstant :=
    zero_le_one.trans one_le_gsA10CanonicalLogRatioConstant
  calc
    gsA10CanonicalLogRatioConstant / K =
        gsA10CanonicalLogRatioConstant * ((1 : ℝ) / K) := by ring
    _ ≤ gsA10CanonicalLogRatioConstant *
        ((4 * Real.sqrt (S : ℝ)) / Real.sqrt (L : ℝ)) :=
      mul_le_mul_of_nonneg_left hinv hconst0
    _ = (4 * gsA10CanonicalLogRatioConstant * Real.sqrt S) *
        ((L : ℝ) ^ (-(1 / 2 : ℝ))) := by rw [← hrpow]; ring

/-- Binary and natural logarithms differ only by an absolute factor in the
negative-half-power direction needed here. -/
theorem natLog_two_rpow_neg_half_le_realLog_rpow_neg_half
    {Z : ℕ} (hZ : 4 ≤ Z) :
    ((Nat.log 2 Z : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      Real.sqrt (2 * Real.log 2) *
        ((Real.log (Z : ℝ)) ^ (-(1 / 2 : ℝ))) := by
  let L := Nat.log 2 Z
  have hZpos : (0 : ℝ) < Z := by positivity
  have hlogZ : 0 < Real.log (Z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hLnat : 1 ≤ L := by
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hLnat
  have hupperNat : Z < 2 ^ (L + 1) := by
    simpa only [L, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) Z
  have hupper : (Z : ℝ) ≤ ((2 ^ (L + 1) : ℕ) : ℝ) := by
    exact_mod_cast hupperNat.le
  have hpowpos : (0 : ℝ) < ((2 ^ (L + 1) : ℕ) : ℝ) := by positivity
  have hlogUpper := Real.strictMonoOn_log.monotoneOn
    hZpos hpowpos hupper
  rw [Nat.cast_pow, Real.log_pow] at hlogUpper
  have hlogCompare : Real.log (Z : ℝ) ≤
      (2 * Real.log 2) * (L : ℝ) := by
    have hLtwo : ((L + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by
      norm_cast
      omega
    have hlogTwo0 : 0 ≤ Real.log (2 : ℝ) :=
      (Real.log_pos (by norm_num)).le
    calc
      Real.log (Z : ℝ) ≤ ((L + 1 : ℕ) : ℝ) * Real.log 2 := hlogUpper
      _ ≤ (2 * (L : ℝ)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hLtwo hlogTwo0
      _ = (2 * Real.log 2) * L := by ring
  let A : ℝ := 2 * Real.log 2
  have hA : 0 < A := by dsimp only [A]; positivity
  have hsqrtLogSq : (Real.sqrt (Real.log (Z : ℝ))) ^ 2 =
      Real.log (Z : ℝ) := Real.sq_sqrt hlogZ.le
  have hsqrtASq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA.le
  have hsqrtLSq : (Real.sqrt (L : ℝ)) ^ 2 = L :=
    Real.sq_sqrt hLpos.le
  have hsqrtBound : Real.sqrt (Real.log (Z : ℝ)) ≤
      Real.sqrt A * Real.sqrt (L : ℝ) := by
    have hright0 : 0 ≤ Real.sqrt A * Real.sqrt (L : ℝ) := by positivity
    change Real.log (Z : ℝ) ≤ A * L at hlogCompare
    nlinarith [Real.sqrt_nonneg (Real.log (Z : ℝ)),
      Real.sqrt_nonneg A, Real.sqrt_nonneg (L : ℝ)]
  have hinv : (1 : ℝ) / Real.sqrt (L : ℝ) ≤
      Real.sqrt A / Real.sqrt (Real.log (Z : ℝ)) := by
    apply (div_le_div_iff₀ (Real.sqrt_pos.2 hLpos)
      (Real.sqrt_pos.2 hlogZ)).2
    simpa only [one_mul, mul_comm] using hsqrtBound
  have hleft : (1 : ℝ) / Real.sqrt (L : ℝ) =
      (L : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hLpos.le,
      div_eq_mul_inv, one_mul]
  have hright : (1 : ℝ) / Real.sqrt (Real.log (Z : ℝ)) =
      (Real.log (Z : ℝ)) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hlogZ.le,
      div_eq_mul_inv, one_mul]
  rw [← hleft, ← hright]
  calc
    (1 : ℝ) / Real.sqrt (L : ℝ) ≤
        Real.sqrt A / Real.sqrt (Real.log (Z : ℝ)) := hinv
    _ = Real.sqrt A * (1 / Real.sqrt (Real.log (Z : ℝ))) := by ring

/-- Fully scheduled two-block atypical density.  The beta-sieve remainder,
block ratios, disjointness, common upper cutoff, and low-prime outside
condition are all discharged by the canonical construction. -/
theorem exists_gsA10Canonical_scheduled_atypicalFactorizationSet_le :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ Z : ℕ, 2 ^ (16 * S) ≤ Z →
        let K := gsA10CanonicalBlockExponent S Z
        ((atypicalFactorizationSet
            {gsA10CanonicalFirstBlock K,
              gsA10CanonicalSecondBlock K} Z).card : ℝ) ≤
          C * (gsA10CanonicalLogRatioConstant / K) * Z := by
  obtain ⟨C, hC, S, hS, hcanonical⟩ :=
    exists_gsA10Canonical_atypicalFactorizationSet_le
  refine ⟨C, hC, S, hS, ?_⟩
  intro Z hZ
  dsimp only
  let K := gsA10CanonicalBlockExponent S Z
  have hK : 2 ≤ K := by
    simpa only [K] using
      two_le_gsA10CanonicalBlockExponent (S := S) (Z := Z) (by omega) hZ
  have hrem := sum_gsA10Canonical_betaRemainder_le_density
    (S := S) (Z := Z) (show 1 ≤ S by omega)
    (by simpa only [K] using hK)
  exact hcanonical K Z hK (by simpa only [K] using hrem)

/-- Literal fixed negative-log-power form of the canonical atypical-set
bound (with binary logarithm, hence equivalent to the natural-log form up
to an absolute factor). -/
theorem exists_gsA10Canonical_scheduled_atypicalFactorizationSet_le_log_half :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ Z : ℕ, 2 ^ (16 * S) ≤ Z →
        let K := gsA10CanonicalBlockExponent S Z
        ((atypicalFactorizationSet
            {gsA10CanonicalFirstBlock K,
              gsA10CanonicalSecondBlock K} Z).card : ℝ) ≤
          C * ((Nat.log 2 Z : ℝ) ^ (-(1 / 2 : ℝ))) * Z := by
  obtain ⟨C₀, hC₀, S, hS, hscheduled⟩ :=
    exists_gsA10Canonical_scheduled_atypicalFactorizationSet_le
  let C : ℝ := C₀ *
    (4 * gsA10CanonicalLogRatioConstant * Real.sqrt S)
  have hfactor : 0 < 4 * gsA10CanonicalLogRatioConstant * Real.sqrt S := by
    have hconst : 0 < gsA10CanonicalLogRatioConstant :=
      zero_lt_one.trans_le one_le_gsA10CanonicalLogRatioConstant
    have hSpos : (0 : ℝ) < S := by positivity
    positivity
  have hC : 0 < C := mul_pos hC₀ hfactor
  refine ⟨C, hC, S, hS, ?_⟩
  intro Z hZ
  dsimp only
  let K := gsA10CanonicalBlockExponent S Z
  have hK : 2 ≤ K := by
    simpa only [K] using
      two_le_gsA10CanonicalBlockExponent (S := S) (Z := Z) (by omega) hZ
  have hbase := hscheduled Z hZ
  dsimp only at hbase
  have hrho := div_canonicalBlockExponent_le_log_rpow_neg_half
    (S := S) (Z := Z) (by omega) (by simpa only [K] using hK)
  calc
    ((atypicalFactorizationSet
        {gsA10CanonicalFirstBlock K,
          gsA10CanonicalSecondBlock K} Z).card : ℝ) ≤
        C₀ * (gsA10CanonicalLogRatioConstant / K) * Z := by
      simpa only [K] using hbase
    _ ≤ C₀ *
          ((4 * gsA10CanonicalLogRatioConstant * Real.sqrt S) *
            ((Nat.log 2 Z : ℝ) ^ (-(1 / 2 : ℝ)))) * Z := by
      gcongr
    _ = C * ((Nat.log 2 Z : ℝ) ^ (-(1 / 2 : ℝ))) * Z := by
      dsimp only [C]
      ring

/-- Natural-log version consumed by the source hierarchy. -/
theorem exists_gsA10Canonical_scheduled_atypicalFactorizationSet_le_realLog_half :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ Z : ℕ, 2 ^ (16 * S) ≤ Z →
        let K := gsA10CanonicalBlockExponent S Z
        ((atypicalFactorizationSet
            {gsA10CanonicalFirstBlock K,
              gsA10CanonicalSecondBlock K} Z).card : ℝ) ≤
          C * ((Real.log (Z : ℝ)) ^ (-(1 / 2 : ℝ))) * Z := by
  obtain ⟨C₀, hC₀, S, hS, hbinary⟩ :=
    exists_gsA10Canonical_scheduled_atypicalFactorizationSet_le_log_half
  let C : ℝ := C₀ * Real.sqrt (2 * Real.log 2)
  have hsqrt : 0 < Real.sqrt (2 * Real.log 2) := by positivity
  have hC : 0 < C := mul_pos hC₀ hsqrt
  refine ⟨C, hC, S, hS, ?_⟩
  intro Z hZ
  dsimp only
  have hZfour : 4 ≤ Z := by
    have hSone : 1 ≤ S := by omega
    have hpow : 4 ≤ 2 ^ (16 * S) := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (16 * S) := Nat.pow_le_pow_right (by omega) (by omega)
    exact hpow.trans hZ
  have hbase := hbinary Z hZ
  dsimp only at hbase
  have hlog := natLog_two_rpow_neg_half_le_realLog_rpow_neg_half hZfour
  calc
    ((atypicalFactorizationSet
        {gsA10CanonicalFirstBlock (gsA10CanonicalBlockExponent S Z),
          gsA10CanonicalSecondBlock (gsA10CanonicalBlockExponent S Z)} Z).card : ℝ) ≤
        C₀ * ((Nat.log 2 Z : ℝ) ^ (-(1 / 2 : ℝ))) * Z := hbase
    _ ≤ C₀ * (Real.sqrt (2 * Real.log 2) *
          ((Real.log (Z : ℝ)) ^ (-(1 / 2 : ℝ)))) * Z := by
      gcongr
    _ = C * ((Real.log (Z : ℝ)) ^ (-(1 / 2 : ℝ))) * Z := by
      dsimp only [C]
      ring

end

end Erdos67

#print axioms Erdos67.disjoint_primesInBlock_gsA10Canonical
#print axioms Erdos67.gsA10CanonicalBlock_uppers_le
#print axioms Erdos67.mrTwoBlockOutside_gsA10Canonical_of_le_three
#print axioms Erdos67.exists_twoBlock_atypicalFactorizationSet_le_of_logRatios
#print axioms Erdos67.exists_gsA10Canonical_atypicalFactorizationSet_le
#print axioms Erdos67.sum_gsA10Canonical_betaRemainder_le_density
#print axioms
  Erdos67.exists_gsA10Canonical_scheduled_atypicalFactorizationSet_le
#print axioms
  Erdos67.exists_gsA10Canonical_scheduled_atypicalFactorizationSet_le_log_half
#print axioms
  Erdos67.exists_gsA10Canonical_scheduled_atypicalFactorizationSet_le_realLog_half
