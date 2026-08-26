import ErdosProblems.Erdos67b.MRGSA10TwoBlockAtypicalScalar

/-!
# Canonical A.10 blocks with the small primes removed

The moving A.10 contour treats every prime below `23` as part of the
outside factor.  Accordingly, this file replaces the first canonical
block `(3,2^K]` by `(23,2^K]`.  Since `primesInBlock` uses a closed
natural interval, the latter is encoded by `(24,2^K)`.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

/-- First large-prime A.10 block, representing `(23,2^K]`. -/
def gsA10CanonicalLargeFirstBlock (K : ℕ) : ℕ × ℕ := (24, 2 ^ K)

/-- The second block is unchanged. -/
def gsA10CanonicalLargeSecondBlock (K : ℕ) : ℕ × ℕ :=
  gsA10CanonicalSecondBlock K

/-- A common constant for the new first-block ratio and the old
beta-remainder density. -/
def gsA10CanonicalLargeLogRatioConstant : ℝ :=
  max (Real.log 23 / Real.log 2) gsA10CanonicalLogRatioConstant

theorem canonicalLogRatioConstant_le_large :
    gsA10CanonicalLogRatioConstant ≤ gsA10CanonicalLargeLogRatioConstant :=
  le_max_right _ _

theorem one_le_gsA10CanonicalLargeLogRatioConstant :
    1 ≤ gsA10CanonicalLargeLogRatioConstant :=
  one_le_gsA10CanonicalLogRatioConstant.trans canonicalLogRatioConstant_le_large

/-- The narrowed blocks are disjoint. -/
theorem disjoint_primesInBlock_gsA10CanonicalLarge
    {K : ℕ} (hK : 5 ≤ K) :
    Disjoint (primesInBlock (gsA10CanonicalLargeFirstBlock K))
      (primesInBlock (gsA10CanonicalLargeSecondBlock K)) := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  have hp₁' := (mem_primesInBlock.mp hp₁).2.2
  have hp₂' := (mem_primesInBlock.mp hp₂).2.1
  dsimp only [gsA10CanonicalLargeFirstBlock,
    gsA10CanonicalLargeSecondBlock, gsA10CanonicalSecondBlock,
    Prod.fst, Prod.snd] at hp₁' hp₂'
  omega

/-- Both narrowed blocks have the source upper cutoff `2^(K^2)`. -/
theorem gsA10CanonicalLargeBlock_uppers_le
    {K : ℕ} (hK : 5 ≤ K) :
    (gsA10CanonicalLargeFirstBlock K).2 ≤ 2 ^ (K ^ 2) ∧
      (gsA10CanonicalLargeSecondBlock K).2 ≤ 2 ^ (K ^ 2) := by
  exact gsA10CanonicalBlock_uppers_le (by omega)

/-- Every prime at most `23` belongs to the outside factor. -/
theorem mrTwoBlockOutside_gsA10CanonicalLarge_of_le_twentyThree
    {K p : ℕ} (hK : 5 ≤ K) (hp : p.Prime) (hp23 : p ≤ 23) :
    mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
      (gsA10CanonicalLargeSecondBlock K) p := by
  constructor
  · intro hp₁
    have hp₁' := (mem_primesInBlock.mp hp₁).2.1
    dsimp only [gsA10CanonicalLargeFirstBlock, Prod.fst] at hp₁'
    omega
  · intro hp₂
    have hp₂' := (mem_primesInBlock.mp hp₂).2.1
    dsimp only [gsA10CanonicalLargeSecondBlock, gsA10CanonicalSecondBlock,
      Prod.fst] at hp₂'
    have hpow : 32 ≤ 2 ^ K := by
      have := Nat.pow_le_pow_right (by omega : 0 < 2) hK
      norm_num at this ⊢
      exact this
    omega

/-- Membership in either selected block forces the prime to be at least
`23`, the exact compatibility hypothesis used by the moving contour. -/
theorem twentyThree_le_of_mem_gsA10CanonicalLarge
    {K p : ℕ} (hK : 5 ≤ K) (hp : p.Prime)
    (hmem : p ∈ primesInBlock (gsA10CanonicalLargeFirstBlock K) ∨
      p ∈ primesInBlock (gsA10CanonicalLargeSecondBlock K)) :
    23 ≤ p := by
  rcases hmem with hmem | hmem
  · have h := (mem_primesInBlock.mp hmem).2.1
    dsimp only [gsA10CanonicalLargeFirstBlock, Prod.fst] at h
    omega
  · have h := (mem_primesInBlock.mp hmem).2.1
    dsimp only [gsA10CanonicalLargeSecondBlock, gsA10CanonicalSecondBlock,
      Prod.fst] at h
    have hpow : 32 ≤ 2 ^ K := by
      have := Nat.pow_le_pow_right (by omega : 0 < 2) hK
      norm_num at this ⊢
      exact this
    omega

theorem gsA10CanonicalLargeBlocks_valid
    {K : ℕ} (hK : 5 ≤ K) :
    ∀ I ∈ ({gsA10CanonicalLargeFirstBlock K,
        gsA10CanonicalLargeSecondBlock K} : Finset (ℕ × ℕ)),
      3 ≤ I.1 ∧ I.1 ≤ I.2 := by
  intro I hI
  simp only [Finset.mem_insert, Finset.mem_singleton] at hI
  rcases hI with rfl | rfl
  · dsimp only [gsA10CanonicalLargeFirstBlock, Prod.fst, Prod.snd]
    constructor
    · norm_num
    · have := Nat.pow_le_pow_right (by omega : 0 < 2) hK
      norm_num at this ⊢
      omega
  · simpa only [gsA10CanonicalLargeSecondBlock] using
      gsA10CanonicalBlocks_valid (K := K) (by omega)
        (gsA10CanonicalSecondBlock K) (by simp)

theorem gsA10CanonicalLargeFirstBlock_logRatio_le
    {K : ℕ} (hK : 5 ≤ K) :
    Real.log (((gsA10CanonicalLargeFirstBlock K).1 - 1 : ℕ) : ℝ) /
        Real.log ((gsA10CanonicalLargeFirstBlock K).2 : ℝ) ≤
      gsA10CanonicalLargeLogRatioConstant / K := by
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hconst : Real.log 23 / Real.log 2 ≤
      gsA10CanonicalLargeLogRatioConstant := le_max_left _ _
  dsimp only [gsA10CanonicalLargeFirstBlock, Prod.fst, Prod.snd]
  norm_num only
  rw [Nat.cast_pow, Real.log_pow]
  calc
    Real.log 23 / ((K : ℝ) * Real.log 2) =
        (Real.log 23 / Real.log 2) / K := by field_simp
    _ ≤ gsA10CanonicalLargeLogRatioConstant / K := by
      exact div_le_div_of_nonneg_right hconst (by positivity)

theorem gsA10CanonicalLargeSecondBlock_logRatio_le
    {K : ℕ} (hK : 5 ≤ K) :
    Real.log (((gsA10CanonicalLargeSecondBlock K).1 - 1 : ℕ) : ℝ) /
        Real.log ((gsA10CanonicalLargeSecondBlock K).2 : ℝ) ≤
      gsA10CanonicalLargeLogRatioConstant / K := by
  exact (gsA10CanonicalSecondBlock_logRatio_le (by omega)).trans
    (div_le_div_of_nonneg_right canonicalLogRatioConstant_le_large (by positivity))

/-- The beta remainder is unchanged, because only the lower endpoint of
the first block moved. -/
theorem sum_gsA10CanonicalLarge_betaRemainder_le
    {S K : ℕ} (hK : 5 ≤ K) :
    (∑ I ∈ ({gsA10CanonicalLargeFirstBlock K,
        gsA10CanonicalLargeSecondBlock K} : Finset (ℕ × ℕ)),
      (((I.2 ^ S : ℕ) : ℝ) ^ 2)) ≤
        2 * (((2 ^ (K ^ 2 * S) : ℕ) : ℝ) ^ 2) := by
  have hneq : gsA10CanonicalLargeFirstBlock K ≠
      gsA10CanonicalLargeSecondBlock K := by
    intro h
    have hfst := congrArg Prod.fst h
    dsimp only [gsA10CanonicalLargeFirstBlock,
      gsA10CanonicalLargeSecondBlock, gsA10CanonicalSecondBlock,
      Prod.fst] at hfst
    have hpow : 32 ≤ 2 ^ K := by
      have := Nat.pow_le_pow_right (by omega : 0 < 2) hK
      norm_num at this ⊢
      exact this
    omega
  rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using hneq),
    Finset.sum_singleton]
  dsimp only [gsA10CanonicalLargeFirstBlock,
    gsA10CanonicalLargeSecondBlock, gsA10CanonicalSecondBlock, Prod.snd]
  have hbase := sum_gsA10Canonical_betaRemainder_le (S := S) (by omega : 2 ≤ K)
  rw [Finset.sum_insert, Finset.sum_singleton] at hbase
  · simpa only [gsA10CanonicalFirstBlock, gsA10CanonicalSecondBlock,
      Prod.snd] using hbase
  · simp only [Finset.mem_singleton]
    intro h
    have hfst := congrArg Prod.fst h
    dsimp only [gsA10CanonicalFirstBlock, gsA10CanonicalSecondBlock,
      Prod.fst] at hfst
    have hpow : 32 ≤ 2 ^ K := by
      have := Nat.pow_le_pow_right (by omega : 0 < 2) hK
      norm_num at this ⊢
      exact this
    omega

theorem sum_gsA10CanonicalLarge_betaRemainder_le_density
    {S Z : ℕ} (hS : 1 ≤ S)
    (hK : 5 ≤ gsA10CanonicalBlockExponent S Z) :
    (∑ I ∈ ({gsA10CanonicalLargeFirstBlock
          (gsA10CanonicalBlockExponent S Z),
        gsA10CanonicalLargeSecondBlock
          (gsA10CanonicalBlockExponent S Z)} : Finset (ℕ × ℕ)),
      (((I.2 ^ S : ℕ) : ℝ) ^ 2)) ≤
        (gsA10CanonicalLargeLogRatioConstant /
          gsA10CanonicalBlockExponent S Z) * Z := by
  let K := gsA10CanonicalBlockExponent S Z
  have hold := sum_gsA10Canonical_betaRemainder_le_density
    (S := S) (Z := Z) hS (by simpa only [K] using (show 2 ≤ K by omega))
  have hsame :
      (∑ I ∈ ({gsA10CanonicalLargeFirstBlock K,
          gsA10CanonicalLargeSecondBlock K} : Finset (ℕ × ℕ)),
        (((I.2 ^ S : ℕ) : ℝ) ^ 2)) =
      ∑ I ∈ ({gsA10CanonicalFirstBlock K,
          gsA10CanonicalSecondBlock K} : Finset (ℕ × ℕ)),
        (((I.2 ^ S : ℕ) : ℝ) ^ 2) := by
    have hnew := sum_gsA10CanonicalLarge_betaRemainder_le (S := S)
      (by simpa only [K] using hK)
    rw [Finset.sum_insert, Finset.sum_singleton,
      Finset.sum_insert, Finset.sum_singleton]
    · rfl
    · simp only [Finset.mem_singleton]
      intro h
      have hfst := congrArg Prod.fst h
      dsimp only [gsA10CanonicalFirstBlock, gsA10CanonicalSecondBlock,
        Prod.fst] at hfst
      have hpow : 32 ≤ 2 ^ K := by
        have := Nat.pow_le_pow_right (by omega : 0 < 2)
          (by simpa only [K] using hK)
        norm_num at this ⊢
        exact this
      omega
    · simp only [Finset.mem_singleton]
      intro h
      have hfst := congrArg Prod.fst h
      dsimp only [gsA10CanonicalLargeFirstBlock,
        gsA10CanonicalLargeSecondBlock, gsA10CanonicalSecondBlock,
        Prod.fst] at hfst
      have hpow : 32 ≤ 2 ^ K := by
        have := Nat.pow_le_pow_right (by omega : 0 < 2)
          (by simpa only [K] using hK)
        norm_num at this ⊢
        exact this
      omega
  rw [hsame]
  calc
    _ ≤ (gsA10CanonicalLogRatioConstant / K) * Z := by
      simpa only [K] using hold
    _ ≤ (gsA10CanonicalLargeLogRatioConstant / K) * Z := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right canonicalLogRatioConstant_le_large
          (by positivity)) (by positivity)

/-- Canonical narrowed-block density with only its automatic beta
remainder left to instantiate. -/
theorem exists_gsA10CanonicalLarge_atypicalFactorizationSet_le :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ (K Z : ℕ), 5 ≤ K →
        (∑ I ∈ ({gsA10CanonicalLargeFirstBlock K,
            gsA10CanonicalLargeSecondBlock K} : Finset (ℕ × ℕ)),
          (((I.2 ^ S : ℕ) : ℝ) ^ 2)) ≤
            (gsA10CanonicalLargeLogRatioConstant / K) * Z →
        ((atypicalFactorizationSet
            {gsA10CanonicalLargeFirstBlock K,
              gsA10CanonicalLargeSecondBlock K} Z).card : ℝ) ≤
          C * (gsA10CanonicalLargeLogRatioConstant / K) * Z := by
  obtain ⟨C, hC, S, hS, htwo⟩ :=
    exists_twoBlock_atypicalFactorizationSet_le_of_logRatios
  refine ⟨C, hC, S, hS, ?_⟩
  intro K Z hK hrem
  have hvalid := gsA10CanonicalLargeBlocks_valid hK
  have hvalid₁ := hvalid (gsA10CanonicalLargeFirstBlock K) (by simp)
  have hvalid₂ := hvalid (gsA10CanonicalLargeSecondBlock K) (by simp)
  apply htwo (gsA10CanonicalLargeFirstBlock K)
    (gsA10CanonicalLargeSecondBlock K) Z
      (gsA10CanonicalLargeLogRatioConstant / K)
  · exact hvalid₁.1
  · exact hvalid₁.2
  · exact hvalid₂.1
  · exact hvalid₂.2
  · exact div_nonneg
      (zero_le_one.trans one_le_gsA10CanonicalLargeLogRatioConstant) (by positivity)
  · exact gsA10CanonicalLargeFirstBlock_logRatio_le hK
  · exact gsA10CanonicalLargeSecondBlock_logRatio_le hK
  · exact hrem

theorem five_le_gsA10CanonicalBlockExponent
    {S Z : ℕ} (hS : 1 ≤ S) (hZ : 2 ^ (100 * S) ≤ Z) :
    5 ≤ gsA10CanonicalBlockExponent S Z := by
  have hlog : 100 * S ≤ Nat.log 2 Z :=
    Nat.le_log_of_pow_le (by omega) hZ
  have hden : 0 < 4 * S := by positivity
  have hdiv : 25 ≤ Nat.log 2 Z / (4 * S) := by
    rw [Nat.le_div_iff_mul_le hden]
    nlinarith
  rw [gsA10CanonicalBlockExponent, Nat.le_sqrt']
  norm_num
  exact hdiv

theorem exists_gsA10CanonicalLarge_scheduled_atypicalFactorizationSet_le :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ Z : ℕ, 2 ^ (100 * S) ≤ Z →
        let K := gsA10CanonicalBlockExponent S Z
        ((atypicalFactorizationSet
            {gsA10CanonicalLargeFirstBlock K,
              gsA10CanonicalLargeSecondBlock K} Z).card : ℝ) ≤
          C * (gsA10CanonicalLargeLogRatioConstant / K) * Z := by
  obtain ⟨C, hC, S, hS, hcanonical⟩ :=
    exists_gsA10CanonicalLarge_atypicalFactorizationSet_le
  refine ⟨C, hC, S, hS, ?_⟩
  intro Z hZ
  dsimp only
  let K := gsA10CanonicalBlockExponent S Z
  have hK : 5 ≤ K := by
    simpa only [K] using five_le_gsA10CanonicalBlockExponent
      (S := S) (Z := Z) (by omega) hZ
  have hrem := sum_gsA10CanonicalLarge_betaRemainder_le_density
    (S := S) (Z := Z) (show 1 ≤ S by omega)
    (by simpa only [K] using hK)
  exact hcanonical K Z hK (by simpa only [K] using hrem)

/-- The scheduled narrowed blocks have genuine negative-half-power
atypical density in the natural logarithm. -/
theorem exists_gsA10CanonicalLarge_scheduled_atypicalFactorizationSet_le_realLog_half :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ Z : ℕ, 2 ^ (100 * S) ≤ Z →
        let K := gsA10CanonicalBlockExponent S Z
        ((atypicalFactorizationSet
            {gsA10CanonicalLargeFirstBlock K,
              gsA10CanonicalLargeSecondBlock K} Z).card : ℝ) ≤
          C * ((Real.log (Z : ℝ)) ^ (-(1 / 2 : ℝ))) * Z := by
  obtain ⟨C₀, hC₀, S, hS, hsched⟩ :=
    exists_gsA10CanonicalLarge_scheduled_atypicalFactorizationSet_le
  let F : ℝ := gsA10CanonicalLargeLogRatioConstant *
    (4 * gsA10CanonicalLogRatioConstant * Real.sqrt S) *
      Real.sqrt (2 * Real.log 2)
  let C : ℝ := C₀ * F
  have hF : 0 < F := by
    dsimp only [F]
    have hlarge : 0 < gsA10CanonicalLargeLogRatioConstant :=
      zero_lt_one.trans_le one_le_gsA10CanonicalLargeLogRatioConstant
    have hold : 0 < gsA10CanonicalLogRatioConstant :=
      zero_lt_one.trans_le one_le_gsA10CanonicalLogRatioConstant
    positivity
  refine ⟨C, mul_pos hC₀ hF, S, hS, ?_⟩
  intro Z hZ
  dsimp only
  let K := gsA10CanonicalBlockExponent S Z
  have hK : 5 ≤ K := by
    simpa only [K] using five_le_gsA10CanonicalBlockExponent
      (S := S) (Z := Z) (by omega) hZ
  have hbase := hsched Z hZ
  dsimp only at hbase
  have hold := div_canonicalBlockExponent_le_log_rpow_neg_half
    (S := S) (Z := Z) (by omega) (by simpa only [K] using (show 2 ≤ K by omega))
  have hbinary : gsA10CanonicalLargeLogRatioConstant / K ≤
      (gsA10CanonicalLargeLogRatioConstant *
        (4 * gsA10CanonicalLogRatioConstant * Real.sqrt S)) *
          ((Nat.log 2 Z : ℝ) ^ (-(1 / 2 : ℝ))) := by
    have hKpos : (0 : ℝ) < K := by positivity
    calc
      gsA10CanonicalLargeLogRatioConstant / K =
          gsA10CanonicalLargeLogRatioConstant * (1 / (K : ℝ)) := by ring
      _ ≤ gsA10CanonicalLargeLogRatioConstant *
          (gsA10CanonicalLogRatioConstant / K) := by
        exact mul_le_mul_of_nonneg_left
          (by
            simpa only [one_div] using
              (div_le_div_of_nonneg_right one_le_gsA10CanonicalLogRatioConstant
                (by positivity : (0 : ℝ) ≤ K)))
          (zero_le_one.trans one_le_gsA10CanonicalLargeLogRatioConstant)
      _ ≤ gsA10CanonicalLargeLogRatioConstant *
          ((4 * gsA10CanonicalLogRatioConstant * Real.sqrt S) *
            ((Nat.log 2 Z : ℝ) ^ (-(1 / 2 : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left (by simpa only [K] using hold)
          (zero_le_one.trans one_le_gsA10CanonicalLargeLogRatioConstant)
      _ = _ := by ring
  have hZfour : 4 ≤ Z := by
    have hpow : 4 ≤ 2 ^ (100 * S) := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (100 * S) := Nat.pow_le_pow_right (by omega) (by omega)
    exact hpow.trans hZ
  have hlog := natLog_two_rpow_neg_half_le_realLog_rpow_neg_half hZfour
  calc
    ((atypicalFactorizationSet
        {gsA10CanonicalLargeFirstBlock K,
          gsA10CanonicalLargeSecondBlock K} Z).card : ℝ) ≤
        C₀ * (gsA10CanonicalLargeLogRatioConstant / K) * Z := by
      simpa only [K] using hbase
    _ ≤ C₀ * ((gsA10CanonicalLargeLogRatioConstant *
          (4 * gsA10CanonicalLogRatioConstant * Real.sqrt S)) *
          ((Nat.log 2 Z : ℝ) ^ (-(1 / 2 : ℝ)))) * Z := by
      gcongr
    _ ≤ C₀ * ((gsA10CanonicalLargeLogRatioConstant *
          (4 * gsA10CanonicalLogRatioConstant * Real.sqrt S)) *
          (Real.sqrt (2 * Real.log 2) *
            ((Real.log (Z : ℝ)) ^ (-(1 / 2 : ℝ))))) * Z := by
      have hfactor : 0 ≤ gsA10CanonicalLargeLogRatioConstant *
          (4 * gsA10CanonicalLogRatioConstant * Real.sqrt S) := by
        exact mul_nonneg
          (zero_le_one.trans one_le_gsA10CanonicalLargeLogRatioConstant)
          (mul_nonneg
            (mul_nonneg (by norm_num)
              (zero_le_one.trans one_le_gsA10CanonicalLogRatioConstant))
            (Real.sqrt_nonneg _))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hlog hfactor) hC₀.le)
        (by positivity)
    _ = C * ((Real.log (Z : ℝ)) ^ (-(1 / 2 : ℝ))) * Z := by
      dsimp only [C, F]
      ring

end

end Erdos67b

#print axioms Erdos67b.disjoint_primesInBlock_gsA10CanonicalLarge
#print axioms Erdos67b.mrTwoBlockOutside_gsA10CanonicalLarge_of_le_twentyThree
#print axioms Erdos67b.twentyThree_le_of_mem_gsA10CanonicalLarge
#print axioms Erdos67b.exists_gsA10CanonicalLarge_scheduled_atypicalFactorizationSet_le_realLog_half
