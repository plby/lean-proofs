import ErdosProblems.Erdos888.SquarefreeBlocks

/-!
# Regrouping the linear core term

This file performs the finite, purely combinatorial rearrangement of the
linear term `2 T(i,j) N(j)` in the coloured KST estimate.  The source sum is
over the blocks actually occupied by the admissible set.  The target sum is
independent of that set: it is grouped by the left dyadic index, then by a
squarefree smooth core, and finally by every compatible right dyadic index.
-/

open scoped BigOperators

namespace Erdos888
namespace CoreBridgeBlocks

noncomputable section

/-- Dyadic indices which can occur below `n`. -/
def coreScaleIndexSet (n : ℕ) : Finset ℕ :=
  Finset.range (Nat.log 2 n + 1)

/-- Possible cores at a fixed left dyadic scale.  The condition
`c * 2^(2i) ≤ n` follows from the ordering `i ≤ j`. -/
def coreScaleCoreSet (n i : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun c ↦
    Squarefree c ∧ c * 2 ^ (2 * i) ≤ n ∧
      ∀ r ∈ c.primeFactors, r < 2 ^ (i + 1)

/-- Right dyadic indices compatible with a fixed left scale and core. -/
def rightIndexSet (n i c : ℕ) : Finset ℕ :=
  (coreScaleIndexSet n).filter fun j ↦
    i ≤ j ∧ c * 2 ^ i * 2 ^ j ≤ n

@[simp] theorem mem_coreScaleIndexSet {n i : ℕ} :
    i ∈ coreScaleIndexSet n ↔ i < Nat.log 2 n + 1 := by
  simp [coreScaleIndexSet]

@[simp] theorem mem_coreScaleCoreSet {n i c : ℕ} :
    c ∈ coreScaleCoreSet n i ↔
      1 ≤ c ∧ c ≤ n ∧ Squarefree c ∧ c * 2 ^ (2 * i) ≤ n ∧
        ∀ r ∈ c.primeFactors, r < 2 ^ (i + 1) := by
  simp [coreScaleCoreSet, and_assoc]

@[simp] theorem mem_rightIndexSet {n i c j : ℕ} :
    j ∈ rightIndexSet n i c ↔
      j < Nat.log 2 n + 1 ∧ i ≤ j ∧ c * 2 ^ i * 2 ^ j ≤ n := by
  simp [rightIndexSet]

/-- The exact linear core contribution over occupied blocks.  The parameter
`n` is retained in the name of the finite estimate even though the source
sum itself is determined by `A`. -/
def coreBlockSum (A : Finset ℕ) (_n : ℕ) : ℝ :=
  ∑ ij ∈ occupiedBlockIndices A,
    2 * ((squarefreeBlockCoreSet A ij.1 ij.2).card : ℝ) *
      ((dyadicPrimeBlock ij.2).card : ℝ)

/-- The exact occupied block sum is the corresponding nested sum over the
individual cores in each block. -/
theorem coreBlockSum_eq_sum_cores (A : Finset ℕ) (n : ℕ) :
    coreBlockSum A n =
      ∑ ij ∈ occupiedBlockIndices A,
        ∑ _c ∈ squarefreeBlockCoreSet A ij.1 ij.2,
          2 * ((dyadicPrimeBlock ij.2).card : ℝ) := by
  classical
  unfold coreBlockSum
  apply Finset.sum_congr rfl
  intro ij hij
  simp
  ring

/-- Every occupied `(block,core)` key satisfies the set-independent
arithmetic constraints of the regrouped sum. -/
theorem squarefreeBlockCoreSet_subset_coreScaleCoreSet
    {A : Finset ℕ} {n i j : ℕ} (hA : RequiredCondition A n)
    (hij : i ≤ j) :
    squarefreeBlockCoreSet A i j ⊆ coreScaleCoreSet n i := by
  intro c hc
  have hcSpec := squarefreeBlockCoreSet_spec hA hc
  rw [mem_coreScaleCoreSet]
  refine ⟨hcSpec.1, ?_, hcSpec.2.1, ?_, hcSpec.2.2.2⟩
  · have hpowpos : 0 < 2 ^ i * 2 ^ j := by positivity
    calc
      c ≤ c * (2 ^ i * 2 ^ j) := by
        nth_rewrite 1 [← mul_one c]
        exact Nat.mul_le_mul_left c (by omega)
      _ ≤ n := by simpa [mul_assoc] using hcSpec.2.2.1
  · have hpow : 2 ^ i ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by norm_num) hij
    calc
      c * 2 ^ (2 * i) = c * 2 ^ i * 2 ^ i := by
        rw [show 2 * i = i + i by omega, pow_add, mul_assoc]
      _ ≤ c * 2 ^ i * 2 ^ j :=
        Nat.mul_le_mul_left (c * 2 ^ i) hpow
      _ ≤ n := hcSpec.2.2.1

theorem squarefreeBlockCoreSet_subset_rightFilter
    {A : Finset ℕ} {n i j : ℕ} (hA : RequiredCondition A n)
    (hijOcc : (i, j) ∈ occupiedBlockIndices A) :
    squarefreeBlockCoreSet A i j ⊆
      (coreScaleCoreSet n i).filter fun c ↦ j ∈ rightIndexSet n i c := by
  intro c hc
  have hijOrder := occupiedBlockIndices_fst_le_snd hijOcc
  have hijRange := occupiedBlockIndices_lt_log_add_one hA hijOcc
  have hcSpec := squarefreeBlockCoreSet_spec hA hc
  rw [Finset.mem_filter]
  refine ⟨squarefreeBlockCoreSet_subset_coreScaleCoreSet hA hijOrder hc, ?_⟩
  exact mem_rightIndexSet.2 ⟨hijRange.2, hijOrder, hcSpec.2.2.1⟩

/-- The source contribution from one occupied block is bounded by summing
over every compatible core at that pair of scales. -/
theorem sum_block_cores_le_rightFilter
    {A : Finset ℕ} {n i j : ℕ} (hA : RequiredCondition A n)
    (hijOcc : (i, j) ∈ occupiedBlockIndices A) :
    (∑ _c ∈ squarefreeBlockCoreSet A i j,
        2 * ((dyadicPrimeBlock j).card : ℝ)) ≤
      ∑ _c ∈ (coreScaleCoreSet n i).filter
          (fun c ↦ j ∈ rightIndexSet n i c),
        2 * ((dyadicPrimeBlock j).card : ℝ) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (squarefreeBlockCoreSet_subset_rightFilter hA hijOcc)
    (by intro c hc hnot; positivity)

/-- Every occupied pair is in the rectangular logarithmic index range. -/
theorem occupiedBlockIndices_subset_scaleProduct
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n) :
    occupiedBlockIndices A ⊆
      (coreScaleIndexSet n).product (coreScaleIndexSet n) := by
  intro ij hij
  have hRange := occupiedBlockIndices_lt_log_add_one hA hij
  exact Finset.mem_product.2 ⟨mem_coreScaleIndexSet.2 hRange.1,
    mem_coreScaleIndexSet.2 hRange.2⟩

/-- Before commuting the last two finite sums, the set-independent
majorant is naturally ordered by `(i,j,c)`. -/
def scalePairCoreSum (n : ℕ) : ℝ :=
  ∑ ij ∈ (coreScaleIndexSet n).product (coreScaleIndexSet n),
    ∑ _c ∈ (coreScaleCoreSet n ij.1).filter
        (fun c ↦ ij.2 ∈ rightIndexSet n ij.1 c),
      2 * ((dyadicPrimeBlock ij.2).card : ℝ)

theorem coreBlockSum_le_scalePairCoreSum
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n) :
    coreBlockSum A n ≤ scalePairCoreSum n := by
  rw [coreBlockSum_eq_sum_cores]
  unfold scalePairCoreSum
  calc
    (∑ ij ∈ occupiedBlockIndices A,
        ∑ _c ∈ squarefreeBlockCoreSet A ij.1 ij.2,
          2 * ((dyadicPrimeBlock ij.2).card : ℝ)) ≤
        ∑ ij ∈ occupiedBlockIndices A,
          ∑ _c ∈ (coreScaleCoreSet n ij.1).filter
              (fun c ↦ ij.2 ∈ rightIndexSet n ij.1 c),
            2 * ((dyadicPrimeBlock ij.2).card : ℝ) := by
      apply Finset.sum_le_sum
      intro ij hij
      exact sum_block_cores_le_rightFilter hA hij
    _ ≤ ∑ ij ∈ (coreScaleIndexSet n).product (coreScaleIndexSet n),
          ∑ _c ∈ (coreScaleCoreSet n ij.1).filter
              (fun c ↦ ij.2 ∈ rightIndexSet n ij.1 c),
            2 * ((dyadicPrimeBlock ij.2).card : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (occupiedBlockIndices_subset_scaleProduct hA)
        (by intro ij hij hnot; positivity)

/-- The regrouped, set-independent form of the linear core majorant. -/
def regroupedCoreSum (n : ℕ) : ℝ :=
  ∑ i ∈ coreScaleIndexSet n,
    ∑ c ∈ coreScaleCoreSet n i,
      2 * ∑ j ∈ rightIndexSet n i c,
        ((dyadicPrimeBlock j).card : ℝ)

theorem scalePairCoreSum_eq_regroupedCoreSum (n : ℕ) :
    scalePairCoreSum n = regroupedCoreSum n := by
  classical
  unfold scalePairCoreSum regroupedCoreSum
  rw [show
      (∑ ij ∈ (coreScaleIndexSet n).product (coreScaleIndexSet n),
        ∑ _c ∈ (coreScaleCoreSet n ij.1).filter
            (fun c ↦ ij.2 ∈ rightIndexSet n ij.1 c),
          2 * ((dyadicPrimeBlock ij.2).card : ℝ)) =
        ∑ i ∈ coreScaleIndexSet n, ∑ j ∈ coreScaleIndexSet n,
          ∑ _c ∈ (coreScaleCoreSet n i).filter
              (fun c ↦ j ∈ rightIndexSet n i c),
            2 * ((dyadicPrimeBlock j).card : ℝ) by
      convert
        (Finset.sum_product (coreScaleIndexSet n) (coreScaleIndexSet n)
          (fun ij : ℕ × ℕ ↦
            ∑ _c ∈ (coreScaleCoreSet n ij.1).filter
                (fun c ↦ ij.2 ∈ rightIndexSet n ij.1 c),
              2 * ((dyadicPrimeBlock ij.2).card : ℝ))) using 1 <;> simp]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  have hfilter : (coreScaleIndexSet n).filter
      (fun j ↦ j ∈ rightIndexSet n i c) = rightIndexSet n i c := by
    ext j
    simp [rightIndexSet]
  rw [← Finset.sum_filter, hfilter, Finset.mul_sum]

/-- Exact finite regrouping inequality for the `2 T(i,j) N(j)` term.  The
right side is grouped by `i < log₂ n + 1`, by squarefree cores satisfying
`c·2^(2i) ≤ n` whose prime factors are below `2^(i+1)`, and by compatible
right indices `j` satisfying `i ≤ j` and `c·2^i·2^j ≤ n`. -/
theorem coreBlockSum_le_regroupedCoreSum
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n) :
    coreBlockSum A n ≤ regroupedCoreSum n := by
  rw [← scalePairCoreSum_eq_regroupedCoreSum]
  exact coreBlockSum_le_scalePairCoreSum hA

end
end CoreBridgeBlocks
end Erdos888
