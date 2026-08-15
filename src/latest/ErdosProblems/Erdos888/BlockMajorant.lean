import ErdosProblems.Erdos888.BlockEncoding
import ErdosProblems.Erdos888.PrimeEstimates

/-!
# Set-independent dyadic block majorants for Erdős problem 888

This module contains the finite arithmetic functions shared by the block
encoding and the three analytic bridge modules.  Keeping them below the
assembly module avoids import cycles.
-/

open scoped BigOperators

namespace Erdos888

/-- The set of all arithmetically possible cores at an ordered pair of
endpoint scales. -/
noncomputable def blockCoreCandidates (n i j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun c ↦
    i ≤ j ∧ Squarefree c ∧ c * 2 ^ i * 2 ^ j ≤ n ∧
      ∀ r ∈ c.primeFactors, r < 2 ^ (i + 1)

@[simp] theorem mem_blockCoreCandidates {n i j c : ℕ} :
    c ∈ blockCoreCandidates n i j ↔
      1 ≤ c ∧ c ≤ n ∧ i ≤ j ∧ Squarefree c ∧
        c * 2 ^ i * 2 ^ j ≤ n ∧
          ∀ r ∈ c.primeFactors, r < 2 ^ (i + 1) := by
  simp [blockCoreCandidates, and_assoc]

theorem blockCoreCandidates_mono {n m i j : ℕ} (hnm : n ≤ m) :
    blockCoreCandidates n i j ⊆ blockCoreCandidates m i j := by
  intro c hc
  obtain ⟨hc1, hcn, hij, hsf, hsize, hsmooth⟩ :=
    mem_blockCoreCandidates.mp hc
  exact mem_blockCoreCandidates.mpr
    ⟨hc1, hcn.trans hnm, hij, hsf, hsize.trans hnm, hsmooth⟩

/-- The radical form of `x^(3/4)` used in the coloured KST estimate. -/
noncomputable def threeQuarterRoot (x : ℝ) : ℝ :=
  Real.sqrt (x * Real.sqrt x)

theorem threeQuarterRoot_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    threeQuarterRoot x ≤ threeQuarterRoot y := by
  unfold threeQuarterRoot
  apply Real.sqrt_le_sqrt
  exact mul_le_mul hxy (Real.sqrt_le_sqrt hxy) (Real.sqrt_nonneg _)
    (hx.trans hxy)

/-- Set-independent KST majorant for one ordered block. -/
noncomputable def universalBlockKSTBound (n i j : ℕ) : ℝ :=
  let T := ((blockCoreCandidates n i j).card : ℝ)
  let M := ((dyadicPrimeBlock i).card : ℝ)
  let N := ((dyadicPrimeBlock j).card : ℝ)
  2 * T * N + 2 * T * M * Real.sqrt N + 2 * threeQuarterRoot T * M * N

/-- The logarithmically bounded triangle containing every canonical block. -/
def triangularBlockIndices (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (Nat.log 2 n + 1)).product
    (Finset.range (Nat.log 2 n + 1))).filter fun ij ↦ ij.1 ≤ ij.2

@[simp] theorem mem_triangularBlockIndices {n i j : ℕ} :
    (i, j) ∈ triangularBlockIndices n ↔
      i < Nat.log 2 n + 1 ∧ j < Nat.log 2 n + 1 ∧ i ≤ j := by
  simp [triangularBlockIndices, and_assoc]

theorem triangularBlockIndices_mono {n m : ℕ} (hnm : n ≤ m) :
    triangularBlockIndices n ⊆ triangularBlockIndices m := by
  intro ij hij
  have h := mem_triangularBlockIndices.mp hij
  have hlog : Nat.log 2 n ≤ Nat.log 2 m := Nat.log_mono_right hnm
  exact mem_triangularBlockIndices.mpr ⟨by omega, by omega, h.2.2⟩

/-- The linear-in-`T` contribution `2 T N`. -/
noncomputable def universalCoreTerm (n : ℕ) : ℝ :=
  ∑ ij ∈ triangularBlockIndices n,
    2 * ((blockCoreCandidates n ij.1 ij.2).card : ℝ) *
      (dyadicPrimeBlock ij.2).card

/-- The mixed contribution `2 T M sqrt N`. -/
noncomputable def universalSmoothCoreTerm (n : ℕ) : ℝ :=
  ∑ ij ∈ triangularBlockIndices n,
    2 * ((blockCoreCandidates n ij.1 ij.2).card : ℝ) *
      (dyadicPrimeBlock ij.1).card *
        Real.sqrt ((dyadicPrimeBlock ij.2).card : ℝ)

/-- The three-quarter-root contribution `2 T^(3/4) M N`. -/
noncomputable def universalRectangleTerm (n : ℕ) : ℝ :=
  ∑ ij ∈ triangularBlockIndices n,
    2 * threeQuarterRoot ((blockCoreCandidates n ij.1 ij.2).card : ℝ) *
      (dyadicPrimeBlock ij.1).card * (dyadicPrimeBlock ij.2).card

noncomputable def universalNonexceptionalTerm (n : ℕ) : ℝ :=
  universalCoreTerm n + universalSmoothCoreTerm n + universalRectangleTerm n

theorem sum_universalBlockKSTBound_eq (n : ℕ) :
    (∑ ij ∈ triangularBlockIndices n,
      universalBlockKSTBound n ij.1 ij.2) = universalNonexceptionalTerm n := by
  simp only [universalBlockKSTBound, universalNonexceptionalTerm,
    universalCoreTerm, universalSmoothCoreTerm, universalRectangleTerm]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

theorem universalBlockKSTBound_nonneg (n i j : ℕ) :
    0 ≤ universalBlockKSTBound n i j := by
  unfold universalBlockKSTBound
  dsimp
  have hroot : 0 ≤ threeQuarterRoot
      ((blockCoreCandidates n i j).card : ℝ) := Real.sqrt_nonneg _
  positivity

theorem universalCoreTerm_nonneg (n : ℕ) : 0 ≤ universalCoreTerm n := by
  exact Finset.sum_nonneg fun ij hij ↦
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem universalSmoothCoreTerm_nonneg (n : ℕ) :
    0 ≤ universalSmoothCoreTerm n := by
  exact Finset.sum_nonneg fun ij hij ↦
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _))
      (Real.sqrt_nonneg _)

theorem universalRectangleTerm_nonneg (n : ℕ) :
    0 ≤ universalRectangleTerm n := by
  exact Finset.sum_nonneg fun ij hij ↦
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)

theorem monotone_universalCoreTerm : Monotone universalCoreTerm := by
  intro n m hnm
  unfold universalCoreTerm
  calc
    (∑ ij ∈ triangularBlockIndices n,
        2 * ((blockCoreCandidates n ij.1 ij.2).card : ℝ) *
          (dyadicPrimeBlock ij.2).card) ≤
        ∑ ij ∈ triangularBlockIndices n,
          2 * ((blockCoreCandidates m ij.1 ij.2).card : ℝ) *
            (dyadicPrimeBlock ij.2).card := by
      apply Finset.sum_le_sum
      intro ij hij
      have hcard := Finset.card_le_card
        (blockCoreCandidates_mono (i := ij.1) (j := ij.2) hnm)
      have hcardR : ((blockCoreCandidates n ij.1 ij.2).card : ℝ) ≤
          (blockCoreCandidates m ij.1 ij.2).card := by exact_mod_cast hcard
      gcongr
    _ ≤ ∑ ij ∈ triangularBlockIndices m,
          2 * ((blockCoreCandidates m ij.1 ij.2).card : ℝ) *
            (dyadicPrimeBlock ij.2).card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (triangularBlockIndices_mono hnm)
      intro ij hij hnot
      positivity

theorem monotone_universalSmoothCoreTerm : Monotone universalSmoothCoreTerm := by
  intro n m hnm
  unfold universalSmoothCoreTerm
  calc
    (∑ ij ∈ triangularBlockIndices n,
        2 * ((blockCoreCandidates n ij.1 ij.2).card : ℝ) *
          (dyadicPrimeBlock ij.1).card *
            Real.sqrt ((dyadicPrimeBlock ij.2).card : ℝ)) ≤
        ∑ ij ∈ triangularBlockIndices n,
          2 * ((blockCoreCandidates m ij.1 ij.2).card : ℝ) *
            (dyadicPrimeBlock ij.1).card *
              Real.sqrt ((dyadicPrimeBlock ij.2).card : ℝ) := by
      apply Finset.sum_le_sum
      intro ij hij
      have hcard := Finset.card_le_card
        (blockCoreCandidates_mono (i := ij.1) (j := ij.2) hnm)
      have hcardR : ((blockCoreCandidates n ij.1 ij.2).card : ℝ) ≤
          (blockCoreCandidates m ij.1 ij.2).card := by exact_mod_cast hcard
      gcongr
    _ ≤ ∑ ij ∈ triangularBlockIndices m,
          2 * ((blockCoreCandidates m ij.1 ij.2).card : ℝ) *
            (dyadicPrimeBlock ij.1).card *
              Real.sqrt ((dyadicPrimeBlock ij.2).card : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (triangularBlockIndices_mono hnm)
      intro ij hij hnot
      positivity

theorem monotone_universalRectangleTerm : Monotone universalRectangleTerm := by
  intro n m hnm
  unfold universalRectangleTerm
  calc
    (∑ ij ∈ triangularBlockIndices n,
        2 * threeQuarterRoot
            ((blockCoreCandidates n ij.1 ij.2).card : ℝ) *
          (dyadicPrimeBlock ij.1).card * (dyadicPrimeBlock ij.2).card) ≤
        ∑ ij ∈ triangularBlockIndices n,
          2 * threeQuarterRoot
              ((blockCoreCandidates m ij.1 ij.2).card : ℝ) *
            (dyadicPrimeBlock ij.1).card * (dyadicPrimeBlock ij.2).card := by
      apply Finset.sum_le_sum
      intro ij hij
      have hcard := Finset.card_le_card
        (blockCoreCandidates_mono (i := ij.1) (j := ij.2) hnm)
      have hcardR : ((blockCoreCandidates n ij.1 ij.2).card : ℝ) ≤
          (blockCoreCandidates m ij.1 ij.2).card := by exact_mod_cast hcard
      have hroot := threeQuarterRoot_mono (Nat.cast_nonneg _) hcardR
      gcongr
    _ ≤ ∑ ij ∈ triangularBlockIndices m,
          2 * threeQuarterRoot
              ((blockCoreCandidates m ij.1 ij.2).card : ℝ) *
            (dyadicPrimeBlock ij.1).card * (dyadicPrimeBlock ij.2).card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (triangularBlockIndices_mono hnm)
      intro ij hij hnot
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)

end Erdos888
