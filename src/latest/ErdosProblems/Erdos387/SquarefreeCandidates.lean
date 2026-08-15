/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RefinedErrorCounting
import Mathlib.Analysis.PSeries

/-!
# Removing the negligible nonsquarefree residual candidates

The analytic Kloosterman arguments may be restricted to candidates for which
every residual factor is squarefree.  A failure is witnessed by a prime
square dividing one of the `k` shifted numerator terms; this file records the
finite union bound that starts that reduction.
-/

namespace Erdos387

open scoped BigOperators

namespace CoverBPZ

/-- Refined sifted candidates whose individual cover quotients are all
squarefree. -/
noncomputable def RefinedSquarefreeCandidates {B K : ℕ}
    (S : BPZSection6Input B K) (X z : ℕ) : Finset ℕ := by
  classical
  exact (RefinedSiftedCandidates S X z).filter fun n =>
    ∀ i : Fin S.k, Squarefree ((n - i) / S.g i)

/-- The complementary exceptional subset. -/
noncomputable def RefinedNonSquarefreeCandidates {B K : ℕ}
    (S : BPZSection6Input B K) (X z : ℕ) : Finset ℕ := by
  classical
  exact (RefinedSiftedCandidates S X z).filter fun n =>
    ¬∀ i : Fin S.k, Squarefree ((n - i) / S.g i)

theorem refinedSiftedCandidates_eq_squarefree_union_nonSquarefree
    {B K X z : ℕ} (S : BPZSection6Input B K) :
    RefinedSiftedCandidates S X z =
      RefinedSquarefreeCandidates S X z ∪
        RefinedNonSquarefreeCandidates S X z := by
  classical
  ext n
  simp only [RefinedSquarefreeCandidates, RefinedNonSquarefreeCandidates,
    Finset.mem_union, Finset.mem_filter]
  tauto

theorem disjoint_refinedSquarefree_nonSquarefree
    {B K X z : ℕ} (S : BPZSection6Input B K) :
    Disjoint (RefinedSquarefreeCandidates S X z)
      (RefinedNonSquarefreeCandidates S X z) := by
  classical
  rw [Finset.disjoint_left]
  intro n hnSq hnNon
  rw [RefinedSquarefreeCandidates, Finset.mem_filter] at hnSq
  rw [RefinedNonSquarefreeCandidates, Finset.mem_filter] at hnNon
  exact hnNon.2 hnSq.2

/-- One residue class in the ambient initial interval on which `p²` divides
the shifted term `n-i`. -/
def squareDivisorClass (X i p : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter fun n => n ≡ i [MOD p ^ 2]

/-- Union of all possible prime-square witnesses in the relevant ranges. -/
noncomputable def squareDivisorWitnessUnion (X k z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range k).biUnion fun i =>
    (Finset.Icc z (Nat.sqrt X)).biUnion fun p => squareDivisorClass X i p

/-- Every nonsquarefree refined candidate has a prime-square witness in one
of its shifted numerator terms. -/
theorem refinedNonSquarefreeCandidates_subset_witnessUnion
    {B K X z : ℕ} (S : BPZSection6Input B K) :
    RefinedNonSquarefreeCandidates S X z ⊆
      squareDivisorWitnessUnion X S.k z := by
  classical
  intro n hnNon
  rw [RefinedNonSquarefreeCandidates, Finset.mem_filter] at hnNon
  obtain ⟨hnS, hnNotSquarefree⟩ := hnNon
  have hnData := hnS
  rw [RefinedSiftedCandidates, Finset.mem_filter,
    mem_RefinedBaseCandidates] at hnData
  obtain ⟨⟨hnWindow, hn, hnRefined⟩, hrough⟩ := hnData
  push Not at hnNotSquarefree
  obtain ⟨i, hiNotSquarefree⟩ := hnNotSquarefree
  rw [Nat.squarefree_iff_prime_squarefree] at hiNotSquarefree
  push Not at hiNotSquarefree
  obtain ⟨p, hpPrime, hpSq⟩ := hiNotSquarefree
  have hprog := refinement_progression_implies_public S hnRefined
  let D := S.toCoverFactorization hn hprog
  have hpDvdQuotient : p ∣ (n - i) / S.g i := by
    exact (dvd_mul_right p p).trans hpSq
  have hpDvdChoose : p ∣ n.choose S.k := by
    have hqDvd : (n - i) / S.g i ∣ n.choose S.k := by
      simpa only [D, BPZSection6Input.toCoverFactorization,
        S.gNat_eq i.isLt] using
        coverQuotient_dvd_choose D i.isLt
    exact hpDvdQuotient.trans hqDvd
  have hpLower : z ≤ p := by
    by_contra hpz
    exact hrough p hpPrime (by omega) hpDvdChoose
  have hpSqDvdTerm : p ^ 2 ∣ n - i := by
    have hqDvd : (n - i) / S.g i ∣ n - i := by
      simpa only [D, BPZSection6Input.toCoverFactorization,
        S.gNat_eq i.isLt] using
        coverQuotient_dvd_term D i.isLt
    simpa [pow_two] using hpSq.trans hqDvd
  have hiN : (i : ℕ) ≤ n := by
    exact le_trans i.isLt.le hn.le
  have htermPos : 0 < n - i := Nat.sub_pos_of_lt (lt_of_lt_of_le i.isLt hn.le)
  have hpSqLeX : p ^ 2 ≤ X :=
    (Nat.le_of_dvd htermPos hpSqDvdTerm).trans
      ((Nat.sub_le n i).trans (Finset.mem_Ioc.mp hnWindow).2)
  have hpUpper : p ≤ Nat.sqrt X := by
    rw [Nat.le_sqrt']
    simpa [pow_two] using hpSqLeX
  rw [squareDivisorWitnessUnion, Finset.mem_biUnion]
  refine ⟨i, Finset.mem_range.mpr i.isLt, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨p, Finset.mem_Icc.mpr ⟨hpLower, hpUpper⟩, ?_⟩
  rw [squareDivisorClass, Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (by
      have hnX := (Finset.mem_Ioc.mp hnWindow).2
      omega),
    (Nat.modEq_iff_dvd' hiN).mpr hpSqDvdTerm |>.symm⟩

/-- A single square-divisor congruence class has at most one incomplete
endpoint beyond its complete blocks. -/
theorem card_squareDivisorClass_le
    {X i p : ℕ} (hp : 0 < p) :
    (squareDivisorClass X i p).card ≤ (X + 1) / p ^ 2 + 1 := by
  unfold squareDivisorClass
  rw [← Nat.count_eq_card_filter_range]
  rw [Nat.count_modEq_card (X + 1) (pow_pos hp 2) i]
  split <;> omega

/-- Finite union bound before estimating the inverse-square tail. -/
theorem card_squareDivisorWitnessUnion_le
    {X k z : ℕ} (hz : 0 < z) :
    (squareDivisorWitnessUnion X k z).card ≤
      ∑ _i ∈ Finset.range k, ∑ p ∈ Finset.Icc z (Nat.sqrt X),
        ((X + 1) / p ^ 2 + 1) := by
  classical
  unfold squareDivisorWitnessUnion
  calc
    ((Finset.range k).biUnion fun i =>
        (Finset.Icc z (Nat.sqrt X)).biUnion fun p =>
          squareDivisorClass X i p).card ≤
      ∑ i ∈ Finset.range k,
        ((Finset.Icc z (Nat.sqrt X)).biUnion fun p =>
          squareDivisorClass X i p).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range k,
        ∑ p ∈ Finset.Icc z (Nat.sqrt X),
          (squareDivisorClass X _i p).card := by
      apply Finset.sum_le_sum
      intro i _hi
      exact Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range k,
        ∑ p ∈ Finset.Icc z (Nat.sqrt X),
          ((X + 1) / p ^ 2 + 1) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro p hpMem
      exact card_squareDivisorClass_le (lt_of_lt_of_le hz
        (Finset.mem_Icc.mp hpMem).1)

/-- The elementary inverse-square tail in precisely the finite interval used
by the square-divisor witnesses. -/
theorem sum_Icc_inv_sq_le_two_div
    {z R : ℕ} (hz : 0 < z) :
    (∑ p ∈ Finset.Icc z R, ((p : ℝ) ^ 2)⁻¹) ≤ 2 / (z : ℝ) := by
  have hinterval : Finset.Icc z R = Finset.Ioo (z - 1) (R + 1) := by
    ext p
    simp only [Finset.mem_Icc, Finset.mem_Ioo]
    omega
  rw [hinterval]
  calc
    (∑ p ∈ Finset.Ioo (z - 1) (R + 1), ((p : ℝ) ^ 2)⁻¹) ≤
        2 / (((z - 1 : ℕ) : ℝ) + 1) :=
      sum_Ioo_inv_sq_le (α := ℝ) (z - 1) (R + 1)
    _ = 2 / (z : ℝ) := by
      congr 1
      norm_cast
      omega

theorem card_Icc_le_succ_right (z R : ℕ) :
    (Finset.Icc z R).card ≤ R + 1 := by
  have hsub : Finset.Icc z R ⊆ Finset.range (R + 1) := by
    intro p hp
    exact Finset.mem_range.mpr (by
      have := (Finset.mem_Icc.mp hp).2
      omega)
  simpa using Finset.card_le_card hsub

/-- Quantitative squarefree-exception estimate.  No prime counting is used:
the full inverse-square tail is already small enough. -/
theorem card_refinedNonSquarefreeCandidates_real_le
    {B K X z : ℕ} (S : BPZSection6Input B K) (hz : 0 < z) :
    ((RefinedNonSquarefreeCandidates S X z).card : ℝ) ≤
      (S.k : ℝ) *
        (((X + 1 : ℕ) : ℝ) * (2 / (z : ℝ)) +
          (Nat.sqrt X + 1 : ℕ)) := by
  have hsubset := refinedNonSquarefreeCandidates_subset_witnessUnion
    (X := X) (z := z) S
  have hcardSubset :
      (RefinedNonSquarefreeCandidates S X z).card ≤
        (squareDivisorWitnessUnion X S.k z).card :=
    Finset.card_le_card hsubset
  have hunion := card_squareDivisorWitnessUnion_le
    (X := X) (k := S.k) hz
  have hnat := hcardSubset.trans hunion
  calc
    ((RefinedNonSquarefreeCandidates S X z).card : ℝ) ≤
        ∑ _i ∈ Finset.range S.k,
          ∑ p ∈ Finset.Icc z (Nat.sqrt X),
            ((((X + 1) / p ^ 2 + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hnat
    _ ≤ ∑ _i ∈ Finset.range S.k,
          ∑ p ∈ Finset.Icc z (Nat.sqrt X),
            ((((X + 1 : ℕ) : ℝ) / (p : ℝ) ^ 2) + 1) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro p _hp
      have hdiv :
          ((((X + 1) / p ^ 2 : ℕ) : ℝ)) ≤
            (((X + 1 : ℕ) : ℝ) / ((p ^ 2 : ℕ) : ℝ)) :=
        Nat.cast_div_le
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] using
        add_le_add_left hdiv (1 : ℝ)
    _ = (S.k : ℝ) *
          ∑ p ∈ Finset.Icc z (Nat.sqrt X),
            ((((X + 1 : ℕ) : ℝ) / (p : ℝ) ^ 2) + 1) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (S.k : ℝ) *
          ((((X + 1 : ℕ) : ℝ) *
              ∑ p ∈ Finset.Icc z (Nat.sqrt X), ((p : ℝ) ^ 2)⁻¹) +
            (Finset.Icc z (Nat.sqrt X)).card) := by
      congr 1
      rw [Finset.sum_add_distrib]
      simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_const,
        nsmul_eq_mul, mul_one]
    _ ≤ (S.k : ℝ) *
        (((X + 1 : ℕ) : ℝ) * (2 / (z : ℝ)) +
          (Nat.sqrt X + 1 : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (sum_Icc_inv_sq_le_two_div hz) (by positivity)
      · exact_mod_cast card_Icc_le_succ_right z (Nat.sqrt X)

end CoverBPZ

end Erdos387
