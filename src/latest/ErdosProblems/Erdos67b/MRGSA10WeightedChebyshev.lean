import ErdosProblems.Erdos48.BadRootMass
import Mathlib.NumberTheory.Chebyshev

/-!
# The weighted Chebyshev estimate in GS Lemma 2.4

The second secondary term is estimated by summing its distinguished
generalized-Mangoldt variable first.  This file records the exact elementary
input: uniformly for `0 ≤ alpha ≤ 1/2`, the partial sum of
`Λ(n) n⁻ᵅ` is `O(K^(1-α))`.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

noncomputable section

private theorem sum_vonMangoldt_subset_Icc_le
    {s : Finset ℕ} {K : ℕ} (hs : s ⊆ Finset.Icc 0 K) :
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n) ≤
      (Real.log 4 + 4) * (K : ℝ) := by
  calc
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n) ≤
        ∑ n ∈ Finset.Icc 0 K, ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hs
        (fun _ _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg)
    _ = Chebyshev.psi (K : ℝ) := by
      rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    _ ≤ (Real.log 4 + 4) * (K : ℝ) :=
      Chebyshev.psi_le_const_mul_self (by positivity)

private theorem weighted_vonMangoldt_shell_le
    {alpha : ℝ} (halpha0 : 0 ≤ alpha) (K j : ℕ)
    (hj : 1 ≤ j) :
    (∑ n ∈ Erdos48.badRootLogShell (Finset.Icc 2 K) j,
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-alpha)) ≤
      2 * (Real.log 4 + 4) *
        (((2 : ℝ) ^ (1 - alpha)) ^ j) := by
  let E := Erdos48.badRootLogShell (Finset.Icc 2 K) j
  have hpoint : ∀ n ∈ E,
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-alpha) ≤
        ((2 : ℝ) ^ j) ^ (-alpha) *
          ArithmeticFunction.vonMangoldt n := by
    intro n hn
    have hn' : n ∈ Erdos48.badRootLogShell (Finset.Icc 2 K) j := by
      simpa only [E] using hn
    have hnData := Finset.mem_filter.mp
      (show n ∈ (Finset.Icc 2 K).filter (fun q ↦ Nat.log 2 q = j) by
        simpa only [Erdos48.badRootLogShell] using hn')
    have hnBounds := Finset.mem_Icc.mp hnData.1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hpowNat : 2 ^ j ≤ n := by
      rw [← hnData.2]
      exact Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have hpowPos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hrpow : (n : ℝ) ^ (-alpha) ≤ ((2 : ℝ) ^ j) ^ (-alpha) := by
      exact Real.rpow_le_rpow_of_nonpos hpowPos
        (by exact_mod_cast hpowNat) (by linarith)
    calc
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-alpha) ≤
          ArithmeticFunction.vonMangoldt n * ((2 : ℝ) ^ j) ^ (-alpha) :=
        mul_le_mul_of_nonneg_left hrpow ArithmeticFunction.vonMangoldt_nonneg
      _ = _ := by ring
  calc
    (∑ n ∈ E, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-alpha)) ≤
        ∑ n ∈ E, ((2 : ℝ) ^ j) ^ (-alpha) *
          ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum fun n hn ↦ hpoint n hn
    _ = ((2 : ℝ) ^ j) ^ (-alpha) *
        (∑ n ∈ E, ArithmeticFunction.vonMangoldt n) := by
      rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) ^ j) ^ (-alpha) *
        ((Real.log 4 + 4) * ((2 ^ (j + 1) : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · apply sum_vonMangoldt_subset_Icc_le
        intro n hn
        have hnData := Finset.mem_filter.mp
          (show n ∈ (Finset.Icc 2 K).filter (fun q ↦ Nat.log 2 q = j) by
            simpa only [E, Erdos48.badRootLogShell] using hn)
        have hnUpper : n < 2 ^ (j + 1) := by
          rw [← hnData.2]
          exact Nat.lt_pow_succ_log_self (by omega) n
        exact Finset.mem_Icc.mpr ⟨by omega, hnUpper.le⟩
      · positivity
    _ = 2 * (Real.log 4 + 4) * (((2 : ℝ) ^ (1 - alpha)) ^ j) := by
      rw [show ((2 ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) by norm_cast,
        pow_succ]
      have hcombine :
          (((2 : ℝ) ^ j) ^ (-alpha)) * ((2 : ℝ) ^ j) =
            (((2 : ℝ) ^ (1 - alpha)) ^ j) := by
        calc
          (((2 : ℝ) ^ j) ^ (-alpha)) * ((2 : ℝ) ^ j) =
              ((2 : ℝ) ^ j) ^ (-alpha + 1) := by
            rw [Real.rpow_add (by positivity), Real.rpow_one]
          _ = ((2 : ℝ) ^ j) ^ (1 - alpha) := by ring_nf
          _ = (((2 : ℝ) ^ (1 - alpha)) ^ j) :=
            (Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)
              (1 - alpha) j).symm
      calc
        ((2 : ℝ) ^ j) ^ (-alpha) *
            ((Real.log 4 + 4) * ((2 : ℝ) ^ j * 2)) =
            2 * (Real.log 4 + 4) *
              ((((2 : ℝ) ^ j) ^ (-alpha)) * ((2 : ℝ) ^ j)) := by ring
        _ = _ := by rw [hcombine]

private theorem sum_geometric_Icc_le_six_last
    {b : ℝ} (hbLower : (4 : ℝ) / 3 ≤ b) (hbUpper : b ≤ 2) (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M, b ^ j) ≤ 6 * b ^ M := by
  have hb1 : 1 < b := by linarith
  have hb0 : 0 ≤ b := le_trans (by norm_num) hbLower
  calc
    (∑ j ∈ Finset.Icc 1 M, b ^ j) ≤ ∑ j ∈ Finset.range (M + 1), b ^ j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        rw [Finset.mem_range]
        have := Finset.mem_Icc.mp hj
        omega
      · intro j _ _
        positivity
    _ = (b ^ (M + 1) - 1) / (b - 1) := by
      rw [geom_sum_eq (ne_of_gt hb1)]
    _ ≤ b ^ (M + 1) / (b - 1) := by
      apply div_le_div_of_nonneg_right (by linarith) (by linarith)
    _ ≤ 3 * b ^ (M + 1) := by
      rw [div_le_iff₀ (by linarith : 0 < b - 1)]
      nlinarith [pow_nonneg hb0 (M + 1)]
    _ ≤ 6 * b ^ M := by
      rw [pow_succ]
      nlinarith [pow_nonneg hb0 M]

/-- Weighted Chebyshev, in the exact range needed after the source choice
`alpha ∈ [0, 1 / log y]` with `y ≥ 10`. -/
theorem sum_vonMangoldt_mul_rpow_neg_le
    {K : ℕ} {alpha : ℝ} (hK : 2 ≤ K)
    (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2) :
    (∑ n ∈ Finset.Icc 1 K,
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-alpha)) ≤
      12 * (Real.log 4 + 4) * (K : ℝ) ^ (1 - alpha) := by
  classical
  let E : Finset ℕ := Finset.Icc 2 K
  let M : ℕ := Nat.log 2 K
  let b : ℝ := (2 : ℝ) ^ (1 - alpha)
  have hE : ∀ n ∈ E, 2 ≤ n ∧ n ≤ K := fun n hn ↦ Finset.mem_Icc.mp hn
  have hremoveOne :
      (∑ n ∈ Finset.Icc 1 K,
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-alpha)) =
        ∑ n ∈ E, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-alpha) := by
    rw [show Finset.Icc 1 K = insert 1 E by
      ext n
      simp only [E, Finset.mem_Icc, Finset.mem_insert]
      omega]
    rw [Finset.sum_insert]
    · simp
    · simp [E]
  have hbLower : (4 : ℝ) / 3 ≤ b := by
    dsimp only [b]
    calc
      (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
        rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 3)
          (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
      _ ≤ (2 : ℝ) ^ (1 - alpha) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
  have hbUpper : b ≤ 2 := by
    dsimp only [b]
    calc
      (2 : ℝ) ^ (1 - alpha) ≤ (2 : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
      _ = 2 := by simp
  have hpowMK : ((2 : ℝ) ^ M) ^ (1 - alpha) ≤
      (K : ℝ) ^ (1 - alpha) := by
    apply Real.rpow_le_rpow (by positivity)
    · exact_mod_cast Nat.pow_log_le_self 2 (by omega : K ≠ 0)
    · linarith
  rw [hremoveOne, ← Erdos48.biUnion_badRootLogShell hE,
    Finset.sum_biUnion (Erdos48.pairwiseDisjoint_badRootLogShell E M)]
  calc
    (∑ j ∈ Finset.Icc 1 M,
        ∑ n ∈ Erdos48.badRootLogShell E j,
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-alpha)) ≤
        ∑ j ∈ Finset.Icc 1 M,
          2 * (Real.log 4 + 4) * b ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      exact weighted_vonMangoldt_shell_le halpha0 K j
        (Finset.mem_Icc.mp hj).1
    _ = 2 * (Real.log 4 + 4) *
        (∑ j ∈ Finset.Icc 1 M, b ^ j) := by rw [Finset.mul_sum]
    _ ≤ 2 * (Real.log 4 + 4) * (6 * b ^ M) := by
      apply mul_le_mul_of_nonneg_left
      · exact sum_geometric_Icc_le_six_last hbLower hbUpper M
      · positivity
    _ = 12 * (Real.log 4 + 4) * (((2 : ℝ) ^ M) ^ (1 - alpha)) := by
      dsimp only [b]
      rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ ≤ 12 * (Real.log 4 + 4) * (K : ℝ) ^ (1 - alpha) := by
      exact mul_le_mul_of_nonneg_left hpowMK (by positivity)

/-- Weighted Chebyshev up to the critical exponent.  As the exponent tends
to one, the geometric ratio tends to one as well; retaining the number of
dyadic shells gives the source-appropriate additional `log K` factor. -/
theorem sum_vonMangoldt_mul_rpow_neg_le_one
    {K : ℕ} {alpha : ℝ} (hK : 2 ≤ K)
    (halpha0 : 0 ≤ alpha) (halphaOne : alpha ≤ 1) :
    (∑ n ∈ Finset.Icc 1 K,
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-alpha)) ≤
      2 * (Real.log 4 + 4) * (Nat.log 2 K : ℝ) *
        (K : ℝ) ^ (1 - alpha) := by
  classical
  let E : Finset ℕ := Finset.Icc 2 K
  let M : ℕ := Nat.log 2 K
  let b : ℝ := (2 : ℝ) ^ (1 - alpha)
  have hE : ∀ n ∈ E, 2 ≤ n ∧ n ≤ K := fun n hn ↦ Finset.mem_Icc.mp hn
  have hremoveOne :
      (∑ n ∈ Finset.Icc 1 K,
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-alpha)) =
        ∑ n ∈ E, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-alpha) := by
    rw [show Finset.Icc 1 K = insert 1 E by
      ext n
      simp only [E, Finset.mem_Icc, Finset.mem_insert]
      omega]
    rw [Finset.sum_insert]
    · simp
    · simp [E]
  have hbOne : 1 ≤ b := by
    dsimp only [b]
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith : 0 ≤ 1 - alpha)
  have hpowMK : ((2 : ℝ) ^ M) ^ (1 - alpha) ≤
      (K : ℝ) ^ (1 - alpha) := by
    apply Real.rpow_le_rpow (by positivity)
    · exact_mod_cast Nat.pow_log_le_self 2 (by omega : K ≠ 0)
    · linarith
  have hpowShell : ∀ j ∈ Finset.Icc 1 M, b ^ j ≤ b ^ M := by
    intro j hj
    exact pow_le_pow_right₀ hbOne (Finset.mem_Icc.mp hj).2
  rw [hremoveOne, ← Erdos48.biUnion_badRootLogShell hE,
    Finset.sum_biUnion (Erdos48.pairwiseDisjoint_badRootLogShell E M)]
  calc
    (∑ j ∈ Finset.Icc 1 M,
        ∑ n ∈ Erdos48.badRootLogShell E j,
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-alpha)) ≤
        ∑ j ∈ Finset.Icc 1 M,
          2 * (Real.log 4 + 4) * b ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      exact weighted_vonMangoldt_shell_le halpha0 K j
        (Finset.mem_Icc.mp hj).1
    _ ≤ ∑ _j ∈ Finset.Icc 1 M,
          2 * (Real.log 4 + 4) * b ^ M := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hpowShell j hj) (by positivity)
    _ = 2 * (Real.log 4 + 4) * (M : ℝ) * b ^ M := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.Icc 1 M).card = M := by simp
      rw [hcard]
      ring
    _ = 2 * (Real.log 4 + 4) * (M : ℝ) *
        (((2 : ℝ) ^ M) ^ (1 - alpha)) := by
      dsimp only [b]
      rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (Real.log 4 + 4) * (M : ℝ) *
        (K : ℝ) ^ (1 - alpha) := by
      exact mul_le_mul_of_nonneg_left hpowMK (by positivity)

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.sum_vonMangoldt_mul_rpow_neg_le
#print axioms Erdos67b.MRHalaszBands.sum_vonMangoldt_mul_rpow_neg_le_one
