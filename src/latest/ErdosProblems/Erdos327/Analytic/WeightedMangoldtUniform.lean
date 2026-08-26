import ErdosProblems.Erdos327.Analytic.WeightedMangoldt

/-!
# Uniform weighted Mangoldt constant

The cutoff weights used in the maximal-tail argument vary with `L` and
`X`.  This file replaces the weight-dependent prime-power tail constant
by a single dominating weight, so the Halberstam--Richert estimate is
uniform over every local weight in the permitted range.
-/

namespace Erdos327.Analytic

open Finset Real

/-- Pointwise maximal local weight allowed by the weighted Mangoldt
argument: one at `2`, and `5/2` at every other prime. -/
noncomputable def maximalPrimeWeight (p : ℕ) : ℝ :=
  if p = 2 then 1 else 5 / 2

theorem maximalPrimeWeight_nonneg (p : ℕ) :
    0 ≤ maximalPrimeWeight p := by
  unfold maximalPrimeWeight
  split <;> norm_num

theorem maximalPrimeWeight_le_five_halves (p : ℕ) :
    maximalPrimeWeight p ≤ 5 / 2 := by
  unfold maximalPrimeWeight
  split <;> norm_num

@[simp] theorem maximalPrimeWeight_two :
    maximalPrimeWeight 2 = 1 := by
  simp [maximalPrimeWeight]

/-- Prime-factor products are monotone in their nonnegative local
weights. -/
theorem factorWeight_mono
    {w v : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hwv : ∀ p, w p ≤ v p) (n : ℕ) :
    factorWeight w n ≤ factorWeight v n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [factorWeight_apply hn, factorWeight_apply hn]
  induction n.primeFactorsList with
  | nil => simp
  | cons p l ih =>
      simp only [List.map_cons, List.prod_cons]
      have hwProd0 : 0 ≤ (l.map w).prod := by
        apply List.prod_nonneg
        intro x hx
        rcases List.mem_map.mp hx with ⟨r, _hr, rfl⟩
        exact hw0 r
      have hvp0 : 0 ≤ v p := (hw0 p).trans (hwv p)
      exact mul_le_mul (hwv p) ih hwProd0 hvp0

/-- The normalized non-prime Mangoldt term is monotone in the local
prime weights. -/
theorem weightedNonprimeMangoldtTerm_mono
    {w v : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hwv : ∀ p, w p ≤ v p) (n : ℕ) :
    weightedNonprimeMangoldtTerm w n ≤
      weightedNonprimeMangoldtTerm v n := by
  unfold weightedNonprimeMangoldtTerm
  split_ifs
  · exact le_rfl
  · have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (factorWeight_mono hw0 hwv n) hΛ0) hn0

/-- Any permitted local weight is bounded by `maximalPrimeWeight`. -/
theorem le_maximalPrimeWeight
    {w : ℕ → ℝ} (hw : ∀ p, w p ≤ 5 / 2)
    (hw2 : w 2 ≤ 1) (p : ℕ) :
    w p ≤ maximalPrimeWeight p := by
  by_cases hp : p = 2
  · subst p
    simpa using hw2
  · simp [maximalPrimeWeight, hp, hw p]

/-- The weight-dependent prime-power tail is bounded by one fixed tail
constant. -/
theorem weightedMangoldtTailConstant_le_maximal
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, w p ≤ 5 / 2) (hw2 : w 2 ≤ 1) :
    weightedMangoldtTailConstant w ≤
      weightedMangoldtTailConstant maximalPrimeWeight := by
  unfold weightedMangoldtTailConstant
  exact (summable_weightedNonprimeMangoldtTerm hw0 hw hw2).tsum_le_tsum
    (fun n ↦ weightedNonprimeMangoldtTerm_mono hw0
      (le_maximalPrimeWeight hw hw2) n)
    (summable_weightedNonprimeMangoldtTerm
      maximalPrimeWeight_nonneg maximalPrimeWeight_le_five_halves
      (by simp))

/-- A single finite constant valid for every cutoff weight used in the
proof. -/
noncomputable def uniformWeightedMangoldtConstant : ℝ :=
  weightedMangoldtConstant maximalPrimeWeight

theorem uniformWeightedMangoldtConstant_nonneg :
    0 ≤ uniformWeightedMangoldtConstant := by
  unfold uniformWeightedMangoldtConstant
  exact weightedMangoldtConstant_nonneg maximalPrimeWeight_nonneg

theorem weightedMangoldtConstant_le_uniform
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, w p ≤ 5 / 2) (hw2 : w 2 ≤ 1) :
    weightedMangoldtConstant w ≤ uniformWeightedMangoldtConstant := by
  unfold uniformWeightedMangoldtConstant
  unfold weightedMangoldtConstant
  linarith [weightedMangoldtTailConstant_le_maximal hw0 hw hw2]

/-- Uniform weighted von Mangoldt moment. -/
theorem factorWeight_vonMangoldt_le_uniform
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, w p ≤ 5 / 2) (hw2 : w 2 ≤ 1)
    (X : ℕ) :
    (∑ d ∈ Icc 1 X,
      factorWeight w d * ArithmeticFunction.vonMangoldt d) ≤
        uniformWeightedMangoldtConstant * X := by
  calc
    (∑ d ∈ Icc 1 X,
        factorWeight w d * ArithmeticFunction.vonMangoldt d) ≤
      weightedMangoldtConstant w * X :=
        factorWeight_vonMangoldt_le_five_halves hw0 hw hw2 X
    _ ≤ uniformWeightedMangoldtConstant * X := by
      exact mul_le_mul_of_nonneg_right
        (weightedMangoldtConstant_le_uniform hw0 hw hw2)
        (Nat.cast_nonneg X)

/-- Uniform finite-Euler-product Halberstam--Richert estimate for every
local weight in the permitted range. -/
theorem factorWeight_partialSum_le_eulerProduct_uniform
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, w p ≤ 5 / 2) (hw2 : w 2 ≤ 1)
    {Y : ℕ} (hY : 2 ≤ Y) :
    partialSum (factorWeight w) Y ≤
      ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
        Y.factorial.factorization.prod (fun p e ↦
          ∑ k ∈ range (e + 1), ((w p) / p) ^ k) := by
  have h := partialSum_le_eulerProduct
    (g := factorWeight w) (C := uniformWeightedMangoldtConstant)
    (factorWeight_nonneg hw0)
    (factorWeight_one w)
    (factorWeight_isMultiplicative w).2
    factorWeight_submultiplicative
    uniformWeightedMangoldtConstant_nonneg
    (factorWeight_vonMangoldt_le_uniform hw0 hw hw2)
    hY
  rw [factorWeight_eulerProduct_eq] at h
  exact h

end Erdos327.Analytic
