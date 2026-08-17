/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos175.VaughanFourSums

/-!
# Product expansions for the two Type-II Vaughan terms

This module is separate from `VaughanFourSums` so the basic four-piece
identity and the Type-I development do not depend on these further
reindexings.
-/

noncomputable section

namespace Erdos175.VaughanTypeIIExpansion

open scoped ArithmeticFunction BigOperators
open Vaughan VaughanFourSums

/-- Restrict an arithmetic function to indices at most `U`. -/
def truncateUpper (U : ℕ) (A : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then A n else 0, by simp⟩

/-- Truncating the first factor above `U` does not change a convolution at an
index `n ≤ U`. -/
theorem truncateUpper_mul_apply_of_le
    (U n : ℕ) (A B : ArithmeticFunction ℝ) (hn : n ≤ U) :
    (truncateUpper U A * B) n = (A * B) n := by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl fun ml hml => ?_
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hml).1
  have hlpos : 0 < ml.2 := Nat.pos_of_ne_zero
    (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hml)
  have hmle : ml.1 ≤ n := by
    have h := Nat.le_mul_of_pos_right ml.1 hlpos
    rwa [hprod] at h
  change (if ml.1 ≤ U then A ml.1 else 0) * B ml.2 = A ml.1 * B ml.2
  rw [if_pos (hmle.trans hn)]

/-- The finite product regrouping with the automatic upper cutoff `y'`. -/
theorem finiteWeightedSum_Ioc_mul_eq_outer_to_endpoint
    (y y' : ℕ) (w : ℕ → ℂ) (A B : ArithmeticFunction ℝ) :
    finiteWeightedSum (Finset.Ioc y y') w (A * B) =
      ∑ m ∈ Finset.Icc 1 y', ∑ l ∈ Finset.Ioc (y / m) (y' / m),
        (A m : ℂ) * (B l : ℂ) * w (m * l) := by
  calc
    finiteWeightedSum (Finset.Ioc y y') w (A * B) =
        finiteWeightedSum (Finset.Ioc y y') w (truncateUpper y' A * B) := by
      unfold finiteWeightedSum
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [truncateUpper_mul_apply_of_le y' n A B (Finset.mem_Ioc.mp hn).2]
    _ = ∑ m ∈ Finset.Icc 1 y', ∑ l ∈ innerProductInterval y y' m,
          (truncateUpper y' A m : ℂ) * (B l : ℂ) * w (m * l) := by
      apply finiteWeightedSum_Ioc_mul_eq_outer
      intro m hm
      change (if m ≤ y' then A m else 0) = 0
      rw [if_neg (not_le.mpr hm)]
    _ = ∑ m ∈ Finset.Icc 1 y', ∑ l ∈ Finset.Ioc (y / m) (y' / m),
          (A m : ℂ) * (B l : ℂ) * w (m * l) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [innerProductInterval_eq_Ioc y y' m (Finset.mem_Icc.mp hm).1]
      change (∑ l ∈ Finset.Ioc (y / m) (y' / m),
          (((if m ≤ y' then A m else 0 : ℝ)) : ℂ) *
            (B l : ℂ) * w (m * l)) = _
      rw [if_pos (Finset.mem_Icc.mp hm).2]

/-- Lower-annular form of the endpoint regrouping. -/
theorem finiteWeightedSum_Ioc_mul_eq_outer_endpoint_Ioc
    (y y' L : ℕ) (w : ℕ → ℂ) (A B : ArithmeticFunction ℝ)
    (hBelow : ∀ m, m ≤ L → A m = 0) :
    finiteWeightedSum (Finset.Ioc y y') w (A * B) =
      ∑ m ∈ Finset.Ioc L y', ∑ l ∈ Finset.Ioc (y / m) (y' / m),
        (A m : ℂ) * (B l : ℂ) * w (m * l) := by
  rw [finiteWeightedSum_Ioc_mul_eq_outer_to_endpoint]
  symm
  refine Finset.sum_subset (M := ℂ) ?_ ?_
  · intro m hm
    have hm' := Finset.mem_Ioc.mp hm
    exact Finset.mem_Icc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) hm'.1, hm'.2⟩
  · intro m hmIcc hmnot
    have hmle : m ≤ L := by
      by_contra hnotle
      apply hmnot
      exact Finset.mem_Ioc.mpr ⟨lt_of_not_ge hnotle, (Finset.mem_Icc.mp hmIcc).2⟩
    simp [hBelow m hmle]

/-- Regroup a convolution whose first factor is supported on `(L,U]`. -/
theorem finiteWeightedSum_Ioc_mul_eq_outer_Ioc
    (y y' L U : ℕ) (w : ℕ → ℂ) (A B : ArithmeticFunction ℝ)
    (hAbove : ∀ m, U < m → A m = 0)
    (hBelow : ∀ m, m ≤ L → A m = 0) :
    finiteWeightedSum (Finset.Ioc y y') w (A * B) =
      ∑ m ∈ Finset.Ioc L U, ∑ l ∈ Finset.Ioc (y / m) (y' / m),
        (A m : ℂ) * (B l : ℂ) * w (m * l) := by
  rw [finiteWeightedSum_Ioc_mul_eq_outer y y' U w A B hAbove]
  have hconvert :
      (∑ m ∈ Finset.Icc 1 U, ∑ l ∈ innerProductInterval y y' m,
          (A m : ℂ) * (B l : ℂ) * w (m * l)) =
        ∑ m ∈ Finset.Icc 1 U, ∑ l ∈ Finset.Ioc (y / m) (y' / m),
          (A m : ℂ) * (B l : ℂ) * w (m * l) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [innerProductInterval_eq_Ioc y y' m (Finset.mem_Icc.mp hm).1]
  rw [hconvert]
  symm
  refine Finset.sum_subset (M := ℂ) ?_ ?_
  · intro m hm
    have hm' := Finset.mem_Ioc.mp hm
    exact Finset.mem_Icc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) hm'.1, hm'.2⟩
  · intro m hmIcc hmnot
    have hmle : m ≤ L := by
      by_contra hnotle
      apply hmnot
      exact Finset.mem_Ioc.mpr ⟨lt_of_not_ge hnotle, (Finset.mem_Icc.mp hmIcc).2⟩
    simp [hBelow m hmle]

/-- Exact outer-sum expansion of the paper's `Σ₂,₂`. -/
theorem sigma22_Ioc_eq_outer
    (y y' M K : ℕ) (w : ℕ → ℂ) :
    sigma22 (Finset.Ioc y y') w M K =
      ∑ r ∈ Finset.Ioc M (M * K), ∑ l ∈ Finset.Ioc (y / r) (y' / r),
        (bCoeff M K r : ℂ) * w (r * l) := by
  unfold sigma22 sigma22AF
  rw [mul_comm (ArithmeticFunction.zeta : ArithmeticFunction ℝ) (bHigh M K)]
  rw [finiteWeightedSum_Ioc_mul_eq_outer_Ioc]
  · refine Finset.sum_congr rfl fun r hr => ?_
    refine Finset.sum_congr rfl fun l hl => ?_
    have hrgt := (Finset.mem_Ioc.mp hr).1
    have hlne : l ≠ 0 := Nat.ne_of_gt
      (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hl).1)
    change ((if M < r then bCoeff M K r else 0 : ℝ) : ℂ) *
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) l : ℂ) * w (r * l) = _
    rw [if_pos hrgt]
    simp [hlne]
  · intro r hr
    change (if M < r then bCoeff M K r else 0) = 0
    by_cases hMr : M < r
    · rw [if_pos hMr, bCoeff_eq_zero_of_mul_lt M K r hr]
    · rw [if_neg hMr]
  · intro r hr
    change (if M < r then bCoeff M K r else 0) = 0
    rw [if_neg (not_lt.mpr hr)]

/-- Exact outer-sum expansion of the paper's `Σ₃`. -/
theorem sigma3_Ioc_eq_outer
    (y y' M K : ℕ) (w : ℕ → ℂ) :
    sigma3 (Finset.Ioc y y') w M K =
      ∑ l ∈ Finset.Ioc M y',
        ∑ k ∈ Finset.Ioc (max K (y / l)) (y' / l),
          (aCoeff M l : ℂ) *
            (ArithmeticFunction.vonMangoldt k : ℂ) * w (k * l) := by
  unfold sigma3 sigma3AF
  rw [mul_comm (lambdaHigh K) (aHigh M)]
  rw [finiteWeightedSum_Ioc_mul_eq_outer_endpoint_Ioc]
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hlgt := (Finset.mem_Ioc.mp hl).1
    change ∑ k ∈ Finset.Ioc (y / l) (y' / l),
        ((if M < l then aCoeff M l else 0 : ℝ) : ℂ) *
          (lambdaHigh K k : ℂ) * w (l * k) = _
    rw [if_pos hlgt]
    have hset :
        (Finset.Ioc (y / l) (y' / l)).filter (fun k => K < k) =
          Finset.Ioc (max K (y / l)) (y' / l) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      omega
    rw [← hset, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _hk => ?_
    change (aCoeff M l : ℂ) *
        (((if K < k then ArithmeticFunction.vonMangoldt k else 0 : ℝ)) : ℂ) *
          w (l * k) =
        if K < k then
          (aCoeff M l : ℂ) *
            (ArithmeticFunction.vonMangoldt k : ℂ) * w (k * l)
        else 0
    by_cases hKk : K < k
    · simp [hKk, Nat.mul_comm]
    · simp [hKk]
  · intro l hl
    change (if M < l then aCoeff M l else 0) = 0
    rw [if_neg (not_lt.mpr hl)]

end Erdos175.VaughanTypeIIExpansion
