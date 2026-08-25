import ErdosProblems.Erdos964.ScalarCorrectionLocalBound
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries

/-!
# Absolute convergence of the scalar Euler corrections

The finite local absolute masses are bounded by `1+416/p²`. Smooth-number
Euler products therefore uniformly bound the ordinary absolute partial sums.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem arithmeticFunction_summable_abs_of_local_bound (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ p : ℕ, p.Prime → Summable (fun j : ℕ => |f (p ^ j)|))
    (hbound : ∀ p : ℕ, p.Prime → (∑' j : ℕ, |f (p ^ j)|) ≤ 1 + C / (p : ℝ) ^ 2) :
    Summable (fun n : ℕ => |f n|) := by
  let w : ℕ → ℝ := fun n => |f n|
  let A : ℝ := ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2
  have hseries : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hprod (N : ℕ) : (∏ p ∈ N.primesBelow, ∑' j : ℕ, w (p ^ j)) ≤ Real.exp (C * A) := by
    calc
      _ ≤ ∏ p ∈ N.primesBelow, (1 + C / (p : ℝ) ^ 2) := by
        apply Finset.prod_le_prod (fun p _ => tsum_nonneg (fun j => abs_nonneg _))
        intro p hp
        exact hbound p (Nat.prime_of_mem_primesBelow hp)
      _ ≤ Real.exp (∑ p ∈ N.primesBelow, C / (p : ℝ) ^ 2) :=
        Real.prod_one_add_le_exp_sum _ (fun p => by positivity)
      _ ≤ Real.exp (C * A) := by
        apply Real.exp_le_exp.mpr
        have hsum := hseries.sum_le_tsum N.primesBelow (fun _ _ => by positivity)
        calc
          _ = C * (∑ p ∈ N.primesBelow, (1 : ℝ) / (p : ℝ) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            ring
          _ ≤ C * A := mul_le_mul_of_nonneg_left hsum hC
  have hlocal' : ∀ {p : ℕ}, p.Prime → Summable (fun j : ℕ => ‖w (p ^ j)‖) := by
    intro p hp
    simpa only [w, Real.norm_eq_abs, abs_abs] using hlocal p hp
  apply summable_of_sum_range_le (c := Real.exp (C * A)) (fun n => abs_nonneg _)
  intro N
  have hEuler := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (show w 1 = 1 by dsimp only [w]; rw [hf.map_one, abs_one])
    (fun {m n} hmn => by
      dsimp only [w]
      rw [hf.map_mul_of_coprime hmn, abs_mul]) hlocal' N
  have hIndicator : Summable (N.smoothNumbers.indicator w) :=
    summable_subtype_iff_indicator.mp hEuler.2.summable
  calc
    _ = ∑ n ∈ Finset.range N, w n := rfl
    _ ≤ ∑ n ∈ Finset.range N, N.smoothNumbers.indicator w n := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn0 : n = 0
      · subst n
        rw [Set.indicator_of_notMem (fun h => (Nat.ne_zero_of_mem_smoothNumbers h) rfl)]
        simp only [w, ArithmeticFunction.map_zero, abs_zero, le_refl]
      · rw [Set.indicator_of_mem
          (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn0) (Finset.mem_range.mp hn))]
    _ ≤ ∑' n : ℕ, N.smoothNumbers.indicator w n := by
      apply hIndicator.sum_le_tsum
      intro n hn
      by_cases hmem : n ∈ N.smoothNumbers
      · rw [Set.indicator_of_mem hmem]
        exact abs_nonneg _
      · rw [Set.indicator_of_notMem hmem]
    _ = ∑' n : N.smoothNumbers, w n := (tsum_subtype N.smoothNumbers w).symm
    _ = ∏ p ∈ N.primesBelow, ∑' j : ℕ, w (p ^ j) := hEuler.2.tsum_eq
    _ ≤ Real.exp (C * A) := hprod N

theorem summable_abs_scalarMomentCorrectionAF (M k : ℕ) (hk : k ≤ 3)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) :
    Summable (fun n : ℕ => |scalarMomentCorrectionAF M k n|) := by
  apply arithmeticFunction_summable_abs_of_local_bound (scalarMomentCorrectionAF M k)
    (scalarMomentCorrectionAF_multiplicative M k) 416 (by norm_num)
  · intro p hp
    apply summable_of_ne_finset_zero (s := Finset.range (k + 2))
    intro j hj
    rw [scalarMomentCorrectionAF_prime_pow_eq_zero M k j hp
      (by simp only [Finset.mem_range] at hj; omega), abs_zero]
  · intro p hp
    exact scalarMomentCorrectionAF_local_abs_tsum_le M k hk h2M h3M hp

theorem scalarMomentCorrectionAF_tsum_two_eq_three (M : ℕ) (h2M : 2 ∣ M) (h3M : 3 ∣ M) :
    (∑' n : ℕ, scalarMomentCorrectionAF M 2 n) = ∑' n : ℕ, scalarMomentCorrectionAF M 3 n := by
  have hnorm (k : ℕ) (hk : k ≤ 3) : Summable (fun n : ℕ => ‖scalarMomentCorrectionAF M k n‖) := by
    simpa only [Real.norm_eq_abs] using summable_abs_scalarMomentCorrectionAF M k hk h2M h3M
  rw [← (scalarMomentCorrectionAF_multiplicative M 2).eulerProduct_tprod (hnorm 2 (by decide)),
    ← (scalarMomentCorrectionAF_multiplicative M 3).eulerProduct_tprod (hnorm 3 le_rfl)]
  apply tprod_congr
  intro p
  exact scalarMomentCorrectionAF_local_tsum_two_eq_three M h3M p.property

theorem scalarMomentCorrectionAF_tsum_three_ge_one (M : ℕ) (h2M : 2 ∣ M) (h3M : 3 ∣ M) :
    1 ≤ ∑' n : ℕ, scalarMomentCorrectionAF M 3 n := by
  have hnorm : Summable (fun n : ℕ => ‖scalarMomentCorrectionAF M 3 n‖) := by
    simpa only [Real.norm_eq_abs] using summable_abs_scalarMomentCorrectionAF M 3 le_rfl h2M h3M
  have hlimit := (scalarMomentCorrectionAF_multiplicative M 3).eulerProduct hnorm
  apply ge_of_tendsto hlimit
  exact Filter.Eventually.of_forall (fun N => Finset.one_le_prod (fun p hp =>
    scalarMomentCorrectionAF_local_tsum_three_ge_one M h2M h3M (Nat.prime_of_mem_primesBelow hp)))

end Erdos964
