import ErdosProblems.Erdos49.Smooth
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# A finite Rankin majorant for smooth numbers

This file proves the exact Euler-product inequality underlying the two
smooth-number estimates in Tao's proof.  Bounds for the product itself are
kept separate from the unique-factorization argument.
-/

open scoped BigOperators Topology

namespace Erdos49

noncomputable section

/-- The coarse Rankin exponent used in this formalization. -/
def rankinAlpha (y : ℕ) : ℝ := 1 - 1 / (2 * Real.log (y : ℝ))

/-- Completely multiplicative Rankin weight, with the value at zero removed. -/
def rankinWeight (y n : ℕ) : ℝ :=
  if n = 0 then 0 else (n : ℝ) ^ (-rankinAlpha y)

@[simp] lemma rankinWeight_zero (y : ℕ) : rankinWeight y 0 = 0 := by
  simp [rankinWeight]

@[simp] lemma rankinWeight_one (y : ℕ) : rankinWeight y 1 = 1 := by
  simp [rankinWeight]

lemma rankinWeight_nonneg (y n : ℕ) : 0 ≤ rankinWeight y n := by
  unfold rankinWeight
  split_ifs
  · rfl
  · positivity

lemma rankinWeight_mul (y : ℕ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    rankinWeight y (m * n) = rankinWeight y m * rankinWeight y n := by
  simp only [rankinWeight, if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn)]
  push_cast
  exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)

lemma rankinWeight_coprime_mul (y : ℕ) {m n : ℕ} (_hmn : m.Coprime n) :
    rankinWeight y (m * n) = rankinWeight y m * rankinWeight y n := by
  by_cases hm : m = 0
  · subst m
    simp
  by_cases hn : n = 0
  · subst n
    simp
  exact rankinWeight_mul y hm hn

lemma rankinAlpha_pos {y : ℕ} (hy : Real.exp 1 < y) : 0 < rankinAlpha y := by
  have hy0 : 0 < (y : ℝ) := lt_trans (Real.exp_pos 1) (by exact_mod_cast hy)
  have hlog : 1 < Real.log (y : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hy0]
    exact_mod_cast hy
  unfold rankinAlpha
  have hden : 0 < 2 * Real.log (y : ℝ) := by linarith
  have : 1 / (2 * Real.log (y : ℝ)) < 1 := by
    rw [div_lt_one hden]
    linarith
  linarith

lemma rankin_prime_ratio_nonneg (y : ℕ) (p : ℕ) :
    0 ≤ (p : ℝ) ^ (-rankinAlpha y) := by positivity

lemma rankin_prime_ratio_lt_one {y p : ℕ} (hy : Real.exp 1 < y)
    (hp : p.Prime) : (p : ℝ) ^ (-rankinAlpha y) < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp.one_lt) (neg_lt_zero.mpr (rankinAlpha_pos hy))

lemma rankinWeight_prime_pow {y p j : ℕ} (hp : p.Prime) :
    rankinWeight y (p ^ j) = ((p : ℝ) ^ (-rankinAlpha y)) ^ j := by
  have hp0 : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
  simp only [rankinWeight, if_neg hp0]
  push_cast
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (Nat.cast_nonneg p)]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (Nat.cast_nonneg p)]
  ring_nf

lemma summable_rankinWeight_prime_pow {y p : ℕ} (hy : Real.exp 1 < y)
    (hp : p.Prime) :
    Summable (fun j : ℕ ↦ ‖rankinWeight y (p ^ j)‖) := by
  have hr0 := rankin_prime_ratio_nonneg y p
  have hr1 := rankin_prime_ratio_lt_one hy hp
  simpa only [rankinWeight_prime_pow hp, Real.norm_eq_abs,
    abs_pow, abs_of_nonneg hr0] using
      (summable_geometric_of_norm_lt_one
        (by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1))

/-- Exact local geometric factor in the Rankin Euler product. -/
lemma tsum_rankinWeight_prime_pow {y p : ℕ} (hy : Real.exp 1 < y)
    (hp : p.Prime) :
    (∑' j : ℕ, rankinWeight y (p ^ j)) =
      (1 - (p : ℝ) ^ (-rankinAlpha y))⁻¹ := by
  rw [show (fun j : ℕ ↦ rankinWeight y (p ^ j)) =
      fun j : ℕ ↦ ((p : ℝ) ^ (-rankinAlpha y)) ^ j by
    funext j
    exact rankinWeight_prime_pow hp]
  exact tsum_geometric_of_lt_one
    (rankin_prime_ratio_nonneg y p) (rankin_prime_ratio_lt_one hy hp)

/-- The finite Euler product bounding a Rankin-weighted smooth sum. -/
def rankinEulerProduct (y : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ) ^ (-rankinAlpha y))⁻¹

/-- A finite partial sum over positive `y`-smooth integers is bounded by the
corresponding full Euler product. -/
theorem smooth_rankin_sum_le_euler {X y : ℕ} (hy : Real.exp 1 < y) :
    (∑ n ∈ smoothUpTo X y, (n : ℝ) ^ (-rankinAlpha y)) ≤
      rankinEulerProduct y := by
  let f : ℕ → ℝ := rankinWeight y
  have hEuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := f) (rankinWeight_one y) (rankinWeight_coprime_mul y)
      (fun hp ↦ summable_rankinWeight_prime_pow hy hp) (y + 1)
  let e : {n // n ∈ smoothUpTo X y} ↪ (y + 1).smoothNumbers :=
    { toFun := fun n ↦ ⟨n, (smooth_iff_mem_nat_smoothNumbers.mp
          (mem_smoothUpTo.mp n.property).2)⟩
      inj' := fun a b hab ↦ by
        apply Subtype.ext
        change (a : ℕ) = (b : ℕ)
        exact congrArg (fun z : (y + 1).smoothNumbers ↦ (z : ℕ)) hab }
  let S : Finset ((y + 1).smoothNumbers) := (smoothUpTo X y).attach.map e
  have hsum :
      (∑ n ∈ smoothUpTo X y, (n : ℝ) ^ (-rankinAlpha y)) =
        ∑ n ∈ S, f n := by
    calc
      (∑ n ∈ smoothUpTo X y, (n : ℝ) ^ (-rankinAlpha y)) =
          ∑ n ∈ (smoothUpTo X y).attach,
            ((n : ℕ) : ℝ) ^ (-rankinAlpha y) :=
        (Finset.sum_attach _ _).symm
      _ = ∑ n ∈ (smoothUpTo X y).attach, f n := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [f, rankinWeight, if_neg (smooth_ne_zero
          (mem_smoothUpTo.mp n.property).2)]
      _ = ∑ n ∈ S, f n := by
        change (∑ n ∈ (smoothUpTo X y).attach, f n) =
          ∑ n ∈ (smoothUpTo X y).attach.map e, f n
        rw [Finset.sum_map]
        rfl
  rw [hsum]
  calc
    (∑ n ∈ S, f n) ≤ ∑' n : (y + 1).smoothNumbers, f n :=
      hEuler.1.of_norm.sum_le_tsum S
        (fun n _ ↦ rankinWeight_nonneg y n)
    _ = ∏ p ∈ (y + 1).primesBelow,
        ∑' j : ℕ, f (p ^ j) := hEuler.2.tsum_eq
    _ = rankinEulerProduct y := by
      unfold rankinEulerProduct
      rw [show (y + 1).primesBelow = Nat.primesLE y from rfl]
      apply Finset.prod_congr rfl
      intro p hp
      exact tsum_rankinWeight_prime_pow hy (Nat.prime_of_mem_primesLE hp)

#print axioms smooth_rankin_sum_le_euler

end

end Erdos49
