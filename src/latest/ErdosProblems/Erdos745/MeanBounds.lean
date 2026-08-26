import ErdosProblems.Erdos745.TreeMoments
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Explicit estimates for critical tree-component means

Only coarse constants are needed.  The quadratic logarithm error and an upper
Stirling bound retain the square-root factor required at the critical scale.
-/

open scoped BigOperators

namespace Erdos745

theorem log_one_sub_lower {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    -x - 2 * x ^ 2 ≤ Real.log (1 - x) := by
  have hxlt : |x| < 1 := by rw [abs_of_nonneg hx]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hxlt 1
  norm_num only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_one, div_one,
    abs_of_nonneg hx] at h
  have hden : 0 < 1 - x := by linarith
  have hfrac : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ hden]
    have hmul := mul_le_mul_of_nonneg_left hxhalf (sq_nonneg x)
    nlinarith
  have hlow := (abs_le.mp (h.trans hfrac)).1
  linarith

theorem exp_neg_quadratic_le_one_sub {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.exp (-x - 2 * x ^ 2) ≤ 1 - x := by
  calc
    _ ≤ Real.exp (Real.log (1 - x)) := Real.exp_le_exp.mpr (log_one_sub_lower hx hxhalf)
    _ = _ := Real.exp_log (by linarith)

/-- Upper Stirling bound with a fixed explicit constant. -/
theorem factorial_le_exp_sqrt {k : ℕ} (hk : 0 < k) :
    (k.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt k * ((k : ℝ) / Real.exp 1) ^ k := by
  have hseq : Stirling.stirlingSeq k ≤ Real.exp 1 / Real.sqrt 2 := by
    have h := Stirling.stirlingSeq'_antitone (Nat.zero_le (k - 1))
    simpa only [Function.comp_apply, Nat.succ_eq_add_one, Nat.zero_add,
      Nat.sub_add_cancel hk, Stirling.stirlingSeq_one] using h
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Stirling.stirlingSeq, div_le_iff₀ (by positivity)] at hseq
  calc
    _ ≤ (Real.exp 1 / Real.sqrt 2) *
        (Real.sqrt (2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) := hseq
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
      field_simp

theorem sum_range_cast_eq (k : ℕ) :
    (∑ i ∈ Finset.range k, (i : ℝ)) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem sum_range_cast_sq_le (k : ℕ) :
    (∑ i ∈ Finset.range k, (i : ℝ) ^ 2) ≤ (k : ℝ) ^ 3 := by
  calc
    _ ≤ ∑ _i ∈ Finset.range k, (k : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply pow_le_pow_left₀ (Nat.cast_nonneg i)
      exact_mod_cast (Finset.mem_range.mp hi).le
    _ = _ := by simp; ring

/-- The product left after extracting `n^k` from the falling factorial. -/
noncomputable def fallingProduct (n k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, (1 - (i : ℝ) / n)

theorem fallingProduct_lower {n k : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n) :
    Real.exp (-(k : ℝ) * ((k : ℝ) - 1) / (2 * n) - 2 * (k : ℝ) ^ 3 / (n : ℝ) ^ 2) ≤
      fallingProduct n k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcoord (i : ℕ) (hi : i ∈ Finset.range k) : (i : ℝ) / n ≤ 1 / 2 := by
    rw [div_le_iff₀ hnR]
    have hik : (i : ℝ) ≤ k := by exact_mod_cast (Finset.mem_range.mp hi).le
    have hkn : (2 : ℝ) * k ≤ n := by exact_mod_cast hk
    linarith
  have hsum : -(k : ℝ) * ((k : ℝ) - 1) / (2 * n) -
      2 * (k : ℝ) ^ 3 / (n : ℝ) ^ 2 ≤
      ∑ i ∈ Finset.range k, (-(i : ℝ) / n - 2 * ((i : ℝ) / n) ^ 2) := by
    have heq : (∑ i ∈ Finset.range k, (-(i : ℝ) / n - 2 * ((i : ℝ) / n) ^ 2)) =
        -(∑ i ∈ Finset.range k, (i : ℝ)) / n -
          2 * (∑ i ∈ Finset.range k, (i : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
      simp only [Finset.sum_sub_distrib, neg_div, Finset.sum_neg_distrib,
        div_pow, ← Finset.mul_sum, ← Finset.sum_div]
      ring
    rw [heq, sum_range_cast_eq, neg_div, div_div]
    have hdiv := div_le_div_of_nonneg_right (sum_range_cast_sq_le k) (sq_nonneg (n : ℝ))
    linear_combination 2 * hdiv
  calc
    _ ≤ Real.exp (∑ i ∈ Finset.range k, (-(i : ℝ) / n - 2 * ((i : ℝ) / n) ^ 2)) :=
      Real.exp_le_exp.mpr hsum
    _ = ∏ i ∈ Finset.range k, Real.exp (-(i : ℝ) / n - 2 * ((i : ℝ) / n) ^ 2) :=
      Real.exp_sum _ _
    _ ≤ fallingProduct n k := by
      apply Finset.prod_le_prod
      · intro i _
        exact (Real.exp_pos _).le
      · intro i hi
        simpa only [neg_div] using
          exp_neg_quadratic_le_one_sub (div_nonneg (Nat.cast_nonneg i) hnR.le) (hcoord i hi)

theorem descFactorial_eq_fallingProduct {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    (n.descFactorial k : ℝ) = (n : ℝ) ^ k * fallingProduct n k := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  calc
    _ = ∏ i ∈ Finset.range k, (n : ℝ) * (1 - (i : ℝ) / n) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hin : i ≤ n := (Finset.mem_range.mp hi).le.trans hk
      rw [Nat.cast_sub hin]
      field_simp
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const,
        Finset.card_range, fallingProduct]

theorem choose_eq_fallingProduct {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    (n.choose k : ℝ) = (n : ℝ) ^ k * fallingProduct n k / k.factorial := by
  apply (eq_div_iff (by positivity : (k.factorial : ℝ) ≠ 0)).mpr
  rw [← descFactorial_eq_fallingProduct hn hk, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, mul_comm]

theorem choose_two_difference {n k : ℕ} (hk : k ≤ n) :
    n.choose 2 - (n - k).choose 2 = k * (n - k) + k.choose 2 := by
  have hsum : n.choose 2 = (n - k).choose 2 + k * (n - k) + k.choose 2 := by
    have hr : (n.choose 2 : ℝ) = ((n - k).choose 2 : ℝ) +
        (k : ℝ) * (n - k : ℕ) + (k.choose 2 : ℝ) := by
      rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_sub hk]
      ring
    exact_mod_cast hr
  omega

theorem tree_absent_count_cast {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    ((n.choose 2 - (n - k).choose 2 - (k - 1) : ℕ) : ℝ) =
      (k : ℝ) * n - (k : ℝ) * ((k : ℝ) + 3) / 2 + 1 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsmall : k - 1 ≤ k.choose 2 := by
    have hr : ((k - 1 : ℕ) : ℝ) ≤ (k.choose 2 : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one, Nat.cast_choose_two]
      nlinarith
    exact_mod_cast hr
  rw [choose_two_difference hkn, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub hkn, Nat.cast_choose_two, Nat.cast_sub (by omega), Nat.cast_one]
  ring

theorem tree_absent_count_le_mul {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    ((n.choose 2 - (n - k).choose 2 - (k - 1) : ℕ) : ℝ) ≤ (k : ℝ) * n := by
  rw [tree_absent_count_cast hk hkn]
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

theorem critical_absence_power_lower {n : ℕ} (hn : 2 ≤ n) (b : ℕ) :
    Real.exp (-(b : ℝ) / n - 2 * (b : ℝ) / (n : ℝ) ^ 2) ≤ (1 - 1 / (n : ℝ)) ^ b := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hhalf : (1 : ℝ) / n ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < n)]
    linarith
  have h := pow_le_pow_left₀ (Real.exp_pos _).le
    (exp_neg_quadratic_le_one_sub (by positivity : (0 : ℝ) ≤ 1 / n) hhalf) b
  rw [← Real.exp_nat_mul] at h
  convert h using 1
  congr 1
  ring

theorem critical_product_lower {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : 2 * k ≤ n) :
    Real.exp (-(k : ℝ) - 2 * (k : ℝ) / n - 2 * (k : ℝ) ^ 3 / (n : ℝ) ^ 2) ≤
      fallingProduct n k * (1 - 1 / (n : ℝ)) ^
        (n.choose 2 - (n - k).choose 2 - (k - 1)) := by
  let b := n.choose 2 - (n - k).choose 2 - (k - 1)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : k ≤ n := by omega
  have hb : (b : ℝ) ≤ (k : ℝ) * n := tree_absent_count_le_mul hk hkn'
  have hbdiv : (b : ℝ) / (n : ℝ) ^ 2 ≤ (k : ℝ) / n := by
    calc
      _ ≤ ((k : ℝ) * n) / (n : ℝ) ^ 2 := div_le_div_of_nonneg_right hb (sq_nonneg _)
      _ = _ := by field_simp
  have hpositive : 0 ≤ (2 * (k : ℝ) - 1) / n := div_nonneg (by linarith) hnR.le
  have hexp : -(k : ℝ) - 2 * (k : ℝ) / n - 2 * (k : ℝ) ^ 3 / (n : ℝ) ^ 2 ≤
      (-(k : ℝ) * ((k : ℝ) - 1) / (2 * n) - 2 * (k : ℝ) ^ 3 / (n : ℝ) ^ 2) +
        (-(b : ℝ) / n - 2 * (b : ℝ) / (n : ℝ) ^ 2) := by
    have heq : (-(k : ℝ) * ((k : ℝ) - 1) / (2 * n) - 2 * (k : ℝ) ^ 3 / (n : ℝ) ^ 2) +
        (-(b : ℝ) / n - 2 * (b : ℝ) / (n : ℝ) ^ 2) =
        -(k : ℝ) + (2 * (k : ℝ) - 1) / n - 2 * (k : ℝ) ^ 3 / (n : ℝ) ^ 2 -
          2 * (b : ℝ) / (n : ℝ) ^ 2 := by
      have hbcast : (b : ℝ) = (k : ℝ) * n - (k : ℝ) * ((k : ℝ) + 3) / 2 + 1 :=
        tree_absent_count_cast hk hkn'
      rw [hbcast]
      field_simp
      ring
    rw [heq]
    linear_combination 2 * hbdiv + hpositive
  have hfall := fallingProduct_lower (by omega : 0 < n) hkn
  calc
    _ ≤ Real.exp ((-(k : ℝ) * ((k : ℝ) - 1) / (2 * n) -
        2 * (k : ℝ) ^ 3 / (n : ℝ) ^ 2) + (-(b : ℝ) / n - 2 * (b : ℝ) / (n : ℝ) ^ 2)) :=
      Real.exp_le_exp.mpr hexp
    _ ≤ _ := by
      rw [Real.exp_add]
      exact mul_le_mul hfall (critical_absence_power_lower hn b)
        (Real.exp_pos _).le ((Real.exp_pos _).le.trans hfall)

theorem critical_treeMean_eq_product {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n) :
    treeMean 1 n k = (n : ℝ) * labelledTreeCount k / k.factorial *
      (fallingProduct n k * (1 - 1 / (n : ℝ)) ^
        (n.choose 2 - (n - k).choose 2 - (k - 1))) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hpow : (n : ℝ) ^ k * (1 / (n : ℝ)) ^ (k - 1) = n := by
    conv_lhs => arg 1; rw [← Nat.sub_add_cancel hk, pow_succ]
    rw [one_div_pow]
    field_simp
  rw [treeMean, edgeProbability_one, coe_criticalEdgeProbability (by omega),
    choose_eq_fallingProduct hn hkn]
  calc
    _ = ((n : ℝ) ^ k * (1 / (n : ℝ)) ^ (k - 1)) * labelledTreeCount k / k.factorial *
        (fallingProduct n k * (1 - 1 / (n : ℝ)) ^
          (n.choose 2 - (n - k).choose 2 - (k - 1))) := by ring
    _ = _ := by rw [hpow]

theorem critical_prefactor_identity {k : ℕ} (hk : 2 ≤ k) (n d : ℝ) :
    (n * (k : ℝ) ^ (k - 2) /
      (Real.exp 1 * Real.sqrt k * ((k : ℝ) / Real.exp 1) ^ k)) * Real.exp (-(k : ℝ) - d) =
      n / (Real.exp 1 * (k : ℝ) ^ 2 * Real.sqrt k) * Real.exp (-d) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hsqrt : Real.sqrt (k : ℝ) ≠ 0 := by positivity
  have hexp : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
    simpa only [mul_one] using Real.exp_nat_mul 1 k
  have hpow : (k : ℝ) ^ k = (k : ℝ) ^ (k - 2) * (k : ℝ) ^ 2 := by
    calc
      _ = (k : ℝ) ^ (k - 2 + 2) := by rw [Nat.sub_add_cancel hk]
      _ = _ := pow_add _ _ _
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, hexp, div_pow, hpow]
  field_simp

/-- Explicit critical tree mean lower bound before choosing a scaling window. -/
theorem critical_treeMean_lower {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : 2 * k ≤ n) :
    (n : ℝ) / (Real.exp 1 * (k : ℝ) ^ 2 * Real.sqrt k) *
        Real.exp (-2 * (k : ℝ) / n - 2 * (k : ℝ) ^ 3 / (n : ℝ) ^ 2) ≤ treeMean 1 n k := by
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcount : (k : ℝ) ^ (k - 2) ≤ labelledTreeCount k := by
    exact_mod_cast labelledTreeCount_lower hk
  let d := 2 * (k : ℝ) / n + 2 * (k : ℝ) ^ 3 / (n : ℝ) ^ 2
  have hprod := critical_product_lower hn hk hkn
  calc
    _ = (n : ℝ) / (Real.exp 1 * (k : ℝ) ^ 2 * Real.sqrt k) * Real.exp (-d) := by
      congr 2
      ring
    _ = ((n : ℝ) * (k : ℝ) ^ (k - 2) /
        (Real.exp 1 * Real.sqrt k * ((k : ℝ) / Real.exp 1) ^ k)) *
          Real.exp (-(k : ℝ) - d) := (critical_prefactor_identity hk n d).symm
    _ ≤ ((n : ℝ) * (k : ℝ) ^ (k - 2) / k.factorial) * Real.exp (-(k : ℝ) - d) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (factorial_le_exp_sqrt (by omega))) (Real.exp_pos _).le
    _ ≤ ((n : ℝ) * labelledTreeCount k / k.factorial) * Real.exp (-(k : ℝ) - d) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcount hnR) (by positivity))
        (Real.exp_pos _).le
    _ ≤ ((n : ℝ) * labelledTreeCount k / k.factorial) *
        (fallingProduct n k * (1 - 1 / (n : ℝ)) ^
          (n.choose 2 - (n - k).choose 2 - (k - 1))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have he : -(k : ℝ) - d =
          -(k : ℝ) - 2 * (k : ℝ) / n - 2 * (k : ℝ) ^ 3 / (n : ℝ) ^ 2 := by
        dsimp [d]
        ring
      rw [he]
      exact hprod
    _ = _ := (critical_treeMean_eq_product (by omega) (by omega) (by omega)).symm

theorem critical_treeMean_lower_constant {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k)
    (hkn : 2 * k ≤ n) (hscale : (k : ℝ) ^ 3 ≤ 8 * (n : ℝ) ^ 2) :
    Real.exp (-19) * (n : ℝ) / ((k : ℝ) ^ 2 * Real.sqrt k) ≤ treeMean 1 n k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdiv : (k : ℝ) / n ≤ 1 := by
    rw [div_le_one hnR]
    exact_mod_cast (show k ≤ n by omega)
  have hdiv3 : (k : ℝ) ^ 3 / (n : ℝ) ^ 2 ≤ 8 :=
    (div_le_iff₀ (sq_pos_of_pos hnR)).mpr hscale
  calc
    _ = (n : ℝ) / (Real.exp 1 * (k : ℝ) ^ 2 * Real.sqrt k) * Real.exp (-18) := by
      have h : Real.exp (-19) = Real.exp (-18) / Real.exp 1 := by
        rw [← Real.exp_sub]
        norm_num
      rw [h]
      ring
    _ ≤ (n : ℝ) / (Real.exp 1 * (k : ℝ) ^ 2 * Real.sqrt k) *
        Real.exp (-2 * (k : ℝ) / n - 2 * (k : ℝ) ^ 3 / (n : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      linear_combination 2 * hdiv + 2 * hdiv3
    _ ≤ _ := critical_treeMean_lower hn hk hkn

end Erdos745
