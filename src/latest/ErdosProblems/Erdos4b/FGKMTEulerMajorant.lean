/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSquarefreeWeights
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Quantitative Euler-product majorants

Local absolute convergence and a uniform bound on finite Euler products
imply global summability. The quarter-power weight then controls both the
absolute sum and its logarithmic moment, without differentiating an Euler
product or introducing a dimension-dependent exponent.
-/

namespace Erdos4b.FGKMT

noncomputable section

open ArithmeticFunction
open scoped BigOperators

theorem sum_range_le_of_local_products (f : ℕ → ℝ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hpos : ∀ n, 0 ≤ f n)
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hlocal : ∀ {p : ℕ}, p.Prime → Summable (fun j => ‖f (p ^ j)‖))
    {C : ℝ} (hprod : ∀ N : ℕ, (∏ p ∈ N.primesBelow, ∑' j, f (p ^ j)) ≤ C) (N : ℕ) :
    (∑ n ∈ Finset.range N, f n) ≤ C := by
  have hEuler := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf1 hmul hlocal N
  have hIndicator : Summable (N.smoothNumbers.indicator f) :=
    summable_subtype_iff_indicator.mp hEuler.2.summable
  calc
    (∑ n ∈ Finset.range N, f n) ≤
        ∑ n ∈ Finset.range N, N.smoothNumbers.indicator f n := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn0 : n = 0
      · subst n
        rw [Set.indicator_of_notMem (fun h => (Nat.ne_zero_of_mem_smoothNumbers h) rfl), hf0]
      · rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn0)
          (Finset.mem_range.mp hn))]
    _ ≤ ∑' n, N.smoothNumbers.indicator f n := by
      apply hIndicator.sum_le_tsum
      intro n _
      by_cases hn : n ∈ N.smoothNumbers
      · rw [Set.indicator_of_mem hn]
        exact hpos n
      · rw [Set.indicator_of_notMem hn]
    _ = ∑' n : N.smoothNumbers, f n := (tsum_subtype N.smoothNumbers f).symm
    _ = ∏ p ∈ N.primesBelow, ∑' j, f (p ^ j) := hEuler.2.tsum_eq
    _ ≤ C := hprod N

theorem summable_and_tsum_le_of_local_products (f : ℕ → ℝ)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hpos : ∀ n, 0 ≤ f n)
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hlocal : ∀ {p : ℕ}, p.Prime → Summable (fun j => ‖f (p ^ j)‖))
    {C : ℝ} (hprod : ∀ N : ℕ, (∏ p ∈ N.primesBelow, ∑' j, f (p ^ j)) ≤ C) :
    Summable f ∧ (∑' n, f n) ≤ C := by
  have hsum := sum_range_le_of_local_products f hf0 hf1 hpos hmul hlocal hprod
  exact ⟨summable_of_sum_range_le hpos hsum, Real.tsum_le_of_sum_range_le hpos hsum⟩

def quarterMomentTerm (f : ArithmeticFunction ℝ) (n : ℕ) : ℝ :=
  |f n| * (n : ℝ) ^ (1 / 4 : ℝ)

theorem quarterMomentTerm_nonneg (f : ArithmeticFunction ℝ) (n : ℕ) :
    0 ≤ quarterMomentTerm f n := by unfold quarterMomentTerm; positivity

theorem quarterMomentTerm_mul {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    {m n : ℕ} (hmn : Nat.Coprime m n) :
    quarterMomentTerm f (m * n) = quarterMomentTerm f m * quarterMomentTerm f n := by
  unfold quarterMomentTerm
  rw [hf.map_mul_of_coprime hmn, abs_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

theorem quarterMomentTerm_local_summable (f : ArithmeticFunction ℝ) {p : ℕ}
    (hhigh : ∀ j, 3 ≤ j → f (p ^ j) = 0) :
    Summable (fun j => ‖quarterMomentTerm f (p ^ j)‖) := by
  apply summable_of_ne_finset_zero (s := Finset.range 3)
  intro j hj
  have hj3 : 3 ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
  simp only [quarterMomentTerm, hhigh j hj3, abs_zero, zero_mul, norm_zero]

theorem quarterMomentTerm_local_tsum_eq {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {p : ℕ}
    (hhigh : ∀ j, 3 ≤ j → f (p ^ j) = 0) :
    (∑' j, quarterMomentTerm f (p ^ j)) =
      1 + |f p| * (p : ℝ) ^ (1 / 4 : ℝ) +
        |f (p ^ 2)| * (p : ℝ) ^ (1 / 2 : ℝ) := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun j hj => by
    have hj3 : 3 ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
    simp only [quarterMomentTerm, hhigh j hj3, abs_zero, zero_mul])]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, quarterMomentTerm,
    pow_zero, pow_one, hf.map_one, abs_one, Nat.cast_one, Real.one_rpow,
    mul_one, zero_add, Nat.cast_pow]
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg p) 2 (1 / 4 : ℝ)]
  norm_num

theorem quarterMomentTerm_local_tsum_le {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {p : ℕ} (hp : p.Prime) {A B : ℝ}
    (hA : 0 ≤ A) (hprime : |f p| ≤ A / (p : ℝ) ^ 2)
    (hsquare : |f (p ^ 2)| ≤ B / (p : ℝ) ^ 2)
    (hhigh : ∀ j, 3 ≤ j → f (p ^ j) = 0) :
    (∑' j, quarterMomentTerm f (p ^ j)) ≤
      1 + (A + B) * (p : ℝ) ^ (-3 / 2 : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hquarter : (p : ℝ) ^ (1 / 4 : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) (by norm_num)
  have hpower : (p : ℝ) ^ (1 / 2 : ℝ) / (p : ℝ) ^ 2 =
      (p : ℝ) ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_sub hpR]
    norm_num
  rw [quarterMomentTerm_local_tsum_eq hf hhigh]
  calc
    _ ≤ 1 + (A / (p : ℝ) ^ 2) * (p : ℝ) ^ (1 / 2 : ℝ) +
        (B / (p : ℝ) ^ 2) * (p : ℝ) ^ (1 / 2 : ℝ) := by
      apply add_le_add
      · exact add_le_add le_rfl
          (mul_le_mul hprime hquarter (by positivity) (div_nonneg hA (sq_nonneg _)))
      · exact mul_le_mul_of_nonneg_right hsquare (by positivity)
    _ = 1 + (A + B) * ((p : ℝ) ^ (1 / 2 : ℝ) / (p : ℝ) ^ 2) := by ring
    _ = _ := by rw [hpower]

theorem abs_le_quarterMomentTerm (f : ArithmeticFunction ℝ) (n : ℕ) :
    |f n| ≤ quarterMomentTerm f n := by
  by_cases hn : n = 0
  · subst n
    simp [quarterMomentTerm]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow hn1 (by norm_num)
    exact (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)).trans_eq' (by simp)

theorem abs_log_le_four_quarterMomentTerm (f : ArithmeticFunction ℝ) (n : ℕ) :
    |f n| * Real.log n ≤ 4 * quarterMomentTerm f n := by
  have hlog := Real.log_natCast_le_rpow_div n (by norm_num : (0 : ℝ) < 1 / 4)
  have h := mul_le_mul_of_nonneg_left hlog (abs_nonneg (f n))
  dsimp [quarterMomentTerm]
  nlinarith

theorem moments_of_quarterMoment_summable (f : ArithmeticFunction ℝ)
    (hs : Summable (quarterMomentTerm f)) {C : ℝ} (hC : (∑' n, quarterMomentTerm f n) ≤ C) :
    Summable (fun n => |f n|) ∧ (∑' n, |f n|) ≤ C ∧
      Summable (fun n => |f n| * Real.log n) ∧
        (∑' n, |f n| * Real.log n) ≤ 4 * C := by
  have hlogpos : ∀ n : ℕ, 0 ≤ |f n| * Real.log n := by
    intro n
    exact mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg n)
  have ha := Summable.of_nonneg_of_le (fun n => abs_nonneg (f n))
    (abs_le_quarterMomentTerm f) hs
  have hl := Summable.of_nonneg_of_le hlogpos (abs_log_le_four_quarterMomentTerm f)
    (hs.mul_left 4)
  refine ⟨ha, (Summable.tsum_le_tsum (abs_le_quarterMomentTerm f) ha hs).trans hC,
    hl, ?_⟩
  calc
    _ ≤ ∑' n, 4 * quarterMomentTerm f n :=
      Summable.tsum_le_tsum (abs_log_le_four_quarterMomentTerm f) hl (hs.mul_left 4)
    _ = 4 * ∑' n, quarterMomentTerm f n := tsum_mul_left
    _ ≤ 4 * C := mul_le_mul_of_nonneg_left hC (by norm_num)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.moments_of_quarterMoment_summable
