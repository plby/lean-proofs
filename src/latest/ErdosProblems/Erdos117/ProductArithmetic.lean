import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

/-!
# Summing the factor errors

For factor clique numbers at least three, the sum of their square roots is
at most twice the square root of their product. Thus a uniform prime-factor
error of order `sqrt(n) * log(n+2)^3` stays of that order under products.
-/

namespace Erdos117

open scoped BigOperators

theorem factor_le_prod_of_one_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 1 ≤ f i) {i : ι} (hi : i ∈ s) : f i ≤ ∏ j ∈ s, f j := by
  classical
  calc
    _ = ∏ j ∈ {i}, f j := by simp
    _ ≤ ∏ j ∈ s, f j := Finset.prod_le_prod_of_subset_of_one_le
      (Finset.singleton_subset_iff.mpr hi)
      (by intro j hj; have hji := Finset.mem_singleton.mp hj; subst j; linarith [hf i hi])
      (fun j hj _ => hf j hj)

theorem three_le_prod_of_nonempty {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hs : s.Nonempty) (hf : ∀ i ∈ s, 3 ≤ f i) : 3 ≤ ∏ i ∈ s, f i := by
  obtain ⟨i, hi⟩ := hs
  exact (hf i hi).trans (factor_le_prod_of_one_le s f (fun j hj => by linarith [hf j hj]) hi)

/-- The sum of nonabelian-factor clique numbers is at most their product. -/
theorem sum_le_prod_of_three_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∀ i ∈ s, 3 ≤ f i) → (∑ i ∈ s, f i) ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro hf
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hfs : ∀ j ∈ s, 3 ≤ f j := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    by_cases hs : s = ∅
    · simp [hs]
    have hprod := three_le_prod_of_nonempty s f (Finset.nonempty_iff_ne_empty.mpr hs) hfs
    have hsum := ih hfs
    have hleft := mul_le_mul_of_nonneg_left (show 2 ≤ ∏ j ∈ s, f j by linarith)
      (show 0 ≤ f i by linarith)
    have hright := mul_le_mul_of_nonneg_right (show 2 ≤ f i by linarith)
      (show 0 ≤ ∏ j ∈ s, f j by linarith)
    nlinarith only [hleft, hright, hsum]

/-- Square-root errors do not gain a factor equal to the number of Sylow
factors. The absolute constant two works for every finite family. -/
theorem sum_sqrt_le_twice_sqrt_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∀ i ∈ s, 3 ≤ f i) →
      (∑ i ∈ s, Real.sqrt (f i)) ≤ 2 * Real.sqrt (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro hf
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hfs : ∀ j ∈ s, 3 ≤ f j := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    by_cases hs : s = ∅
    · simp only [hs, Finset.sum_empty, Finset.prod_empty, add_zero, mul_one]
      nlinarith only [Real.sqrt_nonneg (f i)]
    have hprod := three_le_prod_of_nonempty s f (Finset.nonempty_iff_ne_empty.mpr hs) hfs
    have hsum := ih hfs
    have hsqrt_i : (3 : ℝ) / 2 ≤ Real.sqrt (f i) := by
      nlinarith only [Real.sq_sqrt (show 0 ≤ f i by linarith), Real.sqrt_nonneg (f i), hfi]
    have hsqrt_s : (3 : ℝ) / 2 ≤ Real.sqrt (∏ j ∈ s, f j) := by
      nlinarith only [Real.sq_sqrt (show 0 ≤ ∏ j ∈ s, f j by linarith),
        Real.sqrt_nonneg (∏ j ∈ s, f j), hprod]
    rw [Real.sqrt_mul (show 0 ≤ f i by linarith)]
    have hcross := mul_nonneg
      (show 0 ≤ Real.sqrt (∏ j ∈ s, f j) - 3 / 2 by linarith)
      (show 0 ≤ Real.sqrt (f i) - 1 by linarith)
    nlinarith only [hcross, hsqrt_i, hsum]

/-- The complete square-root/logarithmic error is stable under products. -/
theorem sum_sqrt_log_cube_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 3 ≤ f i) {n : ℝ} (hprod : (∏ i ∈ s, f i) ≤ n) :
    (∑ i ∈ s, Real.sqrt (f i) * (Real.log (f i + 2)) ^ 3) ≤
      2 * Real.sqrt n * (Real.log (n + 2)) ^ 3 := by
  have hprod1 : 1 ≤ ∏ i ∈ s, f i := Finset.one_le_prod (fun i hi => by linarith [hf i hi])
  have hn : 1 ≤ n := hprod1.trans hprod
  have hlog : 0 ≤ Real.log (n + 2) := Real.log_nonneg (by linarith)
  have hpoint (i : ι) (hi : i ∈ s) :
      Real.log (f i + 2) ≤ Real.log (n + 2) := by
    have hfi : f i ≤ n :=
      (factor_le_prod_of_one_le s f (fun j hj => by linarith [hf j hj]) hi).trans hprod
    exact Real.log_le_log (by linarith [hf i hi]) (by linarith)
  calc
    _ ≤ ∑ i ∈ s, Real.sqrt (f i) * (Real.log (n + 2)) ^ 3 := by
      apply Finset.sum_le_sum
      intro i hi
      have hli : 0 ≤ Real.log (f i + 2) := Real.log_nonneg (by linarith [hf i hi])
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hli (hpoint i hi) 3) (Real.sqrt_nonneg _)
    _ = (∑ i ∈ s, Real.sqrt (f i)) * (Real.log (n + 2)) ^ 3 :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * Real.sqrt (∏ i ∈ s, f i) * (Real.log (n + 2)) ^ 3 := by
      exact mul_le_mul_of_nonneg_right (sum_sqrt_le_twice_sqrt_prod s f hf) (by positivity)
    _ ≤ _ := by gcongr

/-- A common linear, square-root, and constant budget for the nonabelian
factors can be summed without a loss in the linear coefficient. -/
theorem sum_factor_cost_le {ι : Type*} (s : Finset ι) (c : ι → ℕ) (f : ι → ℝ)
    (hc : ∀ i ∈ s, 3 ≤ c i) {n : ℕ} (hprod : (∏ i ∈ s, c i) ≤ n)
    {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hf : ∀ i ∈ s, f i ≤ a * c i + b * Real.sqrt (c i) + d) :
    (∑ i ∈ s, f i) ≤ a * n + 2 * b * Real.sqrt n + d * Nat.log 2 n := by
  have hc' (i : ι) (hi : i ∈ s) : (3 : ℝ) ≤ c i := by exact_mod_cast hc i hi
  have hprod' : (∏ i ∈ s, (c i : ℝ)) ≤ n := by exact_mod_cast hprod
  have hsum : (∑ i ∈ s, (c i : ℝ)) ≤ n :=
    (sum_le_prod_of_three_le s (fun i => (c i : ℝ)) hc').trans hprod'
  have hroot : (∑ i ∈ s, Real.sqrt (c i)) ≤ 2 * Real.sqrt n :=
    (sum_sqrt_le_twice_sqrt_prod s (fun i => (c i : ℝ)) hc').trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hprod') (by norm_num))
  have hpow : 2 ^ s.card ≤ n := by
    calc
      _ = ∏ _i ∈ s, 2 := by simp
      _ ≤ ∏ i ∈ s, c i := Finset.prod_le_prod' (fun i hi => (by decide : 2 ≤ 3).trans (hc i hi))
      _ ≤ n := hprod
  have hn : n ≠ 0 := by
    have hpos : 0 < 2 ^ s.card := Nat.pow_pos (by decide)
    omega
  have hcard : s.card ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) hn).mpr hpow
  have hcard' : (s.card : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hcard
  calc
    _ ≤ ∑ i ∈ s, (a * c i + b * Real.sqrt (c i) + d) :=
      Finset.sum_le_sum (fun i hi => hf i hi)
    _ = a * (∑ i ∈ s, (c i : ℝ)) + b * (∑ i ∈ s, Real.sqrt (c i)) + s.card * d := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ a * n + b * (2 * Real.sqrt n) + Nat.log 2 n * d :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hsum ha)
        (mul_le_mul_of_nonneg_left hroot hb)) (mul_le_mul_of_nonneg_right hcard' hd)
    _ = _ := by ring

end Erdos117
