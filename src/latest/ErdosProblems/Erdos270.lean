/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 270.
https://www.erdosproblems.com/forum/thread/270

Informal authors:
- T. Crmarić
- Vjekoslav Kovač

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos270.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 270

Crmarić and Kovač proved that every positive real number is a sum

`∑ n ≥ 1, 1 / ((n + 1) ⋯ (n + f n))`

for a positive-integer-valued function `f` tending to infinity.  This gives the
strongest possible negative answer to Erdős and Graham's irrationality question.

The detailed mathematical proof and the Leanization map are in `tex/270.tex`.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos270

noncomputable section

/-- The zero-based version of the summand in Erdős Problem 270.  Thus
`productTerm n k = 1 / ((n+2) * ... * (n+k+1))`. -/
def productTerm (n k : ℕ) : ℝ :=
  ((n + 2).ascFactorial k : ℝ)⁻¹

lemma productTerm_eq_prod (n k : ℕ) :
    productTerm n k =
      (∏ i ∈ range k, (((n + 2 + i : ℕ) : ℝ)))⁻¹ := by
  rw [productTerm, Nat.ascFactorial_eq_prod_range]
  norm_cast

lemma productTerm_pos (n k : ℕ) : 0 < productTerm n k := by
  rw [productTerm]
  positivity

lemma productTerm_nonneg (n k : ℕ) : 0 ≤ productTerm n k :=
  (productTerm_pos n k).le

lemma productTerm_le_inv_pow (n k : ℕ) :
    productTerm n k ≤ (((n + 2 : ℕ) : ℝ) ^ k)⁻¹ := by
  rw [productTerm]
  gcongr
  exact_mod_cast Nat.pow_succ_le_ascFactorial (n + 2) k

lemma inv_pow_add_le_productTerm (n k : ℕ) :
    (((n + k + 1 : ℕ) : ℝ) ^ k)⁻¹ ≤ productTerm n k := by
  rw [productTerm]
  gcongr
  exact_mod_cast (show (n + 2).ascFactorial k ≤ (n + k + 1) ^ k by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.ascFactorial_le_pow_add (n + 1) k)

lemma productTerm_le_two_inv_pow (n k : ℕ) :
    productTerm n k ≤ ((2 : ℝ)⁻¹) ^ k := by
  calc
    productTerm n k ≤ (((n + 2 : ℕ) : ℝ) ^ k)⁻¹ := productTerm_le_inv_pow n k
    _ ≤ (((2 : ℕ) : ℝ) ^ k)⁻¹ := by
      gcongr
      exact_mod_cast (show 2 ≤ n + 2 by omega)
    _ = ((2 : ℝ) ^ k)⁻¹ := by norm_cast
    _ = ((2 : ℝ)⁻¹) ^ k := by rw [inv_pow]

lemma tendsto_productTerm_length (n : ℕ) :
    Tendsto (productTerm n) atTop (nhds 0) := by
  apply squeeze_zero (fun k => productTerm_nonneg n k) (productTerm_le_two_inv_pow n)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹)
    (by norm_num) (by norm_num)

/-- At a fixed index a sufficiently long product has arbitrarily small reciprocal,
and the length may simultaneously be required to exceed any natural threshold. -/
lemma exists_large_length_small (n L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k > L, productTerm n k < ε := by
  have hsmall : ∀ᶠ k in atTop, productTerm n k < ε :=
    (tendsto_order.1 (tendsto_productTerm_length n)).2 ε hε
  have hlarge : ∀ᶠ k : ℕ in atTop, L < k := eventually_gt_atTop L
  exact (hsmall.and hlarge).exists.imp fun _ hk => ⟨hk.2, hk.1⟩

/-! ## Kakeya's binary subsum lemma -/

/-- The sum of a summable sequence from index `n` onward. -/
def tailSum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' k, a (n + k)

lemma tailSum_zero (a : ℕ → ℝ) : tailSum a 0 = ∑' k, a k := by
  simp [tailSum]

lemma tailSum_succ {a : ℕ → ℝ} (ha : Summable a) (n : ℕ) :
    tailSum a n = a n + tailSum a (n + 1) := by
  have hs : Summable (fun k => a (n + k)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff n).2 ha
  have h := hs.sum_add_tsum_nat_add 1
  simpa only [tailSum, sum_range_one, Nat.zero_add, Nat.add_zero, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using h.symm

lemma tailSum_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    0 ≤ tailSum a n := by
  exact tsum_nonneg fun k => ha (n + k)

lemma tendsto_tailSum_zero {a : ℕ → ℝ} (ha : Summable a) :
    Tendsto (tailSum a) atTop (nhds 0) := by
  have hpartial := ha.tendsto_sum_tsum_nat
  have hdiff : Tendsto (fun n => (∑' k, a k) - ∑ k ∈ range n, a k)
      atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds (x := ∑' k, a k)).sub hpartial)
  apply hdiff.congr'
  filter_upwards [] with n
  have hsplit := ha.sum_add_tsum_nat_add n
  calc
    (∑' k, a k) - ∑ k ∈ range n, a k = ∑' k, a (k + n) := by
      linarith
    _ = tailSum a n := by
      apply tsum_congr
      intro k
      simp [Nat.add_comm]

/-- Residual in the greedy proof of Kakeya's binary subsum lemma. -/
def greedyResidual (a : ℕ → ℝ) (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if a n ≤ greedyResidual a x n then greedyResidual a x n - a n
      else greedyResidual a x n

/-- The term selected by the greedy binary subsum algorithm. -/
def greedyTerm (a : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  if a n ≤ greedyResidual a x n then a n else 0

lemma sum_greedyTerm (a : ℕ → ℝ) (x : ℝ) (n : ℕ) :
    ∑ k ∈ range n, greedyTerm a x k = x - greedyResidual a x n := by
  induction n with
  | zero => simp [greedyResidual]
  | succ n ih =>
      rw [sum_range_succ, ih]
      simp only [greedyTerm, greedyResidual]
      split_ifs <;> ring

lemma greedyResidual_bounds {a : ℕ → ℝ} (ha : Summable a)
    (_ha0 : ∀ n, 0 ≤ a n)
    (hdom : ∀ n, a n ≤ tailSum a (n + 1))
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ tailSum a 0) :
    ∀ n, 0 ≤ greedyResidual a x n ∧ greedyResidual a x n ≤ tailSum a n := by
  intro n
  induction n with
  | zero => simpa [greedyResidual] using And.intro hx0 hx
  | succ n ih =>
      rw [tailSum_succ ha n] at ih
      simp only [greedyResidual]
      split_ifs with hchoose
      · constructor
        · exact sub_nonneg.mpr hchoose
        · linarith
      · constructor
        · exact ih.1
        · exact (lt_of_not_ge hchoose).le.trans (hdom n)

/-- Kakeya's binary subsum lemma in the exact form needed below. -/
theorem exists_hasSum_zeroOne_of_le_tail {a : ℕ → ℝ} (ha : Summable a)
    (ha0 : ∀ n, 0 ≤ a n)
    (hdom : ∀ n, a n ≤ tailSum a (n + 1))
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ ∑' n, a n) :
    ∃ ε : ℕ → Bool, HasSum (fun n => if ε n then a n else 0) x := by
  have hbounds := greedyResidual_bounds ha ha0 hdom hx0 (by simpa [tailSum] using hx)
  have hres : Tendsto (greedyResidual a x) atTop (nhds 0) := by
    apply squeeze_zero (fun n => (hbounds n).1) (fun n => (hbounds n).2)
    exact tendsto_tailSum_zero ha
  let ε : ℕ → Bool := fun n => decide (a n ≤ greedyResidual a x n)
  have hterm (n : ℕ) : (if ε n then a n else 0) = greedyTerm a x n := by
    simp only [ε, greedyTerm, decide_eq_true_eq]
  have hnonneg (n : ℕ) : 0 ≤ greedyTerm a x n := by
    simp only [greedyTerm]
    split_ifs
    · exact ha0 n
    · exact le_rfl
  have hle (n : ℕ) : greedyTerm a x n ≤ a n := by
    simp only [greedyTerm]
    split_ifs
    · exact le_rfl
    · exact ha0 n
  have hsum : Summable (greedyTerm a x) :=
    Summable.of_nonneg_of_le hnonneg hle ha
  refine ⟨ε, (hasSum_iff_tendsto_nat_of_summable_norm ?_).2 ?_⟩
  · convert hsum using 1
    funext n
    rw [hterm n, Real.norm_eq_abs, abs_of_nonneg (hnonneg n)]
  · have hpartial : Tendsto (fun n => x - greedyResidual a x n) atTop (nhds x) := by
      simpa using tendsto_const_nhds.sub hres
    convert hpartial using 1
    funext n
    rw [← sum_greedyTerm a x n]
    apply sum_congr rfl
    intro k hk
    exact hterm k

/-- A point in the interior of the Kakeya interval can be approximated strictly
from below by a finite subsum. -/
lemma exists_finset_sum_lt_of_le_tail {a : ℕ → ℝ} (ha : Summable a)
    (ha0 : ∀ n, 0 ≤ a n)
    (hdom : ∀ n, a n ≤ tailSum a (n + 1))
    {x η : ℝ} (hx : 0 < x) (hxtop : x < ∑' n, a n) (hη : 0 < η) :
    ∃ s : Finset ℕ, ∑ n ∈ s, a n < x ∧ x < ∑ n ∈ s, a n + η := by
  let δ := min (x / 2) (η / 2)
  have hδ : 0 < δ := lt_min (half_pos hx) (half_pos hη)
  let y := x - δ
  have hy0 : 0 ≤ y := by
    dsimp [y, δ]
    have := min_le_left (x / 2) (η / 2)
    linarith
  have hyx : y < x := sub_lt_self x hδ
  have hytop : y ≤ ∑' n, a n := hyx.le.trans hxtop.le
  obtain ⟨ε, hε⟩ := exists_hasSum_zeroOne_of_le_tail ha ha0 hdom hy0 hytop
  let b : ℕ → ℝ := fun n => if ε n then a n else 0
  have hb0 (n : ℕ) : 0 ≤ b n := by
    dsimp [b]
    split_ifs
    · exact ha0 n
    · exact le_rfl
  have hbSum : HasSum b y := hε
  obtain ⟨N, hNall⟩ := (Metric.tendsto_atTop.1 hbSum.tendsto_sum_nat) δ hδ
  have hN := hNall N le_rfl
  let s := (range N).filter fun n => ε n
  have hsum : ∑ n ∈ s, a n = ∑ n ∈ range N, b n := by
    rw [sum_filter]
  have hle : ∑ n ∈ range N, b n ≤ y := by
    have hbs : Summable b := hbSum.summable
    calc
      ∑ n ∈ range N, b n ≤ ∑' n, b n := hbs.sum_le_tsum _ fun n _ => hb0 n
      _ = y := hbSum.tsum_eq
  refine ⟨s, ?_, ?_⟩
  · rw [hsum]
    exact hle.trans_lt hyx
  · rw [hsum]
    rw [Real.dist_eq] at hN
    have hlower : y - δ < ∑ n ∈ range N, b n := by
      linarith [(abs_lt.mp hN).1]
    dsimp [y, δ] at hlower ⊢
    have hδle : δ ≤ η / 2 := min_le_right _ _
    linarith

/-! ## The dyadic partition -/

/-- Zero-based enumeration of the positive integers with exact `2`-adic row `j`:
`dyadicIndex j k + 1 = 2^j * (2*k+1)`. -/
def dyadicIndex (j k : ℕ) : ℕ :=
  2 ^ j * (2 * k + 1) - 1

@[simp]
lemma dyadicIndex_add_one (j k : ℕ) :
    dyadicIndex j k + 1 = 2 ^ j * (2 * k + 1) := by
  rw [dyadicIndex]
  have : 0 < 2 ^ j * (2 * k + 1) := by positivity
  omega

lemma dyadicIndex_injective :
    Function.Injective (Function.uncurry dyadicIndex) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  change dyadicIndex j k = dyadicIndex j' k' at h
  have hprod : 2 ^ j * (2 * k + 1) = 2 ^ j' * (2 * k' + 1) := by
    simpa only [← dyadicIndex_add_one] using congrArg (· + 1) h
  have hfac := congrArg (fun n : ℕ => n.factorization 2) hprod
  have hodd (r : ℕ) : (2 * r + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (Nat.two_not_dvd_two_mul_add_one r)
  have hj : j = j' := by
    simpa [Nat.factorization_mul, hodd, Nat.prime_two.factorization_pow] using hfac
  subst j'
  have hk : k = k' := by
    have hp : 0 < 2 ^ j := by positivity
    have := Nat.eq_of_mul_eq_mul_left hp hprod
    omega
  simp [hk]

lemma dyadicIndex_surjective :
    Function.Surjective (Function.uncurry dyadicIndex) := by
  intro n
  obtain ⟨j, m, hm, heq⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.succ_ne_zero n)
  rcases hm with ⟨k, hk⟩
  subst m
  refine ⟨(j, k), ?_⟩
  change dyadicIndex j k = n
  rw [dyadicIndex, ← heq]
  omega

/-- The equivalence implementing the dyadic partition of all positive indices. -/
def dyadicEquiv : ℕ × ℕ ≃ ℕ :=
  Equiv.ofBijective (Function.uncurry dyadicIndex)
    ⟨dyadicIndex_injective, dyadicIndex_surjective⟩

@[simp]
lemma dyadicEquiv_apply (p : ℕ × ℕ) :
    dyadicEquiv p = dyadicIndex p.1 p.2 := rfl

/-- The term obtained on row `j` when the short length `j+1` is used. -/
def rowTerm (j k : ℕ) : ℝ :=
  productTerm (dyadicIndex j k) (j + 1)

lemma rowTerm_pos (j k : ℕ) : 0 < rowTerm j k :=
  productTerm_pos _ _

lemma rowTerm_nonneg (j k : ℕ) : 0 ≤ rowTerm j k :=
  (rowTerm_pos j k).le

@[simp]
lemma rowTerm_zero (k : ℕ) : rowTerm 0 k = 1 / ((2 * k + 2 : ℕ) : ℝ) := by
  simp [rowTerm, productTerm, dyadicIndex, Nat.ascFactorial, one_div]

lemma k_add_one_le_dyadicIndex_add_two (j k : ℕ) :
    k + 1 ≤ dyadicIndex j k + 2 := by
  rw [show dyadicIndex j k + 2 = (dyadicIndex j k + 1) + 1 by omega,
    dyadicIndex_add_one]
  have hp : 1 ≤ 2 ^ j := one_le_pow₀ (by omega)
  nlinarith

lemma rowTerm_le_pseries (j k : ℕ) :
    rowTerm j k ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ (j + 1) := by
  calc
    rowTerm j k ≤ 1 / (((dyadicIndex j k + 2 : ℕ) : ℝ) ^ (j + 1)) := by
      simpa only [rowTerm, one_div] using
        productTerm_le_inv_pow (dyadicIndex j k) (j + 1)
    _ ≤ 1 / (((k + 1 : ℕ) : ℝ) ^ (j + 1)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · apply pow_le_pow_left₀
        · positivity
        · exact_mod_cast k_add_one_le_dyadicIndex_add_two j k

lemma summable_rowTerm {j : ℕ} (hj : 1 ≤ j) : Summable (rowTerm j) := by
  have hp : 1 < j + 1 := by omega
  have hmajor : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ (j + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.mpr hp)
  exact Summable.of_nonneg_of_le (rowTerm_nonneg j) (rowTerm_le_pseries j) hmajor

/-- A coarse linear denominator bound for the block `k < l ≤ 2*k`. -/
lemma block_denominator_le (j k r : ℕ) (hk : 1 ≤ k) (hr : r < k) :
    dyadicIndex j (k + 1 + r) + j + 2 ≤
      (5 * 2 ^ j + j + 1) * k := by
  rw [show dyadicIndex j (k + 1 + r) + j + 2 =
    (dyadicIndex j (k + 1 + r) + 1) + j + 1 by omega,
    dyadicIndex_add_one]
  have hrle : r + 1 ≤ k := by omega
  have hp : 1 ≤ 2 ^ j := one_le_pow₀ (by omega)
  nlinarith

lemma block_lower_bound (j k r : ℕ) (hk : 1 ≤ k) (hr : r < k) :
    (1 / ((((5 * 2 ^ j + j + 1) * k : ℕ) : ℝ) ^ (j + 1))) ≤
      rowTerm j (k + 1 + r) := by
  calc
    1 / ((((5 * 2 ^ j + j + 1) * k : ℕ) : ℝ) ^ (j + 1)) ≤
        1 / (((dyadicIndex j (k + 1 + r) + j + 2 : ℕ) : ℝ) ^ (j + 1)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · gcongr
        exact_mod_cast block_denominator_le j k r hk hr
    _ ≤ rowTerm j (k + 1 + r) := by
      simpa only [rowTerm, one_div, Nat.add_assoc] using
        inv_pow_add_le_productTerm (dyadicIndex j (k + 1 + r)) (j + 1)

lemma current_rowTerm_upper (j k : ℕ) (hk : 1 ≤ k) :
    rowTerm j k ≤ 1 / ((((2 ^ j) * k : ℕ) : ℝ) ^ (j + 1)) := by
  calc
    rowTerm j k ≤ 1 / (((dyadicIndex j k + 2 : ℕ) : ℝ) ^ (j + 1)) := by
      simpa only [rowTerm, one_div] using
        productTerm_le_inv_pow (dyadicIndex j k) (j + 1)
    _ ≤ 1 / ((((2 ^ j) * k : ℕ) : ℝ) ^ (j + 1)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · apply pow_le_pow_left₀
        · positivity
        · exact_mod_cast (show 2 ^ j * k ≤ dyadicIndex j k + 2 by
            rw [show dyadicIndex j k + 2 = (dyadicIndex j k + 1) + 1 by omega,
              dyadicIndex_add_one]
            have hp : 1 ≤ 2 ^ j := one_le_pow₀ (by omega)
            nlinarith)

lemma inv_current_le_block_mass (j k : ℕ) (hk : (5 * 2 ^ j + j + 1) ^ (j + 1) ≤ k) :
    1 / ((((2 ^ j) * k : ℕ) : ℝ) ^ (j + 1)) ≤
      (k : ℝ) * (1 / ((((5 * 2 ^ j + j + 1) * k : ℕ) : ℝ) ^ (j + 1))) := by
  let A : ℕ := 2 ^ j
  let C : ℕ := 5 * 2 ^ j + j + 1
  let p : ℕ := j + 1
  have hA : 1 ≤ A ^ p := by
    apply one_le_pow₀
    dsimp [A]
    have hp : 0 < 2 ^ j := pow_pos (by omega : 0 < (2 : ℕ)) j
    omega
  have hnat : (C * k) ^ p ≤ k * (A * k) ^ p := by
    rw [mul_pow, mul_pow]
    have hC : C ^ p ≤ k := by simpa [C, p] using hk
    calc
      C ^ p * k ^ p ≤ k * k ^ p := Nat.mul_le_mul_right (k ^ p) hC
      _ ≤ (k * A ^ p) * k ^ p :=
        Nat.mul_le_mul_right (k ^ p) (by nlinarith)
      _ = k * (A ^ p * k ^ p) := by ring
  have hX : 0 < (((C * k : ℕ) : ℝ) ^ p) := by
    have hkpos : 0 < k := lt_of_lt_of_le (by positivity) hk
    positivity
  have hY : 0 < (((A * k : ℕ) : ℝ) ^ p) := by
    have hkpos : 0 < k := lt_of_lt_of_le (by positivity) hk
    positivity
  have hreal : (((C * k : ℕ) : ℝ) ^ p) ≤
      (k : ℝ) * (((A * k : ℕ) : ℝ) ^ p) := by
    exact_mod_cast hnat
  calc
    1 / (((A * k : ℕ) : ℝ) ^ p) ≤
        (k : ℝ) / (((C * k : ℕ) : ℝ) ^ p) := by
      apply (le_div_iff₀ hX).2
      calc
        1 / (((A * k : ℕ) : ℝ) ^ p) * (((C * k : ℕ) : ℝ) ^ p) =
            (((C * k : ℕ) : ℝ) ^ p) / (((A * k : ℕ) : ℝ) ^ p) := by
              rw [one_div, inv_mul_eq_div]
        _ ≤ (k : ℝ) := (div_le_iff₀ hY).2 hreal
    _ = (k : ℝ) * (1 / (((C * k : ℕ) : ℝ) ^ p)) := by
      rw [div_eq_mul_inv, one_div]
  
  

/-- The fixed-length row satisfies Kakeya's tail-domination condition from an
explicit (deliberately coarse) threshold onward. -/
lemma rowTerm_le_tail {j k : ℕ} (hj : 1 ≤ j)
    (hk : (5 * 2 ^ j + j + 1) ^ (j + 1) ≤ k) :
    rowTerm j k ≤ tailSum (rowTerm j) (k + 1) := by
  have hk1 : 1 ≤ k := by
    have : 1 ≤ (5 * 2 ^ j + j + 1) ^ (j + 1) := one_le_pow₀ (by omega)
    omega
  have hs := summable_rowTerm hj
  calc
    rowTerm j k ≤ 1 / ((((2 ^ j) * k : ℕ) : ℝ) ^ (j + 1)) :=
      current_rowTerm_upper j k hk1
    _ ≤ (k : ℝ) * (1 / ((((5 * 2 ^ j + j + 1) * k : ℕ) : ℝ) ^ (j + 1))) :=
      inv_current_le_block_mass j k hk
    _ = ∑ r ∈ range k,
        (1 / ((((5 * 2 ^ j + j + 1) * k : ℕ) : ℝ) ^ (j + 1))) := by simp
    _ ≤ ∑ r ∈ range k, rowTerm j (k + 1 + r) := by
      apply sum_le_sum
      intro r hr
      exact block_lower_bound j k r hk1 (mem_range.mp hr)
    _ ≤ ∑' r, rowTerm j (k + 1 + r) := by
      have hshift : Summable (fun r => rowTerm j (k + 1 + r)) := by
        simpa only [Nat.add_comm] using (summable_nat_add_iff (k + 1)).2 hs
      exact hshift.sum_le_tsum _ fun r _ => rowTerm_nonneg j _
    _ = tailSum (rowTerm j) (k + 1) := by
      apply tsum_congr
      intro r
      simp [Nat.add_comm]

/-! ## Summable Kakeya tails on the positive rows -/

/-- The explicit point beyond which row `j` has tail domination. -/
def rowStart (j : ℕ) : ℕ :=
  (5 * 2 ^ j + j + 1) ^ (j + 1)

/-- The Kakeya tail of the fixed-length row `j`. -/
def tailRow (j k : ℕ) : ℝ :=
  rowTerm j (rowStart j + k)

lemma tailRow_pos (j k : ℕ) : 0 < tailRow j k :=
  rowTerm_pos _ _

lemma tailRow_nonneg (j k : ℕ) : 0 ≤ tailRow j k :=
  (tailRow_pos j k).le

lemma summable_tailRow {j : ℕ} (hj : 1 ≤ j) : Summable (tailRow j) := by
  apply ((summable_nat_add_iff (rowStart j)).2 (summable_rowTerm hj)).congr
  intro k
  simp only [tailRow, Nat.add_comm]

lemma tailSum_tailRow {j : ℕ} (_hj : 1 ≤ j) (k : ℕ) :
    tailSum (tailRow j) k = tailSum (rowTerm j) (rowStart j + k) := by
  apply tsum_congr
  intro r
  simp only [tailRow]
  congr 1
  omega

lemma tailRow_le_tail {j : ℕ} (hj : 1 ≤ j) (k : ℕ) :
    tailRow j k ≤ tailSum (tailRow j) (k + 1) := by
  rw [tailSum_tailRow hj]
  exact rowTerm_le_tail hj (by simp [rowStart])

/-- Total capacity of the Kakeya tail of row `j`. -/
def rowCapacity (j : ℕ) : ℝ :=
  ∑' k, tailRow j k

lemma rowCapacity_pos {j : ℕ} (hj : 1 ≤ j) : 0 < rowCapacity j := by
  have hs := summable_tailRow hj
  calc
    0 < tailRow j 0 := tailRow_pos j 0
    _ ≤ ∑' k, tailRow j k := by
      simpa using hs.sum_le_tsum {0} (by
        intro k hk
        exact tailRow_nonneg j k)
    _ = rowCapacity j := rfl

lemma exists_positive_row_finset {j : ℕ} (hj : 1 ≤ j)
    {x η : ℝ} (hx : 0 < x) (hcap : x < rowCapacity j) (hη : 0 < η) :
    ∃ s : Finset ℕ,
      ∑ k ∈ s, rowTerm j k < x ∧ x < ∑ k ∈ s, rowTerm j k + η ∧
      ∀ k ∈ s, rowStart j ≤ k := by
  obtain ⟨s, hsx, hxs⟩ := exists_finset_sum_lt_of_le_tail
    (summable_tailRow hj) (tailRow_nonneg j) (tailRow_le_tail hj)
    hx hcap hη
  let t := s.image (rowStart j + ·)
  have hinj : Function.Injective (rowStart j + ·) := fun _ _ h => Nat.add_left_cancel h
  have hsum : ∑ k ∈ t, rowTerm j k = ∑ r ∈ s, tailRow j r := by
    rw [show t = s.image (rowStart j + ·) by rfl, sum_image]
    · rfl
    · intro a ha b hb hab
      exact hinj hab
  refine ⟨t, ?_, ?_, ?_⟩
  · rw [hsum]
    exact hsx
  · rw [hsum]
    exact hxs
  · intro k hk
    simp only [t, mem_image] at hk
    obtain ⟨r, -, rfl⟩ := hk
    omega

/-! ## The divergent first row -/

lemma exists_finset_approx_of_tendsto_zero_divergent
    {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n)
    (hzero : Tendsto a atTop (nhds 0))
    (hdiv : Tendsto (fun N => ∑ n ∈ range N, a n) atTop atTop)
    {x η : ℝ} (hx : 0 < x) (hη : 0 < η) :
    ∃ s : Finset ℕ, ∑ n ∈ s, a n < x ∧ x < ∑ n ∈ s, a n + η := by
  have hsmall : ∀ᶠ n in atTop, a n < η :=
    (tendsto_order.1 hzero).2 η hη
  obtain ⟨K, hK⟩ := eventually_atTop.1 hsmall
  have hnot : ¬ Summable a :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg ha0).2 hdiv
  have hnotShift : ¬ Summable (fun n => a (K + n)) := by
    intro hs
    apply hnot
    apply (summable_nat_add_iff K).1
    exact hs.congr fun n => by rw [Nat.add_comm]
  have hdivShift : Tendsto (fun N => ∑ n ∈ range N, a (K + n)) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun n => ha0 (K + n))).1 hnotShift
  obtain ⟨M, hM⟩ : ∃ M, x ≤ ∑ n ∈ range M, a (K + n) :=
    ((tendsto_atTop.1 hdivShift x).exists)
  have hM0 : M ≠ 0 := by
    intro h
    subst M
    simp at hM
    linarith
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  let P : ℕ → Prop := fun N => x ≤ ∑ n ∈ range (N + 1), a (K + n)
  have hP : ∃ N, P N := ⟨m, by simpa [P]⟩
  let N := Nat.find hP
  have hcross : x ≤ ∑ n ∈ range (N + 1), a (K + n) := Nat.find_spec hP
  have hbefore : ∑ n ∈ range N, a (K + n) < x := by
    by_cases hN0 : N = 0
    · simpa [hN0] using hx
    · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hN0
      rw [hn]
      exact lt_of_not_ge (Nat.find_min hP (by
        dsimp [N] at hn
        omega))
  have hlast : a (K + N) < η := hK (K + N) (by omega)
  have hclose : x < ∑ n ∈ range N, a (K + n) + η := by
    rw [sum_range_succ] at hcross
    linarith
  let s := (range N).image (K + ·)
  have hinj : Function.Injective (K + ·) := fun _ _ h => Nat.add_left_cancel h
  have hsum : ∑ n ∈ s, a n = ∑ n ∈ range N, a (K + n) := by
    rw [show s = (range N).image (K + ·) by rfl]
    exact sum_image hinj.injOn
  exact ⟨s, by simpa only [hsum] using hbefore, by simpa only [hsum] using hclose⟩

lemma tendsto_rowTerm_zero : Tendsto (rowTerm 0) atTop (nhds 0) := by
  have hbase : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmul := (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul hbase
  convert hmul using 1
  · funext k
    rw [rowTerm_zero]
    push_cast
    field_simp
  · norm_num

lemma tendsto_rowTerm_partialSum_atTop :
    Tendsto (fun N => ∑ k ∈ range N, rowTerm 0 k) atTop atTop := by
  have h := Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop
    (show 0 < (1 / 2 : ℝ) by norm_num)
  convert h using 1
  funext N
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [rowTerm_zero]
  push_cast
  field_simp

lemma exists_zero_row_finset {x η : ℝ} (hx : 0 < x) (hη : 0 < η) :
    ∃ s : Finset ℕ,
      ∑ k ∈ s, rowTerm 0 k < x ∧ x < ∑ k ∈ s, rowTerm 0 k + η :=
  exists_finset_approx_of_tendsto_zero_divergent (rowTerm_nonneg 0)
    tendsto_rowTerm_zero tendsto_rowTerm_partialSum_atTop hx hη

/-! ## Completing a finite choice by negligible long fillers -/

/-- On row `j`, finitely many indices receive the short length `j+1`; all
other indices receive individually chosen long filler lengths. -/
structure RowChoice (j : ℕ) where
  selected : Finset ℕ
  fillerLength : ℕ → ℕ

instance (j : ℕ) : Inhabited (RowChoice j) :=
  ⟨⟨∅, fun _ => 1⟩⟩

def RowChoice.length {j : ℕ} (c : RowChoice j) (k : ℕ) : ℕ :=
  if k ∈ c.selected then j + 1 else c.fillerLength k

def RowChoice.term {j : ℕ} (c : RowChoice j) (k : ℕ) : ℝ :=
  productTerm (dyadicIndex j k) (c.length k)

def RowChoice.value {j : ℕ} (c : RowChoice j) : ℝ :=
  ∑' k, c.term k

lemma RowChoice.term_nonneg {j : ℕ} (c : RowChoice j) (k : ℕ) :
    0 ≤ c.term k := productTerm_nonneg _ _

lemma RowChoice.term_of_mem {j : ℕ} (c : RowChoice j) {k : ℕ}
    (hk : k ∈ c.selected) : c.term k = rowTerm j k := by
  simp [RowChoice.term, RowChoice.length, rowTerm, hk]

lemma RowChoice.term_of_not_mem {j : ℕ} (c : RowChoice j) {k : ℕ}
    (hk : k ∉ c.selected) :
    c.term k = productTerm (dyadicIndex j k) (c.fillerLength k) := by
  simp [RowChoice.term, RowChoice.length, hk]

/-- Any finite short choice which lies just below `x` can be completed by
positive long fillers without consuming more than one quarter of the gap. -/
lemma exists_completed_rowChoice (j : ℕ) (s : Finset ℕ)
    {x η : ℝ} (hsx : ∑ k ∈ s, rowTerm j k < x)
    (hxs : x < ∑ k ∈ s, rowTerm j k + η) :
    ∃ c : RowChoice j,
      Summable c.term ∧
      (∀ k, dyadicIndex j k + j + 1 < c.fillerLength k) ∧
      0 < x - c.value ∧ x - c.value < η := by
  let q : ℝ := x - ∑ k ∈ s, rowTerm j k
  have hq : 0 < q := by dsimp [q]; linarith
  have hqη : q < η := by dsimp [q]; linarith
  let major : ℕ → ℝ := fun k => (q / 8) * (1 / 2 : ℝ) ^ k
  have hmajorPos (k : ℕ) : 0 < major k := by
    dsimp [major]
    positivity
  have hlength (k : ℕ) : ∃ l > dyadicIndex j k + j + 1,
      productTerm (dyadicIndex j k) l < major k :=
    exists_large_length_small _ _ (hmajorPos k)
  choose g hgLong hgSmall using hlength
  let c : RowChoice j := ⟨s, g⟩
  let chosen : ℕ → ℝ := fun k => if k ∈ s then rowTerm j k else 0
  let filler : ℕ → ℝ := fun k =>
    if k ∈ s then 0 else productTerm (dyadicIndex j k) (g k)
  have hchosen : Summable chosen := by
    apply summable_of_hasFiniteSupport
    apply s.finite_toSet.subset
    intro k hk
    simp only [Function.mem_support, chosen] at hk ⊢
    by_contra hks
    have hknot : k ∉ s := by simpa using hks
    simp [hknot] at hk
  have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    hasSum_geometric_two.summable
  have hmajor : Summable major := by
    exact hgeom.mul_left (q / 8)
  have hfiller0 (k : ℕ) : 0 ≤ filler k := by
    dsimp [filler]
    split_ifs
    · exact le_rfl
    · exact productTerm_nonneg _ _
  have hfillerMajor (k : ℕ) : filler k ≤ major k := by
    dsimp [filler]
    split_ifs
    · exact (hmajorPos k).le
    · exact (hgSmall k).le
  have hfiller : Summable filler :=
    Summable.of_nonneg_of_le hfiller0 hfillerMajor hmajor
  have hmajorSum : ∑' k, major k = q / 4 := by
    rw [show major = fun k : ℕ => (q / 8) * (1 / 2 : ℝ) ^ k by rfl,
      tsum_mul_left, tsum_geometric_two]
    ring
  have hfillerBound : ∑' k, filler k ≤ q / 4 := by
    rw [← hmajorSum]
    exact hfiller.tsum_le_tsum hfillerMajor hmajor
  have hfillerSum0 : 0 ≤ ∑' k, filler k := tsum_nonneg hfiller0
  have hterm (k : ℕ) : c.term k = chosen k + filler k := by
    by_cases hk : k ∈ s
    · simp [c, RowChoice.term_of_mem, chosen, filler, hk]
    · simp [c, RowChoice.term_of_not_mem, chosen, filler, hk]
  have hcSum : Summable c.term := by
    apply (hchosen.add hfiller).congr
    intro k
    exact (hterm k).symm
  have hchosenSum : ∑' k, chosen k = ∑ k ∈ s, rowTerm j k := by
    calc
      ∑' k, chosen k = ∑' k, (↑s : Set ℕ).indicator (rowTerm j) k := by
        apply tsum_congr
        intro k
        simp only [chosen]
        by_cases hk : k ∈ s <;> simp [Set.indicator, hk]
      _ = ∑ k ∈ s, rowTerm j k := (sum_eq_tsum_indicator (rowTerm j) s).symm
  have hcValue : c.value = ∑ k ∈ s, rowTerm j k + ∑' k, filler k := by
    rw [RowChoice.value]
    calc
      ∑' k, c.term k = ∑' k, (chosen k + filler k) := tsum_congr hterm
      _ = (∑' k, chosen k) + ∑' k, filler k := hchosen.tsum_add hfiller
      _ = _ := by rw [hchosenSum]
  refine ⟨c, hcSum, ?_, ?_, ?_⟩
  · intro k
    exact hgLong k
  · rw [hcValue]
    have : ∑' k, filler k < q := lt_of_le_of_lt hfillerBound (by linarith)
    dsimp [q] at this ⊢
    linarith
  · rw [hcValue]
    dsimp [q] at hqη ⊢
    linarith

def ChoiceGood {j : ℕ} (x η : ℝ) (c : RowChoice j) : Prop :=
  Summable c.term ∧
    (∀ k, dyadicIndex j k + j + 1 < c.fillerLength k) ∧
    0 < x - c.value ∧ x - c.value < η

lemma exists_zero_choice {x η : ℝ} (hx : 0 < x) (hη : 0 < η) :
    ∃ c : RowChoice 0, ChoiceGood x η c := by
  obtain ⟨s, hsx, hxs⟩ := exists_zero_row_finset hx hη
  exact exists_completed_rowChoice 0 s hsx hxs

lemma exists_positive_choice {j : ℕ} (hj : 1 ≤ j)
    {x η : ℝ} (hx : 0 < x) (hcap : x < rowCapacity j) (hη : 0 < η) :
    ∃ c : RowChoice j, ChoiceGood x η c := by
  obtain ⟨s, hsx, hxs, hsstart⟩ := exists_positive_row_finset hj hx hcap hη
  exact exists_completed_rowChoice j s hsx hxs

def chooseZeroRow (x η : ℝ) : RowChoice 0 :=
  if h : 0 < x ∧ 0 < η then Classical.choose (exists_zero_choice h.1 h.2)
  else default

lemma chooseZeroRow_good {x η : ℝ} (hx : 0 < x) (hη : 0 < η) :
    ChoiceGood x η (chooseZeroRow x η) := by
  rw [chooseZeroRow, dif_pos ⟨hx, hη⟩]
  exact Classical.choose_spec (exists_zero_choice hx hη)

def choosePositiveRow (j : ℕ) (x η : ℝ) : RowChoice j :=
  if h : 1 ≤ j ∧ 0 < x ∧ x < rowCapacity j ∧ 0 < η then
    Classical.choose (exists_positive_choice h.1 h.2.1 h.2.2.1 h.2.2.2)
  else default

lemma choosePositiveRow_good {j : ℕ} (hj : 1 ≤ j)
    {x η : ℝ} (hx : 0 < x) (hcap : x < rowCapacity j) (hη : 0 < η) :
    ChoiceGood x η (choosePositiveRow j x η) := by
  rw [choosePositiveRow, dif_pos ⟨hj, hx, hcap, hη⟩]
  exact Classical.choose_spec (exists_positive_choice hj hx hcap hη)

/-! ## The recursive row-by-row construction -/

/-- Error budget after row `j`: small enough to fit in the next row and
bounded by a geometric sequence. -/
def stageError (j : ℕ) : ℝ :=
  min (rowCapacity (j + 1)) ((1 / 2 : ℝ) ^ j)

lemma stageError_pos (j : ℕ) : 0 < stageError j := by
  apply lt_min
  · exact rowCapacity_pos (by omega)
  · positivity

lemma stageError_le_capacity (j : ℕ) :
    stageError j ≤ rowCapacity (j + 1) := min_le_left _ _

lemma stageError_le_geometric (j : ℕ) :
    stageError j ≤ (1 / 2 : ℝ) ^ j := min_le_right _ _

structure Stage (j : ℕ) where
  choice : RowChoice j
  remaining : ℝ

/-- Stage `j` records the row choice and the residual after completing that
row.  Each recursive call only uses the preceding residual. -/
def stages (alpha : ℝ) : (j : ℕ) → Stage j
  | 0 =>
      let c := chooseZeroRow alpha (stageError 0)
      ⟨c, alpha - c.value⟩
  | j + 1 =>
      let previous := stages alpha j
      let c := choosePositiveRow (j + 1) previous.remaining (stageError (j + 1))
      ⟨c, previous.remaining - c.value⟩

@[simp]
lemma stages_zero_choice (alpha : ℝ) :
    (stages alpha 0).choice = chooseZeroRow alpha (stageError 0) := rfl

@[simp]
lemma stages_zero_remaining (alpha : ℝ) :
    (stages alpha 0).remaining = alpha - (stages alpha 0).choice.value := rfl

@[simp]
lemma stages_succ_choice (alpha : ℝ) (j : ℕ) :
    (stages alpha (j + 1)).choice =
      choosePositiveRow (j + 1) (stages alpha j).remaining (stageError (j + 1)) := rfl

@[simp]
lemma stages_succ_remaining (alpha : ℝ) (j : ℕ) :
    (stages alpha (j + 1)).remaining =
      (stages alpha j).remaining - (stages alpha (j + 1)).choice.value := rfl

lemma stages_good {alpha : ℝ} (halpha : 0 < alpha) (j : ℕ) :
    Summable (stages alpha j).choice.term ∧
    (∀ k, dyadicIndex j k + j + 1 < (stages alpha j).choice.fillerLength k) ∧
    0 < (stages alpha j).remaining ∧
    (stages alpha j).remaining < stageError j := by
  induction j with
  | zero =>
      have hgood := chooseZeroRow_good halpha (stageError_pos 0)
      simpa [ChoiceGood] using hgood
  | succ j ih =>
      have hcap : (stages alpha j).remaining < rowCapacity (j + 1) :=
        ih.2.2.2.trans_le (stageError_le_capacity j)
      have hgood := choosePositiveRow_good (j := j + 1) (by omega)
        ih.2.2.1 hcap (stageError_pos (j + 1))
      simpa [ChoiceGood] using hgood

lemma tendsto_stages_remaining_zero {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun j => (stages alpha j).remaining) atTop (nhds 0) := by
  apply squeeze_zero
  · intro j
    exact (stages_good halpha j).2.2.1.le
  · intro j
    exact (stages_good halpha j).2.2.2.le.trans (stageError_le_geometric j)
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma sum_stage_values (alpha : ℝ) (N : ℕ) :
    ∑ j ∈ range (N + 1), (stages alpha j).choice.value =
      alpha - (stages alpha N).remaining := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih, stages_succ_remaining]
      ring

lemma hasSum_stage_values {alpha : ℝ} (halpha : 0 < alpha) :
    HasSum (fun j => (stages alpha j).choice.value) alpha := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun j => tsum_nonneg fun k => (stages alpha j).choice.term_nonneg k) alpha).2
  apply (tendsto_add_atTop_iff_nat 1).1
  have hlim := (tendsto_const_nhds (x := alpha)).sub
    (tendsto_stages_remaining_zero halpha)
  have hlim' : Tendsto (fun j => alpha - (stages alpha j).remaining)
      atTop (nhds alpha) := by simpa using hlim
  convert hlim' using 1
  funext N
  exact sum_stage_values alpha N

/-! ## Flattening the rows and proving that the lengths diverge -/

def pairTerm (alpha : ℝ) (p : ℕ × ℕ) : ℝ :=
  (stages alpha p.1).choice.term p.2

lemma pairTerm_nonneg (alpha : ℝ) (p : ℕ × ℕ) :
    0 ≤ pairTerm alpha p :=
  (stages alpha p.1).choice.term_nonneg p.2

lemma summable_pairTerm {alpha : ℝ} (halpha : 0 < alpha) :
    Summable (pairTerm alpha) := by
  apply (summable_prod_of_nonneg (pairTerm_nonneg alpha)).2
  constructor
  · intro j
    exact (stages_good halpha j).1
  · simpa only [pairTerm, RowChoice.value] using (hasSum_stage_values halpha).summable

lemma hasSum_pairTerm {alpha : ℝ} (halpha : 0 < alpha) :
    HasSum (pairTerm alpha) alpha := by
  have hs := summable_pairTerm halpha
  have hsum : ∑' p, pairTerm alpha p = alpha := by
    calc
      ∑' p, pairTerm alpha p = ∑' j, ∑' k, pairTerm alpha (j, k) := hs.tsum_prod
      _ = ∑' j, (stages alpha j).choice.value := by rfl
      _ = alpha := (hasSum_stage_values halpha).tsum_eq
  convert hs.hasSum using 1
  exact hsum.symm

def pairLength (alpha : ℝ) (p : ℕ × ℕ) : ℕ :=
  (stages alpha p.1).choice.length p.2

lemma pairTerm_eq_productTerm (alpha : ℝ) (p : ℕ × ℕ) :
    pairTerm alpha p = productTerm (dyadicIndex p.1 p.2) (pairLength alpha p) := rfl

lemma pairLength_pos {alpha : ℝ} (halpha : 0 < alpha) (p : ℕ × ℕ) :
    0 < pairLength alpha p := by
  by_cases hp : p.2 ∈ (stages alpha p.1).choice.selected
  · simp [pairLength, RowChoice.length, hp]
  · rw [pairLength, RowChoice.length, if_neg hp]
    have hlong := (stages_good halpha p.1).2.1 p.2
    omega

/-- Pairs which can carry a selected short length below `B`. -/
def exceptionalPairs (alpha : ℝ) (B : ℕ) : Finset (ℕ × ℕ) :=
  (range B).biUnion fun j =>
    (stages alpha j).choice.selected.image fun k => (j, k)

lemma mem_exceptionalPairs {alpha : ℝ} {B j k : ℕ}
    (hj : j < B) (hk : k ∈ (stages alpha j).choice.selected) :
    (j, k) ∈ exceptionalPairs alpha B := by
  apply mem_biUnion.mpr
  refine ⟨j, mem_range.mpr hj, ?_⟩
  exact mem_image.mpr ⟨k, hk, rfl⟩

def exceptionalIndices (alpha : ℝ) (B : ℕ) : Finset ℕ :=
  (exceptionalPairs alpha B).image dyadicEquiv

lemma eventually_pairLength_ge {alpha : ℝ} (halpha : 0 < alpha) (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, B ≤ pairLength alpha (dyadicEquiv.symm n) := by
  let bad := exceptionalIndices alpha B
  let N := bad.sup id + B + 1
  filter_upwards [eventually_ge_atTop N] with n hn
  let p := dyadicEquiv.symm n
  have hindex : dyadicIndex p.1 p.2 = n := by
    have he := dyadicEquiv.apply_symm_apply n
    simpa only [dyadicEquiv_apply] using he
  by_cases hk : p.2 ∈ (stages alpha p.1).choice.selected
  · have hj : B ≤ p.1 := by
      by_contra hnot
      have hpbad : p ∈ exceptionalPairs alpha B :=
        mem_exceptionalPairs (Nat.lt_of_not_ge hnot) hk
      have hnbad : n ∈ bad := by
        apply mem_image.mpr
        exact ⟨p, hpbad, by simp [p]⟩
      have hnle : n ≤ bad.sup id := by
        simpa using (Finset.le_sup (f := id) hnbad)
      dsimp [N] at hn
      omega
    change B ≤ (stages alpha p.1).choice.length p.2
    rw [RowChoice.length, if_pos hk]
    omega
  · change B ≤ (stages alpha p.1).choice.length p.2
    rw [RowChoice.length, if_neg hk]
    have hlong := (stages_good halpha p.1).2.1 p.2
    rw [hindex] at hlong
    have hnB : B ≤ n := by
      dsimp [N] at hn
      omega
    omega

/-! ## The function in Erdős Problem 270 and the final resolution -/

/-- The constructed positive-integer-valued function.  The value at zero is
irrelevant to the original one-based series. -/
def erdosFunction (alpha : ℝ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => pairLength alpha (dyadicEquiv.symm n)

lemma erdosFunction_pos {alpha : ℝ} (halpha : 0 < alpha) (n : ℕ) :
    0 < erdosFunction alpha n := by
  cases n with
  | zero => simp [erdosFunction]
  | succ n =>
      simpa only [erdosFunction] using pairLength_pos halpha (dyadicEquiv.symm n)

lemma tendsto_erdosFunction {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (erdosFunction alpha) atTop atTop := by
  apply (tendsto_add_atTop_iff_nat 1).1
  apply tendsto_atTop.2
  intro B
  simpa only [erdosFunction] using eventually_pairLength_ge halpha B

lemma hasSum_erdosFunction {alpha : ℝ} (halpha : 0 < alpha) :
    HasSum (fun n => productTerm n (erdosFunction alpha (n + 1))) alpha := by
  have hpairs := hasSum_pairTerm halpha
  have hreindexed : HasSum (pairTerm alpha ∘ dyadicEquiv.symm) alpha :=
    (dyadicEquiv.symm.hasSum_iff).2 hpairs
  convert hreindexed using 1
  funext n
  let p := dyadicEquiv.symm n
  have hindex : dyadicIndex p.1 p.2 = n := by
    have he := dyadicEquiv.apply_symm_apply n
    simpa only [dyadicEquiv_apply] using he
  rw [Function.comp_apply, pairTerm_eq_productTerm]
  simp only [erdosFunction]
  rw [hindex]

/-- **Crmarić--Kovač's resolution of Erdős Problem 270.**  Every positive
real number is represented by the series in the problem, with a positive
integer-valued length function tending to infinity.  The index `n` below is
zero-based, so its term is the original term with one-based index `n+1`. -/
theorem erdos_270_resolution (alpha : ℝ) (halpha : 0 < alpha) :
    ∃ f : ℕ → ℕ,
      (∀ n, 0 < f n) ∧
      Tendsto f atTop atTop ∧
      HasSum (fun n => (((n + 2).ascFactorial (f (n + 1)) : ℕ) : ℝ)⁻¹) alpha := by
  refine ⟨erdosFunction alpha, erdosFunction_pos halpha,
    tendsto_erdosFunction halpha, ?_⟩
  simpa only [productTerm] using hasSum_erdosFunction halpha

/-- The assertion asked about in Problem 270, stated with the exact zero-based
reindexing of its one-based series. -/
def Erdos270Assertion : Prop :=
  ∀ f : ℕ → ℕ,
    (∀ n, 0 < f n) →
    Tendsto f atTop atTop →
    Irrational (∑' n, productTerm n (f (n + 1)))

/-- Consequently, the answer to Erdős and Graham's question is no. -/
theorem not_erdos_270 :
    ¬ (∀ f : ℕ → ℕ,
      (∀ n, 0 < f n) →
      Tendsto f atTop atTop →
      Irrational (∑' n, productTerm n (f (n + 1)))) := by
  intro hassert
  obtain ⟨f, hfpos, hflim, hsum⟩ := erdos_270_resolution 1 (by norm_num)
  have hsum' : HasSum (fun n => productTerm n (f (n + 1))) 1 := by
    simpa only [productTerm] using hsum
  have hirr := hassert f hfpos hflim
  rw [hsum'.tsum_eq] at hirr
  exact (by norm_num : ¬ Irrational (1 : ℝ)) hirr

#print axioms erdos_270_resolution
#print axioms not_erdos_270

end

end Erdos270

alias _root_.Erdos270.erdos_270 := _root_.Erdos270.not_erdos_270
