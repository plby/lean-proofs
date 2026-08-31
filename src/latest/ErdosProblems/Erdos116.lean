/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 116.
https://www.erdosproblems.com/forum/thread/116

Informal authors:
- Christian Pommerenke

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos116.md
-/
import Mathlib

/-!
# Erdős Problem 116

For `n > 0` and zeros `a i` in the closed unit disk, this file proves an
explicit polynomial lower bound for the planar measure of
`{z : ℂ | ‖∏ i, (z - a i)‖ < 1}`.  The proof follows the elementary reflected
polynomial and finite-Fourier argument documented in `tex/116.tex`.
-/

open scoped BigOperators ENNReal
open Polynomial MeasureTheory Set Metric Complex

noncomputable section

namespace Erdos116

/-- The monic polynomial product occurring literally in Problem 116. -/
def lemniscateProduct {n : ℕ} (a : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∏ i, (z - a i)

/-- The reflected product `∏ i, (1 - conj (a i) X)`. -/
def reflectedPoly {n : ℕ} (a : Fin n → ℂ) : Polynomial ℂ :=
  ∏ i, (1 - C (starRingEnd ℂ (a i)) * X)

@[simp] lemma reflectedPoly_eval {n : ℕ} (a : Fin n → ℂ) (z : ℂ) :
    (reflectedPoly a).eval z = ∏ i, (1 - starRingEnd ℂ (a i) * z) := by
  simp only [reflectedPoly, Polynomial.eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X]

@[simp] lemma reflectedPoly_coeff_zero {n : ℕ} (a : Fin n → ℂ) :
    (reflectedPoly a).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, reflectedPoly_eval]
  simp

lemma reflectedPoly_natDegree_le {n : ℕ} (a : Fin n → ℂ) :
    (reflectedPoly a).natDegree ≤ n := by
  unfold reflectedPoly
  refine (Polynomial.natDegree_prod_le Finset.univ
    (fun i : Fin n => 1 - C (starRingEnd ℂ (a i)) * X)).trans ?_
  calc
    ∑ i : Fin n, (1 - C (starRingEnd ℂ (a i)) * X).natDegree
        ≤ ∑ _i : Fin n, 1 := by
          gcongr with i
          exact (natDegree_sub_le _ _).trans (max_le (by simp)
            (natDegree_mul_le.trans (by simp)))
    _ = n := by simp

lemma blaschke_norm_sq_le (a z : ℂ) (ha : ‖a‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    ‖z - a‖ ^ 2 ≤ ‖1 - starRingEnd ℂ a * z‖ ^ 2 := by
  norm_num [Complex.normSq, Complex.sq_norm] at *
  norm_num [Complex.normSq, Complex.norm_def] at *
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hz)]

lemma blaschke_norm_le (a z : ℂ) (ha : ‖a‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    ‖z - a‖ ≤ ‖1 - starRingEnd ℂ a * z‖ :=
  le_of_pow_le_pow_left₀ (by norm_num) (by positivity) (blaschke_norm_sq_le a z ha hz)

lemma lemniscateProduct_norm_le_reflected {n : ℕ} (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖lemniscateProduct a z‖ ≤ ‖(reflectedPoly a).eval z‖ := by
  simp only [lemniscateProduct, reflectedPoly_eval, norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => blaschke_norm_le _ _ (ha i) hz)

/-! ## The real-variable end of the Fourier argument -/

lemma finite_real_negativity {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0 < n)
    (x : ι → ℝ) (A : ℝ) (hA : 0 < A)
    (hcard : Fintype.card ι = 2 * n + 1)
    (hsum : ∑ i, x i = 0)
    (henergy : ∑ i, (x i) ^ 2 = (Fintype.card ι : ℝ) * A ^ 2 / 2)
    (hbound : ∀ i, |x i| ≤ (n : ℝ) * A) :
    ∃ i, x i ≤ -A / (4 * n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : (0 : ℝ) < 4 * n := mul_pos (by norm_num) hnR
  have habs (i : ι) : |x i| = x i + 2 * max (-x i) 0 := by
    rcases le_total 0 (x i) with hi | hi
    · simp [abs_of_nonneg hi, hi]
    · simp [abs_of_nonpos hi, hi]
      ring
  have habssum : ∑ i, |x i| = 2 * ∑ i, max (-x i) 0 := by
    simp_rw [habs]
    rw [Finset.sum_add_distrib, hsum, zero_add, ← Finset.mul_sum]
  have hsq_le : ∑ i, (x i) ^ 2 ≤ (n : ℝ) * A * (∑ i, |x i|) := by
    calc
      ∑ i, (x i) ^ 2 = ∑ i, |x i| ^ 2 := by
        congr 1 with i
        exact (sq_abs (x i)).symm
      _ ≤ ∑ i, ((n : ℝ) * A) * |x i| := by
        apply Finset.sum_le_sum
        intro i _
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (hbound i) (abs_nonneg _)
      _ = (n : ℝ) * A * (∑ i, |x i|) := by rw [Finset.mul_sum]
  by_contra h
  push Not at h
  have hneg (i : ι) : max (-x i) 0 < A / (4 * n) := by
    rw [max_lt_iff]
    constructor
    · have hi : -(A / (4 * n)) < x i := by
        simpa only [neg_div] using h i
      linarith
    · exact div_pos hA hden
  have huniv : (Finset.univ : Finset ι).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fintype.card_pos_iff.mp (by omega)
  have hnegsum : ∑ i, max (-x i) 0 < (Fintype.card ι : ℝ) * (A / (4 * n)) := by
    calc
      ∑ i, max (-x i) 0 < ∑ _i : ι, A / (4 * n) :=
        Finset.sum_lt_sum_of_nonempty huniv (fun i _ => hneg i)
      _ = (Fintype.card ι : ℝ) * (A / (4 * n)) := by simp [mul_comm]
  rw [henergy, habssum] at hsq_le
  rw [hcard] at hsq_le hnegsum
  norm_num [Nat.cast_add, Nat.cast_mul] at hsq_le hnegsum
  have hnegsum' : 4 * (n : ℝ) * (∑ i, max (-x i) 0) < (2 * (n : ℝ) + 1) * A := by
    calc
      4 * (n : ℝ) * (∑ i, max (-x i) 0)
          < 4 * (n : ℝ) * ((2 * (n : ℝ) + 1) * (A / (4 * n))) :=
            mul_lt_mul_of_pos_left hnegsum hden
      _ = (2 * (n : ℝ) + 1) * A := by field_simp
  have hstrict := mul_lt_mul_of_pos_right hnegsum' (show 0 < A / 2 by positivity)
  nlinarith

/-! ## Roots of unity and finite Fourier identities -/

/-- The standard primitive `N`-th root of unity. -/
def fourierRoot (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

lemma fourierRoot_isPrimitive {N : ℕ} (hN : N ≠ 0) :
    IsPrimitiveRoot (fourierRoot N) N := by
  simpa [fourierRoot] using Complex.isPrimitiveRoot_exp N hN

lemma fourierRoot_norm {N : ℕ} (hN : N ≠ 0) : ‖fourierRoot N‖ = 1 :=
  (fourierRoot_isPrimitive hN).norm'_eq_one hN

lemma sum_fourierRoot_pow_eq_zero {N m : ℕ} (hN : N ≠ 0) (hm0 : m ≠ 0)
    (hmN : m < N) :
    ∑ j : Fin N, fourierRoot N ^ (j.val * m) = 0 := by
  let ω := fourierRoot N
  have hprim : IsPrimitiveRoot ω N := fourierRoot_isPrimitive hN
  have hne : 1 - ω ^ m ≠ 0 := sub_ne_zero.mpr (hprim.pow_ne_one_of_pos_of_lt hm0 hmN).symm
  have hgeom : ∑ j ∈ Finset.range N, (ω ^ m) ^ j = 0 := by
    apply eq_zero_of_ne_zero_of_mul_left_eq_zero hne
    rw [mul_neg_geom_sum]
    simp only [← pow_mul]
    rw [mul_comm m N, pow_mul, hprim.pow_eq_one, one_pow, sub_self]
  simpa only [← Fin.sum_univ_eq_sum_range, pow_mul, Nat.mul_comm] using hgeom

/-- The Fourier sample of the frequencies `1, ..., n`. -/
def fourierSample {n : ℕ} (b : Fin n → ℂ) (j : Fin (2 * n + 1)) : ℂ :=
  ∑ k, b k * fourierRoot (2 * n + 1) ^ (j.val * (k.val + 1))

lemma fourierSample_norm_le {n : ℕ} (b : Fin n → ℂ) (j : Fin (2 * n + 1)) :
    ‖fourierSample b j‖ ≤ ∑ k, ‖b k‖ := by
  unfold fourierSample
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul, norm_pow, fourierRoot_norm (by omega), one_pow, mul_one]

lemma sum_fourierRoot_mul_conj {N k l : ℕ} (hN : N ≠ 0) (hk : k < N) (hl : l < N) :
    ∑ j : Fin N, fourierRoot N ^ (j.val * k) *
        starRingEnd ℂ (fourierRoot N ^ (j.val * l)) =
      if k = l then (N : ℂ) else 0 := by
  let ω := fourierRoot N
  have hωnorm : ‖ω‖ = 1 := fourierRoot_norm hN
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h, norm_zero] at hωnorm
    norm_num at hωnorm
  by_cases hkl : k = l
  · subst l
    calc
      ∑ j : Fin N, ω ^ (j.val * k) * starRingEnd ℂ (ω ^ (j.val * k))
          = ∑ _j : Fin N, (1 : ℂ) := by
              congr 1 with j
              rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, hωnorm, one_pow]
              norm_num
      _ = (N : ℂ) := by simp
      _ = if k = k then (N : ℂ) else 0 := by simp
  · simp only [if_neg hkl]
    wlog hlk : l ≤ k generalizing k l
    · have hswap := this hl hk (Ne.symm hkl) (le_of_not_ge hlk)
      have hconj := congrArg (starRingEnd ℂ) hswap
      simpa only [map_sum, map_mul, map_zero, map_pow, starRingEnd_self_apply,
        mul_comm] using hconj
    have hlt : l < k := lt_of_le_of_ne hlk (Ne.symm hkl)
    have hdiff0 : k - l ≠ 0 := by omega
    have hdiffN : k - l < N := (Nat.sub_le k l).trans_lt hk
    calc
      ∑ j : Fin N, ω ^ (j.val * k) * starRingEnd ℂ (ω ^ (j.val * l))
          = ∑ j : Fin N, ω ^ (j.val * (k - l)) := by
              congr 1 with j
              rw [← Complex.inv_eq_conj]
              · rw [← pow_sub₀ ω hω0 (Nat.mul_le_mul_left j.val hlk),
                  ← Nat.mul_sub_left_distrib]
              · rw [norm_pow, hωnorm, one_pow]
      _ = 0 := sum_fourierRoot_pow_eq_zero hN hdiff0 hdiffN

lemma sum_fourierSample_eq_zero {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ) :
    ∑ j, fourierSample b j = 0 := by
  unfold fourierSample
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k _
  rw [← Finset.mul_sum, sum_fourierRoot_pow_eq_zero (by omega) (by omega) (by omega), mul_zero]

lemma sum_conj_fourierTerm_mul {n : ℕ} (b : Fin n → ℂ) (k l : Fin n) :
    ∑ j : Fin (2 * n + 1),
        starRingEnd ℂ
            (b k * fourierRoot (2 * n + 1) ^ (j.val * (k.val + 1))) *
          (b l * fourierRoot (2 * n + 1) ^ (j.val * (l.val + 1))) =
      if k = l then (2 * n + 1 : ℂ) * starRingEnd ℂ (b k) * b l else 0 := by
  rw [show ∑ j : Fin (2 * n + 1),
      starRingEnd ℂ
          (b k * fourierRoot (2 * n + 1) ^ (j.val * (k.val + 1))) *
        (b l * fourierRoot (2 * n + 1) ^ (j.val * (l.val + 1))) =
      starRingEnd ℂ (b k) * b l * ∑ j : Fin (2 * n + 1),
        fourierRoot (2 * n + 1) ^ (j.val * (l.val + 1)) *
          starRingEnd ℂ (fourierRoot (2 * n + 1) ^ (j.val * (k.val + 1))) by
        rw [Finset.mul_sum]
        congr 1 with j
        simp only [map_mul, map_pow]
        ring]
  rw [sum_fourierRoot_mul_conj (by omega) (by omega) (by omega)]
  by_cases hkl : k = l
  · subst l
    simp only [ite_true]
    simp
    ring
  · have hval : l.val ≠ k.val := by
      intro h
      apply hkl
      exact Fin.ext h.symm
    simp [hkl, hval]

lemma sum_fourierSample_norm_sq {n : ℕ} (b : Fin n → ℂ) :
    ∑ j : Fin (2 * n + 1), ‖fourierSample b j‖ ^ 2 =
      (2 * n + 1 : ℝ) * ∑ k, ‖b k‖ ^ 2 := by
  have hcomplex :
      ∑ j : Fin (2 * n + 1),
          starRingEnd ℂ (fourierSample b j) * fourierSample b j =
        (2 * n + 1 : ℂ) * ∑ k, starRingEnd ℂ (b k) * b k := by
    calc
      ∑ j : Fin (2 * n + 1),
          starRingEnd ℂ (fourierSample b j) * fourierSample b j =
          ∑ j : Fin (2 * n + 1), ∑ k : Fin n, ∑ l : Fin n,
            starRingEnd ℂ
                (b k * fourierRoot (2 * n + 1) ^ (j.val * (k.val + 1))) *
              (b l * fourierRoot (2 * n + 1) ^ (j.val * (l.val + 1))) := by
            congr 1 with j
            simp only [fourierSample, map_sum, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
      _ = ∑ k : Fin n, ∑ l : Fin n, ∑ j : Fin (2 * n + 1),
            starRingEnd ℂ
                (b k * fourierRoot (2 * n + 1) ^ (j.val * (k.val + 1))) *
              (b l * fourierRoot (2 * n + 1) ^ (j.val * (l.val + 1))) := by
            rw [Finset.sum_comm]
            congr 1 with k
            rw [Finset.sum_comm]
      _ = ∑ k : Fin n, ∑ l : Fin n,
            if k = l then (2 * n + 1 : ℂ) * starRingEnd ℂ (b k) * b l else 0 := by
            simp_rw [sum_conj_fourierTerm_mul]
      _ = (2 * n + 1 : ℂ) * ∑ k, starRingEnd ℂ (b k) * b k := by
            simp [Finset.mul_sum, mul_assoc]
  simp_rw [← Complex.normSq_eq_conj_mul_self] at hcomplex
  have hreal :
      ∑ j : Fin (2 * n + 1), Complex.normSq (fourierSample b j) =
        (2 * n + 1 : ℝ) * ∑ k, Complex.normSq (b k) := by
    exact_mod_cast hcomplex
  simpa only [Complex.normSq_eq_norm_sq] using hreal

lemma sum_fourierTerm_mul {n : ℕ} (b : Fin n → ℂ) (k l : Fin n) :
    ∑ j : Fin (2 * n + 1),
        (b k * fourierRoot (2 * n + 1) ^ (j.val * (k.val + 1))) *
          (b l * fourierRoot (2 * n + 1) ^ (j.val * (l.val + 1))) = 0 := by
  rw [show ∑ j : Fin (2 * n + 1),
      (b k * fourierRoot (2 * n + 1) ^ (j.val * (k.val + 1))) *
        (b l * fourierRoot (2 * n + 1) ^ (j.val * (l.val + 1))) =
      b k * b l * ∑ j : Fin (2 * n + 1),
        fourierRoot (2 * n + 1) ^
          (j.val * ((k.val + 1) + (l.val + 1))) by
        rw [Finset.mul_sum]
        congr 1 with j
        rw [Nat.mul_add, pow_add]
        ring]
  rw [sum_fourierRoot_pow_eq_zero (by omega) (by omega) (by omega), mul_zero]

lemma sum_fourierSample_sq {n : ℕ} (b : Fin n → ℂ) :
    ∑ j : Fin (2 * n + 1), (fourierSample b j) ^ 2 = 0 := by
  calc
    ∑ j : Fin (2 * n + 1), (fourierSample b j) ^ 2 =
        ∑ j : Fin (2 * n + 1), ∑ k : Fin n, ∑ l : Fin n,
          (b k * fourierRoot (2 * n + 1) ^ (j.val * (k.val + 1))) *
            (b l * fourierRoot (2 * n + 1) ^ (j.val * (l.val + 1))) := by
          congr 1 with j
          simp only [fourierSample, pow_two, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ l : Fin n, ∑ j : Fin (2 * n + 1),
          (b k * fourierRoot (2 * n + 1) ^ (j.val * (k.val + 1))) *
            (b l * fourierRoot (2 * n + 1) ^ (j.val * (l.val + 1))) := by
          rw [Finset.sum_comm]
          congr 1 with k
          rw [Finset.sum_comm]
    _ = 0 := by simp_rw [sum_fourierTerm_mul, Finset.sum_const_zero]

lemma two_mul_re_sq (z : ℂ) : 2 * z.re ^ 2 = ‖z‖ ^ 2 + (z ^ 2).re := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, pow_two, Complex.mul_re]
  ring

lemma sum_fourierSample_re_sq {n : ℕ} (b : Fin n → ℂ) :
    ∑ j : Fin (2 * n + 1), (fourierSample b j).re ^ 2 =
      (2 * n + 1 : ℝ) * (∑ k, ‖b k‖ ^ 2) / 2 := by
  have hid : 2 * ∑ j : Fin (2 * n + 1), (fourierSample b j).re ^ 2 =
      (∑ j : Fin (2 * n + 1), ‖fourierSample b j‖ ^ 2) +
        ∑ j : Fin (2 * n + 1), ((fourierSample b j) ^ 2).re := by
    calc
      2 * ∑ j : Fin (2 * n + 1), (fourierSample b j).re ^ 2 =
          ∑ j : Fin (2 * n + 1), 2 * (fourierSample b j).re ^ 2 :=
            Finset.mul_sum _ _ _
      _ = ∑ j : Fin (2 * n + 1),
          (‖fourierSample b j‖ ^ 2 + ((fourierSample b j) ^ 2).re) := by
            congr 1 with j
            exact two_mul_re_sq _
      _ = _ := Finset.sum_add_distrib
  have hsquare_re : ∑ j : Fin (2 * n + 1), ((fourierSample b j) ^ 2).re = 0 := by
    have := congrArg Complex.re (sum_fourierSample_sq b)
    simpa only [Complex.re_sum, Complex.zero_re] using this
  rw [sum_fourierSample_norm_sq, hsquare_re, add_zero] at hid
  linarith

lemma fourier_negativity {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ)
    (hb : ∃ k, b k ≠ 0) :
    let A := Real.sqrt (∑ k, ‖b k‖ ^ 2)
    0 < A ∧ ∃ j : Fin (2 * n + 1),
      (fourierSample b j).re ≤ -A / (4 * n) ∧
      ‖fourierSample b j‖ ≤ (n : ℝ) * A := by
  let A := Real.sqrt (∑ k, ‖b k‖ ^ 2)
  have hsnonneg : 0 ≤ ∑ k, ‖b k‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  obtain ⟨k₀, hk₀⟩ := hb
  have hspos : 0 < ∑ k, ‖b k‖ ^ 2 := by
    apply Finset.sum_pos' (fun _ _ => sq_nonneg _)
    exact ⟨k₀, Finset.mem_univ k₀, sq_pos_of_pos (norm_pos_iff.mpr hk₀)⟩
  have hA : 0 < A := Real.sqrt_pos.2 hspos
  have hcoeff (k : Fin n) : ‖b k‖ ≤ A := by
    have hk : ‖b k‖ ^ 2 ≤ ∑ l, ‖b l‖ ^ 2 :=
      Finset.single_le_sum (s := Finset.univ) (f := fun l : Fin n => ‖b l‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    have := Real.sqrt_le_sqrt hk
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, A] using this
  have hsum_norm : ∑ k, ‖b k‖ ≤ (n : ℝ) * A := by
    calc
      ∑ k, ‖b k‖ ≤ ∑ _k : Fin n, A := Finset.sum_le_sum (fun k _ => hcoeff k)
      _ = (n : ℝ) * A := by simp
  have hsample_bound (j : Fin (2 * n + 1)) :
      |(fourierSample b j).re| ≤ (n : ℝ) * A :=
    (abs_re_le_norm _).trans ((fourierSample_norm_le b j).trans hsum_norm)
  have hsum_re : ∑ j : Fin (2 * n + 1), (fourierSample b j).re = 0 := by
    have := congrArg Complex.re (sum_fourierSample_eq_zero hn b)
    simpa only [Complex.re_sum, Complex.zero_re] using this
  have henergy : ∑ j : Fin (2 * n + 1), (fourierSample b j).re ^ 2 =
      (Fintype.card (Fin (2 * n + 1)) : ℝ) * A ^ 2 / 2 := by
    rw [sum_fourierSample_re_sq]
    simp only [Fintype.card_fin, A, Real.sq_sqrt hsnonneg]
    norm_num [Nat.cast_add, Nat.cast_mul]
  obtain ⟨j, hj⟩ := finite_real_negativity hn
    (fun j : Fin (2 * n + 1) => (fourierSample b j).re) A hA (by simp)
    hsum_re henergy hsample_bound
  exact ⟨hA, j, hj, (fourierSample_norm_le b j).trans hsum_norm⟩

/-! ## Uniform product and scale estimates -/

lemma norm_prod_one_sub_le_pow {ι : Type*} (s : Finset ι)
    (u : ι → ℂ) (r : ℝ) (hr : 0 ≤ r) (hu : ∀ i ∈ s, ‖u i‖ ≤ r) :
    ‖(∏ i ∈ s, (1 - u i)) - 1‖ ≤ (1 + r) ^ s.card - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hbase : 1 ≤ 1 + r := by linarith
      have hpow : 0 ≤ (1 + r) ^ s.card - 1 := sub_nonneg.mpr (one_le_pow₀ hbase)
      have hua : ‖u a‖ ≤ r := hu a (Finset.mem_insert_self a s)
      have hus : ∀ i ∈ s, ‖u i‖ ≤ r := fun i hi => hu i (Finset.mem_insert_of_mem hi)
      calc
        ‖(∏ i ∈ insert a s, (1 - u i)) - 1‖ =
            ‖(1 - u a) * ((∏ i ∈ s, (1 - u i)) - 1) - u a‖ := by
              rw [Finset.prod_insert ha]
              congr 1
              ring
        _ ≤ ‖1 - u a‖ * ‖(∏ i ∈ s, (1 - u i)) - 1‖ + ‖u a‖ :=
          by simpa only [norm_mul] using
            norm_sub_le ((1 - u a) * ((∏ i ∈ s, (1 - u i)) - 1)) (u a)
        _ ≤ (1 + r) * ((1 + r) ^ s.card - 1) + r := by
          gcongr
          · exact (norm_sub_le 1 (u a)).trans (by simpa using add_le_add_left hua 1)
          · exact ih hus
        _ = (1 + r) ^ (insert a s).card - 1 := by
          rw [Finset.card_insert_of_notMem ha, pow_succ]
          ring

/-- The sampling radius used in the proof. -/
def rho (n : ℕ) : ℝ := 1 / (2 ^ 8 * (n : ℝ) ^ 4)

/-- The radius of the disk finally placed in the lemniscate. -/
def delta (n : ℕ) : ℝ := rho n / (2 ^ 7 * (n : ℝ) ^ 3)

lemma rho_pos {n : ℕ} (hn : 0 < n) : 0 < rho n := by
  unfold rho
  positivity

lemma rho_le_inv {n : ℕ} (hn : 0 < n) : rho n ≤ (n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn4 : (n : ℝ) ≤ 2 ^ 8 * (n : ℝ) ^ 4 := by
    nlinarith [mul_self_nonneg ((n : ℝ) ^ 2 - 1), pow_pos hnR 2, pow_pos hnR 3]
  unfold rho
  simpa only [one_div] using one_div_le_one_div_of_le hnR hn4

lemma one_add_rho_pow_lt_three {n : ℕ} (hn : 0 < n) :
    (1 + rho n) ^ n < 3 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (1 + rho n) ^ n ≤ (1 + (n : ℝ)⁻¹) ^ n := by
      apply pow_le_pow_left₀ (by positivity [rho_pos hn])
      linarith [rho_le_inv hn]
    _ ≤ Real.exp 1 := Real.one_add_inv_pow_le_exp
    _ < 3 := Real.exp_one_lt_three

lemma one_add_rho_pow_sub_one_lt {n : ℕ} (hn : 0 < n) :
    (1 + rho n) ^ n - 1 < 3 * n * rho n := by
  have hrho : 0 < rho n := rho_pos hn
  have hbase : 1 ≤ 1 + rho n := by linarith
  have hsum : ∑ i ∈ Finset.range n, (1 + rho n) ^ i < (n : ℝ) * 3 := by
    calc
      ∑ i ∈ Finset.range n, (1 + rho n) ^ i <
          ∑ _i ∈ Finset.range n, (3 : ℝ) := by
            apply Finset.sum_lt_sum_of_nonempty
            · exact ⟨0, by simpa using hn⟩
            · intro i hi
              exact (pow_le_pow_right₀ hbase (Nat.le_of_lt (Finset.mem_range.mp hi))).trans_lt
                (one_add_rho_pow_lt_three hn)
      _ = (n : ℝ) * 3 := by simp
  have hgeom :
      (∑ i ∈ Finset.range n, (1 + rho n) ^ i) * rho n + 1 = (1 + rho n) ^ n := by
    simpa [add_comm] using geom_sum_mul_add (rho n) n
  have hmul := mul_lt_mul_of_pos_right hsum hrho
  nlinarith

/-! ## Coefficients of the reflected polynomial -/

lemma reflectedPoly_eval_eq_one_add {n : ℕ} (a : Fin n → ℂ) (z : ℂ) :
    (reflectedPoly a).eval z =
      1 + ∑ k : Fin n, (reflectedPoly a).coeff (k.val + 1) * z ^ (k.val + 1) := by
  rw [Polynomial.eval_eq_sum_range'
    (lt_of_le_of_lt (reflectedPoly_natDegree_le a) (Nat.lt_succ_self n))]
  rw [← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, reflectedPoly_coeff_zero, Fin.val_succ]

lemma reflectedPoly_eq_one_of_coeff {n : ℕ} (a : Fin n → ℂ)
    (hcoeff : ∀ k : Fin n, (reflectedPoly a).coeff (k.val + 1) = 0) :
    reflectedPoly a = 1 := by
  ext m
  by_cases hm0 : m = 0
  · subst m
    simp
  by_cases hmn : m ≤ n
  · let k : Fin n := ⟨m - 1, by omega⟩
    have hmk : m = k.val + 1 := by simp [k]; omega
    rw [hmk, hcoeff]
    rw [coeff_one, if_neg (by omega)]
  · have hdeg : (reflectedPoly a).natDegree < m :=
      lt_of_le_of_lt (reflectedPoly_natDegree_le a) (lt_of_not_ge hmn)
    rw [coeff_eq_zero_of_natDegree_lt hdeg]
    rw [coeff_one, if_neg hm0]

lemma all_roots_zero_of_reflectedPoly_eq_one {n : ℕ} (a : Fin n → ℂ)
    (hpoly : reflectedPoly a = 1) : ∀ i, a i = 0 := by
  intro i
  by_contra hai
  have hconj : starRingEnd ℂ (a i) ≠ 0 := by simpa using hai
  let z : ℂ := (starRingEnd ℂ (a i))⁻¹
  have heval := congrArg (Polynomial.eval z) hpoly
  have hleft : (reflectedPoly a).eval z = 0 := by
    rw [reflectedPoly_eval]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [z, hconj]
  rw [hleft] at heval
  simp at heval

lemma lemniscateProduct_eq_pow_of_reflectedPoly_eq_one {n : ℕ} (a : Fin n → ℂ)
    (hpoly : reflectedPoly a = 1) (z : ℂ) :
    lemniscateProduct a z = z ^ n := by
  simp [lemniscateProduct, all_roots_zero_of_reflectedPoly_eq_one a hpoly]

/-- Coefficients of `q - 1`, scaled to the sampling circle. -/
def scaledCoeffs {n : ℕ} (a : Fin n → ℂ) (k : Fin n) : ℂ :=
  (reflectedPoly a).coeff (k.val + 1) * (rho n : ℂ) ^ (k.val + 1)

lemma fourierSample_scaledCoeffs {n : ℕ} (a : Fin n → ℂ)
    (j : Fin (2 * n + 1)) :
    fourierSample (scaledCoeffs a) j =
      (reflectedPoly a).eval
          ((rho n : ℂ) * fourierRoot (2 * n + 1) ^ j.val) - 1 := by
  rw [reflectedPoly_eval_eq_one_add, add_sub_cancel_left]
  unfold fourierSample scaledCoeffs
  congr 1 with k
  rw [mul_pow, pow_mul]
  ring

lemma scaledCoeffs_nonzero_of_reflectedPoly_ne_one {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℂ) (hpoly : reflectedPoly a ≠ 1) :
    ∃ k, scaledCoeffs a k ≠ 0 := by
  by_contra h
  push Not at h
  apply hpoly
  apply reflectedPoly_eq_one_of_coeff
  intro k
  have hk := h k
  unfold scaledCoeffs at hk
  exact (mul_eq_zero.mp hk).resolve_right
    (pow_ne_zero _ (ofReal_ne_zero.mpr (ne_of_gt (rho_pos hn))))

lemma reflectedPoly_eval_sub_one_lt {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (z : ℂ) (hz : ‖z‖ = rho n) :
    ‖(reflectedPoly a).eval z - 1‖ < 3 * n * rho n := by
  rw [reflectedPoly_eval]
  refine (norm_prod_one_sub_le_pow Finset.univ
    (fun i => starRingEnd ℂ (a i) * z) (rho n) (rho_pos hn).le ?_).trans_lt ?_
  · intro i _
    rw [norm_mul, norm_conj, hz]
    exact mul_le_of_le_one_left (rho_pos hn).le (ha i)
  · simpa using one_add_rho_pow_sub_one_lt hn

lemma scaledCoeffs_sqrt_sum_lt {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) :
    Real.sqrt (∑ k, ‖scaledCoeffs a k‖ ^ 2) < 3 * n * rho n := by
  let B : ℝ := 3 * n * rho n
  have hB : 0 < B := by
    dsimp [B]
    positivity [rho_pos hn]
  have hsample (j : Fin (2 * n + 1)) : ‖fourierSample (scaledCoeffs a) j‖ < B := by
    rw [fourierSample_scaledCoeffs]
    apply reflectedPoly_eval_sub_one_lt hn a ha
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (rho_pos hn), norm_pow,
      fourierRoot_norm (by omega), one_pow, mul_one]
  have hsquares (j : Fin (2 * n + 1)) :
      ‖fourierSample (scaledCoeffs a) j‖ ^ 2 < B ^ 2 := by
    exact (sq_lt_sq₀ (norm_nonneg _) hB.le).2 (hsample j)
  have hsum_lt :
      ∑ j : Fin (2 * n + 1), ‖fourierSample (scaledCoeffs a) j‖ ^ 2 <
        (2 * n + 1 : ℝ) * B ^ 2 := by
    calc
      ∑ j : Fin (2 * n + 1), ‖fourierSample (scaledCoeffs a) j‖ ^ 2 <
          ∑ _j : Fin (2 * n + 1), B ^ 2 := by
            apply Finset.sum_lt_sum_of_nonempty
            · simp
            · exact fun j _ => hsquares j
      _ = (2 * n + 1 : ℝ) * B ^ 2 := by
        simp
  rw [sum_fourierSample_norm_sq] at hsum_lt
  have hsum_coeff : ∑ k, ‖scaledCoeffs a k‖ ^ 2 < B ^ 2 := by
    have hN : (0 : ℝ) < 2 * n + 1 := by positivity
    nlinarith
  exact (Real.sqrt_lt' hB).2 hsum_coeff

/-! ## A coefficient-relative local Lipschitz estimate -/

lemma norm_pow_sub_pow_le (w z : ℂ) (m : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hw : ‖w‖ ≤ R) (hz : ‖z‖ ≤ R) :
    ‖w ^ m - z ^ m‖ ≤ (m : ℝ) * R ^ (m - 1) * ‖w - z‖ := by
  rw [← (Commute.all w z).mul_geom_sum₂ m, norm_mul]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
  have hterm (i : ℕ) (hi : i ∈ Finset.range m) :
      ‖w ^ i * z ^ (m - 1 - i)‖ ≤ R ^ (m - 1) := by
    rw [norm_mul, norm_pow, norm_pow]
    have hi' : i ≤ m - 1 := by
      have him := Finset.mem_range.mp hi
      omega
    calc
      ‖w‖ ^ i * ‖z‖ ^ (m - 1 - i) ≤ R ^ i * R ^ (m - 1 - i) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hw i)
          (pow_le_pow_left₀ (norm_nonneg _) hz (m - 1 - i)) (by positivity) (by positivity)
      _ = R ^ (i + (m - 1 - i)) := (pow_add R i (m - 1 - i)).symm
      _ = R ^ (m - 1) := by rw [Nat.add_sub_of_le hi']
  calc
    ‖w - z‖ * ∑ i ∈ Finset.range m, ‖w ^ i * z ^ (m - 1 - i)‖
        ≤ ‖w - z‖ * ∑ _i ∈ Finset.range m, R ^ (m - 1) := by
          gcongr with i hi
          exact hterm i hi
    _ = (m : ℝ) * R ^ (m - 1) * ‖w - z‖ := by
      simp
      ring

lemma scaledCoeff_norm_le_sqrt_sum {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (k : Fin n) :
    ‖(reflectedPoly a).coeff (k.val + 1)‖ * rho n ^ (k.val + 1) ≤
      Real.sqrt (∑ l, ‖scaledCoeffs a l‖ ^ 2) := by
  let A := Real.sqrt (∑ l, ‖scaledCoeffs a l‖ ^ 2)
  have hsingle : ‖scaledCoeffs a k‖ ^ 2 ≤ ∑ l, ‖scaledCoeffs a l‖ ^ 2 :=
    Finset.single_le_sum (s := Finset.univ) (f := fun l : Fin n => ‖scaledCoeffs a l‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  have hsqrt := Real.sqrt_le_sqrt hsingle
  have hnorm : ‖scaledCoeffs a k‖ =
      ‖(reflectedPoly a).coeff (k.val + 1)‖ * rho n ^ (k.val + 1) := by
    unfold scaledCoeffs
    rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos (rho_pos hn)]
  rw [Real.sqrt_sq_eq_abs, abs_norm, hnorm] at hsqrt
  exact hsqrt

lemma reflectedPoly_local_lipschitz {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (w z : ℂ)
    (hw : ‖w‖ ≤ rho n * (1 + (n : ℝ)⁻¹))
    (hz : ‖z‖ ≤ rho n * (1 + (n : ℝ)⁻¹)) :
    ‖(reflectedPoly a).eval w - (reflectedPoly a).eval z‖ ≤
      (3 * (n : ℝ) ^ 2 * Real.sqrt (∑ k, ‖scaledCoeffs a k‖ ^ 2) / rho n) * ‖w - z‖ := by
  let A := Real.sqrt (∑ k, ‖scaledCoeffs a k‖ ^ 2)
  let R := rho n * (1 + (n : ℝ)⁻¹)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrho : 0 < rho n := rho_pos hn
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hterm (k : Fin n) :
      ‖(reflectedPoly a).coeff (k.val + 1) *
          (w ^ (k.val + 1) - z ^ (k.val + 1))‖ ≤
        (3 * (n : ℝ) * A / rho n) * ‖w - z‖ := by
    let m := k.val + 1
    have hm0 : 0 < m := by simp [m]
    have hmn : m ≤ n := by dsimp [m]; omega
    have hmR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hscale : ‖(reflectedPoly a).coeff m‖ * rho n ^ m ≤ A := by
      simpa [m, A] using scaledCoeff_norm_le_sqrt_sum hn a k
    have hpow : (1 + (n : ℝ)⁻¹) ^ (m - 1) < 3 := by
      calc
        (1 + (n : ℝ)⁻¹) ^ (m - 1) ≤ (1 + (n : ℝ)⁻¹) ^ n :=
          pow_le_pow_right₀ (by have := inv_nonneg.mpr hnR.le; linarith) (by omega)
        _ ≤ Real.exp 1 := Real.one_add_inv_pow_le_exp
        _ < 3 := Real.exp_one_lt_three
    have hpower := norm_pow_sub_pow_le w z m R hR hw hz
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_left hpower (norm_nonneg _)).trans ?_
    have hid :
        (‖(reflectedPoly a).coeff m‖ *
            ((m : ℝ) * R ^ (m - 1) * ‖w - z‖)) * rho n =
          (‖(reflectedPoly a).coeff m‖ * rho n ^ m) *
            (m : ℝ) * (1 + (n : ℝ)⁻¹) ^ (m - 1) * ‖w - z‖ := by
      dsimp [R]
      have hm_pow : rho n ^ m = rho n ^ (m - 1) * rho n := by
        calc
          rho n ^ m = rho n ^ ((m - 1) + 1) := by congr 1
          _ = rho n ^ (m - 1) * rho n := pow_succ _ _
      rw [mul_pow, hm_pow]
      ring
    rw [show (3 * (n : ℝ) * A / rho n) * ‖w - z‖ =
        (3 * (n : ℝ) * A * ‖w - z‖) / rho n by ring]
    rw [le_div_iff₀ hrho]
    rw [hid]
    calc
      (‖(reflectedPoly a).coeff m‖ * rho n ^ m) *
          (m : ℝ) * (1 + (n : ℝ)⁻¹) ^ (m - 1) * ‖w - z‖
          ≤ A * (m : ℝ) * (1 + (n : ℝ)⁻¹) ^ (m - 1) * ‖w - z‖ := by
            gcongr
      _ ≤ A * (n : ℝ) * (1 + (n : ℝ)⁻¹) ^ (m - 1) * ‖w - z‖ := by
            gcongr
      _ ≤ A * (n : ℝ) * 3 * ‖w - z‖ := by
            gcongr
      _ = 3 * (n : ℝ) * A * ‖w - z‖ := by ring
  have heval :
      (reflectedPoly a).eval w - (reflectedPoly a).eval z =
        ∑ k : Fin n, (reflectedPoly a).coeff (k.val + 1) *
          (w ^ (k.val + 1) - z ^ (k.val + 1)) := by
    rw [reflectedPoly_eval_eq_one_add, reflectedPoly_eval_eq_one_add,
      add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    congr 1 with k
    ring
  rw [heval]
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ k : Fin n, ‖(reflectedPoly a).coeff (k.val + 1) *
        (w ^ (k.val + 1) - z ^ (k.val + 1))‖
        ≤ ∑ _k : Fin n, (3 * (n : ℝ) * A / rho n) * ‖w - z‖ :=
          Finset.sum_le_sum (fun k _ => hterm k)
    _ = (3 * (n : ℝ) ^ 2 * A / rho n) * ‖w - z‖ := by
      simp
      ring

lemma delta_pos {n : ℕ} (hn : 0 < n) : 0 < delta n := by
  unfold delta
  positivity [rho_pos hn]

lemma delta_le_rho_mul_inv {n : ℕ} (hn : 0 < n) :
    delta n ≤ rho n * (n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrho := rho_pos hn
  unfold delta
  rw [div_eq_mul_inv]
  gcongr
  have hpow : (n : ℝ) ^ 1 ≤ (n : ℝ) ^ 3 :=
    pow_le_pow_right₀ (by exact_mod_cast hn) (by norm_num)
  norm_num at hpow
  nlinarith [pow_pos hnR 3]

lemma rho_mul_one_add_inv_lt_one {n : ℕ} (hn : 0 < n) :
    rho n * (1 + (n : ℝ)⁻¹) < 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : (n : ℝ)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ hnR).2 hn1
  have hrho : rho n ≤ (1 : ℝ) / 256 := by
    unfold rho
    apply one_div_le_one_div_of_le (by norm_num)
    have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn1
    norm_num
    nlinarith
  have hrho0 := (rho_pos hn).le
  nlinarith [mul_le_mul hrho (show 1 + (n : ℝ)⁻¹ ≤ 2 by linarith)
    (by positivity) (by positivity)]

lemma scaledCoeffs_sqrt_sum_lt_inv {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) :
    Real.sqrt (∑ k, ‖scaledCoeffs a k‖ ^ 2) < 1 / (8 * (n : ℝ) ^ 3) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine (scaledCoeffs_sqrt_sum_lt hn a ha).trans ?_
  unfold rho
  field_simp [ne_of_gt hnR]
  norm_num

lemma norm_one_add_sq_sub_one (s : ℂ) :
    ‖1 + s‖ ^ 2 - 1 = 2 * s.re + ‖s‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  norm_num [Complex.normSq_apply]
  ring

lemma exists_ball_subset_lemniscate {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) :
    ∃ z₀ : ℂ, Metric.ball z₀ (delta n) ⊆
      {z : ℂ | ‖lemniscateProduct a z‖ < 1} := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrho : 0 < rho n := rho_pos hn
  have hdelta : 0 < delta n := delta_pos hn
  have hdeltaR : delta n ≤ rho n * (n : ℝ)⁻¹ := delta_le_rho_mul_inv hn
  have hRone : rho n * (1 + (n : ℝ)⁻¹) < 1 := rho_mul_one_add_inv_lt_one hn
  by_cases hpoly : reflectedPoly a = 1
  · refine ⟨0, ?_⟩
    intro w hw
    have hwnorm : ‖w‖ < 1 := by
      have hwδ : ‖w‖ < delta n := by simpa [Metric.mem_ball, dist_eq] using hw
      have : delta n < 1 := lt_of_le_of_lt hdeltaR (by
        nlinarith [mul_pos hrho (inv_pos.mpr hnR)])
      exact hwδ.trans this
    change ‖lemniscateProduct a w‖ < 1
    rw [lemniscateProduct_eq_pow_of_reflectedPoly_eq_one a hpoly, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hwnorm hn.ne'
  · let A : ℝ := Real.sqrt (∑ k, ‖scaledCoeffs a k‖ ^ 2)
    obtain ⟨hA, j, hjre, hjsnorm⟩ :=
      fourier_negativity hn (scaledCoeffs a)
        (scaledCoeffs_nonzero_of_reflectedPoly_ne_one hn a hpoly)
    have hA' : 0 < A := hA
    let z₀ : ℂ := (rho n : ℂ) * fourierRoot (2 * n + 1) ^ j.val
    let s : ℂ := fourierSample (scaledCoeffs a) j
    have hz₀norm : ‖z₀‖ = rho n := by
      dsimp [z₀]
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hrho, norm_pow,
        fourierRoot_norm (by omega), one_pow, mul_one]
    have hqz₀ : (reflectedPoly a).eval z₀ = 1 + s := by
      dsimp [z₀, s]
      rw [fourierSample_scaledCoeffs]
      ring
    have hsre : s.re ≤ -A / (4 * n) := hjre
    have hsnorm : ‖s‖ ≤ (n : ℝ) * A := hjsnorm
    have hAsm : A < 1 / (8 * (n : ℝ) ^ 3) :=
      scaledCoeffs_sqrt_sum_lt_inv hn a ha
    have hden8 : 0 < 8 * (n : ℝ) ^ 3 := by positivity
    have hAsm' : A * (8 * (n : ℝ) ^ 3) < 1 := by
      have := (lt_div_iff₀ hden8).mp hAsm
      simpa only [one_mul] using this
    have hquad : (n : ℝ) ^ 2 * A ^ 2 ≤ A / (4 * n) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * n)]
      have hmul := mul_lt_mul_of_pos_right hAsm' (show 0 < A / 2 by positivity)
      nlinarith
    have hsnormsq : ‖s‖ ^ 2 ≤ ((n : ℝ) * A) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hsnorm
    have hsnormsq' : ‖s‖ ^ 2 ≤ A / (4 * n) := by
      calc
        ‖s‖ ^ 2 ≤ ((n : ℝ) * A) ^ 2 := hsnormsq
        _ = (n : ℝ) ^ 2 * A ^ 2 := by ring
        _ ≤ A / (4 * n) := hquad
    have hq_sq : ‖(reflectedPoly a).eval z₀‖ ^ 2 - 1 ≤ -A / (4 * n) := by
      rw [hqz₀, norm_one_add_sq_sub_one]
      have hre2 : 2 * s.re ≤ 2 * (-A / (4 * n)) := mul_le_mul_of_nonneg_left hsre (by norm_num)
      calc
        2 * s.re + ‖s‖ ^ 2 ≤ 2 * (-A / (4 * n)) + A / (4 * n) :=
          add_le_add hre2 hsnormsq'
        _ = -A / (4 * n) := by ring
    have hdeficit : A / (4 * n) ≤ 1 - ‖(reflectedPoly a).eval z₀‖ ^ 2 := by
      calc
        A / (4 * n) = -(-A / (4 * n)) := by ring
        _ ≤ -(‖(reflectedPoly a).eval z₀‖ ^ 2 - 1) := neg_le_neg hq_sq
        _ = 1 - ‖(reflectedPoly a).eval z₀‖ ^ 2 := by ring
    have hqnorm_le_one : ‖(reflectedPoly a).eval z₀‖ ≤ 1 := by
      nlinarith [norm_nonneg ((reflectedPoly a).eval z₀)]
    have hmargin : A / (12 * n) ≤ 1 - ‖(reflectedPoly a).eval z₀‖ := by
      have hfac : 1 - ‖(reflectedPoly a).eval z₀‖ ^ 2 =
          (1 - ‖(reflectedPoly a).eval z₀‖) *
            (1 + ‖(reflectedPoly a).eval z₀‖) := by ring
      have hmul : (1 - ‖(reflectedPoly a).eval z₀‖) *
          (1 + ‖(reflectedPoly a).eval z₀‖) ≤
          (1 - ‖(reflectedPoly a).eval z₀‖) * 2 := by
        exact mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hqnorm_le_one)
      rw [hfac] at hdeficit
      have hden4 : (0 : ℝ) < 4 * n := by positivity
      have hden12 : (0 : ℝ) < 12 * n := by positivity
      have hmain := hdeficit.trans hmul
      rw [div_le_iff₀ hden12]
      have hclear := (div_le_iff₀ hden4).mp hmain
      have hd : 0 ≤ 1 - ‖(reflectedPoly a).eval z₀‖ := sub_nonneg.mpr hqnorm_le_one
      nlinarith [mul_nonneg hnR.le hd]
    refine ⟨z₀, ?_⟩
    intro w hwball
    have hdist : ‖w - z₀‖ < delta n := by
      simpa only [Metric.mem_ball, dist_eq] using hwball
    have hz₀R : ‖z₀‖ ≤ rho n * (1 + (n : ℝ)⁻¹) := by
      rw [hz₀norm]
      nlinarith [mul_pos hrho (inv_pos.mpr hnR)]
    have hwRlt : ‖w‖ < rho n * (1 + (n : ℝ)⁻¹) := by
      calc
        ‖w‖ ≤ ‖w - z₀‖ + ‖z₀‖ := by
          simpa only [sub_add_cancel] using norm_add_le (w - z₀) z₀
        _ < delta n + rho n := add_lt_add_of_lt_of_le hdist hz₀norm.le
        _ ≤ rho n * (n : ℝ)⁻¹ + rho n := by
          simpa [add_comm] using add_le_add_right hdeltaR (rho n)
        _ = rho n * (1 + (n : ℝ)⁻¹) := by ring
    have hlocal := reflectedPoly_local_lipschitz hn a w z₀ hwRlt.le hz₀R
    have hcoefpos :
        0 < 3 * (n : ℝ) ^ 2 * A / rho n :=
      div_pos (mul_pos (by positivity) hA') hrho
    have hdiff :
        ‖(reflectedPoly a).eval w - (reflectedPoly a).eval z₀‖ < A / (12 * n) := by
      calc
        ‖(reflectedPoly a).eval w - (reflectedPoly a).eval z₀‖ ≤
            (3 * (n : ℝ) ^ 2 * A / rho n) * ‖w - z₀‖ := hlocal
        _ < (3 * (n : ℝ) ^ 2 * A / rho n) * delta n :=
          mul_lt_mul_of_pos_left hdist hcoefpos
        _ = 3 * A / (2 ^ 7 * (n : ℝ)) := by
          unfold delta
          field_simp [ne_of_gt hnR, ne_of_gt hrho]
        _ < A / (12 * n) := by
          rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 7 * n)
            (by positivity : (0 : ℝ) < 12 * n)]
          nlinarith
    have hqw : ‖(reflectedPoly a).eval w‖ < 1 := by
      have htri : ‖(reflectedPoly a).eval w‖ ≤
          ‖(reflectedPoly a).eval w - (reflectedPoly a).eval z₀‖ +
            ‖(reflectedPoly a).eval z₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le
          ((reflectedPoly a).eval w - (reflectedPoly a).eval z₀)
          ((reflectedPoly a).eval z₀)
      linarith
    exact (lemniscateProduct_norm_le_reflected a ha w (hwRlt.trans hRone).le).trans_lt hqw

lemma delta_sq_eq {n : ℕ} (hn : 0 < n) :
    delta n ^ 2 = 1 / (2 ^ 30 * (n : ℝ) ^ 14) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold delta rho
  field_simp [ne_of_gt hnR]

/-- **Erdős Problem 116.**  The strict unit lemniscate of every monic product
whose `n > 0` zeros lie in the closed unit disk has an explicit uniform
polynomial area lower bound. -/
theorem erdos_116_explicit {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) :
    ENNReal.ofReal (Real.pi / (2 ^ 31 * (n : ℝ) ^ 14)) <
      volume {z : ℂ | ‖lemniscateProduct a z‖ < 1} := by
  obtain ⟨z₀, hz₀⟩ := exists_ball_subset_lemniscate hn a ha
  refine lt_of_lt_of_le ?_ (measure_mono hz₀)
  rw [Complex.volume_ball]
  have hdelta : 0 ≤ delta n := (delta_pos hn).le
  have hrewrite :
      ENNReal.ofReal (delta n ^ 2 * Real.pi) =
        ENNReal.ofReal (delta n) ^ 2 * NNReal.pi := by
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow hdelta]
    simp [← NNReal.coe_real_pi]
  rw [← hrewrite]
  apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos (sq_pos_of_pos (delta_pos hn)) Real.pi_pos)).2
  rw [delta_sq_eq hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp [ne_of_gt hnR]
  nlinarith [Real.pi_pos]

/-- The conventional `n^{-O(1)}` packaging of `erdos_116_explicit`, with the absolute
constants `c = π / 2^31` and `C = 14`. -/
theorem erdos_116_power_law :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ a : Fin n → ℂ,
      (∀ i, ‖a i‖ ≤ 1) →
      ENNReal.ofReal (c / (n : ℝ) ^ C) <
        volume {z : ℂ | ‖lemniscateProduct a z‖ < 1} := by
  refine ⟨Real.pi / 2 ^ 31, by positivity, 14, ?_⟩
  intro n hn a ha
  simpa only [div_div] using erdos_116_explicit hn a ha

/-- **Erdős Problem 116.**  The area where the product has modulus less than one
has a polynomial lower bound, uniform over all roots in the closed unit disk. -/
theorem erdos_116 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ a : Fin n → ℂ,
      (∀ i, ‖a i‖ ≤ 1) →
      ENNReal.ofReal (c / (n : ℝ) ^ C) <
        volume {z : ℂ | ‖∏ i, (z - a i)‖ < 1} := by
  simpa only [lemniscateProduct] using erdos_116_power_law

#print axioms erdos_116

end Erdos116
