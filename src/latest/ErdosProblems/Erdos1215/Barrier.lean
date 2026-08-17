import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

open scoped BigOperators Topology
open Filter

namespace Erdos1215

open Polynomial

/-!
This file isolates the analytic step in the Farmer--Gorkin version of Mac
Lane's barrier construction. Starting from a polynomial `h` whose real part
is positive on the walls, one approximates `exp (A * h)` by its Taylor
polynomials. The resulting polynomial has constant coefficient one, is
zero-free on the closed unit disk, and is large on every wall.
-/

/-- The Taylor polynomial for `exp (a * h)`. -/
noncomputable def expTaylor (h : ℂ[X]) (a : ℂ) (n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range n, C ((k.factorial : ℂ)⁻¹) * (C a * h) ^ k

@[simp] lemma expTaylor_eval (h : ℂ[X]) (a z : ℂ) (n : ℕ) :
    (expTaylor h a n).eval z =
      ∑ k ∈ Finset.range n, (a * h.eval z) ^ k / k.factorial := by
  rw [expTaylor, eval_finsetSum]
  simp [div_eq_mul_inv, mul_comm]

@[simp] lemma expTaylor_eval_zero_of_eval_zero (h : ℂ[X]) (a : ℂ) (n : ℕ)
    (hn : 0 < n) (hh0 : h.eval 0 = 0) :
    (expTaylor h a n).eval 0 = 1 := by
  rw [expTaylor_eval, hh0, mul_zero]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0
    simp [hb0]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hn)).elim

/-- The scalar Taylor remainders tend to zero uniformly on every norm-bounded
set. The second conjunct is the side condition of `Complex.exp_bound'`. -/
lemma eventually_expTaylor_error_bound (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      R / n.succ ≤ 1 / 2 ∧
      R ^ n / n.factorial * 2 < ε := by
  have hdiv : Tendsto (fun n : ℕ ↦ R / (n.succ : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat R).comp (tendsto_add_atTop_nat 1)
  have hterm : Tendsto (fun n : ℕ ↦ R ^ n / n.factorial * 2) atTop (nhds 0) := by
    simpa only [zero_mul] using
      (Real.summable_pow_div_factorial R).tendsto_atTop_zero.mul_const 2
  filter_upwards [(tendsto_order.1 hdiv).2 (1 / 2) (by norm_num),
    (tendsto_order.1 hterm).2 ε hε] with n hn hn'
  exact ⟨hn.le, hn'⟩

/-- Uniform Taylor approximation on any set on which `a * h` has norm at
most `R`. -/
lemma eventually_expTaylor_uniform (h : ℂ[X]) (a : ℂ) (R ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ z : ℂ, ‖a * h.eval z‖ ≤ R →
      ‖Complex.exp (a * h.eval z) - (expTaylor h a n).eval z‖ < ε := by
  filter_upwards [eventually_expTaylor_error_bound R ε hε] with n hn z hz
  rw [expTaylor_eval]
  calc
    ‖Complex.exp (a * h.eval z) -
        ∑ k ∈ Finset.range n, (a * h.eval z) ^ k / k.factorial‖
        ≤ ‖a * h.eval z‖ ^ n / n.factorial * 2 := by
          apply Complex.exp_bound'
          exact (div_le_div_of_nonneg_right hz (by positivity)).trans hn.1
    _ ≤ R ^ n / n.factorial * 2 := by
          gcongr
    _ < ε := hn.2

/-- The analytic barrier step needed before the Farmer--Gorkin reversal.

If `h(0) = 0`, `Re h > c` on `K`, and `h` is bounded by `B` on the closed
unit disk, then any positive real scale `A` for which `exp (A*c) > q`
produces a Taylor polynomial `p` with `p(0)=1`, no zero in the closed unit
disk, and `|p|>q` on `K` (provided `K` lies in that disk). -/
theorem exists_expTaylor_zeroFree_large
    (K : Set ℂ) (h : ℂ[X]) (c A B q : ℝ)
    (hh0 : h.eval 0 = 0) (hA : 0 < A) (hB : 0 ≤ B)
    (hlarge : q < Real.exp (A * c))
    (hK : ∀ z ∈ K, c < (h.eval z).re)
    (hKdisk : ∀ z ∈ K, ‖z‖ ≤ 1)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖h.eval z‖ ≤ B) :
    ∃ p : ℂ[X],
      p.eval 0 = 1 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → p.eval z ≠ 0) ∧
      ∀ z ∈ K, q < ‖p.eval z‖ := by
  let floor : ℝ := Real.exp (-(A * B))
  let gap : ℝ := Real.exp (A * c) - q
  let ε : ℝ := min floor gap / 2
  have hfloor : 0 < floor := by
    exact Real.exp_pos _
  have hgap : 0 < gap := by
    exact sub_pos.mpr hlarge
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hAB : 0 ≤ A * B := mul_nonneg hA.le hB
  have hεfloor : ε < floor := by
    calc
      ε ≤ floor / 2 := by
        dsimp [ε]
        gcongr
        exact min_le_left _ _
      _ < floor := by linarith
  have hεgap : ε < gap := by
    calc
      ε ≤ gap / 2 := by
        dsimp [ε]
        gcongr
        exact min_le_right _ _
      _ < gap := by linarith
  have hev := eventually_expTaylor_uniform h (A : ℂ) (A * B) ε hε
  have hevpos : ∀ᶠ n : ℕ in atTop, 0 < n := by
    exact eventually_atTop.2 ⟨1, fun n hn ↦ by omega⟩
  obtain ⟨n, hn, hnpos⟩ := (hev.and hevpos).exists
  let p : ℂ[X] := expTaylor h (A : ℂ) n
  have hscaled (z : ℂ) (hz : ‖z‖ ≤ 1) :
      ‖(A : ℂ) * h.eval z‖ ≤ A * B := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
    exact mul_le_mul_of_nonneg_left (hbound z hz) hA.le
  have hexp_lower (z : ℂ) (hz : ‖z‖ ≤ 1) :
      floor ≤ ‖Complex.exp ((A : ℂ) * h.eval z)‖ := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hre : -B ≤ (h.eval z).re := by
      calc
        -B ≤ -‖h.eval z‖ := neg_le_neg (hbound z hz)
        _ ≤ (h.eval z).re := neg_le_of_abs_le (Complex.abs_re_le_norm _)
    nlinarith
  have hexp_large (z : ℂ) (hz : z ∈ K) :
      Real.exp (A * c) < ‖Complex.exp ((A : ℂ) * h.eval z)‖ := by
    rw [Complex.norm_exp]
    apply Real.exp_lt_exp.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_lt_mul_of_pos_left (hK z hz) hA
  refine ⟨p, ?_, ?_, ?_⟩
  · exact expTaylor_eval_zero_of_eval_zero h (A : ℂ) n hnpos hh0
  · intro z hz hpz
    have herr := hn z (hscaled z hz)
    change ‖Complex.exp ((A : ℂ) * h.eval z) - p.eval z‖ < ε at herr
    rw [hpz, sub_zero] at herr
    exact (not_lt_of_ge (hexp_lower z hz)) (herr.trans hεfloor)
  · intro z hz
    have herr := hn z (hscaled z (hKdisk z hz))
    change ‖Complex.exp ((A : ℂ) * h.eval z) - p.eval z‖ < ε at herr
    have htri : ‖Complex.exp ((A : ℂ) * h.eval z)‖ ≤
        ‖Complex.exp ((A : ℂ) * h.eval z) - p.eval z‖ + ‖p.eval z‖ := by
      calc
        ‖Complex.exp ((A : ℂ) * h.eval z)‖ =
            ‖(Complex.exp ((A : ℂ) * h.eval z) - p.eval z) + p.eval z‖ := by
              rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    dsimp [gap] at hεgap
    linarith [hexp_large z hz]

/-- A completely explicit bound for a complex polynomial on the closed unit
disk: the sum of the norms of its coefficients. -/
lemma norm_eval_le_sum_norm_coeff (h : ℂ[X]) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖h.eval z‖ ≤ ∑ i ∈ h.support, ‖h.coeff i‖ := by
  rw [eval_eq_sum]
  calc
    ‖∑ i ∈ h.support, h.coeff i * z ^ i‖
        ≤ ∑ i ∈ h.support, ‖h.coeff i * z ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ h.support, ‖h.coeff i‖ := by
      gcongr with i hi
      rw [Complex.norm_mul, Complex.norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg z) hz)

/-- Barrier polynomial in the exact numerical form used for Problem 1215.
The only analytic input is a polynomial separator `h` whose real part has a
uniform positive lower bound on the wall set. -/
theorem exists_zeroFree_polynomial_large_on_set
    (K : Set ℂ) (h : ℂ[X]) (c : ℝ)
    (hh0 : h.eval 0 = 0) (hc : 0 < c)
    (hK : ∀ z ∈ K, c < (h.eval z).re)
    (hKdisk : ∀ z ∈ K, ‖z‖ ≤ 1) :
    ∃ p : ℂ[X],
      p.eval 0 = 1 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → p.eval z ≠ 0) ∧
      ∀ z ∈ K, (5 : ℝ) / 2 < ‖p.eval z‖ := by
  let A : ℝ := Real.log 3 / c
  let B : ℝ := ∑ i ∈ h.support, ‖h.coeff i‖
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hA : 0 < A := div_pos hlog hc
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun i hi ↦ norm_nonneg _
  have hlarge : (5 : ℝ) / 2 < Real.exp (A * c) := by
    have hc0 : c ≠ 0 := ne_of_gt hc
    rw [show A * c = Real.log 3 by simp [A, hc0]]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num
  exact exists_expTaylor_zeroFree_large K h c A B ((5 : ℝ) / 2)
    hh0 hA hB hlarge hK hKdisk (fun z hz ↦ norm_eval_le_sum_norm_coeff h z hz)

end Erdos1215

#print axioms Erdos1215.exists_zeroFree_polynomial_large_on_set
