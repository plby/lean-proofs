/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.RosserCore
import ErdosProblems.Erdos851.BetaSieveTail
import ErdosProblems.Erdos387.BrunSieve
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Sigma
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Finite beta-sieve weights

This file turns the recursive Buchstab evaluators in `RosserCore` into
explicit finite coefficient lists.  It is the algebraic layer needed before
the quantitative Rosser boundary estimate is applied.
-/

namespace Erdos851

open List

mutual

  /-- Terms in the upper Buchstab polynomial.  The first component records
  the selected ordered sublist and the second its coefficient. -/
  def rosserUpperTerms {α : Type*} (stop : List α → Bool) :
      ℕ → List α → List α → List (List α × ℝ)
    | 0, _selected, _remaining => [([], 1)]
    | fuel + 1, selected, remaining =>
        [([], 1)] ++ (buchstabChildren remaining).flatMap fun q =>
          if stop (selected ++ [q.1]) then
            (rosserLowerTerms stop fuel (selected ++ [q.1]) q.2).map
              fun t => (q.1 :: t.1, -t.2)
          else []

  /-- Terms in the lower Buchstab polynomial. -/
  def rosserLowerTerms {α : Type*} (stop : List α → Bool) :
      ℕ → List α → List α → List (List α × ℝ)
    | 0, _selected, _remaining => [([], 1)]
    | fuel + 1, selected, remaining =>
        [([], 1)] ++ (buchstabChildren remaining).flatMap fun q =>
          (rosserUpperTerms stop fuel (selected ++ [q.1]) q.2).map
            fun t => (q.1 :: t.1, -t.2)

end

/-- Evaluation of a finite list of squarefree monomials. -/
def evalRosserTerms {α : Type*} (x : α → ℝ)
    (terms : List (List α × ℝ)) : ℝ :=
  (terms.map fun t => t.2 * (t.1.map x).prod).sum

private theorem evalRosserTerms_map_cons_neg {α : Type*}
    (x : α → ℝ) (p : α) (terms : List (List α × ℝ)) :
    evalRosserTerms x (terms.map fun t => (p :: t.1, -t.2)) =
      -(x p * evalRosserTerms x terms) := by
  induction terms with
  | nil => simp [evalRosserTerms]
  | cons t terms ih =>
      unfold evalRosserTerms at ih ⊢
      simp only [List.map_map, List.map_cons,
        List.sum_cons, List.prod_cons, neg_mul]
      have ih' :
          (terms.map ((fun t => t.2 * (t.1.map x).prod) ∘
            fun t => (p :: t.1, -t.2))).sum =
            -(x p * (terms.map fun t => t.2 * (t.1.map x).prod).sum) := by
        simpa only [List.map_map] using ih
      rw [ih']
      ring

private theorem evalRosserTerms_flatMap {α β : Type*}
    (x : α → ℝ) (l : List β) (f : β → List (List α × ℝ)) :
    evalRosserTerms x (l.flatMap f) =
      (l.map fun b => evalRosserTerms x (f b)).sum := by
  induction l with
  | nil => simp [evalRosserTerms]
  | cons b l ih =>
      unfold evalRosserTerms at ih ⊢
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      exact congrArg (fun y =>
        (List.map (fun t => t.2 * (List.map x t.1).prod) (f b)).sum + y) ih

private theorem evalRosserTerms_append {α : Type*}
    (x : α → ℝ) (a b : List (List α × ℝ)) :
    evalRosserTerms x (a ++ b) =
      evalRosserTerms x a + evalRosserTerms x b := by
  simp [evalRosserTerms]

private theorem sum_map_neg {α : Type*} (f : α → ℝ) :
    ∀ l : List α, (l.map fun a => -f a).sum = -(l.map f).sum
  | [] => by simp
  | a :: l => by
      simp only [List.map_cons, List.sum_cons, sum_map_neg f l]
      ring

private theorem sum_map_sub {α : Type*} (f g : α → ℝ) :
    ∀ l : List α,
      (l.map fun a => f a - g a).sum = (l.map f).sum - (l.map g).sum
  | [] => by simp
  | a :: l => by
      simp only [List.map_cons, List.sum_cons, sum_map_sub f g l]
      ring

/-- Expanding the recursive upper/lower evaluators produces the explicit
term lists above. -/
theorem eval_rosserTerms_eq_eval {α : Type*}
    (stop : List α → Bool) (x : α → ℝ) :
    ∀ (fuel : ℕ) (selected remaining : List α),
      evalRosserTerms x (rosserUpperTerms stop fuel selected remaining) =
          rosserUpperEval stop x fuel selected remaining ∧
        evalRosserTerms x (rosserLowerTerms stop fuel selected remaining) =
          rosserLowerEval stop x fuel selected remaining := by
  intro fuel
  induction fuel with
  | zero =>
      intro selected remaining
      simp [rosserUpperTerms, rosserLowerTerms, rosserUpperEval,
        rosserLowerEval, evalRosserTerms]
  | succ fuel ih =>
      intro selected remaining
      constructor
      · rw [rosserUpperTerms, rosserUpperEval, evalRosserTerms_append,
          evalRosserTerms_flatMap]
        simp only [evalRosserTerms, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.prod_nil, mul_one, add_zero]
        change 1 +
            ((buchstabChildren remaining).map fun q =>
              evalRosserTerms x
                (if stop (selected ++ [q.1]) then
                  (rosserLowerTerms stop fuel (selected ++ [q.1]) q.2).map
                    fun t => (q.1 :: t.1, -t.2)
                else [])).sum = _
        apply congrArg (fun y : ℝ => 1 + y)
        rw [← sum_map_neg]
        apply congrArg List.sum
        apply List.map_congr_left
        intro q hq
        cases hstop : stop (selected ++ [q.1])
        · simp [evalRosserTerms]
        · simp only [↓reduceIte, evalRosserTerms_map_cons_neg]
          rw [(ih (selected ++ [q.1]) q.2).2]
      · rw [rosserLowerTerms, rosserLowerEval, evalRosserTerms_append,
          evalRosserTerms_flatMap]
        simp only [evalRosserTerms, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.prod_nil, mul_one, add_zero]
        change 1 +
            ((buchstabChildren remaining).map fun q =>
              evalRosserTerms x
                ((rosserUpperTerms stop fuel (selected ++ [q.1]) q.2).map
                  fun t => (q.1 :: t.1, -t.2))).sum = _
        apply congrArg (fun y : ℝ => 1 + y)
        rw [← sum_map_neg]
        apply congrArg List.sum
        apply List.map_congr_left
        intro q hq
        rw [evalRosserTerms_map_cons_neg,
          (ih (selected ++ [q.1]) q.2).1]

/-- Explicit-coefficient form of the finite Rosser inequality. -/
theorem eval_lowerTerms_le_product_le_upperTerms {α : Type*}
    (stop : List α → Bool) (x : α → ℝ)
    (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1)
    (fuel : ℕ) (selected remaining : List α)
    (hlen : remaining.length ≤ fuel) :
    evalRosserTerms x (rosserLowerTerms stop fuel selected remaining) ≤
        buchstabProduct x remaining ∧
      buchstabProduct x remaining ≤
        evalRosserTerms x (rosserUpperTerms stop fuel selected remaining) := by
  rw [(eval_rosserTerms_eq_eval stop x fuel selected remaining).1,
    (eval_rosserTerms_eq_eval stop x fuel selected remaining).2]
  exact rosserLowerEval_le_product_le_upperEval stop x hx0 hx1
    fuel selected remaining hlen

mutual

  /-- Positive first-failure mass for the upper recursion. -/
  def rosserUpperBoundary {α : Type*} (stop : List α → Bool)
      (x : α → ℝ) : ℕ → List α → List α → ℝ
    | 0, _selected, _remaining => 0
    | fuel + 1, selected, remaining =>
        ((buchstabChildren remaining).map fun q =>
          if stop (selected ++ [q.1]) then
            x q.1 * rosserLowerBoundary stop x fuel (selected ++ [q.1]) q.2
          else x q.1 * buchstabProduct x q.2).sum

  /-- Positive propagated boundary mass for the lower recursion. -/
  def rosserLowerBoundary {α : Type*} (stop : List α → Bool)
      (x : α → ℝ) : ℕ → List α → List α → ℝ
    | 0, _selected, _remaining => 0
    | fuel + 1, selected, remaining =>
        ((buchstabChildren remaining).map fun q =>
          x q.1 * rosserUpperBoundary stop x fuel (selected ++ [q.1]) q.2).sum

end


/-- Exact recursive version of the two first-failure identities in the
general combinatorial sieve. -/
theorem rosser_eval_sub_product_eq_boundary {α : Type*}
    (stop : List α → Bool) (x : α → ℝ) :
    ∀ (fuel : ℕ) (selected remaining : List α),
      remaining.length ≤ fuel →
      rosserUpperEval stop x fuel selected remaining -
            buchstabProduct x remaining =
          rosserUpperBoundary stop x fuel selected remaining ∧
        buchstabProduct x remaining -
            rosserLowerEval stop x fuel selected remaining =
          rosserLowerBoundary stop x fuel selected remaining := by
  intro fuel
  induction fuel with
  | zero =>
      intro selected remaining hlen
      have hzero : remaining.length = 0 := Nat.eq_zero_of_le_zero hlen
      have hnil : remaining = [] := List.length_eq_zero_iff.mp hzero
      subst remaining
      simp [rosserUpperEval, rosserLowerEval, rosserUpperBoundary,
        rosserLowerBoundary, buchstabProduct]
  | succ fuel ih =>
      intro selected remaining hlen
      have htail : ∀ q ∈ buchstabChildren remaining, q.2.length ≤ fuel := by
        intro q hq
        exact Nat.lt_succ_iff.mp
          ((length_snd_lt_of_mem_buchstabChildren hq).trans_le hlen)
      constructor
      · rw [rosserUpperEval, rosserUpperBoundary,
          buchstabProduct_eq_one_sub_sum]
        ring_nf
        rw [add_comm]
        rw [← sub_eq_add_neg]
        apply congrArg (fun y : ℝ => y)
        rw [← sum_map_sub]
        apply congrArg List.sum
        apply List.map_congr_left
        intro q hq
        cases hstop : stop (selected ++ [q.1])
        · simp only [Bool.false_eq_true, ↓reduceIte, sub_zero]
        · simp only [↓reduceIte]
          rw [← mul_sub, (ih (selected ++ [q.1]) q.2 (htail q hq)).2]
      · rw [rosserLowerEval, rosserLowerBoundary,
          buchstabProduct_eq_one_sub_sum]
        ring_nf
        rw [add_comm]
        rw [← sub_eq_add_neg]
        apply congrArg (fun y : ℝ => y)
        rw [← sum_map_sub]
        apply congrArg List.sum
        apply List.map_congr_left
        intro q hq
        rw [← mul_sub, (ih (selected ++ [q.1]) q.2 (htail q hq)).1]

/-- Both first-failure boundary masses are nonnegative when the local sieve
densities lie in `[0,1]`. -/
theorem rosserBoundary_nonneg {α : Type*}
    (stop : List α → Bool) (x : α → ℝ)
    (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) :
    ∀ (fuel : ℕ) (selected remaining : List α),
      0 ≤ rosserUpperBoundary stop x fuel selected remaining ∧
        0 ≤ rosserLowerBoundary stop x fuel selected remaining := by
  intro fuel
  induction fuel with
  | zero =>
      intro selected remaining
      simp [rosserUpperBoundary, rosserLowerBoundary]
  | succ fuel ih =>
      intro selected remaining
      constructor
      · rw [rosserUpperBoundary]
        apply List.sum_nonneg
        intro y hy
        simp only [List.mem_map] at hy
        obtain ⟨q, _hq, rfl⟩ := hy
        split
        · exact mul_nonneg (hx0 q.1)
            (ih (selected ++ [q.1]) q.2).2
        · exact mul_nonneg (hx0 q.1) (buchstabProduct_nonneg hx1 q.2)
      · rw [rosserLowerBoundary]
        apply List.sum_nonneg
        intro y hy
        simp only [List.mem_map] at hy
        obtain ⟨q, _hq, rfl⟩ := hy
        exact mul_nonneg (hx0 q.1)
          (ih (selected ++ [q.1]) q.2).1

/-- The exact boundary identities and nonnegativity, in a form convenient
for subsequent quantitative estimates. -/
theorem rosser_eval_errors_eq_nonneg_boundaries {α : Type*}
    (stop : List α → Bool) (x : α → ℝ)
    (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1)
    (fuel : ℕ) (selected remaining : List α)
    (hlen : remaining.length ≤ fuel) :
    rosserUpperEval stop x fuel selected remaining -
          buchstabProduct x remaining =
        rosserUpperBoundary stop x fuel selected remaining ∧
      0 ≤ rosserUpperBoundary stop x fuel selected remaining ∧
      buchstabProduct x remaining -
          rosserLowerEval stop x fuel selected remaining =
        rosserLowerBoundary stop x fuel selected remaining ∧
      0 ≤ rosserLowerBoundary stop x fuel selected remaining := by
  exact ⟨(rosser_eval_sub_product_eq_boundary stop x fuel selected remaining
      hlen).1,
    (rosserBoundary_nonneg stop x hx0 hx1 fuel selected remaining).1,
    (rosser_eval_sub_product_eq_boundary stop x fuel selected remaining
      hlen).2,
    (rosserBoundary_nonneg stop x hx0 hx1 fuel selected remaining).2⟩

namespace BetaSieveFundamental

open scoped BigOperators Topology

/-- The loss `(β + 1) / (β - 1)` occurring in a Rosser boundary chain for
the stopping convention `p₁⋯p_{r-1}p_r^(β+1) ≤ D`, at `β = 100`. -/
noncomputable def betaRatio : ℝ := 101 / 99

/-- The actual (depth-dependent) normalized boundary-chain majorant.  In
particular, the logarithmic factor depends on `r`; it cannot be replaced by
a fixed constant before estimating the tail. -/
noncomputable def betaDepthMajorant (A κ : ℝ) (r : ℕ) : ℝ :=
  A * Real.rpow betaRatio (κ * r) *
    (Real.log A + κ * r * Real.log betaRatio) ^ r /
      (r.factorial : ℝ)

/-- The analytic core of the product-ratio-to-depth estimate.  If `I` is
an inverse Euler-product ratio, `L` is a nonnegative upper bound for the
sum of the local densities in the same interval, and

`I ≤ A * betaRatio ^ (κ*r)`, `L ≤ log I`,

then the usual elementary-symmetric depth term is bounded by the concrete
beta-depth majorant.  This lemma is deliberately stated without
`HasDepthProductRatio`: it is the numerical conversion used after the
finite chain family has been embedded into the interval Euler product. -/
theorem productRatio_factorialTerm_le_betaDepthMajorant
    {A κ I L : ℝ} (r : ℕ)
    (hA : 1 ≤ A) (hI : 0 < I) (hL : 0 ≤ L)
    (hproduct : I ≤ A * Real.rpow betaRatio (κ * r))
    (hsum : L ≤ Real.log I) :
    I * L ^ r / (r.factorial : ℝ) ≤ betaDepthMajorant A κ r := by
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hratioPos : 0 < betaRatio := by norm_num [betaRatio]
  have htargetPos : 0 < A * Real.rpow betaRatio (κ * (r : ℝ)) :=
    mul_pos hApos (Real.rpow_pos_of_pos hratioPos _)
  have hlogI : Real.log I ≤
      Real.log (A * Real.rpow betaRatio (κ * (r : ℝ))) :=
    Real.log_le_log hI hproduct
  have hlogTarget :
      Real.log (A * Real.rpow betaRatio (κ * (r : ℝ))) =
        Real.log A + κ * (r : ℝ) * Real.log betaRatio := by
    calc
      Real.log (A * Real.rpow betaRatio (κ * (r : ℝ))) =
          Real.log A + Real.log (Real.rpow betaRatio (κ * (r : ℝ))) :=
        Real.log_mul hApos.ne' (Real.rpow_pos_of_pos hratioPos _).ne'
      _ = Real.log A + κ * (r : ℝ) * Real.log betaRatio := by
        congr 1
        simpa only [Real.rpow_eq_pow] using
          Real.log_rpow hratioPos (κ * (r : ℝ))
  have hbase : L ≤ Real.log A + κ * (r : ℝ) * Real.log betaRatio := by
    rw [← hlogTarget]
    exact hsum.trans hlogI
  have hbase0 : 0 ≤
      Real.log A + κ * (r : ℝ) * Real.log betaRatio :=
    hL.trans hbase
  unfold betaDepthMajorant
  gcongr

theorem log_betaRatio_le : Real.log betaRatio ≤ 2 / 99 := by
  calc
    Real.log betaRatio ≤ betaRatio - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num [betaRatio])
    _ = 2 / 99 := by norm_num [betaRatio]

theorem betaRatio_rpow_dimension_le_twenty_one_div_twenty {κ : ℝ}
    (_hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2) :
    Real.rpow betaRatio κ ≤ 21 / 20 := by
  calc
    Real.rpow betaRatio κ ≤ Real.rpow betaRatio (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num [betaRatio]) hκ2
    _ = betaRatio ^ (2 : ℕ) := Real.rpow_natCast _ _
    _ ≤ 21 / 20 := by norm_num [betaRatio]

theorem betaRatio_rpow_dimension_mul_le {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2) (r : ℕ) :
    Real.rpow betaRatio (κ * r) ≤ (21 / 20 : ℝ) ^ r := by
  calc
    Real.rpow betaRatio (κ * r) = (Real.rpow betaRatio κ) ^ r :=
      Real.rpow_mul_natCast (by norm_num [betaRatio]) κ r
    _ ≤ (21 / 20 : ℝ) ^ r := pow_le_pow_left₀
      (Real.rpow_nonneg (by norm_num [betaRatio]) _)
      (betaRatio_rpow_dimension_le_twenty_one_div_twenty hκ0 hκ2) r

/-- The elementary estimate `r^r / r! ≤ e^r < (11/4)^r`. -/
theorem self_pow_div_factorial_le_eleven_quarters_pow (r : ℕ) :
    (r : ℝ) ^ r / (r.factorial : ℝ) ≤ (11 / 4 : ℝ) ^ r := by
  calc
    (r : ℝ) ^ r / (r.factorial : ℝ) ≤ Real.exp (r : ℝ) :=
      Real.pow_div_factorial_le_exp (r : ℝ) (by positivity) r
    _ = Real.exp 1 ^ r := (Real.exp_one_pow r).symm
    _ ≤ (11 / 4 : ℝ) ^ r :=
      pow_le_pow_left₀ (Real.exp_pos 1).le
        (Real.exp_one_lt_d9.le.trans (by norm_num)) r

/-- In sieve dimension at most two, once `r` is large enough that
`log A ≤ 2κr / 99`, the full depth-dependent chain majorant is at most
`A · 4⁻ʳ`. -/
theorem betaDepthMajorant_le_quarter_pow
    {A κ : ℝ} (r : ℕ) (hA : 1 ≤ A)
    (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (hlogA : Real.log A ≤ 2 * κ * r / 99) :
    betaDepthMajorant A κ r ≤ A * (1 / 4 : ℝ) ^ r := by
  have hlogc0 : 0 ≤ Real.log betaRatio :=
    Real.log_nonneg (by norm_num [betaRatio])
  have hkr0 : 0 ≤ κ * (r : ℝ) := mul_nonneg hκ0 (by positivity)
  have hlogterm :
      κ * (r : ℝ) * Real.log betaRatio ≤ 2 * κ * (r : ℝ) / 99 := by
    calc
      κ * (r : ℝ) * Real.log betaRatio ≤
          κ * (r : ℝ) * (2 / 99) :=
        mul_le_mul_of_nonneg_left log_betaRatio_le hkr0
      _ = 2 * κ * (r : ℝ) / 99 := by ring
  have hbase0 : 0 ≤ Real.log A + κ * (r : ℝ) * Real.log betaRatio :=
    add_nonneg (Real.log_nonneg hA) (mul_nonneg hkr0 hlogc0)
  have hbase : Real.log A + κ * (r : ℝ) * Real.log betaRatio ≤
      4 * κ * (r : ℝ) / 99 := by linarith
  have hpowbase :
      (Real.log A + κ * (r : ℝ) * Real.log betaRatio) ^ r ≤
        (4 * κ * (r : ℝ) / 99) ^ r :=
    pow_le_pow_left₀ hbase0 hbase r
  have hratio := betaRatio_rpow_dimension_mul_le hκ0 hκ2 r
  have hfac := self_pow_div_factorial_le_eleven_quarters_pow r
  have hA0 : 0 ≤ A := hA.trans' (by norm_num)
  have hpowers :
      (21 / 20 : ℝ) ^ r * (4 * κ * (r : ℝ) / 99) ^ r =
        (7 * κ / 165 : ℝ) ^ r * (r : ℝ) ^ r := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    ring
  have hpowers' :
      (7 * κ / 165 : ℝ) ^ r * (11 / 4 : ℝ) ^ r =
        (77 * κ / 660 : ℝ) ^ r := by
    rw [← mul_pow]
    congr 1
    ring
  have hbaseQuarter : (77 * κ / 660 : ℝ) ≤ 1 / 4 := by
    linarith
  have hbaseFinal0 : 0 ≤ (77 * κ / 660 : ℝ) := by positivity
  unfold betaDepthMajorant
  calc
    A * Real.rpow betaRatio (κ * ↑r) *
          (Real.log A + κ * ↑r * Real.log betaRatio) ^ r /
          ↑r.factorial ≤
        A * (21 / 20 : ℝ) ^ r * (4 * κ * (r : ℝ) / 99) ^ r /
          (r.factorial : ℝ) := by
      gcongr
    _ = A * (7 * κ / 165 : ℝ) ^ r *
          ((r : ℝ) ^ r / (r.factorial : ℝ)) := by
      rw [mul_assoc, hpowers]
      ring
    _ ≤ A * (7 * κ / 165 : ℝ) ^ r * (11 / 4 : ℝ) ^ r := by
      gcongr
    _ = A * (77 * κ / 660 : ℝ) ^ r := by
      rw [mul_assoc, hpowers']
    _ ≤ A * (1 / 4 : ℝ) ^ r := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hbaseFinal0 hbaseQuarter r) hA0

theorem sum_quarter_pow_add_le (s m : ℕ) :
    (∑ i ∈ Finset.range m, (1 / 4 : ℝ) ^ (s + i)) ≤
      (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ s := by
  have hsum :
      (∑ i ∈ Finset.range m, (1 / 4 : ℝ) ^ i) ≤ 4 / 3 := by
    calc
      (∑ i ∈ Finset.range m, (1 / 4 : ℝ) ^ i) ≤
          ∑' i : ℕ, (1 / 4 : ℝ) ^ i := by
        exact (summable_geometric_of_norm_lt_one (by norm_num :
          ‖(1 / 4 : ℝ)‖ < 1)).sum_le_tsum (Finset.range m)
            (fun i _hi => by positivity)
      _ = (1 - (1 / 4 : ℝ))⁻¹ :=
        tsum_geometric_of_lt_one (by norm_num) (by norm_num)
      _ = 4 / 3 := by norm_num
  calc
    (∑ i ∈ Finset.range m, (1 / 4 : ℝ) ^ (s + i)) =
        (1 / 4 : ℝ) ^ s *
          ∑ i ∈ Finset.range m, (1 / 4 : ℝ) ^ i := by
      simp_rw [pow_add]
      rw [Finset.mul_sum]
    _ ≤ (1 / 4 : ℝ) ^ s * (4 / 3) := by gcongr
    _ = (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ s := by ring

/-- Correct geometric absorption of the full, `r`-dependent boundary
majorant.  This is the numerical tail estimate used for beta `100`; unlike a
fixed-`C` factorial lemma, its hypothesis is exactly the chain bound supplied
by the product-ratio argument. -/
theorem sum_betaDepthMajorant_le
    {A κ : ℝ} (s m : ℕ) (hA : 1 ≤ A)
    (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (hlogA : ∀ i < m,
      Real.log A ≤ 2 * κ * (s + i : ℕ) / 99) :
    (∑ i ∈ Finset.range m, betaDepthMajorant A κ (s + i)) ≤
      (4 * A / 3) * (1 / 4 : ℝ) ^ s := by
  calc
    (∑ i ∈ Finset.range m, betaDepthMajorant A κ (s + i)) ≤
        ∑ i ∈ Finset.range m, A * (1 / 4 : ℝ) ^ (s + i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact betaDepthMajorant_le_quarter_pow (s + i) hA hκ0 hκ2
        (hlogA i (Finset.mem_range.mp hi))
    _ = A * ∑ i ∈ Finset.range m, (1 / 4 : ℝ) ^ (s + i) := by
      rw [Finset.mul_sum]
    _ ≤ A * ((4 / 3 : ℝ) * (1 / 4 : ℝ) ^ s) := by
      gcongr
      exact sum_quarter_pow_add_le s m
    _ = (4 * A / 3) * (1 / 4 : ℝ) ^ s := by ring

/-- The part of the abstract-sieve remainder supported up to the finite
level `D`. -/
def levelRemainder (s : BoundingSieve) (D : ℕ) : ℝ :=
  ∑ d ∈ (Nat.divisors s.prodPrimes).filter (fun d => d ≤ D), |s.rem d|

/-- Coefficients bounded by one and supported on `d ≤ D` incur no more than
the level-`D` remainder.  This is the support step needed to turn Rosser
weights into a usable finite sieve estimate. -/
theorem errSum_le_levelRemainder
    (s : BoundingSieve) (D : ℕ) (lambda : ℕ → ℝ)
    (hcoeff : ∀ d ∈ Nat.divisors s.prodPrimes, |lambda d| ≤ 1)
    (hsupport : ∀ d ∈ Nat.divisors s.prodPrimes, D < d → lambda d = 0) :
    s.errSum lambda ≤ levelRemainder s D := by
  rw [BoundingSieve.errSum, levelRemainder]
  calc
    (∑ d ∈ Nat.divisors s.prodPrimes, |lambda d| * |s.rem d|) =
        ∑ d ∈ Nat.divisors s.prodPrimes,
          if d ≤ D then |lambda d| * |s.rem d| else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdD : d ≤ D
      · simp [hdD]
      · have hzero := hsupport d hd (Nat.lt_of_not_ge hdD)
        simp [hdD, hzero]
    _ = ∑ d ∈ (Nat.divisors s.prodPrimes).filter (fun d => d ≤ D),
          |lambda d| * |s.rem d| := by
      rw [Finset.sum_filter]
    _ ≤ ∑ d ∈ (Nat.divisors s.prodPrimes).filter (fun d => d ≤ D),
          |s.rem d| := by
      apply Finset.sum_le_sum
      intro d hd
      have hddiv : d ∈ Nat.divisors s.prodPrimes :=
        (Finset.mem_filter.mp hd).1
      calc
        |lambda d| * |s.rem d| ≤ 1 * |s.rem d| :=
          mul_le_mul_of_nonneg_right (hcoeff d hddiv) (abs_nonneg _)
        _ = |s.rem d| := one_mul _

/-- Ready-to-use finite lower and upper bounds for a generic
`BoundingSieve`.  A beta-sieve construction supplies the two localized
Möbius properties, the coefficient/support facts, and the two quantitative
main-sum estimates (the latter follow from the product-ratio hypothesis and
the boundary estimate above). -/
theorem boundingSieve_bounds_of_level_weights
    (s : BoundingSieve) (D : ℕ)
    (lambdaMinus lambdaPlus : ℕ → ℝ) (V eta : ℝ)
    (hmass : 0 ≤ s.totalMass)
    (hlower : s.IsLowerMoebiusOnProdPrimes lambdaMinus)
    (hupper : s.IsUpperMoebiusOnProdPrimes lambdaPlus)
    (hcoeffMinus : ∀ d ∈ Nat.divisors s.prodPrimes,
      |lambdaMinus d| ≤ 1)
    (hcoeffPlus : ∀ d ∈ Nat.divisors s.prodPrimes,
      |lambdaPlus d| ≤ 1)
    (hsupportMinus : ∀ d ∈ Nat.divisors s.prodPrimes,
      D < d → lambdaMinus d = 0)
    (hsupportPlus : ∀ d ∈ Nat.divisors s.prodPrimes,
      D < d → lambdaPlus d = 0)
    (hmainLower : (1 - eta) * V ≤ s.mainSum lambdaMinus)
    (hmainUpper : s.mainSum lambdaPlus ≤ (1 + eta) * V) :
    s.totalMass * ((1 - eta) * V) - levelRemainder s D ≤
          s.siftedSum ∧
      s.siftedSum ≤
          s.totalMass * ((1 + eta) * V) + levelRemainder s D := by
  have herrMinus : s.errSum lambdaMinus ≤ levelRemainder s D :=
    errSum_le_levelRemainder s D lambdaMinus hcoeffMinus hsupportMinus
  have herrPlus : s.errSum lambdaPlus ≤ levelRemainder s D :=
    errSum_le_levelRemainder s D lambdaPlus hcoeffPlus hsupportPlus
  constructor
  · calc
      s.totalMass * ((1 - eta) * V) - levelRemainder s D ≤
          s.totalMass * s.mainSum lambdaMinus - s.errSum lambdaMinus :=
        sub_le_sub (mul_le_mul_of_nonneg_left hmainLower hmass) herrMinus
      _ ≤ s.siftedSum :=
        s.totalMass_mainSum_sub_errSum_le_siftedSum lambdaMinus hlower
  · calc
      s.siftedSum ≤
          s.totalMass * s.mainSum lambdaPlus + s.errSum lambdaPlus :=
        s.siftedSum_le_totalMass_mainSum_add_errSum lambdaPlus hupper
      _ ≤ s.totalMass * ((1 + eta) * V) + levelRemainder s D :=
        add_le_add (mul_le_mul_of_nonneg_left hmainUpper hmass) herrPlus

/-! ### Explicit first-failure chains and the quantitative bridge -/

mutual
  /-- Upper first-failure chains, paired with the unselected suffix whose
  Euler product multiplies the chain. -/
  def upperFailureTerms {α : Type*} (stop : List α → Bool) :
      ℕ → List α → List α → List (List α × List α)
    | 0, _selected, _remaining => []
    | fuel + 1, selected, remaining =>
        (buchstabChildren remaining).flatMap fun q =>
          if stop (selected ++ [q.1]) then
            (lowerFailureTerms stop fuel (selected ++ [q.1]) q.2).map
              fun t => (q.1 :: t.1, t.2)
          else [([q.1], q.2)]

  /-- Lower first-failure chains. -/
  def lowerFailureTerms {α : Type*} (stop : List α → Bool) :
      ℕ → List α → List α → List (List α × List α)
    | 0, _selected, _remaining => []
    | fuel + 1, selected, remaining =>
        (buchstabChildren remaining).flatMap fun q =>
          (upperFailureTerms stop fuel (selected ++ [q.1]) q.2).map
            fun t => (q.1 :: t.1, t.2)
end

/-- Mass of a finite list of first-failure chains. -/
def evalFailureTerms {α : Type*} (x : α → ℝ)
    (terms : List (List α × List α)) : ℝ :=
  (terms.map fun t => (t.1.map x).prod * buchstabProduct x t.2).sum

private theorem evalFailureTerms_map_cons {α : Type*}
    (x : α → ℝ) (p : α) (terms : List (List α × List α)) :
    evalFailureTerms x (terms.map fun t => (p :: t.1, t.2)) =
      x p * evalFailureTerms x terms := by
  induction terms with
  | nil => simp [evalFailureTerms]
  | cons t terms ih =>
      unfold evalFailureTerms at ih ⊢
      simp only [List.map_map, List.map_cons, List.sum_cons, List.prod_cons]
      have ih' :
          (terms.map ((fun t => (t.1.map x).prod * buchstabProduct x t.2) ∘
            fun t => (p :: t.1, t.2))).sum =
            x p * (terms.map fun t =>
              (t.1.map x).prod * buchstabProduct x t.2).sum := by
        simpa only [List.map_map] using ih
      rw [ih']
      ring

private theorem evalFailureTerms_flatMap {α β : Type*}
    (x : α → ℝ) (l : List β) (f : β → List (List α × List α)) :
    evalFailureTerms x (l.flatMap f) =
      (l.map fun b => evalFailureTerms x (f b)).sum := by
  induction l with
  | nil => simp [evalFailureTerms]
  | cons b l ih =>
      unfold evalFailureTerms at ih ⊢
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      exact congrArg (fun y =>
        (List.map (fun t => (List.map x t.1).prod * buchstabProduct x t.2)
          (f b)).sum + y) ih

/-- The explicit chain lists evaluate to the recursive boundary masses. -/
theorem eval_failureTerms_eq_boundary {α : Type*}
    (stop : List α → Bool) (x : α → ℝ) :
    ∀ (fuel : ℕ) (selected remaining : List α),
      evalFailureTerms x (upperFailureTerms stop fuel selected remaining) =
          rosserUpperBoundary stop x fuel selected remaining ∧
        evalFailureTerms x (lowerFailureTerms stop fuel selected remaining) =
          rosserLowerBoundary stop x fuel selected remaining := by
  intro fuel
  induction fuel with
  | zero =>
      intro selected remaining
      simp [upperFailureTerms, lowerFailureTerms, evalFailureTerms,
        rosserUpperBoundary, rosserLowerBoundary]
  | succ fuel ih =>
      intro selected remaining
      constructor
      · rw [upperFailureTerms, rosserUpperBoundary, evalFailureTerms_flatMap]
        apply congrArg List.sum
        apply List.map_congr_left
        intro q _hq
        cases hstop : stop (selected ++ [q.1])
        · simp only [Bool.false_eq_true, ↓reduceIte, evalFailureTerms,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            List.prod_cons, List.prod_nil, mul_one, add_zero]
        · simp only [↓reduceIte, evalFailureTerms_map_cons]
          rw [(ih (selected ++ [q.1]) q.2).2]
      · rw [lowerFailureTerms, rosserLowerBoundary, evalFailureTerms_flatMap]
        apply congrArg List.sum
        apply List.map_congr_left
        intro q _hq
        rw [evalFailureTerms_map_cons,
          (ih (selected ++ [q.1]) q.2).1]

theorem failureTerms_length_bounds {α : Type*}
    (stop : List α → Bool) :
    ∀ (fuel : ℕ) (selected remaining : List α),
      (∀ t ∈ upperFailureTerms stop fuel selected remaining,
          1 ≤ t.1.length ∧ t.1.length ≤ fuel) ∧
        (∀ t ∈ lowerFailureTerms stop fuel selected remaining,
          1 ≤ t.1.length ∧ t.1.length ≤ fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro selected remaining
      simp [upperFailureTerms, lowerFailureTerms]
  | succ fuel ih =>
      intro selected remaining
      constructor
      · intro t ht
        simp only [upperFailureTerms, List.mem_flatMap] at ht
        obtain ⟨q, _hq, ht⟩ := ht
        cases hstop : stop (selected ++ [q.1])
        · simp only [hstop, Bool.false_eq_true, ↓reduceIte,
            List.mem_singleton] at ht
          subst t
          simp
        · simp only [hstop, ↓reduceIte, List.mem_map] at ht
          obtain ⟨u, hu, rfl⟩ := ht
          have hub := (ih (selected ++ [q.1]) q.2).2 u hu
          simp only [List.length_cons]
          omega
      · intro t ht
        simp only [lowerFailureTerms, List.mem_flatMap] at ht
        obtain ⟨q, _hq, ht⟩ := ht
        simp only [List.mem_map] at ht
        obtain ⟨u, hu, rfl⟩ := ht
        have hub := (ih (selected ++ [q.1]) q.2).1 u hu
        simp only [List.length_cons]
        omega

/-- First-failure mass at one exact chain depth.  `zipIdx` retains repeated
terms while permitting a finite fiber decomposition by depth. -/
noncomputable def depthFailureMass {α : Type*} (x : α → ℝ)
    (terms : List (List α × List α)) (r : ℕ) : ℝ := by
  classical
  exact ∑ z ∈ terms.zipIdx.toFinset with z.1.1.length = r,
    (z.1.1.map x).prod * buchstabProduct x z.1.2

theorem sum_depthFailureMass_eq_eval {α : Type*}
    (x : α → ℝ) (terms : List (List α × List α)) (fuel : ℕ)
    (hlen : ∀ t ∈ terms, t.1.length ≤ fuel) :
    (∑ r ∈ Finset.range (fuel + 1), depthFailureMass x terms r) =
      evalFailureTerms x terms := by
  classical
  unfold depthFailureMass evalFailureTerms
  have hmaps : ∀ z ∈ terms.zipIdx.toFinset,
      z.1.1.length ∈ Finset.range (fuel + 1) := by
    intro z hz
    have hzlist : z ∈ terms.zipIdx := List.mem_toFinset.mp hz
    have hzterm : z.1 ∈ terms := by
      have : z.1 ∈ terms.zipIdx.map Prod.fst :=
        List.mem_map.mpr ⟨z, hzlist, rfl⟩
      simpa using this
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hlen z.1 hzterm))
  rw [Finset.sum_fiberwise_of_maps_to hmaps]
  have hnodup : terms.zipIdx.Nodup :=
    List.Nodup.of_map Prod.snd (List.nodup_zipIdx_map_snd terms)
  have hsum := List.sum_toFinset
    (fun z => (z.1.1.map x).prod * buchstabProduct x z.1.2) hnodup
  rw [hsum]
  let F : (List α × List α) → ℝ := fun t =>
    (t.1.map x).prod * buchstabProduct x t.2
  have hzipAux : ∀ (l : List (List α × List α)) (n : ℕ),
      (l.zipIdx n).map (fun z => F z.1) = l.map F := by
    intro l
    induction l with
    | nil => intro n; simp
    | cons a l ih =>
        intro n
        simp only [List.zipIdx, List.map_cons]
        rw [ih]
  exact congrArg List.sum (hzipAux terms 0)

/-- The finite per-depth consequence of the dimension/product-ratio
hypothesis.  Depths below `start` have no first failure; at later depths the
normalized mass is bounded by the full beta-chain majorant. -/
def HasDepthProductRatio {α : Type*} (x : α → ℝ)
    (terms : List (List α × List α)) (V A κ : ℝ)
    (start fuel : ℕ) : Prop :=
  ∀ r ≤ fuel, depthFailureMass x terms r ≤
    if start ≤ r then V * betaDepthMajorant A κ r else 0

/-- The product-ratio depth bounds imply the quantitative fundamental-lemma
error, with the corrected depth-dependent majorant. -/
theorem evalFailureTerms_le_geometric_of_depthProductRatio
    {α : Type*} (x : α → ℝ)
    (terms : List (List α × List α))
    {V A κ : ℝ} {start fuel : ℕ}
    (hV : 0 ≤ V) (hA : 1 ≤ A) (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (hlen : ∀ t ∈ terms, t.1.length ≤ fuel)
    (hratio : HasDepthProductRatio x terms V A κ start fuel)
    (hlogA : ∀ r, start ≤ r → r ≤ fuel →
      Real.log A ≤ 2 * κ * r / 99) :
    evalFailureTerms x terms ≤
      V * ((4 * A / 3) * (1 / 4 : ℝ) ^ start) := by
  rw [← sum_depthFailureMass_eq_eval x terms fuel hlen]
  calc
    (∑ r ∈ Finset.range (fuel + 1), depthFailureMass x terms r) ≤
        ∑ r ∈ Finset.range (fuel + 1),
          if start ≤ r then V * betaDepthMajorant A κ r else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      exact hratio r (Nat.le_of_lt_succ (Finset.mem_range.mp hr))
    _ ≤ ∑ r ∈ Finset.range (fuel + 1),
          if start ≤ r then V * (A * (1 / 4 : ℝ) ^ r) else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      split
      · gcongr
        exact betaDepthMajorant_le_quarter_pow r hA hκ0 hκ2
          (hlogA r (by assumption)
            (Nat.le_of_lt_succ (Finset.mem_range.mp hr)))
      · rfl
    _ = V * A * ∑ r ∈ Finset.Ico start (fuel + 1),
          (1 / 4 : ℝ) ^ r := by
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.range (fuel + 1)).filter (fun r => start ≤ r) =
            Finset.Ico start (fuel + 1) := by
        ext r
        simp [and_comm]
      rw [hfilter]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ ≤ V * A * ((1 / 4 : ℝ) ^ start / (1 - 1 / 4)) := by
      gcongr
      exact geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ = V * ((4 * A / 3) * (1 / 4 : ℝ) ^ start) := by
      ring

/-- Quantitative beta-sieve boundary bound, exported in the recursive
`RosserCore` representation. -/
theorem rosserBoundaries_le_geometric_of_depthProductRatio
    {α : Type*} (stop : List α → Bool) (x : α → ℝ)
    {V A κ : ℝ} {start fuel : ℕ} (selected remaining : List α)
    (hV : 0 ≤ V) (hA : 1 ≤ A) (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (hupper : HasDepthProductRatio x
      (upperFailureTerms stop fuel selected remaining) V A κ start fuel)
    (hlower : HasDepthProductRatio x
      (lowerFailureTerms stop fuel selected remaining) V A κ start fuel)
    (hlogA : ∀ r, start ≤ r → r ≤ fuel →
      Real.log A ≤ 2 * κ * r / 99) :
    rosserUpperBoundary stop x fuel selected remaining ≤
          V * ((4 * A / 3) * (1 / 4 : ℝ) ^ start) ∧
      rosserLowerBoundary stop x fuel selected remaining ≤
          V * ((4 * A / 3) * (1 / 4 : ℝ) ^ start) := by
  rw [← (eval_failureTerms_eq_boundary stop x fuel selected remaining).1,
    ← (eval_failureTerms_eq_boundary stop x fuel selected remaining).2]
  constructor
  · exact evalFailureTerms_le_geometric_of_depthProductRatio x _ hV hA
      hκ0 hκ2
      (fun t ht => (failureTerms_length_bounds stop fuel selected remaining).1
        t ht |>.2)
      hupper hlogA
  · exact evalFailureTerms_le_geometric_of_depthProductRatio x _ hV hA
      hκ0 hκ2
      (fun t ht => (failureTerms_length_bounds stop fuel selected remaining).2
        t ht |>.2)
      hlower hlogA

end BetaSieveFundamental

end Erdos851
