import Mathlib

/-!
# Quantitative interpolation bounds for Erdős Problem 228

This file contains the finite-dimensional estimate used in the Howell
interpolation step of the flat Littlewood-polynomial construction.  The
analytic interpolation theorem writes a derivative as a weighted sum of
function values, up to a remainder.  The lemmas below bound the Lagrange
weights from separation of the nodes and then propagate uniform bounds on the
values and the remainder to the derivative.
-/

namespace Erdos228.Interpolation

open scoped BigOperators

/-! ### Repeated Rolle theorem -/

/-- If a `C^k` real function vanishes at `k+1` strictly increasing points,
then its `k`th derivative vanishes somewhere between the first and last
point.  This is the analytic core of the interpolation remainder argument. -/
theorem exists_iteratedDeriv_eq_zero_of_strictMono :
    ∀ (k : ℕ) (g : ℝ → ℝ) (x : Fin (k + 1) → ℝ),
      ContDiff ℝ k g → StrictMono x → (∀ i, g (x i) = 0) →
      ∃ z ∈ Set.Icc (x 0) (x (Fin.last k)), iteratedDeriv k g z = 0 := by
  intro k
  induction k with
  | zero =>
      intro g x _hg _hx hzero
      refine ⟨x 0, ⟨le_rfl, ?_⟩, ?_⟩
      · simp
      · simpa using hzero 0
  | succ k ih =>
      intro g x hg hx hzero
      have hrolle (i : Fin (k + 1)) :
          ∃ c ∈ Set.Ioo (x i.castSucc) (x i.succ), deriv g c = 0 := by
        apply exists_deriv_eq_zero
        · exact hx Fin.castSucc_lt_succ
        · exact hg.continuous.continuousOn
        · rw [hzero i.castSucc, hzero i.succ]
      let c : Fin (k + 1) → ℝ := fun i ↦ Classical.choose (hrolle i)
      have hc_mem (i : Fin (k + 1)) :
          c i ∈ Set.Ioo (x i.castSucc) (x i.succ) :=
        (Classical.choose_spec (hrolle i)).1
      have hc_zero (i : Fin (k + 1)) : deriv g (c i) = 0 :=
        (Classical.choose_spec (hrolle i)).2
      have hc_mono : StrictMono c := by
        intro i j hij
        have hij' : i.succ ≤ j.castSucc := by
          apply Fin.mk_le_mk.mpr
          omega
        exact (hc_mem i).2.trans ((hx.monotone hij').trans_lt (hc_mem j).1)
      have hderiv : ContDiff ℝ k (deriv g) := hg.deriv'
      obtain ⟨z, hz, hz0⟩ := ih (deriv g) c hderiv hc_mono hc_zero
      refine ⟨z, ⟨?_, ?_⟩, ?_⟩
      · exact (hc_mem 0).1.le.trans hz.1
      · exact hz.2.trans (hc_mem (Fin.last k)).2.le
      · simpa only [iteratedDeriv_succ'] using hz0

/-- The coefficient of the top-degree term of the `j`th Lagrange basis
polynomial, multiplied by `k!`.  Thus these are the weights occurring when
the `k`th derivative of the interpolating polynomial is evaluated. -/
noncomputable def lagrangeDerivativeWeight (k : ℕ) (y : Fin (k + 1) → ℝ)
    (j : Fin (k + 1)) : ℝ :=
  (k.factorial : ℝ) /
    ∏ i ∈ (Finset.univ.erase j), (y j - y i)

/-- The `k`th derivative of the degree-`k` Lagrange interpolant is the
weighted sum defined by `lagrangeDerivativeWeight`. -/
theorem eval_iterate_derivative_interpolate_top (k : ℕ)
    (y : Fin (k + 1) → ℝ) (v : Fin (k + 1) → ℝ) (hy : Function.Injective y)
    (x : ℝ) :
    ((Polynomial.derivative^[k])
      (Lagrange.interpolate Finset.univ y v)).eval x =
      ∑ i, lagrangeDerivativeWeight k y i * v i := by
  rw [Lagrange.iterate_derivative_interpolate v hy.injOn (by simp)]
  simp [lagrangeDerivativeWeight, Finset.mul_sum, div_eq_mul_inv, mul_comm]
  simp [Polynomial.eval_finsetSum, mul_left_comm]

/-- Iterated analytic differentiation of a polynomial evaluation agrees with
iteration of its formal polynomial derivative. -/
theorem iteratedDeriv_polynomial_eval (k : ℕ) (P : Polynomial ℝ) (x : ℝ) :
    iteratedDeriv k (fun t ↦ P.eval t) x =
      ((Polynomial.derivative^[k]) P).eval x := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ']
      have hfun : deriv (fun t ↦ P.eval t) = fun t ↦ P.derivative.eval t := by
        funext t
        exact P.deriv
      rw [hfun, ih]
      rw [Function.iterate_succ_apply']
      exact congrArg (Polynomial.eval x)
        ((Function.Commute.self_iterate
          (Polynomial.derivative : Polynomial ℝ → Polynomial ℝ) k) P).symm

/-- Howell's derivative interpolation estimate on the real line.

The nodes are strictly increasing, lie at distance at most `Delta` from the
basepoint `x`, and the `(k+1)`st derivative is bounded by `M`.  The `k`th
derivative at `x` is therefore within `Delta * M` of the `k`th derivative of
the Lagrange interpolant through the sampled values. -/
theorem howell_derivative_approximation (k : ℕ) (f : ℝ → ℝ)
    (y : Fin (k + 1) → ℝ) (x Delta M : ℝ)
    (hf : ContDiff ℝ (k + 1) f) (hy : StrictMono y)
    (_hDelta : 0 ≤ Delta) (hM : 0 ≤ M)
    (hyx : ∀ i, |y i - x| ≤ Delta)
    (hderiv : ∀ t, |iteratedDeriv (k + 1) f t| ≤ M) :
    |iteratedDeriv k f x -
      ∑ i, lagrangeDerivativeWeight k y i * f (y i)| ≤ Delta * M := by
  let P : Polynomial ℝ := Lagrange.interpolate Finset.univ y (fun i ↦ f (y i))
  let g : ℝ → ℝ := fun t ↦ f t - P.eval t
  have hP : ContDiff ℝ (k + 1) (fun t ↦ P.eval t) := by
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
    | monomial n a =>
        simp only [Polynomial.eval_monomial]
        fun_prop
  have hg : ContDiff ℝ k g := by
    apply ContDiff.sub (hf.of_le (by norm_num)) (hP.of_le (by norm_num))
  have hzero : ∀ i, g (y i) = 0 := by
    intro i
    have hPi : P.eval (y i) = f (y i) := by
      dsimp only [P]
      exact Lagrange.eval_interpolate_at_node _ hy.injective.injOn (Finset.mem_univ i)
    dsimp only [g]
    rw [hPi, sub_self]
  obtain ⟨z, hz, hz0⟩ :=
    exists_iteratedDeriv_eq_zero_of_strictMono k g y hg hy hzero
  have hPAt : ContDiffAt ℝ k (fun t ↦ P.eval t) z := (hP.of_le (by norm_num)).contDiffAt
  have hfAt : ContDiffAt ℝ k f z := (hf.of_le (by norm_num)).contDiffAt
  have hzEq : iteratedDeriv k f z =
      ∑ i, lagrangeDerivativeWeight k y i * f (y i) := by
    change iteratedDeriv k (f - fun t ↦ P.eval t) z = 0 at hz0
    rw [iteratedDeriv_sub hfAt hPAt, iteratedDeriv_polynomial_eval,
      eval_iterate_derivative_interpolate_top k y (fun i ↦ f (y i)) hy.injective z] at hz0
    linarith
  have hzDist : |z - x| ≤ Delta := by
    have hleft := (abs_le.mp (hyx (0 : Fin (k + 1)))).1
    have hright := (abs_le.mp (hyx (Fin.last k))).2
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hdiff : Differentiable ℝ (iteratedDeriv k f) :=
    hf.differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)
  have hmean :
      |iteratedDeriv k f x - iteratedDeriv k f z| ≤ M * |x - z| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (f := iteratedDeriv k f) (x := z) (y := x)
      (fun t _ ↦ hdiff.differentiableAt)
      (fun t _ ↦ by
        rw [← iteratedDeriv_succ]
        simpa only [Real.norm_eq_abs] using hderiv t)
      convex_univ (Set.mem_univ z) (Set.mem_univ x)
    simpa only [Real.norm_eq_abs] using h
  rw [← hzEq]
  calc
    |iteratedDeriv k f x - iteratedDeriv k f z| ≤ M * |x - z| := hmean
    _ = M * |z - x| := by rw [abs_sub_comm]
    _ ≤ M * Delta := mul_le_mul_of_nonneg_left hzDist hM
    _ = Delta * M := mul_comm _ _

/-- A product of `k` factors, each of absolute value at least `eta`, has
absolute value at least `eta ^ k`. -/
theorem pow_le_abs_prod_of_separated (k : ℕ) (y : Fin (k + 1) → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (j : Fin (k + 1)) :
    eta ^ k ≤ |∏ i ∈ (Finset.univ.erase j), (y j - y i)| := by
  classical
  rw [Finset.abs_prod]
  have hcard : (Finset.univ.erase j).card = k := by simp
  calc
    eta ^ k = eta ^ (Finset.univ.erase j).card := congrArg (eta ^ ·) hcard.symm
    _ = ∏ _i ∈ (Finset.univ.erase j), eta := by simp
    _ ≤ ∏ i ∈ (Finset.univ.erase j), |y j - y i| := by
      apply Finset.prod_le_prod (fun _i _hi ↦ heta)
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simpa only [abs_sub_comm] using hsep i j hij

/-- Separation of the interpolation nodes bounds every top-derivative
Lagrange weight by `k! / eta^k`. -/
theorem abs_lagrangeDerivativeWeight_le (k : ℕ) (y : Fin (k + 1) → ℝ) (eta : ℝ)
    (heta : 0 < eta)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (j : Fin (k + 1)) :
    |lagrangeDerivativeWeight k y j| ≤ (k.factorial : ℝ) / eta ^ k := by
  rw [lagrangeDerivativeWeight, abs_div, abs_of_nonneg (Nat.cast_nonneg _)]
  have hprod := pow_le_abs_prod_of_separated k y eta heta.le hsep j
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hprod

/-- Uniformly bounded summands have a uniformly bounded finite sum. -/
theorem abs_sum_le_card_mul {n : ℕ} (u : Fin n → ℝ) (A : ℝ)
    (hA : ∀ i, |u i| ≤ A) :
    |∑ i, u i| ≤ n * A := by
  calc
    |∑ i, u i| ≤ ∑ i, |u i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, A := Finset.sum_le_sum fun i _ ↦ hA i
    _ = n * A := by simp [nsmul_eq_mul]

/-- The interpolation sum is small when the nodes are separated and all
sampled function values are small. -/
theorem abs_lagrange_sum_le (k : ℕ) (y : Fin (k + 1) → ℝ) (eta epsilon : ℝ)
    (heta : 0 < eta) (_hepsilon : 0 ≤ epsilon)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (v : Fin (k + 1) → ℝ) (hv : ∀ i, |v i| ≤ epsilon) :
    |∑ i, lagrangeDerivativeWeight k y i * v i| ≤
      (k + 1) * ((k.factorial : ℝ) / eta ^ k * epsilon) := by
  have h := abs_sum_le_card_mul
    (fun i ↦ lagrangeDerivativeWeight k y i * v i)
    ((k.factorial : ℝ) / eta ^ k * epsilon) (fun i ↦ by
      rw [abs_mul]
      exact mul_le_mul
        (abs_lagrangeDerivativeWeight_le k y eta heta hsep i) (hv i)
        (abs_nonneg _) (by positivity))
  simpa [Nat.cast_add, Nat.cast_one] using h

/-- Quantitative Howell estimate, in the form needed by the construction.

The analytic part of derivative interpolation supplies `happrox`: the
derivative `d` differs from the derivative of the Lagrange interpolant by at
most `remainder`.  This lemma performs the complete quantitative estimate
from node separation and small sampled values. -/
theorem howell_bound_of_approximation (k : ℕ) (y : Fin (k + 1) → ℝ)
    (eta epsilon remainder d : ℝ)
    (heta : 0 < eta) (hepsilon : 0 ≤ epsilon) (_hremainder : 0 ≤ remainder)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (v : Fin (k + 1) → ℝ) (hv : ∀ i, |v i| ≤ epsilon)
    (happrox : |d - ∑ i, lagrangeDerivativeWeight k y i * v i| ≤ remainder) :
    |d| ≤ remainder + (k + 1) * ((k.factorial : ℝ) / eta ^ k * epsilon) := by
  have hsum := abs_lagrange_sum_le k y eta epsilon heta hepsilon hsep v hv
  calc
    |d| = |(d - ∑ i, lagrangeDerivativeWeight k y i * v i) +
        ∑ i, lagrangeDerivativeWeight k y i * v i| := by ring_nf
    _ ≤ |d - ∑ i, lagrangeDerivativeWeight k y i * v i| +
        |∑ i, lagrangeDerivativeWeight k y i * v i| := abs_add_le _ _
    _ ≤ remainder + (k + 1) * ((k.factorial : ℝ) / eta ^ k * epsilon) :=
      add_le_add happrox hsum

/-- The numerical specialization used in the seven-cell small-value
argument.  For derivative orders `1`, `2`, and `3`, values of size at most
`eta^3 / 128`, node separation `eta`, and interpolation remainder at most
`126 * eta` force the derivative to have absolute value strictly below
`1 / 4` whenever `eta < 2⁻¹¹`.

The constant `126` is `7 * 18`: every node is within `7 * eta` of the
basepoint and the fourth-derivative bound in the application is
`2^4 + 2 = 18`. -/
theorem howell_lt_quarter (k : ℕ) (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3)
    (y : Fin (k + 1) → ℝ) (eta d : ℝ)
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (v : Fin (k + 1) → ℝ) (hv : ∀ i, |v i| ≤ eta ^ 3 / 128)
    (happrox : |d - ∑ i, lagrangeDerivativeWeight k y i * v i| ≤ 126 * eta) :
    |d| < 1 / 4 := by
  have hetaPow : 0 ≤ eta ^ 3 / 128 := by positivity
  have hbound := howell_bound_of_approximation k y eta (eta ^ 3 / 128)
    (126 * eta) d heta hetaPow (by positivity) hsep v hv happrox
  have hetaOne : eta < 1 := by
    calc
      eta < (1 : ℝ) / 2048 := hetaSmall
      _ < 1 := by norm_num
  have hetaLeOne : eta ≤ 1 := hetaOne.le
  have hetaSqLeOne : eta ^ 2 ≤ 1 := by nlinarith [sq_nonneg eta]
  have hinterp :
      (k + 1 : ℝ) * ((k.factorial : ℝ) / eta ^ k * (eta ^ 3 / 128)) ≤ 3 / 16 := by
    interval_cases k <;> norm_num at hk₁ hk₃ ⊢
    · field_simp [ne_of_gt heta]
      nlinarith [sq_nonneg eta]
    · field_simp [ne_of_gt heta]
      nlinarith
    · field_simp [ne_of_gt heta]
      norm_num
  have hrem : 126 * eta < 1 / 16 := by
    norm_num at hetaSmall ⊢
    nlinarith
  nlinarith

/-- Fully analytic form of the Howell estimate used for derivative orders
`1`, `2`, and `3` in the seven-cell argument.  This combines repeated Rolle,
Lagrange interpolation, the derivative remainder estimate, the separated-node
weight bound, and the final numerical calculation. -/
theorem howell_lt_quarter_of_nodes (k : ℕ) (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3)
    (f : ℝ → ℝ) (y : Fin (k + 1) → ℝ) (x eta : ℝ)
    (hf : ContDiff ℝ (k + 1) f) (hy : StrictMono y)
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (hyx : ∀ i, |y i - x| ≤ 7 * eta)
    (hvalue : ∀ i, |f (y i)| ≤ eta ^ 3 / 128)
    (hderiv : ∀ t, |iteratedDeriv (k + 1) f t| ≤ 18) :
    |iteratedDeriv k f x| < 1 / 4 := by
  have happrox' := howell_derivative_approximation k f y x (7 * eta) 18 hf hy
    (by positivity) (by norm_num) hyx hderiv
  have happrox :
      |iteratedDeriv k f x -
        ∑ i, lagrangeDerivativeWeight k y i * f (y i)| ≤ 126 * eta := by
    convert happrox' using 1
    ring
  exact howell_lt_quarter k hk₁ hk₃ y eta (iteratedDeriv k f x) heta hetaSmall
    hsep (fun i ↦ f (y i)) hvalue happrox

end Erdos228.Interpolation
