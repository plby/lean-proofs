/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1196.
https://www.erdosproblems.com/forum/thread/1196

Informal authors:
- Liam Price
- GPT-5.4 Pro

Formal authors:
- gauss-math-inc
- Math, Inc.

URLs:
- https://www.erdosproblems.com/forum/thread/1196#post-5469
- https://github.com/math-inc/Erdos1196/tree/02fba13be7487cc51315f68d8fa7ef277633d3c8
- https://github.com/math-inc/Erdos1196/blob/02fba13be7487cc51315f68d8fa7ef277633d3c8/PrimitiveSetsAboveX/FormalConjecturesErdos1196.lean
- https://github.com/math-inc/Erdos1196/blob/02fba13be7487cc51315f68d8fa7ef277633d3c8/source.tex
-/
import Mathlib

namespace Erdos1196



/-!
# Basic definitions for primitive sets above `x`

This file introduces the core objects used throughout the development: the arithmetic sums
appearing in the analytic estimates, the entry weights and normalization data `b_x`, `B_x`,
and `μ_x`, and the abstract Markov-layer interface used for the visit-probability argument.

## Main definitions

* `PrimitiveSet`
* `mertensPartialSum`
* `tailSum`
* `ry`
* `entryWeight`
* `normalizationConstant`
* `initialDistribution`
* `MarkovLayer`
-/


open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/-- The primitive-set predicate used throughout the local development. -/
def PrimitiveSet (A : Set ℕ) : Prop :=
  ∀ ⦃m n : ℕ⦄, m ∈ A → n ∈ A → m ∣ n → m = n

/-- Partial sums of `Λ(q) / q`. -/
noncomputable def mertensPartialSum (t : ℕ) : ℝ :=
  (Finset.Icc 1 t).sum fun q => Λ q / (q : ℝ)

/-- The logarithmic tail sum `T(m, y)` used in the normalization estimates. -/
noncomputable def tailSum (m y : ℕ) : ℝ :=
  ∑' q : ℕ,
    if y ≤ q then
      Λ q / ((q : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)
    else 0

/-- The quantity `R_Y(m)` introduced in the proof of the main theorem. -/
noncomputable def ry (Y m : ℕ) : ℝ :=
  ∑' q : ℕ,
    if Y ≤ q then
      (Real.log (m : ℝ) / (Real.log ((m * q : ℕ) : ℝ)) ^ 2) * (Λ q / (q : ℝ))
    else 0

/-- The transition weight `p(m, mq)` of the sub-Markov chain. -/
noncomputable def transitionWeight (Y m q : ℕ) : ℝ :=
  if Y ≤ q then
    (Real.log (m : ℝ) / (Real.log ((m * q : ℕ) : ℝ)) ^ 2) * (Λ q / (q : ℝ))
  else 0

/-- The entry weight `b_x(n)` used to define the initial distribution of the chain. -/
noncomputable def entryWeight (x Y n : ℕ) : ℝ :=
  1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) *
    (((n.divisors.filter (fun q => q < Y)).sum fun q => Λ q) +
      ((n.divisors.filter (fun q => Y ≤ q ∧ n / q < x)).sum fun q => Λ q))

/-- The normalizing constant `B_x`. -/
noncomputable def normalizationConstant (x Y : ℕ) : ℝ :=
  ∑' n : ℕ, if x ≤ n then entryWeight x Y n else 0

/-- The normalized initial distribution `μ_x(n) = b_x(n) / B_x`. -/
noncomputable def initialDistribution (x Y n : ℕ) : ℝ :=
  entryWeight x Y n / normalizationConstant x Y

/--
An abstract sub-Markov layer on the state space `n ≥ x`, together with a candidate
visit-probability function satisfying the last-jump recurrence.
-/
structure MarkovLayer (x Y : ℕ) where
  /-- The transition weights satisfy the required sub-Markov row-sum bound. -/
  transitionSubMarkov :
    ∀ ⦃m : ℕ⦄, x ≤ m → (∑' q : ℕ, transitionWeight Y m q) ≤ 1
  /-- The probability that the chain ever visits `n` when started from `μ_x`. -/
  visitProbability : ℕ → ℝ
  /-- The last-jump recurrence for the visiting probabilities. -/
  visitProbabilityRecurrence :
    ∀ ⦃n : ℕ⦄, x ≤ n →
      visitProbability n =
        initialDistribution x Y n +
          ∑' q : ℕ,
            if Y ≤ q ∧ q ∣ n ∧ x ≤ n / q then
              visitProbability (n / q) * transitionWeight Y (n / q) q
            else 0

end PrimitiveSetsAboveX



/-!
# Arithmetic preliminaries for primitive sets above `x`

This file collects the exact divisor identities, factorial decompositions, and bounded-error
Mertens estimate used later in the normalization and tail-sum arguments.

## Main statements

* `mertensEstimate`
-/


open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/-- The fractional-part correction in the standard factorial proof of Mertens' estimate. -/
private noncomputable def mertensFractionalError (t : ℕ) : ℝ :=
  (1 / t) * ∑ m ∈ Finset.Icc 1 t, Λ m * ((t : ℝ) / m - ((t / m : ℕ) : ℝ))

/--
On a positive index `m`, scaling the real quotient `(t : ℝ) / m` by `1 / t` recovers division by
`m`.
-/
private lemma one_div_mul_mul_natCast_div {a : ℝ} {t m : ℕ} (ht : t ≠ 0) :
    (1 / (t : ℝ)) * (a * ((t : ℝ) / m)) = a / (m : ℝ) := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  grind only

/-- The truncation error from replacing `t / m` by the integer quotient is `↑(t % m) / m`. -/
private lemma truncation_eq_mod_div {t m : ℕ} :
    ((t : ℝ) / m - ↑(t / m)) = ↑(t % m) / m := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp
  · have hmR : (m : ℝ) ≠ 0 := by
      exact_mod_cast hm.ne'
    apply (eq_div_iff hmR).2
    have hdecomp : (↑(t % m) : ℝ) + ↑(t / m) * m = t := by
      have h : (↑(t % m + m * (t / m)) : ℝ) = t := by
        exact_mod_cast (Nat.mod_add_div t m)
      simpa [Nat.cast_add, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using h
    grind only

/-- The floor-truncation term in the Mertens decomposition is the fractional part of `t / m`. -/
private lemma truncation_eq_fract {t m : ℕ} :
    ((t : ℝ) / m - ↑(t / m)) = Int.fract ((t : ℝ) / m) := by
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  exact truncation_eq_mod_div

/--
Rearranging the multiple count gives the factorial identity
`∑_{m ≤ N} Λ(m) * ⌊N / m⌋ = log (N!)`.
-/
private lemma sum_vonMangoldt_mul_div_eq_log_factorial (N : ℕ) :
    (Finset.Icc 1 N).sum (fun m => Λ m * ((N / m : ℕ) : ℝ)) =
      Real.log (Nat.factorial N) := by
  have hI : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  have hlogsum :
      (Finset.Icc 1 N).sum (fun n => Real.log (n : ℝ)) =
        Real.log (∏ n ∈ Finset.Icc 1 N, (n : ℝ)) := by
    symm
    refine Real.log_prod ?_
    intro n hn
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.succ_le_iff.mp (Finset.mem_Icc.mp hn).1))
  have hprodRange : (∏ i ∈ Finset.range N, ((i + 1 : ℕ) : ℝ)) = Nat.factorial N := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial N
  have hprod : (∏ n ∈ Finset.Icc 1 N, (n : ℝ)) = Nat.factorial N := by
    rw [← Finset.Ico_add_one_right_eq_Icc 1 N, Finset.prod_Ico_eq_prod_range]
    simpa [Nat.succ_eq_add_one, add_comm] using hprodRange
  calc
    (Finset.Icc 1 N).sum (fun m => Λ m * ((N / m : ℕ) : ℝ)) =
        ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) := by
          rw [hI]
    _ = ∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.vonMangoldt * ArithmeticFunction.zeta) n := by
          simpa using
            (ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum ArithmeticFunction.vonMangoldt N).symm
    _ = ∑ n ∈ Finset.Ioc 0 N, Real.log (n : ℝ) := by
          simp [ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.log]
    _ = ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := by
          rw [← hI]
    _ = Real.log (Nat.factorial N) := by
          rw [hlogsum, hprod]

/-- Writing `N!` as a product of the integers `1, …, N` turns `log (N!)` into a sum of logs. -/
private lemma log_factorial_eq_sum_range (N : ℕ) :
    Real.log (Nat.factorial N) = ∑ i ∈ Finset.range N, Real.log ((i + 1 : ℕ) : ℝ) := by
  rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod, Real.log_prod]
  grind only

/-- The lower integral comparison `∫_1^N log t dt ≤ log N!`. -/
private lemma integral_log_le_log_factorial {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x ≤ Real.log (Nat.factorial N) := by
  have hmono : MonotoneOn Real.log (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y hy hxy
    have hx1 : (0 : ℝ) < x :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)) hx.1
    exact Real.log_le_log hx1 hxy
  calc
    ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x
      ≤ ∑ i ∈ Finset.Ico 1 N, Real.log ((i + 1 : ℕ) : ℝ) :=
        MonotoneOn.integral_le_sum_Ico (f := Real.log) hN hmono
    _ = ∑ i ∈ Finset.range N, Real.log ((i + 1 : ℕ) : ℝ) := by
        have hpred : N - 1 + 1 = N := Nat.sub_add_cancel hN
        rw [Finset.sum_Ico_eq_sum_range]
        rw [← hpred, Finset.sum_range_succ']
        simp [Nat.cast_add, add_left_comm, add_comm]
    _ = Real.log (Nat.factorial N) := (log_factorial_eq_sum_range N).symm

/-- The upper integral comparison `log N! ≤ log N + ∫_1^N log t dt`. -/
private lemma log_factorial_le_log_add_integral_log {N : ℕ} (hN : 1 ≤ N) :
    Real.log (Nat.factorial N) ≤ Real.log N + ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x := by
  have hmono : MonotoneOn Real.log (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y hy hxy
    have hx1 : (0 : ℝ) < x :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)) hx.1
    exact Real.log_le_log hx1 hxy
  have hsum :
      ∑ i ∈ Finset.Ico 1 N, Real.log (i : ℝ) ≤ ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x :=
    MonotoneOn.sum_le_integral_Ico (f := Real.log) hN hmono
  have hsum' : ∑ i ∈ Finset.Ico 1 N, Real.log (i : ℝ) = Real.log (Nat.factorial (N - 1)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simpa [Nat.cast_add, add_comm] using (log_factorial_eq_sum_range (N - 1)).symm
  have hfacNat : Nat.factorial N = N * Nat.factorial (N - 1) := by
    have hpred : N - 1 + 1 = N := Nat.sub_add_cancel hN
    simpa [Nat.succ_eq_add_one, hpred] using (Nat.factorial_succ (N - 1))
  have hfac :
      Real.log (Nat.factorial N) = Real.log N + Real.log (Nat.factorial (N - 1)) := by
    rw [hfacNat, Nat.cast_mul, Real.log_mul]
    · exact_mod_cast Nat.ne_of_gt hN
    · exact_mod_cast Nat.factorial_ne_zero (N - 1)
  grind only

/-- Elementary two-sided bounds for `log N! / N`. -/
private lemma abs_log_factorial_div_sub_log_le_one {N : ℕ} (hN : 1 ≤ N) :
    |Real.log (Nat.factorial N) / N - Real.log N| ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hint :
      ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x = (N : ℝ) * Real.log N - N + 1 := by
    simp [integral_log]
  have hlower :
      Real.log N - 1 ≤ Real.log (Nat.factorial N) / N := by
    apply (le_div_iff₀ hNpos).2
    have hcomp : (N : ℝ) * Real.log N - N + 1 ≤ Real.log (Nat.factorial N) := by
      simpa [hint] using integral_log_le_log_factorial hN
    linarith
  have hupper :
      Real.log (Nat.factorial N) / N ≤ Real.log N := by
    apply (div_le_iff₀ hNpos).2
    have hcomp :
        Real.log (Nat.factorial N) ≤ Real.log N + ((N : ℝ) * Real.log N - N + 1) := by
      simpa [hint] using log_factorial_le_log_add_integral_log hN
    have hlog : Real.log N ≤ N - 1 := by
      simpa using Real.log_le_sub_one_of_pos hNpos
    linarith
  grind only [= abs.eq_1, = max_def]

/-- The factorial decomposition of the Mertens partial sums. -/
private lemma mertensPartialSum_eq_log_factorial_div_add_fractional (t : ℕ) :
    mertensPartialSum t = Real.log (Nat.factorial t) / t + mertensFractionalError t := by
  by_cases ht : t = 0
  · subst ht
    simp [mertensPartialSum, mertensFractionalError]
  · rw [mertensPartialSum, mertensFractionalError]
    calc
      ∑ m ∈ Finset.Icc 1 t, Λ m / (m : ℝ) =
          ∑ m ∈ Finset.Icc 1 t,
            ((1 / (t : ℝ)) * (Λ m * (((t / m : ℕ) : ℝ))) +
              (1 / (t : ℝ)) * (Λ m * ((t : ℝ) / m - ↑(t / m)))) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            calc
              Λ m / (m : ℝ) = (1 / (t : ℝ)) * (Λ m * ((t : ℝ) / m)) := by
                symm
                exact one_div_mul_mul_natCast_div (a := Λ m) ht
              _ = (1 / (t : ℝ)) * (Λ m * (((t / m : ℕ) : ℝ))) +
                    (1 / (t : ℝ)) * (Λ m * ((t : ℝ) / m - ↑(t / m))) := by
                    ring
      _ = (1 / (t : ℝ)) * ∑ m ∈ Finset.Icc 1 t, Λ m * (((t / m : ℕ) : ℝ)) +
            (1 / (t : ℝ)) *
              ∑ m ∈ Finset.Icc 1 t,
                Λ m * ((t : ℝ) / m - ↑(t / m)) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = Real.log (Nat.factorial t) / t + mertensFractionalError t := by
            rw [sum_vonMangoldt_mul_div_eq_log_factorial]
            rw [mertensFractionalError]
            ring_nf

/-- The fractional correction term is nonnegative. -/
private lemma mertensFractionalError_nonneg {t : ℕ} (ht : 1 ≤ t) :
    0 ≤ mertensFractionalError t := by
  rw [mertensFractionalError]
  refine mul_nonneg ?_ (Finset.sum_nonneg ?_)
  · exact one_div_nonneg.mpr (show (0 : ℝ) ≤ t by positivity)
  · intro m hm
    rw [truncation_eq_fract]
    exact mul_nonneg
      ArithmeticFunction.vonMangoldt_nonneg
      (Int.fract_nonneg _)

/-- The fractional correction term is uniformly bounded by Chebyshev's estimate. -/
private lemma mertensFractionalError_le {t : ℕ} (ht : 2 ≤ t) :
    mertensFractionalError t ≤ Real.log 4 + 4 := by
  rw [mertensFractionalError]
  have hsum :
      ∑ m ∈ Finset.Icc 1 t, Λ m * ((t : ℝ) / m - ↑(t / m))
        ≤ ∑ m ∈ Finset.Icc 1 t, Λ m := by
    refine Finset.sum_le_sum ?_
    intro m hm
    rw [truncation_eq_fract]
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := m), (Int.fract_lt_one ((t : ℝ) / m)).le]
  have hcheb : Chebyshev.psi t ≤ (Real.log 4 + 4) * t := by
    simpa using
      Chebyshev.psi_le_const_mul_self (x := (t : ℝ)) (show 0 ≤ (t : ℝ) by positivity)
  have hI : Finset.Icc 1 t = Finset.Ioc 0 t := by
    ext n
    simp [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  calc
    (1 / t : ℝ) * ∑ m ∈ Finset.Icc 1 t, Λ m * ((t : ℝ) / m - ↑(t / m))
      ≤ (1 / t : ℝ) * ∑ m ∈ Finset.Icc 1 t, Λ m :=
        mul_le_mul_of_nonneg_left hsum
          (one_div_nonneg.mpr (show (0 : ℝ) ≤ t by positivity))
    _ = Chebyshev.psi t / t := by
        simp [hI, Chebyshev.psi, Nat.floor_natCast, div_eq_mul_inv, mul_comm]
    _ ≤ Real.log 4 + 4 := by
        have htR : 0 < (t : ℝ) := by positivity
        exact (div_le_iff₀ htR).mpr hcheb

/-- Bounded-error form of Mertens' estimate:
`∑_{q ≤ t} Λ(q) / q = log t + O(1)` on the natural numbers. -/
lemma mertensEstimate :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃t : ℕ⦄, 2 ≤ t →
        |mertensPartialSum t - Real.log (t : ℝ)| ≤ C := by
  refine ⟨Real.log 4 + 5, by positivity, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := by omega
  rw [mertensPartialSum_eq_log_factorial_div_add_fractional t]
  calc
    |Real.log (Nat.factorial t) / t + mertensFractionalError t - Real.log (t : ℝ)|
      = |(Real.log (Nat.factorial t) / t - Real.log (t : ℝ)) + mertensFractionalError t| := by
          congr
          ring
    _ ≤ |Real.log (Nat.factorial t) / t - Real.log (t : ℝ)| + |mertensFractionalError t| :=
        abs_add_le _ _
    _ = |Real.log (Nat.factorial t) / t - Real.log (t : ℝ)| + mertensFractionalError t := by
        rw [abs_of_nonneg (mertensFractionalError_nonneg ht1)]
    _ ≤ 1 + (Real.log 4 + 4) := by
        gcongr
        · exact abs_log_factorial_div_sub_log_le_one ht1
        · exact mertensFractionalError_le ht
    _ = Real.log 4 + 5 := by ring

end PrimitiveSetsAboveX



/-!
# Auxiliary tail lemmas for primitive sets above `x`

This file contains the standalone calculus lemmas reused in the proof of `tailEstimate`.
Its main output is a small API for the model kernels `1 / (t log(ct)^2)` and
`2 / (t log(ct)^3)`: each kernel is integrable on an admissible tail, and its tail integral can
be computed exactly.

## Main statements

* `integrableOn_Ioi_inv_log_sq`
* `integral_Ioi_inv_log_sq`
* `integrableOn_Ioi_two_inv_log_cube`
* `integral_Ioi_two_inv_log_cube`
-/


open scoped ArithmeticFunction BigOperators Topology
open Filter MeasureTheory

namespace PrimitiveSetsAboveX

/--
The logarithmic antiderivative underlying `tailEstimate` has derivative
`-1 / (t log(ct)^2)`.
-/
lemma hasDerivAt_inv_log_mul {c t : ℝ} (hc : 0 < c) (hct : 1 < c * t) :
    HasDerivAt (fun u => (Real.log (c * u))⁻¹)
      (-(1 / (t * Real.log (c * t) ^ 2))) t := by
  have hmul : HasDerivAt (fun u => c * u) c t := by
    simpa [mul_comm] using (hasDerivAt_id t).const_mul c
  have hlog : HasDerivAt (fun u => Real.log (c * u)) ((c * t)⁻¹ * c) t :=
    (Real.hasDerivAt_log (show c * t ≠ 0 by positivity)).comp t hmul
  have hlog_ne : Real.log (c * t) ≠ 0 :=
    Real.log_ne_zero.mpr ⟨by linarith, by constructor <;> linarith⟩
  convert hlog.inv hlog_ne using 1
  field_simp

/--
Squaring the inverse logarithm gives the exact derivative
`-2 / (t log(ct)^3)`.
-/
lemma hasDerivAt_inv_log_sq_mul {c t : ℝ} (hc : 0 < c) (hct : 1 < c * t) :
    HasDerivAt (fun u => (Real.log (c * u))⁻¹ ^ 2)
      (-(2 / (t * Real.log (c * t) ^ 3))) t := by
  have h := (hasDerivAt_inv_log_mul hc hct).pow 2
  convert h using 1
  ring

/-- The logarithmic kernel `1 / (t log(ct)^2)` is integrable on every admissible tail, and its
integral is exactly `1 / log(cy)`. -/
private lemma integrableOn_Ioi_inv_log_sq_and_integral_eq {c y : ℝ} (hc : 0 < c)
    (hy : 1 < c * y) :
    IntegrableOn (fun t => (1 : ℝ) / (t * Real.log (c * t) ^ 2)) (Set.Ioi y) ∧
      ∫ t in Set.Ioi y, (1 : ℝ) / (t * Real.log (c * t) ^ 2) = (Real.log (c * y))⁻¹ := by
  have hderiv : ∀ x ∈ Set.Ici y, HasDerivAt (fun u => (Real.log (c * u))⁻¹)
      (-(1 / (x * Real.log (c * x) ^ 2))) x := by
    intro x hx
    apply hasDerivAt_inv_log_mul hc
    have hxy : y ≤ x := hx
    have hcx : c * y ≤ c * x := mul_le_mul_of_nonneg_left hxy hc.le
    exact lt_of_lt_of_le hy hcx
  have hlim_log : Tendsto (fun u => Real.log (c * u)) atTop atTop := by
    have hmul : Tendsto (fun u : ℝ => c * u) atTop atTop := by
      simpa [mul_comm] using tendsto_id.const_mul_atTop' hc
    exact Real.tendsto_log_atTop.comp hmul
  have hlim : Tendsto (fun u => (Real.log (c * u))⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp hlim_log
  have hint : IntegrableOn (fun x => -(1 / (x * Real.log (c * x) ^ 2))) (Set.Ioi y) := by
    refine integrableOn_Ioi_deriv_of_nonpos' hderiv ?_ hlim
    intro x hx
    have hxy : y < x := hx
    have hcx : c * y < c * x := mul_lt_mul_of_pos_left hxy hc
    have hx' : 1 < c * x := lt_trans hy hcx
    have hnonneg : 0 ≤ 1 / (x * Real.log (c * x) ^ 2) := by
      have hx0 : 0 < x := by nlinarith [hc, hx']
      have hlog : 0 < Real.log (c * x) := Real.log_pos hx'
      positivity
    linarith
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  refine ⟨?_, ?_⟩
  · simpa [integrableOn_neg_iff] using hint
  · have hneg := congrArg Neg.neg hmain
    simpa [sub_eq_add_neg, integral_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hneg

/-- The logarithmic kernel `1 / (t log(ct)^2)` is integrable on every admissible tail. -/
lemma integrableOn_Ioi_inv_log_sq {c y : ℝ} (hc : 0 < c) (hy : 1 < c * y) :
    IntegrableOn (fun t => (1 : ℝ) / (t * Real.log (c * t) ^ 2)) (Set.Ioi y) :=
  (integrableOn_Ioi_inv_log_sq_and_integral_eq hc hy).1

/-- The integral of `1 / (t log(ct)^2)` over a tail is exactly `1 / log(cy)`. -/
lemma integral_Ioi_inv_log_sq {c y : ℝ} (hc : 0 < c) (hy : 1 < c * y) :
    ∫ t in Set.Ioi y, (1 : ℝ) / (t * Real.log (c * t) ^ 2) = (Real.log (c * y))⁻¹ :=
  (integrableOn_Ioi_inv_log_sq_and_integral_eq hc hy).2

/-- The cubic logarithmic kernel `2 / (t log(ct)^3)` is integrable on every admissible tail, and
its integral equals the square of the inverse logarithm. -/
private lemma integrableOn_Ioi_two_inv_log_cube_and_integral_eq {c y : ℝ} (hc : 0 < c)
    (hy : 1 < c * y) :
    IntegrableOn (fun t => 2 / (t * Real.log (c * t) ^ 3)) (Set.Ioi y) ∧
      ∫ t in Set.Ioi y, 2 / (t * Real.log (c * t) ^ 3) = (Real.log (c * y))⁻¹ ^ 2 := by
  have hderiv : ∀ x ∈ Set.Ici y, HasDerivAt (fun u => (Real.log (c * u))⁻¹ ^ 2)
      (-(2 / (x * Real.log (c * x) ^ 3))) x := by
    intro x hx
    apply hasDerivAt_inv_log_sq_mul hc
    have hxy : y ≤ x := hx
    have hcx : c * y ≤ c * x := mul_le_mul_of_nonneg_left hxy hc.le
    exact lt_of_lt_of_le hy hcx
  have hlim_log : Tendsto (fun u => Real.log (c * u)) atTop atTop := by
    have hmul : Tendsto (fun u : ℝ => c * u) atTop atTop := by
      simpa [mul_comm] using tendsto_id.const_mul_atTop' hc
    exact Real.tendsto_log_atTop.comp hmul
  have hlim : Tendsto (fun u => (Real.log (c * u))⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hlim_log).pow 2
  have hint : IntegrableOn (fun x => -(2 / (x * Real.log (c * x) ^ 3))) (Set.Ioi y) := by
    refine integrableOn_Ioi_deriv_of_nonpos' hderiv ?_ hlim
    intro x hx
    have hxy : y < x := hx
    have hcx : c * y < c * x := mul_lt_mul_of_pos_left hxy hc
    have hx' : 1 < c * x := lt_trans hy hcx
    have hnonneg : 0 ≤ 2 / (x * Real.log (c * x) ^ 3) := by
      have hx0 : 0 < x := by nlinarith [hc, hx']
      have hlog : 0 < Real.log (c * x) := Real.log_pos hx'
      positivity
    linarith
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  refine ⟨?_, ?_⟩
  · simpa [integrableOn_neg_iff] using hint
  · have hneg := congrArg Neg.neg hmain
    simpa [sub_eq_add_neg, integral_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hneg

/-- The cubic logarithmic kernel `2 / (t log(ct)^3)` is integrable on every admissible tail. -/
lemma integrableOn_Ioi_two_inv_log_cube {c y : ℝ} (hc : 0 < c) (hy : 1 < c * y) :
    IntegrableOn (fun t => 2 / (t * Real.log (c * t) ^ 3)) (Set.Ioi y) :=
  (integrableOn_Ioi_two_inv_log_cube_and_integral_eq hc hy).1

/-- The integral of `2 / (t log(ct)^3)` over a tail equals the square of the inverse logarithm. -/
lemma integral_Ioi_two_inv_log_cube {c y : ℝ} (hc : 0 < c) (hy : 1 < c * y) :
    ∫ t in Set.Ioi y, 2 / (t * Real.log (c * t) ^ 3) = (Real.log (c * y))⁻¹ ^ 2 :=
  (integrableOn_Ioi_two_inv_log_cube_and_integral_eq hc hy).2

end PrimitiveSetsAboveX



/-!
# Tail estimates for primitive sets above `x`

This file proves the logarithmic tail estimate used later in the Markov-chain arguments.
It combines the arithmetic input from `PrimitiveSetsAboveX.PreliminariesMertens`,
Abel summation, and explicit calculus on the model kernel `1 / log (mt)^2`.
The arithmetic input for the Mertens partial sums lives in
`PrimitiveSetsAboveX.PreliminariesMertens`.

## Main statements

* `tailEstimate`
-/


open scoped ArithmeticFunction BigOperators Topology
open Filter MeasureTheory

namespace PrimitiveSetsAboveX

/-- The kernel `t ↦ 1 / log (m t)^2` that appears in the tail estimate. -/
private noncomputable def tailKernel (m : ℕ) (t : ℝ) : ℝ :=
  (Real.log ((m : ℝ) * t) ^ 2)⁻¹

/-- The truncated coefficients used to start Abel summation at `y`. -/
private noncomputable def tailCutoffCoeff (y q : ℕ) : ℝ :=
  if y ≤ q then Λ q / (q : ℝ) else 0

/-- The `0`-term in `mertensPartialSum` vanishes, so the same sum may start at `0`. -/
private lemma mertensPartialSum_eq_sum_Icc_zero (n : ℕ) :
    mertensPartialSum n = (Finset.Icc 0 n).sum (fun q => Λ q / (q : ℝ)) := by
  have hI : Finset.Ioc 0 n = Finset.Icc 1 n := by
    rfl
  rw [mertensPartialSum, ← Finset.add_sum_Ioc_eq_sum_Icc
    (f := fun q => Λ q / (q : ℝ)) (Nat.zero_le n)]
  simp [hI]

/-- The cutoff coefficients sum to a difference of Mertens partial sums. -/
private lemma tailCutoffCoeff_partialSum {y n : ℕ} (hy0 : 1 ≤ y) (hy : y ≤ n) :
    (Finset.Icc 0 n).sum (tailCutoffCoeff y) =
      mertensPartialSum n - mertensPartialSum (y - 1) := by
  have hfilter :
      (Finset.Icc 0 n).filter (fun q => y ≤ q) = Finset.Icc y n := by
    ext q
    simp
    omega
  have hunion : Finset.Icc 0 n = Finset.Icc 0 (y - 1) ∪ Finset.Icc y n := by
    ext q
    simp
    omega
  have hdisj : Disjoint (Finset.Icc 0 (y - 1)) (Finset.Icc y n) := by
    refine Finset.disjoint_left.mpr ?_
    intro q hq0 hqy
    rcases Finset.mem_Icc.mp hq0 with ⟨_, hq0u⟩
    rcases Finset.mem_Icc.mp hqy with ⟨hqyl, _⟩
    omega
  calc
    (Finset.Icc 0 n).sum (tailCutoffCoeff y)
        = ((Finset.Icc 0 n).filter (fun q => y ≤ q)).sum (fun q => Λ q / (q : ℝ)) := by
            simpa [tailCutoffCoeff] using
              (Finset.sum_filter (s := Finset.Icc 0 n) (p := fun q => y ≤ q)
                (f := fun q => Λ q / (q : ℝ))).symm
    _ = (Finset.Icc y n).sum (fun q => Λ q / (q : ℝ)) := by rw [hfilter]
    _ = (Finset.Icc 0 n).sum (fun q => Λ q / (q : ℝ)) -
          (Finset.Icc 0 (y - 1)).sum (fun q => Λ q / (q : ℝ)) := by
            rw [hunion, Finset.sum_union hdisj]
            ring
    _ = mertensPartialSum n - mertensPartialSum (y - 1) := by
          rw [← mertensPartialSum_eq_sum_Icc_zero, ← mertensPartialSum_eq_sum_Icc_zero]

/-- The cutoff coefficients vanish before the cutoff point. -/
private lemma tailCutoffCoeff_partialSum_floor {y : ℕ} {t : ℝ}
    (hy : 2 ≤ y) (ht : (y : ℝ) ≤ t) :
    (Finset.Icc 0 ⌊t⌋₊).sum (tailCutoffCoeff y) =
      mertensPartialSum ⌊t⌋₊ - mertensPartialSum (y - 1) := by
  refine tailCutoffCoeff_partialSum (by omega) ?_
  exact Nat.le_floor ht

/-- The cutoff coefficients are zero at `0`. -/
private lemma tailCutoffCoeff_zero (y : ℕ) : tailCutoffCoeff y 0 = 0 := by
  by_cases hy : y ≤ 0
  · simp [tailCutoffCoeff, hy]
  · simp [tailCutoffCoeff, hy]

/-- The cutoff coefficients are zero at `1` once `y ≥ 2`. -/
private lemma tailCutoffCoeff_one {y : ℕ} (hy : 2 ≤ y) : tailCutoffCoeff y 1 = 0 := by
  have hy1 : ¬ y ≤ 1 := by omega
  simp [tailCutoffCoeff, hy1]

/-- The kernel is differentiable on the domain relevant to the tail estimate. -/
private lemma hasDerivAt_tailKernel {m : ℕ} {t : ℝ} (hmt : 1 < (m : ℝ) * t) :
    HasDerivAt (tailKernel m) (-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) t := by
  have hm : 0 < (m : ℝ) := by
    by_contra hm
    have hm0 : (m : ℝ) = 0 := by linarith
    rw [hm0, zero_mul] at hmt
    linarith
  convert hasDerivAt_inv_log_sq_mul (c := (m : ℝ)) (t := t) hm hmt using 1
  · funext u
    rw [tailKernel]
    exact (inv_pow (Real.log ((m : ℝ) * u)) 2).symm
  · ring_nf

/-- The derivative formula for the tail kernel. -/
private lemma deriv_tailKernel {m : ℕ} {t : ℝ} (hmt : 1 < (m : ℝ) * t) :
    deriv (tailKernel m) t = -2 / (t * Real.log ((m : ℝ) * t) ^ 3) :=
  (hasDerivAt_tailKernel hmt).deriv

/-- The explicit derivative factor for `tailKernel` is continuous on admissible closed tails. -/
private lemma continuousOn_tailKernelDerivFactor_Ici {m y : ℕ} (hm : 1 ≤ m) (hy : 2 ≤ y) :
    ContinuousOn
      (fun t : ℝ => -2 / (t * Real.log ((m : ℝ) * t) ^ 3))
      (Set.Ici (y : ℝ)) := by
  intro t ht
  have ht_pos : 0 < t := by
    have hy0 : (0 : ℝ) < y := by positivity
    exact lt_of_lt_of_le hy0 ht
  have hmt : 1 < (m : ℝ) * t := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hy1 : (1 : ℝ) < y := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hy)
    have ht1 : 1 < t := lt_of_lt_of_le hy1 ht
    nlinarith
  have hlog_ne : Real.log ((m : ℝ) * t) ≠ 0 := (Real.log_pos hmt).ne'
  refine ContinuousWithinAt.div ?_ ?_ ?_
  · exact continuousWithinAt_const.neg
  · have hmul : ContinuousWithinAt (fun x : ℝ => (m : ℝ) * x) (Set.Ici (y : ℝ)) t := by
      simpa [mul_comm] using continuousWithinAt_id.const_mul (m : ℝ)
    exact continuousWithinAt_id.mul
      ((ContinuousWithinAt.log hmul
        (mul_ne_zero
          (by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm)))
          ht_pos.ne')).pow 3)
  · exact mul_ne_zero ht_pos.ne' (pow_ne_zero 3 hlog_ne)

/-- The tail kernel is nonnegative. -/
private lemma tailKernel_nonneg (m : ℕ) (t : ℝ) : 0 ≤ tailKernel m t := by
  unfold tailKernel
  positivity

/-- The floor/log discrepancy on a unit interval is bounded by `log 2`. -/
private lemma abs_log_floor_sub_log_le_log_two {t : ℝ} (ht : 2 ≤ t) :
    |Real.log ((⌊t⌋₊ : ℕ) : ℝ) - Real.log t| ≤ Real.log 2 := by
  have hfloor_pos : 0 < ((⌊t⌋₊ : ℕ) : ℝ) := by
    have hfloor_one : (1 : ℝ) < ((⌊t⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le one_lt_two (Nat.le_floor ht)
    linarith
  have ht_pos : 0 < t := by linarith
  have hfloor_le : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht_pos.le
  have htwo : t ≤ ((⌊t⌋₊ : ℕ) : ℝ) * 2 := by
    have hlt : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
    grind only
  have hsub_nonneg : 0 ≤ Real.log t - Real.log ((⌊t⌋₊ : ℕ) : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log hfloor_pos hfloor_le)
  have habs : Real.log ((⌊t⌋₊ : ℕ) : ℝ) - Real.log t ≤ 0 := by linarith
  rw [abs_of_nonpos habs, neg_sub, ← Real.log_div
    (show t ≠ 0 by linarith) (show (((⌊t⌋₊ : ℕ) : ℝ) ≠ 0) by positivity)]
  have hratio_pos : 0 < t / (((⌊t⌋₊ : ℕ) : ℝ)) := by positivity
  refine Real.log_le_log hratio_pos ?_
  exact (div_le_iff₀' hfloor_pos).mpr htwo

/-- The cutoff partial sums vanish below the cutoff. -/
private lemma tailCutoffCoeff_partialSum_eq_zero_of_lt {y : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t < y) :
    (Finset.Icc 0 ⌊t⌋₊).sum (tailCutoffCoeff y) = 0 := by
  have hfloor : ⌊t⌋₊ < y := (Nat.floor_lt ht0).2 ht
  refine Finset.sum_eq_zero ?_
  intro q hq
  have hqle : q ≤ ⌊t⌋₊ := (Finset.mem_Icc.mp hq).2
  have hyq : ¬ y ≤ q := by omega
  simp [tailCutoffCoeff, hyq]

/-- Abel summation for the finite truncations of the tail sum. -/
private lemma tailPartialSum_abel {m y n : ℕ} (hm : 1 ≤ m) (hy : 2 ≤ y) (hyn : y ≤ n) :
    (Finset.Icc 0 n).sum (fun q => tailKernel m q * tailCutoffCoeff y q) =
      tailKernel m n * (mertensPartialSum n - mertensPartialSum (y - 1)) -
        ∫ t in (y : ℝ)..n, deriv (tailKernel m) t *
          (mertensPartialSum ⌊t⌋₊ - mertensPartialSum (y - 1)) := by
  have hmn : (2 : ℝ) ≤ n := by exact_mod_cast (le_trans hy hyn)
  have hmy : (y : ℝ) ≤ n := by exact_mod_cast hyn
  have hmt : ∀ {t : ℝ}, t ∈ Set.Icc (2 : ℝ) n → 1 < (m : ℝ) * t := by
    intro t ht
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [ht.1, hm']
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) n, DifferentiableAt ℝ (tailKernel m) t := by
    intro t ht
    exact (hasDerivAt_tailKernel (hmt ht)).differentiableAt
  have hcont :
      ContinuousOn (fun t : ℝ => -2 / (t * Real.log ((m : ℝ) * t) ^ 3))
        (Set.Icc (2 : ℝ) n) := by
    exact (continuousOn_tailKernelDerivFactor_Ici hm (by decide : 2 ≤ 2)).mono
      Set.Icc_subset_Ici_self
  have hcontDeriv : ContinuousOn (deriv (tailKernel m)) (Set.Icc (2 : ℝ) n) := by
    refine ContinuousOn.congr hcont ?_
    intro t ht
    rw [deriv_tailKernel (hmt ht)]
  have hint : MeasureTheory.IntegrableOn (deriv (tailKernel m)) (Set.Icc (2 : ℝ) n) :=
    ContinuousOn.integrableOn_Icc hcontDeriv
  have habel0 := sum_mul_eq_sub_integral_mul₁ (c := tailCutoffCoeff y) (f := tailKernel m)
    (tailCutoffCoeff_zero y) (tailCutoffCoeff_one hy) n hdiff hint
  rw [← intervalIntegral.integral_of_le hmn] at habel0
  have habel := by simpa [Nat.floor_natCast] using habel0
  have hprod_int : MeasureTheory.IntegrableOn
      (fun t => deriv (tailKernel m) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tailCutoffCoeff y k)
      (Set.Icc (2 : ℝ) n) :=
    integrableOn_mul_sum_Icc (c := tailCutoffCoeff y) (m := 0) (a := (2 : ℝ))
      (b := n) (ha := by norm_num) hint
  have hprod_2y : IntervalIntegrable
      (fun t => deriv (tailKernel m) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tailCutoffCoeff y k)
      MeasureTheory.volume (2 : ℝ) y := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (show (2 : ℝ) ≤ y by exact_mod_cast hy)]
    exact hprod_int.mono_set (Set.Icc_subset_Icc_right hmy)
  have hprod_yn : IntervalIntegrable
      (fun t => deriv (tailKernel m) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tailCutoffCoeff y k)
      MeasureTheory.volume (y : ℝ) n := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hmy]
    exact hprod_int.mono_set (Set.Icc_subset_Icc_left (show (2 : ℝ) ≤ y by exact_mod_cast hy))
  rw [← intervalIntegral.integral_add_adjacent_intervals hprod_2y hprod_yn] at habel
  have hzero :
      ∫ t in (2 : ℝ)..y, deriv (tailKernel m) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tailCutoffCoeff y k =
        0 := by
    rw [intervalIntegral.integral_congr_ae (μ := MeasureTheory.volume)
      (g := fun _ => (0 : ℝ))]
    · simp
    · filter_upwards
        [MeasureTheory.Ioo_ae_eq_Ioc (μ := MeasureTheory.volume) (a := (2 : ℝ)) (b := y)]
        with t hEq ht
      have htIoc : t ∈ Set.Ioc (2 : ℝ) y := by
        simpa [Set.uIoc_of_le (show (2 : ℝ) ≤ y by exact_mod_cast hy)] using ht
      have hmem : t ∈ Set.Ioo (2 : ℝ) y := hEq.symm.mp htIoc
      rw [tailCutoffCoeff_partialSum_eq_zero_of_lt (by linarith [hmem.1.le]) hmem.2, mul_zero]
  have hyrewrite :
      ∫ t in (y : ℝ)..n, deriv (tailKernel m) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tailCutoffCoeff y k =
        ∫ t in (y : ℝ)..n, deriv (tailKernel m) t *
          (mertensPartialSum ⌊t⌋₊ - mertensPartialSum (y - 1)) := by
    rw [intervalIntegral.integral_congr_ae (μ := MeasureTheory.volume)]
    exact Filter.Eventually.of_forall fun t ht => by
      have hmem : t ∈ Set.Ioc (y : ℝ) n := by
        simpa [Set.uIoc_of_le hmy] using ht
      rw [tailCutoffCoeff_partialSum_floor hy hmem.1.le]
  rw [tailCutoffCoeff_partialSum (by omega) hyn, hzero, hyrewrite] at habel
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using habel

/-- The Mertens error at `⌊t⌋` differs from the continuous `log t` error by at most `log 2`. -/
private lemma abs_mertensPartialSum_floor_sub_log_le {C : ℝ} {t : ℝ}
    (hC : ∀ ⦃u : ℕ⦄, 2 ≤ u →
      |mertensPartialSum u - Real.log (u : ℝ)| ≤ C)
    (ht : 2 ≤ t) :
    |mertensPartialSum ⌊t⌋₊ - Real.log t| ≤ C + Real.log 2 := by
  have hfloor : 2 ≤ ⌊t⌋₊ := Nat.le_floor ht
  calc
    |mertensPartialSum ⌊t⌋₊ - Real.log t|
      ≤ |mertensPartialSum ⌊t⌋₊ - Real.log ((⌊t⌋₊ : ℕ) : ℝ)| +
          |Real.log ((⌊t⌋₊ : ℕ) : ℝ) - Real.log t| := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              abs_sub_le (mertensPartialSum ⌊t⌋₊) (Real.log ((⌊t⌋₊ : ℕ) : ℝ)) (Real.log t)
    _ ≤ C + Real.log 2 := add_le_add (hC hfloor) (abs_log_floor_sub_log_le_log_two ht)

/-- Consecutive logarithms differ by at most `log 2` once the index is at least `2`. -/
private lemma abs_log_natPred_sub_log_le_log_two {y : ℕ} (hy : 2 ≤ y) :
    |Real.log ((y - 1 : ℕ) : ℝ) - Real.log (y : ℝ)| ≤ Real.log 2 := by
  by_cases hy2 : y = 2
  · subst hy2
    have hlog2_nonneg : 0 ≤ Real.log 2 := by positivity
    simp [abs_of_nonneg hlog2_nonneg]
  · have hy3 : 3 ≤ y := by omega
    have hpred_pos_nat : 0 < y - 1 := by omega
    have hpred_pos : 0 < ((y - 1 : ℕ) : ℝ) := by exact_mod_cast hpred_pos_nat
    have hy_pos : 0 < (y : ℝ) := by positivity
    have hy_le : ((y - 1 : ℕ) : ℝ) ≤ y := by
      exact_mod_cast Nat.sub_le y 1
    have hratio : (y : ℝ) / ((y - 1 : ℕ) : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hpred_pos]
      have hmul : y ≤ 2 * (y - 1) := by omega
      exact_mod_cast hmul
    have hlog_ratio :
        Real.log ((y : ℝ) / ((y - 1 : ℕ) : ℝ)) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) hratio
    have hlog_le : Real.log (y : ℝ) - Real.log ((y - 1 : ℕ) : ℝ) ≤ Real.log 2 := by
      rwa [Real.log_div (show (y : ℝ) ≠ 0 by positivity)
        (show (((y - 1 : ℕ) : ℝ) ≠ 0) by positivity), sub_eq_add_neg] at hlog_ratio
    have hneg : Real.log ((y - 1 : ℕ) : ℝ) - Real.log (y : ℝ) ≤ 0 := by
      exact sub_nonpos.mpr (Real.log_le_log hpred_pos hy_le)
    rw [abs_of_nonpos hneg, neg_sub]
    exact hlog_le

/-- The predecessor cutoff carries the same uniform Mertens error up to `log 2`. -/
private lemma abs_mertensPartialSum_pred_sub_log_le {C : ℝ}
    (hC : ∀ ⦃u : ℕ⦄, 2 ≤ u →
      |mertensPartialSum u - Real.log (u : ℝ)| ≤ C)
    {y : ℕ} (hy : 2 ≤ y) :
    |mertensPartialSum (y - 1) - Real.log (y : ℝ)| ≤ C + Real.log 2 := by
  by_cases hy2 : y = 2
  · subst hy2
    have hCnonneg : 0 ≤ C := by
      have h₂ := hC (u := 2) (by decide : 2 ≤ 2)
      exact le_trans (abs_nonneg (mertensPartialSum 2 - Real.log (2 : ℝ))) h₂
    have hlog2_pos : 0 < Real.log 2 := by positivity
    have hlog2_nonneg : 0 ≤ Real.log 2 := by positivity
    have h₁ : mertensPartialSum 1 = 0 := by
      simp [mertensPartialSum]
    rw [show (2 - 1 : ℕ) = 1 by decide, h₁, zero_sub]
    norm_num
    rw [abs_of_nonneg hlog2_nonneg]
    linarith
  · have hpred : 2 ≤ y - 1 := by omega
    calc
      |mertensPartialSum (y - 1) - Real.log (y : ℝ)|
        ≤ |mertensPartialSum (y - 1) - Real.log ((y - 1 : ℕ) : ℝ)| +
            |Real.log ((y - 1 : ℕ) : ℝ) - Real.log (y : ℝ)| := by
              exact abs_sub_le (mertensPartialSum (y - 1)) (Real.log ↑(y - 1)) (Real.log ↑y)
      _ ≤ C + Real.log 2 := by
            gcongr
            · exact hC hpred
            · exact abs_log_natPred_sub_log_le_log_two hy

/-- The tail kernel decays to `0` along the naturals. -/
private lemma tendsto_tailKernel_nat_zero {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => tailKernel m n) atTop (𝓝 0) := by
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hmul : Tendsto (fun n : ℕ => (m : ℝ) * n) atTop atTop := by
    simpa [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop hm_pos
  have hlog : Tendsto (fun n : ℕ => Real.log ((m : ℝ) * n)) atTop atTop := by
    exact Real.tendsto_log_atTop.comp hmul
  have hinv : Tendsto (fun n : ℕ => (Real.log ((m : ℝ) * n))⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp hlog
  simpa [tailKernel] using hinv.pow 2

/-- The boundary contribution coming from the continuous Mertens error vanishes at infinity. -/
private lemma tendsto_tailKernel_mul_mertensError_zero {m : ℕ} (hm : 1 ≤ m) {C : ℝ}
    (hC : ∀ ⦃u : ℕ⦄, 2 ≤ u →
      |mertensPartialSum u - Real.log (u : ℝ)| ≤ C) :
    Tendsto
      (fun n : ℕ => tailKernel m n * (mertensPartialSum n - Real.log (n : ℝ)))
      atTop (𝓝 0) := by
  have hkernel : Tendsto (fun n : ℕ => C * tailKernel m n) atTop (𝓝 0) := by
    simpa using (tendsto_tailKernel_nat_zero hm).const_mul C
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        |tailKernel m n * (mertensPartialSum n - Real.log (n : ℝ))| ≤ C * tailKernel m n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hkernel_nonneg : 0 ≤ tailKernel m n := tailKernel_nonneg m n
    rw [abs_mul, abs_of_nonneg hkernel_nonneg]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hC hn) hkernel_nonneg
  have habs :
      Tendsto (fun n : ℕ =>
        |tailKernel m n * (mertensPartialSum n - Real.log (n : ℝ))|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbound hkernel
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa using habs

/-- On the admissible tail `t ≥ y`, the logarithmic difference `log t - log y` is nonnegative and
bounded by `log (m t)`. -/
private lemma log_sub_log_bounds {m y : ℕ} (hm : 1 ≤ m) (hy : 2 ≤ y) {t : ℝ}
    (ht : (y : ℝ) ≤ t) :
    0 ≤ Real.log t - Real.log (y : ℝ) ∧
      Real.log t - Real.log (y : ℝ) ≤ Real.log ((m : ℝ) * t) := by
  have ht_pos : 0 < t := by
    have hy0 : (0 : ℝ) < y := by positivity
    linarith
  have hy_pos : 0 < (y : ℝ) := by positivity
  constructor
  · exact sub_nonneg.mpr <| Real.log_le_log hy_pos ht
  · have hlog_le : Real.log t ≤ Real.log ((m : ℝ) * t) := by
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hle : t ≤ (m : ℝ) * t := by
        have := mul_le_mul_of_nonneg_right hm1 ht_pos.le
        simpa using this
      exact Real.log_le_log ht_pos hle
    have : Real.log t - Real.log (y : ℝ) ≤ Real.log t := by
      have hy1 : (1 : ℝ) ≤ y := by
        exact_mod_cast (le_trans (by decide : 1 ≤ 2) hy)
      linarith [Real.log_nonneg hy1]
    exact le_trans this hlog_le

/-- The logarithmic boundary term vanishes along the real tail. -/
private lemma tendsto_tailKernel_mul_log_sub_log_zero_aux {m y : ℕ} (hm : 1 ≤ m) (hy : 2 ≤ y) :
    Tendsto (fun t : ℝ => tailKernel m t * (Real.log t - Real.log (y : ℝ))) atTop (𝓝 0) := by
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hmul : Tendsto (fun t : ℝ => (m : ℝ) * t) atTop atTop := by
    simpa [mul_comm] using tendsto_id.const_mul_atTop' hm_pos
  have hlog : Tendsto (fun t : ℝ => Real.log ((m : ℝ) * t)) atTop atTop :=
    Real.tendsto_log_atTop.comp hmul
  have hinv : Tendsto (fun t : ℝ => (Real.log ((m : ℝ) * t))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hbound :
      ∀ᶠ t : ℝ in atTop,
        |tailKernel m t * (Real.log t - Real.log (y : ℝ))| ≤
          (Real.log ((m : ℝ) * t))⁻¹ := by
    filter_upwards [eventually_ge_atTop (max y 2 : ℝ)] with t ht
    have hty : (y : ℝ) ≤ t := le_trans (by exact_mod_cast le_max_left y 2) ht
    have ht2 : (2 : ℝ) ≤ t := le_trans (by exact_mod_cast le_max_right y 2) ht
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmt : 1 < (m : ℝ) * t := by
      nlinarith
    have hkernel_nonneg : 0 ≤ tailKernel m t := tailKernel_nonneg m t
    have hdiff := log_sub_log_bounds hm hy hty
    have hdiff_nonneg : 0 ≤ Real.log t - Real.log (y : ℝ) := hdiff.1
    have hdiff_le : Real.log t - Real.log (y : ℝ) ≤ Real.log ((m : ℝ) * t) := hdiff.2
    rw [abs_of_nonneg (mul_nonneg hkernel_nonneg hdiff_nonneg)]
    calc
      tailKernel m t * (Real.log t - Real.log (y : ℝ))
        ≤ tailKernel m t * Real.log ((m : ℝ) * t) := by
            exact mul_le_mul_of_nonneg_left hdiff_le hkernel_nonneg
      _ = (Real.log ((m : ℝ) * t))⁻¹ := by
            have hlog_ne : Real.log ((m : ℝ) * t) ≠ 0 := by
              exact Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hmt)
            unfold tailKernel
            field_simp [hlog_ne]
  have habs :
      Tendsto (fun t : ℝ =>
        |tailKernel m t * (Real.log t - Real.log (y : ℝ))|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbound hinv
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa using habs

/-- The full boundary term in Abel summation vanishes at infinity. -/
private lemma tendsto_tailKernel_mul_mertensTail_zero {m y : ℕ} (hm : 1 ≤ m) (hy : 2 ≤ y)
    {C : ℝ} (hC : ∀ ⦃u : ℕ⦄, 2 ≤ u →
      |mertensPartialSum u - Real.log (u : ℝ)| ≤ C) :
    Tendsto (fun n : ℕ => tailKernel m n * (mertensPartialSum n - mertensPartialSum (y - 1)))
      atTop (𝓝 0) := by
  have h₁ := tendsto_tailKernel_mul_mertensError_zero hm hC
  have h₂ :
      Tendsto (fun n : ℕ => tailKernel m n * (Real.log (n : ℝ) - Real.log (y : ℝ)))
        atTop (𝓝 0) := by
    simpa using (tendsto_tailKernel_mul_log_sub_log_zero_aux hm hy).comp tendsto_natCast_atTop_atTop
  have h₃ : Tendsto (fun n : ℕ => tailKernel m n * (Real.log (y : ℝ) - mertensPartialSum (y - 1)))
      atTop (𝓝 0) := by
    simpa [mul_comm] using (tendsto_tailKernel_nat_zero hm).const_mul
      (Real.log (y : ℝ) - mertensPartialSum (y - 1))
  simpa using (((h₁.add h₂).add h₃).congr' <| by
    filter_upwards with n
    ring)

/-- On the admissible tail, the logarithm in the kernel is always positive. -/
private lemma one_lt_mul_of_mem_Ioi {m y : ℕ} (hm : 1 ≤ m) (hy : 2 ≤ y) {t : ℝ}
    (ht : t ∈ Set.Ioi (y : ℝ)) :
    1 < (m : ℝ) * t := by
  have hy1 : (1 : ℝ) < y := by
    exact_mod_cast lt_of_lt_of_le one_lt_two hy
  have ht1 : 1 < t := lt_trans hy1 ht
  have hm1 : (1 : ℝ) ≤ m := by
    exact_mod_cast hm
  exact one_lt_mul hm1 ht1

/-- Points in the admissible tail are positive. -/
private lemma zero_lt_of_mem_Ioi {y : ℕ} (hy : 2 ≤ y) {t : ℝ} (ht : t ∈ Set.Ioi (y : ℝ)) :
    0 < t := by
  have hy0 : (0 : ℝ) < y := by positivity
  exact lt_trans hy0 ht

/-- The Abel-summation error after subtracting the logarithmic main term is uniformly bounded. -/
private lemma abs_mertensTail_floor_error_le {C : ℝ}
    (hC : ∀ ⦃u : ℕ⦄, 2 ≤ u →
      |mertensPartialSum u - Real.log (u : ℝ)| ≤ C)
    {y : ℕ} (hy : 2 ≤ y) {t : ℝ} (ht : (y : ℝ) ≤ t) :
    |(mertensPartialSum ⌊t⌋₊ - mertensPartialSum (y - 1)) -
        (Real.log t - Real.log (y : ℝ))| ≤ 2 * (C + Real.log 2) := by
  have ht2 : 2 ≤ t :=
    le_trans (by exact_mod_cast hy) ht
  have hfloor := abs_mertensPartialSum_floor_sub_log_le hC ht2
  have hpred := abs_mertensPartialSum_pred_sub_log_le hC hy
  calc
    |(mertensPartialSum ⌊t⌋₊ - mertensPartialSum (y - 1)) -
        (Real.log t - Real.log (y : ℝ))|
      = |(mertensPartialSum ⌊t⌋₊ - Real.log t) -
          (mertensPartialSum (y - 1) - Real.log (y : ℝ))| := by ring_nf
    _ ≤ |mertensPartialSum ⌊t⌋₊ - Real.log t| +
          |mertensPartialSum (y - 1) - Real.log (y : ℝ)| :=
            abs_sub (mertensPartialSum ⌊t⌋₊ - Real.log t)
                  (mertensPartialSum (y - 1) - Real.log ↑y)
    _ ≤ 2 * (C + Real.log 2) := by
          linarith

/--
The explicit derivative factor in the tail kernel is strongly measurable on the admissible tail.
-/
private lemma aestronglyMeasurable_tailKernelDerivFactor {m y : ℕ}
    (hm : 1 ≤ m) (hy : 2 ≤ y) :
    AEStronglyMeasurable
      (fun t : ℝ => -2 / (t * Real.log ((m : ℝ) * t) ^ 3))
      (MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))) := by
  have hcont :
      ContinuousOn
        (fun t : ℝ => -2 / (t * Real.log ((m : ℝ) * t) ^ 3))
        (Set.Ioi (y : ℝ)) :=
    (continuousOn_tailKernelDerivFactor_Ici hm hy).mono Set.Ioi_subset_Ici_self
  exact hcont.aestronglyMeasurable measurableSet_Ioi

/-- The logarithmic main-term integrand is integrable on the tail. -/
private lemma integrableOn_Ioi_deriv_tailKernel_mul_log_sub_log {m y : ℕ}
    (hm : 1 ≤ m) (hy : 2 ≤ y) :
    IntegrableOn
      (fun t => deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ)))
      (Set.Ioi (y : ℝ)) := by
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hmy : 1 < (m : ℝ) * y := by
    have hmy_nat : 2 ≤ m * y := by
      have := Nat.mul_le_mul hm hy
      simpa using this
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hmy_nat)
  have hdom :
      (fun t => deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ))) =ᵐ[
        MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))]
      (fun t =>
        (-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * (Real.log t - Real.log (y : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hmt : 1 < (m : ℝ) * t := one_lt_mul_of_mem_Ioi hm hy ht
    rw [deriv_tailKernel hmt]
  have hmajor :
      IntegrableOn (fun t : ℝ => 2 / (t * Real.log ((m : ℝ) * t) ^ 2)) (Set.Ioi (y : ℝ)) := by
    simpa [two_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (integrableOn_Ioi_inv_log_sq hm_pos hmy).const_mul (2 : ℝ)
  have hmeas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          (-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * (Real.log t - Real.log (y : ℝ)))
        (MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))) := by
    refine (aestronglyMeasurable_tailKernelDerivFactor hm hy).mul ?_
    refine (show ContinuousOn
      (fun t : ℝ => Real.log t - Real.log (y : ℝ))
      (Set.Ioi (y : ℝ)) from ?_).aestronglyMeasurable measurableSet_Ioi
    intro t ht
    exact ((Real.continuousAt_log (zero_lt_of_mem_Ioi hy ht).ne').sub
      continuousAt_const).continuousWithinAt
  have hbound :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))),
        ‖(-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * (Real.log t - Real.log (y : ℝ))‖ ≤
          2 / (t * Real.log ((m : ℝ) * t) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := zero_lt_of_mem_Ioi hy ht
    have hmt : 1 < (m : ℝ) * t := one_lt_mul_of_mem_Ioi hm hy ht
    have hlog_pos : 0 < Real.log ((m : ℝ) * t) := Real.log_pos hmt
    have hdiff := log_sub_log_bounds hm hy ht.le
    have hdiff_nonneg : 0 ≤ Real.log t - Real.log (y : ℝ) := hdiff.1
    have hdiff_le : Real.log t - Real.log (y : ℝ) ≤ Real.log ((m : ℝ) * t) := hdiff.2
    have hfactor_nonneg : 0 ≤ 2 / (t * Real.log ((m : ℝ) * t) ^ 3) := by
      positivity
    calc
      ‖(-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * (Real.log t - Real.log (y : ℝ))‖
        = (2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * (Real.log t - Real.log (y : ℝ)) := by
            have habs_factor :
                |(-2 / (t * Real.log ((m : ℝ) * t) ^ 3))| =
                  2 / (t * Real.log ((m : ℝ) * t) ^ 3) := by
              have hneg :
                  -2 / (t * Real.log ((m : ℝ) * t) ^ 3) =
                    -(2 / (t * Real.log ((m : ℝ) * t) ^ 3)) := by ring
              rw [hneg, abs_neg, abs_of_nonneg hfactor_nonneg]
            rw [Real.norm_eq_abs, abs_mul, habs_factor, abs_of_nonneg hdiff_nonneg]
      _ ≤ (2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * Real.log ((m : ℝ) * t) :=
            mul_le_mul_of_nonneg_left hdiff_le hfactor_nonneg
      _ = 2 / (t * Real.log ((m : ℝ) * t) ^ 2) := by
            have ht_ne : t ≠ 0 := ht_pos.ne'
            have hlog_ne : Real.log ((m : ℝ) * t) ≠ 0 := hlog_pos.ne'
            field_simp [ht_ne, hlog_ne]
  rw [IntegrableOn]
  refine (Integrable.mono' hmajor hmeas hbound).congr hdom.symm

/-- The logarithmic main term is exactly `1 / log (my)`. -/
private lemma integral_tailKernel_mainTerm {m y : ℕ} (hm : 1 ≤ m) (hy : 2 ≤ y) :
    -∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ)) =
      1 / Real.log ((m * y : ℕ) : ℝ) := by
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hmy : 1 < (m : ℝ) * y := by
    have hmy_nat : 2 ≤ m * y := by
      have := Nat.mul_le_mul hm hy
      simpa using this
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hmy_nat)
  have hu :
      ∀ x ∈ Set.Ioi (y : ℝ),
        HasDerivAt (tailKernel m) (-2 / (x * Real.log ((m : ℝ) * x) ^ 3)) x := by
    intro x hx
    exact hasDerivAt_tailKernel (one_lt_mul_of_mem_Ioi hm hy hx)
  have hv :
      ∀ x ∈ Set.Ioi (y : ℝ),
        HasDerivAt (fun t : ℝ => Real.log t - Real.log (y : ℝ)) (1 / x) x := by
    intro x hx
    convert (Real.hasDerivAt_log (show x ≠ 0 by exact (zero_lt_of_mem_Ioi hy hx).ne')).sub_const
      (Real.log (y : ℝ)) using 1
    field_simp
  have huv' :
      IntegrableOn
        ((tailKernel m) * fun t : ℝ => 1 / t)
        (Set.Ioi (y : ℝ)) := by
    simpa [tailKernel, Pi.mul_def, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      integrableOn_Ioi_inv_log_sq hm_pos hmy
  have hu'v :
      IntegrableOn
        ((fun x : ℝ => -2 / (x * Real.log ((m : ℝ) * x) ^ 3)) *
          fun t : ℝ => Real.log t - Real.log (y : ℝ))
        (Set.Ioi (y : ℝ)) := by
    refine (integrableOn_Ioi_deriv_tailKernel_mul_log_sub_log hm hy).congr_fun_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Pi.mul_apply, deriv_tailKernel (one_lt_mul_of_mem_Ioi hm hy ht)]
  have h_zero :
      Tendsto
        ((tailKernel m) * fun t : ℝ => Real.log t - Real.log (y : ℝ))
        (𝓝[>] (y : ℝ)) (𝓝 0) := by
    have hy_pos : 0 < (y : ℝ) := by positivity
    simpa [Pi.mul_def] using
      (tendsto_nhdsWithin_of_tendsto_nhds (hasDerivAt_tailKernel hmy).continuousAt.tendsto).mul
        (tendsto_sub_nhds_zero_iff.mpr <|
          tendsto_nhdsWithin_of_tendsto_nhds (Real.continuousAt_log hy_pos.ne').tendsto)
  have h_inf :
      Tendsto
        ((tailKernel m) * fun t : ℝ => Real.log t - Real.log (y : ℝ))
        atTop (𝓝 0) := by
    simpa [Pi.mul_def] using tendsto_tailKernel_mul_log_sub_log_zero_aux hm hy
  have hparts :
      -∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ)) =
        ∫ t in Set.Ioi (y : ℝ), tailKernel m t * (1 / t) := by
    calc
      -∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ))
        = -∫ t in Set.Ioi (y : ℝ), (-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) *
            (Real.log t - Real.log (y : ℝ)) := by
            refine congrArg Neg.neg ?_
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            rw [deriv_tailKernel (one_lt_mul_of_mem_Ioi hm hy ht)]
      _ = ∫ t in Set.Ioi (y : ℝ), tailKernel m t * (1 / t) := by
            simpa [sub_eq_add_neg, Pi.mul_def] using
              (MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_inf).symm
  have hkernel_eq :
      ∫ t in Set.Ioi (y : ℝ), tailKernel m t * (1 / t) =
        ∫ t in Set.Ioi (y : ℝ), (1 : ℝ) / (t * Real.log ((m : ℝ) * t) ^ 2) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := zero_lt_of_mem_Ioi hy ht
    have hmt : 1 < (m : ℝ) * t := one_lt_mul_of_mem_Ioi hm hy ht
    have hlog_ne : Real.log ((m : ℝ) * t) ≠ 0 := (Real.log_pos hmt).ne'
    unfold tailKernel
    field_simp [ht_pos.ne', hlog_ne]
  calc
    -∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ))
      = ∫ t in Set.Ioi (y : ℝ), tailKernel m t * (1 / t) := hparts
    _ = 1 / Real.log ((m * y : ℕ) : ℝ) := by
          rw [hkernel_eq]
          simpa [Nat.cast_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            integral_Ioi_inv_log_sq hm_pos hmy

/-- The logarithmic tail sum satisfies
`tailSum m y = 1 / log (my) + O(log(my)⁻²)` uniformly for `m ≥ 1` and `y ≥ 2`. -/
lemma tailEstimate :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃m y : ℕ⦄, 1 ≤ m → 2 ≤ y →
        |tailSum m y - 1 / Real.log ((m * y : ℕ) : ℝ)| ≤
          C / (Real.log ((m * y : ℕ) : ℝ)) ^ 2 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := mertensEstimate
  refine ⟨2 * (C₀ + Real.log 2), by positivity, ?_⟩
  intro m y hm hy
  let coeff : ℕ → ℝ := fun q => tailKernel m q * tailCutoffCoeff y q
  let partialS : ℕ → ℝ := fun n => ∑ q ∈ Finset.Icc 0 n, coeff q
  let A : ℝ → ℝ := fun t =>
    deriv (tailKernel m) t * (mertensPartialSum ⌊t⌋₊ - mertensPartialSum (y - 1))
  let E : ℝ → ℝ := fun t =>
    (mertensPartialSum ⌊t⌋₊ - mertensPartialSum (y - 1)) -
      (Real.log t - Real.log (y : ℝ))
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hmy : 1 < (m : ℝ) * y := by
    have hmy_nat : 2 ≤ m * y := by
      have := Nat.mul_le_mul hm hy
      simpa using this
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hmy_nat)
  have hcoeff_nonneg : ∀ q : ℕ, 0 ≤ coeff q := by
    intro q
    by_cases hyq : y ≤ q
    · have hmq_nat : 2 ≤ m * q := by
        have := Nat.mul_le_mul hm hyq
        exact le_trans (by omega) this
      have hmq : 1 < ((m * q : ℕ) : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hmq_nat)
      have hkernel_nonneg : 0 ≤ tailKernel m q := tailKernel_nonneg m q
      have hcutoff_nonneg : 0 ≤ tailCutoffCoeff y q := by
        have hq_pos_nat : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) (le_trans hy hyq)
        have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq_pos_nat
        have hΛ_nonneg : 0 ≤ Λ q := ArithmeticFunction.vonMangoldt_nonneg
        rw [tailCutoffCoeff, if_pos hyq]
        exact div_nonneg hΛ_nonneg hq_pos.le
      exact mul_nonneg hkernel_nonneg hcutoff_nonneg
    · simp [coeff, tailCutoffCoeff, hyq]
  have hAeq :
      A =
        (fun t =>
          deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ)) +
            deriv (tailKernel m) t * E t) := by
    funext t
    simp [A, E]
    ring
  have hEbound :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))),
        |E t| ≤ 2 * (C₀ + Real.log 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact abs_mertensTail_floor_error_le hC₀ hy ht.le
  have hmain_int :
      IntegrableOn
        (fun t => deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ)))
        (Set.Ioi (y : ℝ)) :=
    integrableOn_Ioi_deriv_tailKernel_mul_log_sub_log hm hy
  have hmajor :
      IntegrableOn
        (fun t : ℝ => (2 * (C₀ + Real.log 2)) * (2 / (t * Real.log ((m : ℝ) * t) ^ 3)))
        (Set.Ioi (y : ℝ)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (integrableOn_Ioi_two_inv_log_cube hm_pos hmy).const_mul (2 * (C₀ + Real.log 2))
  have hderivE_dom :
      (fun t => deriv (tailKernel m) t * E t) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))]
        (fun t => (-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * E t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hmt : 1 < (m : ℝ) * t := one_lt_mul_of_mem_Ioi hm hy ht
    rw [deriv_tailKernel hmt]
  have hderivE_bound :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))),
        ‖deriv (tailKernel m) t * E t‖ ≤
          (2 * (C₀ + Real.log 2)) * (2 / (t * Real.log ((m : ℝ) * t) ^ 3)) := by
    filter_upwards [hEbound, ae_restrict_mem measurableSet_Ioi] with t htE ht
    have hmt : 1 < (m : ℝ) * t := one_lt_mul_of_mem_Ioi hm hy ht
    have hfactor_nonneg : 0 ≤ 2 / (t * Real.log ((m : ℝ) * t) ^ 3) := by
      have ht_pos : 0 < t := zero_lt_of_mem_Ioi hy ht
      have hlog_pos : 0 < Real.log ((m : ℝ) * t) := Real.log_pos hmt
      positivity
    calc
      ‖deriv (tailKernel m) t * E t‖
        = ‖(-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * E t‖ := by
            rw [deriv_tailKernel hmt]
      _ = |(-2 / (t * Real.log ((m : ℝ) * t) ^ 3))| * |E t| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤ (2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * (2 * (C₀ + Real.log 2)) := by
            have hneg :
                -2 / (t * Real.log ((m : ℝ) * t) ^ 3) =
                  -(2 / (t * Real.log ((m : ℝ) * t) ^ 3)) := by ring
            rw [hneg, abs_neg, abs_of_nonneg hfactor_nonneg]
            exact mul_le_mul_of_nonneg_left htE hfactor_nonneg
      _ = (2 * (C₀ + Real.log 2)) * (2 / (t * Real.log ((m : ℝ) * t) ^ 3)) := by ring
  have herr_int :
      IntegrableOn (fun t => deriv (tailKernel m) t * E t) (Set.Ioi (y : ℝ)) := by
    have hmeas :
        AEStronglyMeasurable (fun t => deriv (tailKernel m) t * E t)
          (MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))) := by
      have hE_meas :
          AEStronglyMeasurable E (MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))) := by
        measurability
      exact ((aestronglyMeasurable_tailKernelDerivFactor hm hy).mul hE_meas).congr hderivE_dom.symm
    rw [IntegrableOn] at hmajor ⊢
    exact Integrable.mono' hmajor hmeas hderivE_bound
  have hA_int : IntegrableOn A (Set.Ioi (y : ℝ)) := by
    simpa [hAeq] using hmain_int.add herr_int
  have hpartial :
      Tendsto partialS atTop (𝓝 (-∫ t in Set.Ioi (y : ℝ), A t)) := by
    refine Tendsto.congr' ?_ (by
      simpa using
        (tendsto_tailKernel_mul_mertensTail_zero hm hy hC₀).sub
          (intervalIntegral_tendsto_integral_Ioi
            (y : ℝ) hA_int tendsto_natCast_atTop_atTop))
    filter_upwards [eventually_ge_atTop y] with n hn
    simp [partialS, coeff, A, tailPartialSum_abel hm hy hn]
  have hcoeff_sum :
      HasSum coeff (-∫ t in Set.Ioi (y : ℝ), A t) := by
    refine (hasSum_iff_tendsto_nat_of_nonneg hcoeff_nonneg _).2 ?_
    refine Tendsto.congr' ?_ (hpartial.comp (tendsto_sub_atTop_nat 1))
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [partialS, Nat.range_eq_Icc_zero_sub_one n (by omega)]
  have htail :
      tailSum m y = -∫ t in Set.Ioi (y : ℝ), A t := by
    have hcoeff_eq :
        coeff = fun q : ℕ =>
          if y ≤ q then
            Λ q / ((q : ℝ) * Real.log ((m * q : ℕ) : ℝ) ^ 2)
          else 0 := by
      funext q
      unfold coeff
      by_cases hyq : y ≤ q
      · have hcast : ((m : ℝ) * q) = ((m * q : ℕ) : ℝ) := by
          norm_num [Nat.cast_mul]
        rw [if_pos hyq, tailCutoffCoeff, if_pos hyq]
        unfold tailKernel
        rw [hcast]
        field_simp
      · simp [tailCutoffCoeff, hyq]
    calc
      tailSum m y = ∑' q : ℕ, coeff q := by simp [tailSum, hcoeff_eq]
      _ = -∫ t in Set.Ioi (y : ℝ), A t := hcoeff_sum.tsum_eq
  have hmain :
      -∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ)) =
        1 / Real.log ((m * y : ℕ) : ℝ) :=
    integral_tailKernel_mainTerm hm hy
  have htail_split :
      tailSum m y - 1 / Real.log ((m * y : ℕ) : ℝ) =
        -∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * E t := by
    have hmain' :
        ∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ)) =
          -(1 / Real.log ((m * y : ℕ) : ℝ)) := by
      linarith [hmain]
    rw [htail, hAeq, integral_add hmain_int herr_int, hmain']
    ring
  calc
    |tailSum m y - 1 / Real.log ((m * y : ℕ) : ℝ)|
      = |∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * E t| := by
          rw [htail_split, abs_neg]
    _ ≤ ∫ t in Set.Ioi (y : ℝ), ‖deriv (tailKernel m) t * E t‖ := by
          simpa using
            (norm_integral_le_integral_norm
              (μ := MeasureTheory.volume.restrict (Set.Ioi (y : ℝ)))
              (fun t : ℝ => deriv (tailKernel m) t * E t))
    _ ≤
        ∫ t in Set.Ioi (y : ℝ),
          (2 * (C₀ + Real.log 2)) * (2 / (t * Real.log ((m : ℝ) * t) ^ 3)) := by
          exact setIntegral_mono_ae_restrict herr_int.norm hmajor hderivE_bound
    _ = (2 * (C₀ + Real.log 2)) * (1 / Real.log ((m * y : ℕ) : ℝ)) ^ 2 := by
          rw [integral_const_mul]
          simpa [Nat.cast_mul] using congrArg (fun z => (2 * (C₀ + Real.log 2)) * z)
            (integral_Ioi_two_inv_log_cube hm_pos hmy)
    _ = (2 * (C₀ + Real.log 2)) / (Real.log ((m * y : ℕ) : ℝ)) ^ 2 := by
          field_simp

end PrimitiveSetsAboveX



/-!
# First-entry row data

This file packages the row-wise data for the first-entry contribution to the normalization
constant. It introduces the threshold selecting admissible first jumps from a parent state `m`,
the resulting tail sum, and the pairwise weights used later in the fiberwise reindexing of
`B_x`.

## Main definitions

* `entryThreshold`
* `firstEntryTail`
* `firstEntryPairWeight`
-/


open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/-- The least threshold satisfying both `q ≥ Y` and `x ≤ m * q`. -/
def entryThreshold (x Y m : ℕ) : ℕ :=
  max Y (x ⌈/⌉ m)

/-- The first-entry tail sum starting from a parent state `m`. -/
noncomputable def firstEntryTail (x Y m : ℕ) : ℝ :=
  ∑' q : ℕ,
    if entryThreshold x Y m ≤ q then
      Λ q / ((q : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)
    else 0

/-- The pairwise weight indexed by a parent state `m` and jump factor `q`
for the first-entry contribution to `B_x`. -/
noncomputable def firstEntryPairWeight (x Y : ℕ) (mq : ℕ × ℕ) : ℝ :=
  if 1 ≤ mq.1 ∧ mq.1 < x ∧ entryThreshold x Y mq.1 ≤ mq.2 then
    Λ mq.2 / (((mq.1 * mq.2 : ℕ) : ℝ) * (Real.log ((mq.1 * mq.2 : ℕ) : ℝ)) ^ 2)
  else 0

/-- The lower-threshold condition is exactly the conjunction `q ≥ Y` and `x ≤ m * q`. -/
lemma entryThreshold_le_iff (x Y m q : ℕ) (hm : 0 < m) :
    entryThreshold x Y m ≤ q ↔ Y ≤ q ∧ x ≤ m * q := by
  rw [entryThreshold, max_le_iff]
  constructor
  · rintro ⟨hY, hq⟩
    exact ⟨hY, (ceilDiv_le_iff_le_mul hm).1 hq⟩
  · rintro ⟨hY, hxq⟩
    exact ⟨hY, (ceilDiv_le_iff_le_mul hm).2 hxq⟩

/-- For a parent state already known to satisfy `1 ≤ m < x`, the pairwise first-entry weight is
the corresponding scaled tail summand. -/
lemma firstEntryPairWeight_eq {x Y m q : ℕ} (hm1 : 1 ≤ m) (hmx : m < x) :
    firstEntryPairWeight x Y (m, q) =
      (1 / (m : ℝ)) *
        (if entryThreshold x Y m ≤ q then
          Λ q / ((q : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)
        else 0) := by
  by_cases hq : entryThreshold x Y m ≤ q
  · rw [firstEntryPairWeight, if_pos ⟨hm1, hmx, hq⟩, if_pos hq]
    rw [Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv]
    ring_nf
  · rw [firstEntryPairWeight, if_neg, if_neg hq]
    · simp
    · exact fun h => hq h.2.2

/-- For a fixed parent state `m`, the first-entry row is either the scaled tail summand row when
`1 ≤ m < x`, or identically zero otherwise. -/
lemma firstEntryPairWeight_row (x Y m : ℕ) :
    (fun q : ℕ => firstEntryPairWeight x Y (m, q)) =
      if 1 ≤ m ∧ m < x then
        fun q : ℕ =>
          (1 / (m : ℝ)) *
            (if entryThreshold x Y m ≤ q then
              Λ q / ((q : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)
            else 0)
      else fun _ : ℕ => 0 := by
  by_cases hm : 1 ≤ m ∧ m < x
  · rcases hm with ⟨hm1, hmx⟩
    funext q
    simp [firstEntryPairWeight_eq (x := x) (Y := Y) (m := m) (q := q) hm1 hmx, hm1, hmx]
  · funext q
    by_cases hm1 : 1 ≤ m
    · have hmx : ¬ m < x := by
        intro hmx
        exact hm ⟨hm1, hmx⟩
      simp [firstEntryPairWeight, hm1, hmx]
    · simp [firstEntryPairWeight, hm1]

end PrimitiveSetsAboveX



/-!
# Core definitions for the normalization constant

This file contains the shared decomposition of the entry weights and normalization constant into
their small-prime and first-entry pieces, together with the structural reindexing lemmas used by
the two separate estimate files.

## Main definitions

* `entryWeightFactor`
* `smallPrimeDivisorSum`
* `firstEntryDivisorSum`
* `normalizationSmallPrimePart`
* `normalizationFirstEntryPart`
-/


open scoped ArithmeticFunction BigOperators Topology

namespace PrimitiveSetsAboveX

/-- The common prefactor `1 / (n log^2 n)` in the entry weights. -/
noncomputable def entryWeightFactor (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)

/-- The small-prime-power divisor sum appearing in `b_x(n)`. -/
noncomputable def smallPrimeDivisorSum (Y n : ℕ) : ℝ :=
  (n.divisors.filter (fun q => q < Y)).sum fun q => Λ q

/-- The first-entry divisor sum appearing in `b_x(n)`. -/
noncomputable def firstEntryDivisorSum (x Y n : ℕ) : ℝ :=
  (n.divisors.filter (fun q => Y ≤ q ∧ n / q < x)).sum fun q => Λ q

/-- The contribution to `b_x(n)` from divisors `q < Y`. -/
noncomputable def smallPrimeEntryWeight (Y n : ℕ) : ℝ :=
  entryWeightFactor n * smallPrimeDivisorSum Y n

/-- The contribution to `b_x(n)` from divisors `q ≥ Y` with `n / q < x`. -/
noncomputable def firstEntryEntryWeight (x Y n : ℕ) : ℝ :=
  entryWeightFactor n * firstEntryDivisorSum x Y n

/-- The small-prime-power summand in the normalization constant `B_x`. -/
noncomputable def normalizationSmallPrimePart (x Y n : ℕ) : ℝ :=
  if x ≤ n then smallPrimeEntryWeight Y n else 0

/-- The first-entry summand in the normalization constant `B_x`. -/
noncomputable def normalizationFirstEntryPart (x Y n : ℕ) : ℝ :=
  if x ≤ n then firstEntryEntryWeight x Y n else 0

/-- `b_x(n)` splits into the small-prime-power and first-entry contributions. -/
lemma entryWeight_eq_smallPrimeEntryWeight_add_firstEntryEntryWeight (x Y n : ℕ) :
    entryWeight x Y n = smallPrimeEntryWeight Y n + firstEntryEntryWeight x Y n := by
  rw [entryWeight, smallPrimeEntryWeight, firstEntryEntryWeight, entryWeightFactor,
    smallPrimeDivisorSum, firstEntryDivisorSum, mul_add]

/--
Adding the remaining divisor contribution to `b_x(n)` recovers the full weighted divisor sum.
-/
lemma entryWeight_add_filtered_vonMangoldt_eq_entryWeightFactor_sum_divisors (x Y n : ℕ) :
    entryWeight x Y n +
      n.divisors.sum (fun q =>
        if Y ≤ q ∧ x ≤ n / q then entryWeightFactor n * Λ q else 0) =
      entryWeightFactor n * (n.divisors.sum fun q => Λ q) := by
  calc
    entryWeight x Y n +
        n.divisors.sum (fun q =>
          if Y ≤ q ∧ x ≤ n / q then entryWeightFactor n * Λ q else 0)
      = entryWeight x Y n +
          entryWeightFactor n *
            ((n.divisors.filter fun q => Y ≤ q ∧ x ≤ n / q).sum fun q => Λ q) := by
          rw [← Finset.sum_filter, Finset.mul_sum]
    _
      = entryWeightFactor n *
          (((n.divisors.filter fun q => q < Y).sum fun q => Λ q) +
            ((n.divisors.filter fun q => Y ≤ q ∧ n / q < x).sum fun q => Λ q) +
            ((n.divisors.filter fun q => Y ≤ q ∧ x ≤ n / q).sum fun q => Λ q)) := by
          simp [entryWeight, entryWeightFactor]
          ring_nf
    _ = entryWeightFactor n * (n.divisors.sum fun q => Λ q) := by
          congr 1
          rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
            ← Finset.sum_add_distrib]
          calc
            n.divisors.sum (fun q =>
                (if q < Y then Λ q else 0) +
                  (if Y ≤ q ∧ n / q < x then Λ q else 0) +
                    (if Y ≤ q ∧ x ≤ n / q then Λ q else 0))
            _ = n.divisors.sum fun q => Λ q := by
                  refine Finset.sum_congr rfl ?_
                  grind only

/-- The small-prime contribution to `b_x(n)` is nonnegative. -/
lemma smallPrimeEntryWeight_nonneg (Y n : ℕ) : 0 ≤ smallPrimeEntryWeight Y n := by
  unfold smallPrimeEntryWeight entryWeightFactor smallPrimeDivisorSum
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun q _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- The first-entry contribution to `b_x(n)` is nonnegative. -/
lemma firstEntryEntryWeight_nonneg (x Y n : ℕ) : 0 ≤ firstEntryEntryWeight x Y n := by
  unfold firstEntryEntryWeight entryWeightFactor firstEntryDivisorSum
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun q _ => ArithmeticFunction.vonMangoldt_nonneg)

/--
The first-entry threshold always lands in the admissible range `x ≤ m * q`, since it dominates the
ceiling quotient `x ⌈/⌉ m`.
-/
lemma le_mul_entryThreshold (x Y m : ℕ) (hm : 0 < m) :
    x ≤ m * entryThreshold x Y m := by
  have hceil : x ≤ m * (x ⌈/⌉ m) := le_smul_ceilDiv hm
  have hle : x ⌈/⌉ m ≤ entryThreshold x Y m := le_max_right _ _
  exact hceil.trans (Nat.mul_le_mul_left _ hle)

/--
For `m < x`, the ceiling-quotient part of the first-entry threshold overshoots `x / m` by less than
one step, so `m * (x ⌈/⌉ m)` stays below `2x`.
-/
private lemma mul_ceilDiv_lt_two_mul (x m : ℕ) (hm : 0 < m) (hmx : m < x) :
    m * (x ⌈/⌉ m) < 2 * x := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have hmul_div : m * ((x + m - 1) / m) ≤ x + m - 1 := Nat.mul_div_le _ _
  omega

/--
Under the standing regime `Y ≥ 2`, the first-entry threshold satisfies the upper bound
`m * entryThreshold x Y m ≤ xY` whenever `m < x`.
-/
private lemma mul_entryThreshold_le (x Y m : ℕ) (hY : 2 ≤ Y) (hm : 0 < m) (hmx : m < x) :
    m * entryThreshold x Y m ≤ x * Y := by
  rcases le_total Y (x ⌈/⌉ m) with hcase | hcase
  · rw [entryThreshold, max_eq_right hcase]
    have hlt : m * (x ⌈/⌉ m) < 2 * x := mul_ceilDiv_lt_two_mul x m hm hmx
    have hxy : 2 * x ≤ x * Y := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using Nat.mul_le_mul_left x hY
    exact hlt.le.trans hxy
  · rw [entryThreshold, max_eq_left hcase]
    exact Nat.mul_le_mul_right Y hmx.le

/--
If `n ∈ [x, xY]` and `x ≥ 2`, then the reciprocal logarithm at `n` differs from the reciprocal
logarithm at `x` by at most `log Y / log(x)^2`.
-/
private lemma abs_inv_log_sub_inv_log_le (x Y n : ℕ) (hx : 2 ≤ x) (hY : 1 ≤ Y)
    (hxn : x ≤ n) (hnY : n ≤ x * Y) :
    |1 / Real.log (n : ℝ) - 1 / Real.log (x : ℝ)| ≤
      Real.log (Y : ℝ) / (Real.log (x : ℝ)) ^ 2 := by
  have hxpos : 0 < (x : ℝ) := by positivity
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hxlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hnlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (le_trans hx hxn))
  have hlog_le : Real.log (x : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hxpos (by exact_mod_cast hxn)
  have hnonpos : 1 / Real.log (n : ℝ) - 1 / Real.log (x : ℝ) ≤ 0 := by
    linarith [one_div_le_one_div_of_le hxlog hlog_le]
  rw [abs_of_nonpos hnonpos]
  have hident :
      -(1 / Real.log (n : ℝ) - 1 / Real.log (x : ℝ)) =
        (Real.log (n : ℝ) - Real.log (x : ℝ)) /
          (Real.log (x : ℝ) * Real.log (n : ℝ)) := by
    grind only
  rw [hident]
  have hnum_nonneg : 0 ≤ Real.log (n : ℝ) - Real.log (x : ℝ) := sub_nonneg.mpr hlog_le
  have hsq_le : (Real.log (x : ℝ)) ^ 2 ≤ Real.log (x : ℝ) * Real.log (n : ℝ) := by
    nlinarith
  have hfirst :
      (Real.log (n : ℝ) - Real.log (x : ℝ)) /
          (Real.log (x : ℝ) * Real.log (n : ℝ)) ≤
        (Real.log (n : ℝ) - Real.log (x : ℝ)) / (Real.log (x : ℝ)) ^ 2 :=
    div_le_div_of_nonneg_left hnum_nonneg (sq_pos_of_pos hxlog) hsq_le
  have hlog_mul : Real.log ((x * Y : ℕ) : ℝ) = Real.log (x : ℝ) + Real.log (Y : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul (show (x : ℝ) ≠ 0 by exact_mod_cast (show x ≠ 0 by omega))
      (show (Y : ℝ) ≠ 0 by exact_mod_cast (show Y ≠ 0 by omega))]
  have hlog_upper : Real.log (n : ℝ) ≤ Real.log (x : ℝ) + Real.log (Y : ℝ) := by
    calc
      Real.log (n : ℝ) ≤ Real.log ((x * Y : ℕ) : ℝ) := by
        apply Real.log_le_log hnpos
        exact_mod_cast hnY
      _ = Real.log (x : ℝ) + Real.log (Y : ℝ) := hlog_mul
  have hnum_le : Real.log (n : ℝ) - Real.log (x : ℝ) ≤ Real.log (Y : ℝ) := by
    linarith
  have hsecond :
      (Real.log (n : ℝ) - Real.log (x : ℝ)) / (Real.log (x : ℝ)) ^ 2 ≤
        Real.log (Y : ℝ) / (Real.log (x : ℝ)) ^ 2 :=
    (div_le_div_iff_of_pos_right (sq_pos_of_pos hxlog)).2 hnum_le
  exact hfirst.trans hsecond

/--
Specializing the interval estimate to the first-entry threshold gives a uniform logarithmic error
bound along the initial-entry contribution.
-/
private lemma abs_inv_log_entryThreshold_sub_inv_log_le (x Y m : ℕ)
    (hx : 2 ≤ x) (hY : 2 ≤ Y) (hm : 0 < m) (hmx : m < x) :
    |1 / Real.log ((m * entryThreshold x Y m : ℕ) : ℝ) - 1 / Real.log (x : ℝ)| ≤
      Real.log (Y : ℝ) / (Real.log (x : ℝ)) ^ 2 := by
  have hlower : x ≤ m * entryThreshold x Y m := le_mul_entryThreshold x Y m hm
  have hupper : m * entryThreshold x Y m ≤ x * Y := mul_entryThreshold_le x Y m hY hm hmx
  exact abs_inv_log_sub_inv_log_le x Y (m * entryThreshold x Y m) hx (le_of_lt hY) hlower hupper

/--
For fixed `Y ≥ 2`, the first-entry tail at the faithful cutoff `entryThreshold x Y m`
approximates `1 / log x` with a uniform `log⁻² x` error, uniformly for all parent states
`1 ≤ m < x`.
-/
lemma firstEntryTailApproximation {Y : ℕ} (hY : 2 ≤ Y) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {x m : ℕ}, 2 ≤ x → 1 ≤ m → m < x →
        |firstEntryTail x Y m - 1 / Real.log (x : ℝ)| ≤
          C / (Real.log (x : ℝ)) ^ 2 := by
  rcases tailEstimate with ⟨C0, hC0pos, hC0⟩
  refine ⟨C0 + Real.log (Y : ℝ), by
    have hlogY : 0 < Real.log (Y : ℝ) :=
      Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hY))
    linarith, ?_⟩
  intro x m hx hm hmx
  have hthreshold : 2 ≤ entryThreshold x Y m := le_trans hY (le_max_left _ _)
  have htail :
      |firstEntryTail x Y m - 1 / Real.log ((m * entryThreshold x Y m : ℕ) : ℝ)| ≤
        C0 / (Real.log ((m * entryThreshold x Y m : ℕ) : ℝ)) ^ 2 := by
    simpa [firstEntryTail, tailSum] using hC0 hm hthreshold
  have hmul_lower : x ≤ m * entryThreshold x Y m := le_mul_entryThreshold x Y m hm
  have hlogsq :
      C0 / (Real.log ((m * entryThreshold x Y m : ℕ) : ℝ)) ^ 2 ≤
        C0 / (Real.log (x : ℝ)) ^ 2 := by
    have hxlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast hx)
    have hmul_log : Real.log (x : ℝ) ≤ Real.log ((m * entryThreshold x Y m : ℕ) : ℝ) := by
      apply Real.log_le_log
      · positivity
      · exact_mod_cast hmul_lower
    have hsq : (Real.log (x : ℝ)) ^ 2 ≤ (Real.log ((m * entryThreshold x Y m : ℕ) : ℝ)) ^ 2 := by
      nlinarith
    exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hxlog) hsq
  calc
    |firstEntryTail x Y m - 1 / Real.log (x : ℝ)|
      ≤ |firstEntryTail x Y m - 1 / Real.log ((m * entryThreshold x Y m : ℕ) : ℝ)| +
          |1 / Real.log ((m * entryThreshold x Y m : ℕ) : ℝ) - 1 / Real.log (x : ℝ)| := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              abs_sub_le (firstEntryTail x Y m)
                (1 / Real.log ((m * entryThreshold x Y m : ℕ) : ℝ))
                (1 / Real.log (x : ℝ))
    _ ≤ C0 / (Real.log (x : ℝ)) ^ 2 + Real.log (Y : ℝ) / (Real.log (x : ℝ)) ^ 2 := by
      gcongr
      · exact htail.trans hlogsq
      · exact abs_inv_log_entryThreshold_sub_inv_log_le x Y m hx hY hm hmx
    _ = (C0 + Real.log (Y : ℝ)) / (Real.log (x : ℝ)) ^ 2 := by ring

/--
The reciprocal sum up to `x - 1` differs from `log x` by at most `1`, which is the `O(1)` input
used in the normalization argument.
-/
private lemma abs_harmonic_pred_sub_log_le_one (x : ℕ) (hx : 1 ≤ x) :
    |(harmonic (x - 1) : ℝ) - Real.log (x : ℝ)| ≤ 1 := by
  by_cases hx1 : x = 1
  · subst hx1
    norm_num [harmonic_zero]
  have hlower : Real.log (x : ℝ) ≤ (harmonic (x - 1) : ℝ) := by
    simpa [Nat.sub_add_cancel hx] using
      (show Real.log (((x - 1) + 1 : ℕ) : ℝ) ≤ (harmonic (x - 1) : ℝ) from
        log_add_one_le_harmonic (x - 1))
  have hupper0 : (harmonic (x - 1) : ℝ) ≤ 1 + Real.log ((x - 1 : ℕ) : ℝ) := by
    exact_mod_cast harmonic_le_one_add_log (x - 1)
  have hlog_mono : Real.log ((x - 1 : ℕ) : ℝ) ≤ Real.log (x : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < x - 1 by omega)
    · exact_mod_cast Nat.sub_le x 1
  grind only [= abs.eq_1, = max_def]

/-- Equivalently, the finite reciprocal sum `∑_{m < x} 1 / m` is within `1` of `log x`. -/
lemma abs_sum_Icc_inv_sub_log_le_one (x : ℕ) (hx : 1 ≤ x) :
    |(∑ m ∈ Finset.Icc 1 (x - 1), (1 : ℝ) / m) - Real.log (x : ℝ)| ≤ 1 := by
  simpa [one_div, harmonic_eq_sum_Icc] using abs_harmonic_pred_sub_log_le_one x hx

/--
Reindexing the finite union of the divisor antidiagonals for `n < N` gives the finite product set
of positive pairs with product `< N`.
-/
private lemma sum_sigma_divisorsAntidiagonal_eq_sum_product
    (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ z ∈ (Finset.range N).sigma (fun n => n.divisorsAntidiagonal), F z.2.1 z.2.2 =
      ∑ p ∈ (((Finset.range N).product (Finset.range N)).filter
        (fun p : ℕ × ℕ => 0 < p.1 ∧ 0 < p.2 ∧ p.1 * p.2 < N)), F p.1 p.2 := by
  refine Finset.sum_bij'
    (i := fun z _ => z.2)
    (j := fun p _ => ⟨p.1 * p.2, p⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rcases Finset.mem_sigma.1 hz with ⟨hzN, hzdiv⟩
    rcases (Nat.mem_divisorsAntidiagonal.1 hzdiv) with ⟨hmul, hn0⟩
    have hzN' : z.1 < N := Finset.mem_range.1 hzN
    have hz1pos : 0 < z.2.1 := by
      apply Nat.pos_of_ne_zero
      exact Nat.left_ne_zero_of_mem_divisorsAntidiagonal hzdiv
    have hz2pos : 0 < z.2.2 := by
      apply Nat.pos_of_ne_zero
      exact Nat.right_ne_zero_of_mem_divisorsAntidiagonal hzdiv
    refine Finset.mem_filter.2 ?_
    refine ⟨Finset.mem_product.2 ?_, ?_⟩
    · constructor
      · exact Finset.mem_range.2 <|
          lt_of_le_of_lt (Nat.le_mul_of_pos_right z.2.1 hz2pos) (hmul ▸ hzN')
      · exact Finset.mem_range.2 <|
          lt_of_le_of_lt (Nat.le_mul_of_pos_left z.2.2 hz1pos) (hmul ▸ hzN')
    · exact ⟨hz1pos, hz2pos, hmul ▸ hzN'⟩
  · intro p hp
    rcases Finset.mem_filter.1 hp with ⟨hpprod, hpcond⟩
    rcases Finset.mem_product.1 hpprod with ⟨hp1, hp2⟩
    rcases hpcond with ⟨hp1pos, hp2pos, hplt⟩
    refine Finset.mem_sigma.2 ?_
    refine ⟨Finset.mem_range.2 hplt, ?_⟩
    exact Nat.mem_divisorsAntidiagonal.2 ⟨rfl, mul_ne_zero hp1pos.ne' hp2pos.ne'⟩
  · intro z hz
    rcases z with ⟨n, p⟩
    rcases p with ⟨q, m⟩
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    rcases Finset.mem_sigma.1 hz with ⟨_, hzdiv⟩
    exact (Nat.mem_divisorsAntidiagonal.1 hzdiv).1
  · intro p hp
    simp
  · intro z hz
    rfl

/-- The small-prime divisor sum can be rewritten over the divisor antidiagonal. -/
private lemma smallPrimeDivisorSum_eq_sum_divisorsAntidiagonal (Y n : ℕ) :
    smallPrimeDivisorSum Y n =
      ∑ p ∈ n.divisorsAntidiagonal, if p.1 < Y then Λ p.1 else 0 := by
  symm
  simpa [smallPrimeDivisorSum, Finset.sum_filter] using
    (Nat.sum_divisorsAntidiagonal (n := n) (f := fun q _ => if q < Y then Λ q else 0))

/-- Splitting `1 / ((mq) log^2(mq))` at the factor `q` produces the small-prime tail. -/
private lemma entryWeightFactor_mul_vonMangoldt_eq_smallFactor (q m : ℕ) :
    entryWeightFactor (m * q) * Λ q =
      (Λ q / (q : ℝ)) *
        (1 / ((m : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)) := by
  rw [entryWeightFactor, Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv]
  ring_nf

/--
The finite prefix of the small-prime contribution reindexes as a sum over `q < Y` and inner
`m`-tails, with the exact lower cutoff `x ⌈/⌉ q`.
-/
lemma sum_range_normalizationSmallPrimePart_eq
    (N x Y : ℕ) :
    ∑ n ∈ Finset.range N, normalizationSmallPrimePart x Y n =
      ∑ q ∈ Finset.range N, ∑ m ∈ Finset.range N,
        if 0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m then
          (Λ q / (q : ℝ)) *
            (1 / ((m : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2))
        else 0 := by
  let F : ℕ → ℕ → ℝ := fun q m =>
    if x ≤ q * m then
      entryWeightFactor (q * m) * (if q < Y then Λ q else 0)
    else 0
  calc
    ∑ n ∈ Finset.range N, normalizationSmallPrimePart x Y n
      = ∑ n ∈ Finset.range N, ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2 := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          by_cases hx : x ≤ n
          · rw [normalizationSmallPrimePart, if_pos hx, smallPrimeEntryWeight,
              smallPrimeDivisorSum_eq_sum_divisorsAntidiagonal, Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro p hp
            rcases Nat.mem_divisorsAntidiagonal.1 hp with ⟨hp_mul, _⟩
            simp [F, hp_mul, hx]
          · have hzero : ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2 = 0 := by
              refine Finset.sum_eq_zero ?_
              intro p hp
              rcases Nat.mem_divisorsAntidiagonal.1 hp with ⟨hp_mul, _⟩
              simp [F, hp_mul, hx]
            simp [normalizationSmallPrimePart, hx, hzero]
    _ = ∑ z ∈ (Finset.range N).sigma (fun n => n.divisorsAntidiagonal), F z.2.1 z.2.2 := by
          exact Finset.sum_sigma' (Finset.range N) Nat.divisorsAntidiagonal fun _ p => F p.1 p.2
    _ = ∑ p ∈ (((Finset.range N).product (Finset.range N)).filter
          (fun p : ℕ × ℕ => 0 < p.1 ∧ 0 < p.2 ∧ p.1 * p.2 < N)), F p.1 p.2 := by
          simpa [F] using sum_sigma_divisorsAntidiagonal_eq_sum_product N F
    _ = ∑ p ∈ (Finset.range N).product (Finset.range N),
          if 0 < p.1 ∧ 0 < p.2 ∧ p.1 * p.2 < N then F p.1 p.2 else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ q ∈ Finset.range N, ∑ m ∈ Finset.range N,
          if 0 < q ∧ 0 < m ∧ q * m < N then F q m else 0 := by
          simpa [F] using
            (Finset.sum_product' (Finset.range N) (Finset.range N)
              (fun q m => if 0 < q ∧ 0 < m ∧ q * m < N then F q m else 0))
    _ = ∑ q ∈ Finset.range N, ∑ m ∈ Finset.range N,
          if 0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m then
            (Λ q / (q : ℝ)) *
              (1 / ((m : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2))
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          refine Finset.sum_congr rfl ?_
          intro m hm
          by_cases hbase : 0 < q ∧ 0 < m ∧ q * m < N
          · rcases hbase with ⟨hqpos, hmpos, hqmN⟩
            by_cases hxqm : x ≤ q * m <;> by_cases hqY : q < Y
            · simp [F, hqpos, hmpos, hqmN, hxqm, hqY, ceilDiv_le_iff_le_mul hqpos]
              simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, Nat.mul_comm] using
                (entryWeightFactor_mul_vonMangoldt_eq_smallFactor q m)
            · simp [F, hqpos, hmpos, hqmN, hxqm, hqY, ceilDiv_le_iff_le_mul hqpos]
            · simp [F, hqpos, hmpos, hqmN, hxqm, hqY, ceilDiv_le_iff_le_mul hqpos]
            · simp [F, hqpos, hmpos, hqmN, hxqm, hqY, ceilDiv_le_iff_le_mul hqpos]
          · have hcond :
                ¬ (0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m) := by
                  intro h
                  exact hbase ⟨h.1, h.2.1, h.2.2.1⟩
            simp [F, hbase, hcond]

/-- Reindexing the product fiber of `firstEntryPairWeight` recovers the first-entry normalization
summand, including the zero fiber. -/
lemma tsum_firstEntryPairWeight_fiber_prod {x Y n : ℕ} (hx : 1 ≤ x) :
    ∑' p : (fun mq : ℕ × ℕ => mq.1 * mq.2) ⁻¹' {n}, firstEntryPairWeight x Y p =
      normalizationFirstEntryPart x Y n := by
  by_cases hn : n = 0
  · subst hn
    have hzero :
        ∀ p : (fun mq : ℕ × ℕ => mq.1 * mq.2) ⁻¹' ({0} : Set ℕ),
          firstEntryPairWeight x Y p = 0 := by
      rintro ⟨⟨m, q⟩, hp⟩
      by_cases hmq : 1 ≤ m ∧ m < x ∧ entryThreshold x Y m ≤ q
      · have hm_pos : 0 < m := by omega
        have hxle : x ≤ m * q := (entryThreshold_le_iff x Y m q hm_pos).1 hmq.2.2 |>.2
        have : m * q = 0 := by simpa using hp
        omega
      · simp [firstEntryPairWeight, hmq]
    have hx0 : ¬ x ≤ 0 := by omega
    have htsum :
        (∑' p : (fun mq : ℕ × ℕ => mq.1 * mq.2) ⁻¹' ({0} : Set ℕ), firstEntryPairWeight x Y p) =
          ∑' _ : (fun mq : ℕ × ℕ => mq.1 * mq.2) ⁻¹' ({0} : Set ℕ), (0 : ℝ) := by
      exact tsum_congr hzero
    simpa [normalizationFirstEntryPart, hx0] using htsum
  · rw [show (fun mq : ℕ × ℕ => mq.1 * mq.2) ⁻¹' {n} = n.divisorsAntidiagonal by
      ext mq
      simp [Nat.mem_divisorsAntidiagonal, hn],
      Finset.tsum_subtype' n.divisorsAntidiagonal fun mq => firstEntryPairWeight x Y mq,
      Nat.sum_divisorsAntidiagonal' (f := fun m q => firstEntryPairWeight x Y (m, q))]
    by_cases hxn : x ≤ n
    · rw [normalizationFirstEntryPart, if_pos hxn, firstEntryEntryWeight, firstEntryDivisorSum]
      calc
        ∑ q ∈ n.divisors, firstEntryPairWeight x Y (n / q, q) =
            ∑ q ∈ n.divisors,
              entryWeightFactor n * (if Y ≤ q ∧ n / q < x then Λ q else 0) := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              have hq_dvd : q ∣ n := (Nat.mem_divisors.mp hq).1
              have hmq_pos : 0 < n / q := by
                refine Nat.pos_of_dvd_of_pos ?_ (Nat.pos_iff_ne_zero.mpr hn)
                exact ⟨q, by simpa using (Nat.div_mul_cancel hq_dvd).symm⟩
              have hmul : (n / q) * q = n := Nat.div_mul_cancel hq_dvd
              have hiff : entryThreshold x Y (n / q) ≤ q ↔ Y ≤ q := by
                constructor
                · intro hle
                  exact (entryThreshold_le_iff x Y (n / q) q hmq_pos).1 hle |>.1
                · intro hYq
                  exact (entryThreshold_le_iff x Y (n / q) q hmq_pos).2
                    ⟨hYq, by simpa [hmul] using hxn⟩
              have hmq_ge : 1 ≤ n / q := Nat.succ_le_of_lt hmq_pos
              by_cases hcond : Y ≤ q ∧ n / q < x
              · rw [firstEntryPairWeight_eq (x := x) (Y := Y) hmq_ge hcond.2, if_pos hcond]
                rw [if_pos (hiff.2 hcond.1)]
                calc
                  (1 / ((n / q : ℕ) : ℝ)) *
                      (Λ q / ((q : ℝ) * Real.log (((n / q) * q : ℕ) : ℝ) ^ 2)) =
                      entryWeightFactor ((n / q) * q) * Λ q := by
                        simpa [div_eq_mul_inv, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]
                          using (entryWeightFactor_mul_vonMangoldt_eq_smallFactor q (n / q)).symm
                  _ = entryWeightFactor n * Λ q := by simp [hmul]
              · simp [firstEntryPairWeight, hiff, hmq_ge, hcond, and_comm]
        _ = entryWeightFactor n *
              ∑ q ∈ n.divisors, if Y ≤ q ∧ n / q < x then Λ q else 0 := by
              rw [Finset.mul_sum]
        _ = entryWeightFactor n *
              ∑ q ∈ n.divisors.filter (fun q => Y ≤ q ∧ n / q < x), Λ q := by
              rw [Finset.sum_filter]
        _ = entryWeightFactor n * firstEntryDivisorSum x Y n := by
              simp [firstEntryDivisorSum]
    · rw [normalizationFirstEntryPart, if_neg hxn]
      refine Finset.sum_eq_zero ?_
      intro q hq
      have hq_dvd : q ∣ n := (Nat.mem_divisors.mp hq).1
      have hmq_pos : 0 < n / q := by
        refine Nat.pos_of_dvd_of_pos ?_ (Nat.pos_iff_ne_zero.mpr hn)
        exact ⟨q, by simpa using (Nat.div_mul_cancel hq_dvd).symm⟩
      have hx_false : ¬ entryThreshold x Y (n / q) ≤ q := by
        intro hle
        exact hxn <| (entryThreshold_le_iff x Y (n / q) q hmq_pos).1 hle |>.2.trans_eq
          (Nat.div_mul_cancel hq_dvd)
      simp [firstEntryPairWeight, Nat.succ_le_of_lt hmq_pos, hx_false]

/-- The normalization constant `B_x` is exactly the sum of its small-prime and first-entry
contributions. -/
lemma normalizationConstant_eq_tsum_parts (x Y : ℕ) :
    normalizationConstant x Y =
      ∑' n : ℕ, (normalizationSmallPrimePart x Y n + normalizationFirstEntryPart x Y n) := by
  refine tsum_congr fun n => ?_
  by_cases hn : x ≤ n
  · simp [normalizationSmallPrimePart, normalizationFirstEntryPart, hn,
      entryWeight_eq_smallPrimeEntryWeight_add_firstEntryEntryWeight]
  · simp [normalizationSmallPrimePart, normalizationFirstEntryPart, hn]

end PrimitiveSetsAboveX



/-!
# Small-prime bounds for the normalization constant

This file isolates the contribution to `B_x` coming from divisors `q < Y`.
Its main theorem shows that this part is summable and contributes only `O(1 / log x)` for fixed
`Y`.

## Main statements

* `summable_normalizationSmallPrimePart_and_tsum_le`
-/


open scoped ArithmeticFunction BigOperators Topology

namespace PrimitiveSetsAboveX

/-- The natural-number kernel in the small-prime tail. -/
noncomputable def smallPrimeTailTerm (q m : ℕ) : ℝ :=
  1 / ((m : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)

/-- The corresponding real-variable kernel used for integral comparison. -/
noncomputable def smallPrimeKernel (q : ℕ) (t : ℝ) : ℝ :=
  1 / (t * (Real.log (t * q)) ^ 2)

/-- The natural small-prime tail summand is always nonnegative. -/
private lemma smallPrimeTailTerm_nonneg (q m : ℕ) : 0 ≤ smallPrimeTailTerm q m := by
  dsimp [smallPrimeTailTerm]
  positivity

/-- The real kernel is nonnegative once `t q > 1`. -/
private lemma smallPrimeKernel_nonneg {q : ℕ} {t : ℝ} (htq : 1 < t * q) :
    0 ≤ smallPrimeKernel q t := by
  have ht : 0 < t := by
    have hq : (0 : ℝ) ≤ q := by positivity
    nlinarith
  have hlog : 0 < Real.log (t * q) := Real.log_pos htq
  dsimp [smallPrimeKernel]
  positivity

/-- The real kernel is antitone on the tail where the logarithm is positive. -/
private lemma smallPrimeKernel_antitoneOn {q : ℕ} (hq : 0 < q) {a : ℝ} (ha : 1 < a * q) :
    AntitoneOn (smallPrimeKernel q) (Set.Ici a) := by
  intro s hs t ht hst
  have hs' : a ≤ s := hs
  have ht' : a ≤ t := ht
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have has : a * q ≤ s * q := by
    gcongr
  have hat : a * q ≤ t * q := by
    gcongr
  have hsq_gt_one : 1 < s * q := lt_of_lt_of_le ha has
  have htq_gt_one : 1 < t * q := lt_of_lt_of_le ha hat
  have htpos : 0 < t := by nlinarith
  have hmul : s * q ≤ t * q := by gcongr
  have hlog_le : Real.log (s * q) ≤ Real.log (t * q) := by
    exact Real.log_le_log (by positivity) hmul
  have hlog_sq_le : (Real.log (s * q)) ^ 2 ≤ (Real.log (t * q)) ^ 2 := by
    nlinarith [hlog_le, Real.log_pos hsq_gt_one, Real.log_pos htq_gt_one]
  have hden_le : s * (Real.log (s * q)) ^ 2 ≤ t * (Real.log (t * q)) ^ 2 := by
    exact mul_le_mul hst hlog_sq_le (sq_nonneg _) (le_of_lt htpos)
  have hsden_pos : 0 < s * (Real.log (s * q)) ^ 2 := by
    have hspos : 0 < s := by nlinarith
    have hslogpos : 0 < Real.log (s * q) := Real.log_pos hsq_gt_one
    positivity
  exact one_div_le_one_div_of_le hsden_pos hden_le

/-- The shifted kernel tail is summable, and its total mass is bounded by the corresponding
logarithmic integral at the starting point. -/
private lemma summable_smallPrimeKernel_shift_and_tsum_le {q N : ℕ} (hq : 0 < q)
    (hNq : 1 < (N : ℝ) * q) :
    Summable (fun n : ℕ => smallPrimeKernel q (N + n + 1)) ∧
      ∑' n : ℕ, smallPrimeKernel q (N + n + 1) ≤ 1 / Real.log ((N : ℝ) * q) := by
  let g : ℕ → ℝ := fun n => smallPrimeKernel q (N + n + 1)
  have hkernel_eq :
      smallPrimeKernel q = fun t : ℝ => t⁻¹ * (Real.log (t * q) ^ 2)⁻¹ := by
    funext t
    simp [smallPrimeKernel, div_eq_mul_inv, mul_left_comm, mul_comm]
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    have hmul : (N : ℝ) * q ≤ (((N + n + 1 : ℕ) : ℝ) * q) := by
      gcongr
      exact_mod_cast Nat.le_add_right N (n + 1)
    have hgt : 1 < (((N + n + 1 : ℕ) : ℝ) * q) := lt_of_lt_of_le hNq hmul
    exact smallPrimeKernel_nonneg (by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hgt)
  have hbound : ∀ n, (∑ i ∈ Finset.range n, g i) ≤ 1 / Real.log ((N : ℝ) * q) := by
    intro n
    have hanti : AntitoneOn (smallPrimeKernel q) (Set.Icc (N : ℝ) (N + n)) :=
      (smallPrimeKernel_antitoneOn hq hNq).mono Set.Icc_subset_Ici_self
    have hIoi : MeasureTheory.IntegrableOn (smallPrimeKernel q) (Set.Ioi (N : ℝ)) := by
      rw [hkernel_eq]
      simpa [div_eq_mul_inv, mul_left_comm, mul_comm] using
        (integrableOn_Ioi_inv_log_sq (c := (q : ℝ)) (y := (N : ℝ))
          (by exact_mod_cast hq) (by simpa [mul_comm] using hNq))
    have hnonneg :
        0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (N : ℝ))] smallPrimeKernel q := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have hxN : (N : ℝ) < x := hx
      have hmul : (N : ℝ) * q < x * q := by
        gcongr
      exact smallPrimeKernel_nonneg (lt_trans hNq hmul)
    have hNn : (N : ℝ) ≤ (N : ℝ) + n := by
      exact_mod_cast Nat.le_add_right N n
    calc
      ∑ i ∈ Finset.range n, g i
        = ∑ i ∈ Finset.range n, smallPrimeKernel q (N + (i + 1 : ℕ)) := by
            grind only
      _ ≤ ∫ x in (N : ℝ)..N + n, smallPrimeKernel q x := by
            exact AntitoneOn.sum_le_integral hanti
      _ ≤ ∫ x in Set.Ioi (N : ℝ), smallPrimeKernel q x := by
            rw [intervalIntegral.integral_of_le hNn]
            exact MeasureTheory.integral_mono_measure
              (MeasureTheory.Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl) hnonneg hIoi
      _ = 1 / Real.log ((N : ℝ) * q) := by
            rw [hkernel_eq]
            simpa [div_eq_mul_inv, mul_left_comm, mul_comm] using
              (integral_Ioi_inv_log_sq (c := (q : ℝ)) (y := (N : ℝ))
                (by exact_mod_cast hq) (by simpa [mul_comm] using hNq))
  refine ⟨summable_of_sum_range_le (f := g) (c := 1 / Real.log ((N : ℝ) * q)) hg_nonneg hbound, ?_⟩
  exact Real.tsum_le_of_sum_range_le hg_nonneg hbound

/-- Splitting the first active index from the small-prime prefix rewrites it as a head term plus
the shifted kernel tail. -/
private lemma sum_range_smallPrimeTail_eq_head_add {q M N : ℕ} (hMN : M < N) :
    ∑ m ∈ Finset.range N, (if M ≤ m then smallPrimeTailTerm q m else 0) =
      smallPrimeTailTerm q M +
        ∑ n ∈ Finset.range (N - (M + 1)), smallPrimeKernel q (M + n + 1) := by
  have hdecomp :
      ∑ m ∈ Finset.range N, (if M ≤ m then smallPrimeTailTerm q m else 0) =
        smallPrimeTailTerm q M + ∑ m ∈ Finset.Ico (M + 1) N, smallPrimeTailTerm q m := by
    have hsplit :
        ∑ m ∈ Finset.range N, (if M ≤ m then smallPrimeTailTerm q m else 0) =
          (∑ m ∈ Finset.range (M + 1), (if M ≤ m then smallPrimeTailTerm q m else 0)) +
            ∑ m ∈ Finset.Ico (M + 1) N, (if M ≤ m then smallPrimeTailTerm q m else 0) := by
      symm
      exact Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hMN)
    rw [hsplit, Finset.sum_range_succ]
    have hzero : ∑ m ∈ Finset.range M, (if M ≤ m then smallPrimeTailTerm q m else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      grind only [= Finset.mem_range]
    have hIco :
        ∑ m ∈ Finset.Ico (M + 1) N, (if M ≤ m then smallPrimeTailTerm q m else 0) =
          ∑ m ∈ Finset.Ico (M + 1) N, smallPrimeTailTerm q m := by
      refine Finset.sum_congr rfl ?_
      grind only [= Finset.mem_Ico]
    simp_all
  have hreindex :
      ∑ m ∈ Finset.Ico (M + 1) N, smallPrimeTailTerm q m =
        ∑ n ∈ Finset.range (N - (M + 1)), smallPrimeKernel q (M + n + 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp [smallPrimeTailTerm, smallPrimeKernel, Nat.cast_add, Nat.cast_one,
      add_assoc, add_left_comm, add_comm, mul_add, mul_add, mul_comm]
  rw [hdecomp, hreindex]

/--
Every finite prefix of the small-prime tail is bounded by `2 / log x` once `x ≥ 3`. This is the
monotone integral comparison specialized to the exact cutoff `x ⌈/⌉ q`.
-/
lemma sum_range_smallPrimeTail_le_two_inv_log {x q N : ℕ} (hx : 3 ≤ x) (hq : 0 < q) :
    ∑ m ∈ Finset.range N, (if x ⌈/⌉ q ≤ m then smallPrimeTailTerm q m else 0) ≤
      2 / Real.log (x : ℝ) := by
  let M := x ⌈/⌉ q
  have hxq : x ≤ q * M := by
    simpa [M, Nat.mul_comm] using le_smul_ceilDiv hq
  have hx_log_pos : 0 < Real.log (x : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hx))
  have hMq_ge_x : (x : ℝ) ≤ (M : ℝ) * q := by
    exact_mod_cast (by simpa [Nat.mul_comm] using hxq)
  have hMq_gt_one : 1 < (M : ℝ) * q := by
    have hx_one : (1 : ℝ) < x := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hx)
    exact lt_of_lt_of_le hx_one hMq_ge_x
  have hlog_mono : Real.log (x : ℝ) ≤ Real.log ((M : ℝ) * q) := by
    exact Real.log_le_log (by positivity) hMq_ge_x
  have htail := summable_smallPrimeKernel_shift_and_tsum_le (q := q) (N := M) hq hMq_gt_one
  have hkernel_nonneg : ∀ n : ℕ, 0 ≤ smallPrimeKernel q (M + n + 1) := by
    intro n
    have hmul :
        (M : ℝ) * q ≤ (((M + n + 1 : ℕ) : ℝ) * q) := by
      gcongr
      exact_mod_cast Nat.le_add_right M (n + 1)
    have hgt : 1 < (((M + n + 1 : ℕ) : ℝ) * q) := lt_of_lt_of_le hMq_gt_one hmul
    exact smallPrimeKernel_nonneg (by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hgt)
  by_cases hMN : M < N
  · have hhead :
        smallPrimeTailTerm q M ≤ 1 / Real.log (x : ℝ) := by
      have hMpos : 0 < M := by
        by_contra hMpos
        have hM0 : M = 0 := Nat.eq_zero_of_not_pos hMpos
        rw [hM0, Nat.mul_zero] at hxq
        omega
      have hlogMq_ge_one : 1 ≤ Real.log ((M : ℝ) * q) := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) <|
          le_trans Real.exp_one_lt_three.le <| le_trans (by exact_mod_cast hx) hMq_ge_x
      have hden :
          Real.log (x : ℝ) ≤ (M : ℝ) * (Real.log ((M : ℝ) * q)) ^ 2 := by
        have hM_ge_one : (1 : ℝ) ≤ M := by exact_mod_cast Nat.succ_le_of_lt hMpos
        nlinarith
      dsimp [smallPrimeTailTerm, M]
      simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using
        (one_div_le_one_div_of_le hx_log_pos hden)
    have hshift_le :
        ∑' n : ℕ, smallPrimeKernel q (M + n + 1) ≤ 1 / Real.log (x : ℝ) := by
      exact htail.2.trans <| one_div_le_one_div_of_le hx_log_pos hlog_mono
    have hprefix :
        ∑ m ∈ Finset.range N, (if M ≤ m then smallPrimeTailTerm q m else 0) ≤
          smallPrimeTailTerm q M + ∑' n : ℕ, smallPrimeKernel q (M + n + 1) := by
      calc
        ∑ m ∈ Finset.range N, (if M ≤ m then smallPrimeTailTerm q m else 0)
          = smallPrimeTailTerm q M +
              ∑ n ∈ Finset.range (N - (M + 1)), smallPrimeKernel q (M + n + 1) := by
                exact sum_range_smallPrimeTail_eq_head_add hMN
        _ ≤ smallPrimeTailTerm q M + ∑' n : ℕ, smallPrimeKernel q (M + n + 1) := by
              gcongr
              exact htail.1.sum_le_tsum _ (fun n _ => hkernel_nonneg n)
    calc
      ∑ m ∈ Finset.range N, (if x ⌈/⌉ q ≤ m then smallPrimeTailTerm q m else 0)
        ≤ smallPrimeTailTerm q M + ∑' n : ℕ, smallPrimeKernel q (M + n + 1) := by
            simpa [M] using hprefix
      _ ≤ 1 / Real.log (x : ℝ) + 1 / Real.log (x : ℝ) := by
            gcongr
      _ = 2 / Real.log (x : ℝ) := by ring
  · have hzero :
        ∑ m ∈ Finset.range N, (if x ⌈/⌉ q ≤ m then smallPrimeTailTerm q m else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      grind only [= Finset.mem_range]
    simpa [hzero] using (show 0 ≤ 2 / Real.log (x : ℝ) by positivity)

/-- The `q`-th inner row in the small-prime decomposition is bounded by the corresponding
coefficient times `2 / log x`, and vanishes outside `q ∈ Ico 1 Y`. -/
private lemma sum_range_smallPrimeRow_le {x q N Y : ℕ} (hx : 3 ≤ x) :
    let coeff : ℝ := Λ q / (q : ℝ)
    ∑ m ∈ Finset.range N,
      (if 0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m then
        coeff * smallPrimeTailTerm q m
      else 0) ≤
      if 1 ≤ q ∧ q < Y then coeff * (2 / Real.log (x : ℝ)) else 0 := by
  let coeff : ℝ := Λ q / (q : ℝ)
  by_cases hq : 1 ≤ q ∧ q < Y
  · rcases hq with ⟨hq1, hqY⟩
    have hqpos : 0 < q := Nat.succ_le_iff.mp hq1
    have hcoeff_nonneg : 0 ≤ coeff := by
      dsimp [coeff]
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    calc
      ∑ m ∈ Finset.range N,
          (if 0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m then
            coeff * smallPrimeTailTerm q m
          else 0)
        ≤ ∑ m ∈ Finset.range N, coeff * (if x ⌈/⌉ q ≤ m then smallPrimeTailTerm q m else 0) := by
            refine Finset.sum_le_sum ?_
            intro m hm
            by_cases hmcut : x ⌈/⌉ q ≤ m <;> by_cases hbase : 0 < m ∧ q * m < N
            · simp [coeff, hqpos, hqY, hmcut, hbase]
            · simpa [coeff, hqpos, hqY, hmcut, hbase] using
                mul_nonneg hcoeff_nonneg (smallPrimeTailTerm_nonneg q m)
            · simp [coeff, hmcut]
            · simp [coeff, hmcut]
      _ = coeff * ∑ m ∈ Finset.range N, (if x ⌈/⌉ q ≤ m then smallPrimeTailTerm q m else 0) := by
            rw [Finset.mul_sum]
      _ ≤ coeff * (2 / Real.log (x : ℝ)) := by
            exact mul_le_mul_of_nonneg_left
              (sum_range_smallPrimeTail_le_two_inv_log (x := x) (q := q) (N := N) hx hqpos)
              hcoeff_nonneg
      _ = if 1 ≤ q ∧ q < Y then coeff * (2 / Real.log (x : ℝ)) else 0 := by
            simp [hq1, hqY]
  · have hzero :
        ∑ m ∈ Finset.range N,
          (if 0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m then
            coeff * smallPrimeTailTerm q m
          else 0) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro m hm
            have hcond :
                ¬ (0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m) := by
                  grind only [Nat.succ_le_iff]
            simp [hcond]
    simp [coeff, hzero, hq]

/--
For `x ≥ 3`, the small-prime contribution to `B_x` is summable, and its total mass is bounded by
an explicit `O(1 / log x)` term depending only on the fixed cutoff `Y`.
-/
lemma summable_normalizationSmallPrimePart_and_tsum_le {x Y : ℕ} (hx : 3 ≤ x) :
    Summable (fun n : ℕ => normalizationSmallPrimePart x Y n) ∧
      ∑' n : ℕ, normalizationSmallPrimePart x Y n ≤
        (2 * ∑ q ∈ Finset.Ico 1 Y, Λ q / (q : ℝ)) / Real.log (x : ℝ) := by
  let coeff : ℕ → ℝ := fun q => Λ q / (q : ℝ)
  have hcoeff_nonneg : ∀ q, 0 ≤ coeff q := by
    intro q
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hpart_nonneg : ∀ n : ℕ, 0 ≤ normalizationSmallPrimePart x Y n := by
    intro n
    by_cases hn : x ≤ n <;> simp [normalizationSmallPrimePart, hn, smallPrimeEntryWeight_nonneg]
  have hprefix :
      ∀ N : ℕ,
        ∑ n ∈ Finset.range N, normalizationSmallPrimePart x Y n ≤
          (2 * ∑ q ∈ Finset.Ico 1 Y, coeff q) / Real.log (x : ℝ) := by
    intro N
    calc
      ∑ n ∈ Finset.range N, normalizationSmallPrimePart x Y n
        = ∑ q ∈ Finset.range N, ∑ m ∈ Finset.range N,
            if 0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m then
              coeff q * smallPrimeTailTerm q m
            else 0 := by
              simpa [coeff, smallPrimeTailTerm] using sum_range_normalizationSmallPrimePart_eq N x Y
      _ ≤ ∑ q ∈ Finset.range N,
            if 1 ≤ q ∧ q < Y then coeff q * (2 / Real.log (x : ℝ)) else 0 := by
              refine Finset.sum_le_sum ?_
              intro q _
              simpa [coeff] using
                (sum_range_smallPrimeRow_le (x := x) (q := q) (N := N) (Y := Y) hx)
      _ = ∑ q ∈ (Finset.range N).filter (fun q => 1 ≤ q ∧ q < Y),
            coeff q * (2 / Real.log (x : ℝ)) := by
              rw [← Finset.sum_filter]
      _ ≤ ∑ q ∈ Finset.Ico 1 Y, coeff q * (2 / Real.log (x : ℝ)) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro q hq
                exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hq).2
              · intro q hqIco hqnot
                exact mul_nonneg (hcoeff_nonneg q) (by positivity)
      _ = (2 * ∑ q ∈ Finset.Ico 1 Y, coeff q) / Real.log (x : ℝ) := by
              rw [← Finset.sum_mul]
              ring
  refine ⟨?_, ?_⟩
  · exact summable_of_sum_range_le
      (f := fun n : ℕ => normalizationSmallPrimePart x Y n)
      (c := (2 * ∑ q ∈ Finset.Ico 1 Y, coeff q) / Real.log (x : ℝ)) hpart_nonneg hprefix
  · exact Real.tsum_le_of_sum_range_le (hf := hpart_nonneg) (h := hprefix)
end PrimitiveSetsAboveX



/-!
# First-entry bounds for the normalization constant

This file completes the normalization decomposition by summing the first-entry rows and
proving the final estimate for the first-entry contribution to `B_x`.

## Main statements

* `normalizationFirstEntryPart_estimate`
-/


open scoped ArithmeticFunction BigOperators Topology

namespace PrimitiveSetsAboveX

/--
If every first-entry row is summable, then the corresponding contribution to `B_x` is exactly the
finite parent-state sum appearing in the first-entry decomposition.
-/
lemma hasSum_normalizationFirstEntryPart {x Y : ℕ} (hx : 1 ≤ x)
    (hsummable :
      ∀ {m : ℕ}, 1 ≤ m → m < x →
        Summable (fun q : ℕ =>
          if entryThreshold x Y m ≤ q then
            Λ q / ((q : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)
          else 0)) :
    HasSum (fun n : ℕ => normalizationFirstEntryPart x Y n)
      (∑ m ∈ Finset.Icc 1 (x - 1), (1 / (m : ℝ)) * firstEntryTail x Y m) := by
  let row : ℕ → ℝ := fun m => ∑' q : ℕ, firstEntryPairWeight x Y (m, q)
  have hrow :
      ∀ m : ℕ,
        row m = if 1 ≤ m ∧ m < x then (1 / (m : ℝ)) * firstEntryTail x Y m else 0 := by
    intro m
    dsimp [row]
    rw [firstEntryPairWeight_row]
    by_cases hm : 1 ≤ m ∧ m < x
    · rw [if_pos hm, tsum_mul_left, firstEntryTail, if_pos hm]
    · simp [hm]
  have hslice :
      ∀ m : ℕ, Summable (fun q : ℕ => firstEntryPairWeight x Y (m, q)) := by
    intro m
    rw [firstEntryPairWeight_row]
    by_cases hm : 1 ≤ m ∧ m < x
    · rcases hm with ⟨hm1, hmx⟩
      rw [if_pos ⟨hm1, hmx⟩]
      exact (hsummable hm1 hmx).mul_left (1 / (m : ℝ))
    · simp [hm]
  have hIcc : ∀ m : ℕ, (1 ≤ m ∧ m < x) ↔ m ∈ Finset.Icc 1 (x - 1) := by
    intro m
    simp [Finset.mem_Icc]
    omega
  have hrow_zero : ∀ m ∉ Finset.Icc 1 (x - 1), row m = 0 := by
    intro m hm
    rw [hrow m, if_neg]
    simpa [hIcc m] using hm
  have hrow_summable : Summable row := by
    refine summable_of_hasFiniteSupport ((Finset.Icc 1 (x - 1)).finite_toSet.subset ?_)
    intro m hm
    by_contra hm'
    exact hm (hrow_zero m hm')
  have hpair_nonneg : ∀ p : ℕ × ℕ, 0 ≤ firstEntryPairWeight x Y p := by
    rintro ⟨m, q⟩
    by_cases hp : 1 ≤ m ∧ m < x ∧ entryThreshold x Y m ≤ q
    · rw [firstEntryPairWeight, if_pos hp]
      rw [Nat.cast_mul]
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    · simp [firstEntryPairWeight, hp]
  have hpair :
      Summable (fun p : ℕ × ℕ => firstEntryPairWeight x Y p) :=
    (summable_prod_of_nonneg hpair_nonneg).2 ⟨hslice, hrow_summable⟩
  have hfiber :
      HasSum
        (fun n : ℕ =>
          ∑' p : (fun mq : ℕ × ℕ => mq.1 * mq.2) ⁻¹' ({n} : Set ℕ),
            firstEntryPairWeight x Y p)
        (∑' p : ℕ × ℕ, firstEntryPairWeight x Y p) :=
    HasSum.tsum_fiberwise hpair.hasSum (fun mq : ℕ × ℕ => mq.1 * mq.2)
  have hfirst :
      HasSum (fun n : ℕ => normalizationFirstEntryPart x Y n)
        (∑' p : ℕ × ℕ, firstEntryPairWeight x Y p) := by
    convert hfiber using 1
    ext n
    simpa using (tsum_firstEntryPairWeight_fiber_prod (x := x) (Y := Y) (n := n) hx).symm
  have hrows :
      ∑' p : ℕ × ℕ, firstEntryPairWeight x Y p = ∑' m : ℕ, row m := by
    simpa [row] using hpair.tsum_prod' hslice
  rw [hrows] at hfirst
  rw [tsum_eq_sum (s := Finset.Icc 1 (x - 1)) hrow_zero] at hfirst
  convert hfirst using 1
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [hrow m, if_pos]
  simpa [hIcc m] using hm

/--
For fixed `Y ≥ 2`, the first-entry contribution to `B_x` is summable and equals
`1 + O(1 / log x)` as `x → ∞`.
-/
lemma normalizationFirstEntryPart_estimate {Y : ℕ} (hY : 2 ≤ Y) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ,
      ∀ ⦃x : ℕ⦄, x₀ ≤ x →
        Summable (fun n : ℕ => normalizationFirstEntryPart x Y n) ∧
          |(∑' n : ℕ, normalizationFirstEntryPart x Y n) - 1| ≤ C / Real.log (x : ℝ) := by
  rcases firstEntryTailApproximation (Y := Y) hY with ⟨C0, hC0pos, happrox⟩
  let x₀ : ℕ := max 3 ⌈Real.exp (C0 + 1)⌉₊
  refine ⟨1 + 2 * C0, by linarith, x₀, ?_⟩
  intro x hxx
  have hx3 : 3 ≤ x := le_trans (le_max_left 3 ⌈Real.exp (C0 + 1)⌉₊) hxx
  have hx2 : 2 ≤ x := le_trans (by decide : 2 ≤ 3) hx3
  have hx1 : 1 ≤ x := le_trans (by decide : 1 ≤ 3) hx3
  have hexp_le_x : Real.exp (C0 + 1) ≤ (x : ℝ) := by
    calc
      Real.exp (C0 + 1) ≤ (⌈Real.exp (C0 + 1)⌉₊ : ℝ) := by exact_mod_cast Nat.le_ceil _
      _ ≤ (x₀ : ℝ) := by
          exact_mod_cast (le_max_right 3 ⌈Real.exp (C0 + 1)⌉₊)
      _ ≤ (x : ℝ) := by exact_mod_cast hxx
  have hxlog_pos : 0 < Real.log (x : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hx3))
  have hxlog_ne : Real.log (x : ℝ) ≠ 0 := hxlog_pos.ne'
  have hxlog_ge : C0 + 1 ≤ Real.log (x : ℝ) := by
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hexp_le_x
  have hsummable :
      ∀ {m : ℕ}, 1 ≤ m → m < x →
        Summable (fun q : ℕ =>
          if entryThreshold x Y m ≤ q then
            Λ q / ((q : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)
          else 0) := by
    intro m hm1 hmx
    by_contra hs
    have hzero : firstEntryTail x Y m = 0 := by
      rw [firstEntryTail, tsum_eq_zero_of_not_summable hs]
    have hmain : 0 < 1 / Real.log (x : ℝ) - C0 / (Real.log (x : ℝ)) ^ 2 := by
      field_simp [hxlog_ne]
      nlinarith
    have hleft := (abs_le.mp (happrox hx2 hm1 hmx)).1
    rw [hzero] at hleft
    linarith
  have hfirst := hasSum_normalizationFirstEntryPart (x := x) (Y := Y) hx1 hsummable
  have hfirst_eq :
      ∑' n : ℕ, normalizationFirstEntryPart x Y n =
        ∑ m ∈ Finset.Icc 1 (x - 1), (1 / (m : ℝ)) * firstEntryTail x Y m := hfirst.tsum_eq
  let H : ℝ := ∑ m ∈ Finset.Icc 1 (x - 1), (1 : ℝ) / m
  let E : ℝ :=
    ∑ m ∈ Finset.Icc 1 (x - 1),
      (1 / (m : ℝ)) * (firstEntryTail x Y m - 1 / Real.log (x : ℝ))
  have hHabs : |H - Real.log (x : ℝ)| ≤ 1 := by
    simpa [H] using abs_sum_Icc_inv_sub_log_le_one x hx1
  have hEbound :
      |E| ≤ (2 * C0) / Real.log (x : ℝ) := by
    have hnorm :
        ‖∑ m ∈ Finset.Icc 1 (x - 1),
            (1 / (m : ℝ)) * (firstEntryTail x Y m - 1 / Real.log (x : ℝ))‖
          ≤ ∑ m ∈ Finset.Icc 1 (x - 1), (C0 / (Real.log (x : ℝ)) ^ 2) * (1 / (m : ℝ)) := by
      refine norm_sum_le_of_le _ ?_
      intro m hm
      rcases Finset.mem_Icc.mp hm with ⟨hm1, hmx_le⟩
      have hmx : m < x := by omega
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg]
      · simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_le_mul_of_nonneg_left (happrox hx2 hm1 hmx) (by positivity : 0 ≤ 1 / (m : ℝ)))
      · positivity
    calc
      |E| ≤ (C0 / (Real.log (x : ℝ)) ^ 2) * H := by
        simpa [E, H, Finset.mul_sum, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using
          hnorm
      _ ≤ (C0 / (Real.log (x : ℝ)) ^ 2) * (Real.log (x : ℝ) + 1) := by
            gcongr
            linarith [(abs_le.mp hHabs).2]
      _ ≤ (2 * C0) / Real.log (x : ℝ) := by
            field_simp [hxlog_ne]
            nlinarith [hC0pos, hxlog_ge]
  have hsplit :
      ∑ m ∈ Finset.Icc 1 (x - 1), (1 / (m : ℝ)) * firstEntryTail x Y m =
        (1 / Real.log (x : ℝ)) * H + E := by
    calc
      ∑ m ∈ Finset.Icc 1 (x - 1), (1 / (m : ℝ)) * firstEntryTail x Y m
        = ∑ m ∈ Finset.Icc 1 (x - 1),
            ((1 / Real.log (x : ℝ)) * (1 / (m : ℝ)) +
              (1 / (m : ℝ)) * (firstEntryTail x Y m - 1 / Real.log (x : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              ring
      _ = (1 / Real.log (x : ℝ)) * H + E := by
            simp [H, E, Finset.sum_add_distrib, Finset.mul_sum, mul_comm]
  refine ⟨hfirst.summable, ?_⟩
  calc
    |(∑' n : ℕ, normalizationFirstEntryPart x Y n) - 1|
      = |((H - Real.log (x : ℝ)) / Real.log (x : ℝ)) + E| := by
          rw [hfirst_eq, hsplit]
          have hrew :
              (1 / Real.log (x : ℝ)) * H + E - 1 =
                ((H - Real.log (x : ℝ)) / Real.log (x : ℝ)) + E := by
            field_simp [hxlog_ne]
            ring
          simpa [sub_eq_add_neg] using congrArg abs hrew
    _ ≤ |(H - Real.log (x : ℝ)) / Real.log (x : ℝ)| + |E| := abs_add_le _ _
    _ ≤ 1 / Real.log (x : ℝ) + |E| := by
          gcongr
          rw [abs_div, abs_of_pos hxlog_pos]
          exact div_le_div_of_nonneg_right hHabs (le_of_lt hxlog_pos)
    _ ≤ 1 / Real.log (x : ℝ) + (2 * C0) / Real.log (x : ℝ) := by
          gcongr
    _ = (1 + 2 * C0) / Real.log (x : ℝ) := by ring
end PrimitiveSetsAboveX



/-!
# Markov-chain lemmas for primitive sets above `x`

This file proves the main analytic estimates for the Markov-chain construction: the asymptotic
control of `R_Y(m)`, the eventual sub-Markov bound on the transition rows, the eventual estimate
for the normalization constant `B_x`, and the explicit closed formula for the visiting
probabilities.

## Main statements

* `subMarkovRowSumBound`
* `normalizationEstimate`
* `visitProbabilityFormula`
-/


/- ! Markov-chain identities and row-sum bounds used in the proof. -/
open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/-- If a summand vanishes off the divisors of `n`, its infinite sum is the finite sum over
`n.divisors`. -/
lemma tsum_eq_sum_divisors_of_nondivisors_zero {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {n : ℕ} (hn : 0 < n) (f : ℕ → α) (hf : ∀ q, ¬ q ∣ n → f q = 0) :
    (∑' q : ℕ, f q) = n.divisors.sum f := by
  refine tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := n.divisors) ?_
  intro q hq
  exact hf q (by grind only [= Nat.mem_divisors])

/-- If a divisor condition is bundled into the summand, the `tsum` reduces to the finite divisor
sum with that condition removed. -/
lemma tsum_eq_sum_divisors_of_dvd_and {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {n : ℕ} (hn : 0 < n) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → α) :
    (∑' q : ℕ, if q ∣ n ∧ P q then f q else 0) =
      n.divisors.sum (fun q => if P q then f q else 0) := by
  calc
    (∑' q : ℕ, if q ∣ n ∧ P q then f q else 0) =
        n.divisors.sum (fun q => if q ∣ n ∧ P q then f q else 0) := by
          refine tsum_eq_sum_divisors_of_nondivisors_zero (n := n) hn _ ?_
          intro q hq
          simp [hq]
    _ = n.divisors.sum (fun q => if P q then f q else 0) := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          grind only [= Nat.mem_divisors]

/-- Rewriting `R_Y(m)` as `log m` times the tail sum isolates the input from `tailEstimate`. -/
private lemma ryEqLogMulTailSum (Y m : ℕ) :
    ry Y m = Real.log (m : ℝ) * tailSum m Y := by
  calc
    ry Y m =
        ∑' q : ℕ,
          Real.log (m : ℝ) *
            (if Y ≤ q then Λ q / ((q : ℝ) * Real.log ((m * q : ℕ) : ℝ) ^ 2) else 0) := by
          refine tsum_congr ?_
          intro q
          by_cases hq : Y ≤ q <;>
            simp [hq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ = Real.log (m : ℝ) * tailSum m Y := by
          rw [tailSum, tsum_mul_left]

/-- Rewriting the main term gives `R_Y(m) = 1 - log Y / log (mY) + O(1 / log m)`. -/
private lemma ryApproximation :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃Y m : ℕ⦄, 2 ≤ Y → 2 ≤ m →
        |ry Y m - (1 - Real.log (Y : ℝ) / Real.log ((m * Y : ℕ) : ℝ))| ≤
          C / Real.log (m : ℝ) := by
  rcases tailEstimate with ⟨C, hCpos, htail⟩
  refine ⟨C, hCpos, ?_⟩
  intro Y m hY hm
  have hm1 : 1 ≤ m := le_trans (by decide : 1 ≤ 2) hm
  have htail' := htail hm1 hY
  have hm_log_nonneg : 0 ≤ Real.log (m : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hm1)
  have hm_log_pos : 0 < Real.log (m : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hm))
  have hlogMY_pos : 0 < Real.log ((m * Y : ℕ) : ℝ) := by
    exact Real.log_pos (by
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 4) (show 4 ≤ m * Y by
        simpa using Nat.mul_le_mul hm hY)))
  have hsq : (Real.log (m : ℝ)) ^ 2 ≤ (Real.log ((m * Y : ℕ) : ℝ)) ^ 2 := by
    have hlog_le : Real.log (m : ℝ) ≤ Real.log ((m * Y : ℕ) : ℝ) := by
      refine Real.log_le_log ?_ ?_
      · exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
      · exact_mod_cast (by
          have hY1 : 1 ≤ Y := le_trans (by decide : 1 ≤ 2) hY
          simpa using Nat.mul_le_mul_left m hY1 : m ≤ m * Y)
    nlinarith
  have hmain :
      Real.log (m : ℝ) * (1 / Real.log ((m * Y : ℕ) : ℝ)) =
        1 - Real.log (Y : ℝ) / Real.log ((m * Y : ℕ) : ℝ) := by
    have hlogMY_ne : Real.log ((m * Y : ℕ) : ℝ) ≠ 0 := hlogMY_pos.ne'
    have hlog_mul :
        Real.log ((m * Y : ℕ) : ℝ) = Real.log (m : ℝ) + Real.log (Y : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul]
      all_goals positivity
    field_simp [hlogMY_ne]
    linarith
  rw [ryEqLogMulTailSum]
  calc
    |Real.log (m : ℝ) * tailSum m Y - (1 - Real.log (Y : ℝ) / Real.log ((m * Y : ℕ) : ℝ))|
      = |Real.log (m : ℝ) * (tailSum m Y - 1 / Real.log ((m * Y : ℕ) : ℝ))| := by
          rw [← hmain, mul_sub]
    _ = |Real.log (m : ℝ)| * |tailSum m Y - 1 / Real.log ((m * Y : ℕ) : ℝ)| := by
      rw [abs_mul]
    _ ≤ |Real.log (m : ℝ)| * (C / Real.log ((m * Y : ℕ) : ℝ) ^ 2) := by
      gcongr
    _ ≤ C / Real.log (m : ℝ) := by
      rw [abs_of_nonneg hm_log_nonneg]
      have hm_log_ne : Real.log (m : ℝ) ≠ 0 := hm_log_pos.ne'
      have hlogMY_ne : Real.log ((m * Y : ℕ) : ℝ) ≠ 0 := hlogMY_pos.ne'
      field_simp [hm_log_ne, hlogMY_ne]
      exact hsq

/-- Choosing the cutoff `Y` large enough makes every sufficiently late transition row sum at most
`1`, so the outgoing weights define an eventual sub-Markov chain. -/
lemma subMarkovRowSumBound :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃Y : ℕ⦄, Real.exp (2 * C) < (Y : ℝ) →
        ∃ x₀ : ℕ, Y ≤ x₀ ∧
          ∀ ⦃m : ℕ⦄, x₀ ≤ m → (∑' q : ℕ, transitionWeight Y m q) ≤ 1 := by
  rcases ryApproximation with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro Y hYlarge
  refine ⟨Y, le_rfl, ?_⟩
  intro m hm
  have hY_gt_one : (1 : ℝ) < (Y : ℝ) := by
    exact lt_trans
      (by simpa using Real.one_lt_exp_iff.2 (by nlinarith [hCpos]))
      hYlarge
  have hY_nat_gt_one : 1 < Y := by
    exact_mod_cast hY_gt_one
  have hY2 : 2 ≤ Y := by
    simpa using hY_nat_gt_one
  have hm2 : 2 ≤ m := le_trans hY2 hm
  have hm_log_pos : 0 < Real.log (m : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hm2))
  have hmY_ge_four : 4 ≤ m * Y := Nat.mul_le_mul hm2 hY2
  have hlogMY_pos : 0 < Real.log ((m * Y : ℕ) : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 4) hmY_ge_four))
  have hupper : ry Y m ≤ 1 - Real.log (Y : ℝ) / Real.log ((m * Y : ℕ) : ℝ) +
      C / Real.log (m : ℝ) := by
    linarith [(abs_le.mp (hC hY2 hm2)).2]
  rw [show (∑' q : ℕ, transitionWeight Y m q) = ry Y m by simp [transitionWeight, ry]]
  refine hupper.trans ?_
  have hmul_le_sq : (m * Y : ℕ) ≤ m * m := Nat.mul_le_mul_left m hm
  have hlogMY_le : Real.log ((m * Y : ℕ) : ℝ) ≤ 2 * Real.log (m : ℝ) := by
    have hcast_le : ((m * Y : ℕ) : ℝ) ≤ (m : ℝ) * m := by
      exact_mod_cast hmul_le_sq
    calc
      Real.log ((m * Y : ℕ) : ℝ) ≤ Real.log ((m : ℝ) * m) :=
        Real.log_le_log
          (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hmY_ge_four))
          hcast_le
      _ = 2 * Real.log (m : ℝ) := by
        rw [Real.log_mul]
        · ring
        · positivity
        · positivity
  have htwoC_lt_logY : 2 * C < Real.log (Y : ℝ) := by
    simpa [Real.log_exp] using (Real.log_lt_log (Real.exp_pos _) hYlarge)
  have herror :
      C / Real.log (m : ℝ) ≤ Real.log (Y : ℝ) / Real.log ((m * Y : ℕ) : ℝ) := by
    have hm_log_ne : Real.log (m : ℝ) ≠ 0 := hm_log_pos.ne'
    have hlogMY_ne : Real.log ((m * Y : ℕ) : ℝ) ≠ 0 := hlogMY_pos.ne'
    field_simp [hm_log_ne, hlogMY_ne]
    nlinarith
  linarith

/-- For each fixed `Y ≥ 2`, the normalizing constants satisfy the asymptotic estimate
`B_x = 1 + O(1 / log x)`. -/
lemma normalizationEstimate {Y : ℕ} (hY : 2 ≤ Y) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ,
      ∀ ⦃x : ℕ⦄, x₀ ≤ x →
        |normalizationConstant x Y - 1| ≤ C / Real.log (x : ℝ) := by
  let S : ℝ := ∑ q ∈ Finset.Ico 1 Y, Λ q / (q : ℝ)
  have hS_nonneg : 0 ≤ S :=
    Finset.sum_nonneg fun q hq =>
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  rcases normalizationFirstEntryPart_estimate (Y := Y) hY with
    ⟨Centry, hCentry_pos, xentry, hentry⟩
  refine ⟨2 * S + Centry, by nlinarith, max 3 xentry, ?_⟩
  intro x hxx
  have hx3 : 3 ≤ x := le_trans (le_max_left 3 xentry) hxx
  have hsmall := summable_normalizationSmallPrimePart_and_tsum_le (x := x) (Y := Y) hx3
  have hxentry : xentry ≤ x := le_trans (le_max_right 3 xentry) hxx
  have hfirst := hentry hxentry
  have hsmall_nonneg : 0 ≤ ∑' n : ℕ, normalizationSmallPrimePart x Y n :=
    tsum_nonneg fun n => by
      by_cases hn : x ≤ n
      · simp [normalizationSmallPrimePart, hn, smallPrimeEntryWeight_nonneg]
      · simp [normalizationSmallPrimePart, hn]
  have hdecomp :
      normalizationConstant x Y =
        (∑' n : ℕ, normalizationSmallPrimePart x Y n) +
          (∑' n : ℕ, normalizationFirstEntryPart x Y n) := by
    rw [normalizationConstant_eq_tsum_parts, Summable.tsum_add hsmall.1 hfirst.1]
  calc
    |normalizationConstant x Y - 1|
      = |(∑' n : ℕ, normalizationSmallPrimePart x Y n) +
          ((∑' n : ℕ, normalizationFirstEntryPart x Y n) - 1)| := by
            rw [hdecomp]
            congr 1
            ring_nf
    _ ≤ ∑' n : ℕ, normalizationSmallPrimePart x Y n +
          |(∑' n : ℕ, normalizationFirstEntryPart x Y n) - 1| := by
            simpa [abs_of_nonneg hsmall_nonneg] using
              abs_add_le (∑' n : ℕ, normalizationSmallPrimePart x Y n)
                ((∑' n : ℕ, normalizationFirstEntryPart x Y n) - 1)
    _ ≤ (2 * S) / Real.log (x : ℝ) + Centry / Real.log (x : ℝ) :=
          add_le_add hsmall.2 hfirst.2
    _ = (2 * S + Centry) / Real.log (x : ℝ) := by ring

/--
Reindexing the last-jump recurrence by the parent state shows that only divisors `m ∣ n` can
contribute to the probability of visiting `n`.
-/
lemma visitProbabilityRecurrence_sum_parents {x Y : ℕ} (chain : MarkovLayer x Y) {n : ℕ}
    (hxn : x ≤ n) (hn : 0 < n) :
    chain.visitProbability n =
      initialDistribution x Y n +
        n.divisors.sum (fun m =>
          if x ≤ m ∧ Y ≤ n / m then
            chain.visitProbability m * transitionWeight Y m (n / m)
          else 0) := by
  have hswap :
      n.divisors.sum (fun q =>
        if Y ≤ q ∧ x ≤ n / q then
          chain.visitProbability (n / q) * transitionWeight Y (n / q) q
        else 0) =
        n.divisors.sum (fun m =>
          if x ≤ m ∧ Y ≤ n / m then
            chain.visitProbability m * transitionWeight Y m (n / m)
          else 0) := by
    simpa [and_left_comm, and_comm] using
      ((Nat.sum_divisorsAntidiagonal'
          (n := n)
          (f := fun m q =>
            if x ≤ m ∧ Y ≤ q then
              chain.visitProbability m * transitionWeight Y m q
            else 0)).symm.trans
        (Nat.sum_divisorsAntidiagonal
          (n := n)
          (f := fun m q =>
            if x ≤ m ∧ Y ≤ q then
              chain.visitProbability m * transitionWeight Y m q
            else 0)))
  calc
    chain.visitProbability n =
        initialDistribution x Y n +
          ∑' q : ℕ,
            if Y ≤ q ∧ q ∣ n ∧ x ≤ n / q then
              chain.visitProbability (n / q) * transitionWeight Y (n / q) q
            else 0 := by
              simpa using (chain.visitProbabilityRecurrence (n := n) hxn)
    _ = initialDistribution x Y n +
          n.divisors.sum (fun q =>
            if Y ≤ q ∧ x ≤ n / q then
              chain.visitProbability (n / q) * transitionWeight Y (n / q) q
            else 0) := by
          simpa [and_assoc, and_left_comm, and_comm] using
            (tsum_eq_sum_divisors_of_dvd_and (n := n) hn
              (P := fun q => Y ≤ q ∧ x ≤ n / q)
              (fun q => chain.visitProbability (n / q) * transitionWeight Y (n / q) q))
    _ = initialDistribution x Y n +
          n.divisors.sum (fun m =>
            if x ≤ m ∧ Y ≤ n / m then
              chain.visitProbability m * transitionWeight Y m (n / m)
            else 0) := by
          rw [hswap]

/--
For a proper parent `n / q`, any last-jump term with the explicit parent value simplifies to the
common factor `(1 / B_x) * (Λ(q) / (n log^2 n))`.
-/
lemma lastJumpContribution_eq_of_formula {x Y : ℕ} (hx : 2 ≤ x) {n q : ℕ}
    (hq : q ∈ n.divisors) (hqx : Y ≤ q ∧ x ≤ n / q) {v : ℝ}
    (hvisit :
      v = 1 / (normalizationConstant x Y * ((n : ℝ) / q) * Real.log ((n : ℝ) / q))) :
    v * transitionWeight Y (n / q) q =
      (1 / normalizationConstant x Y) *
        ((1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q) := by
  rcases hqx with ⟨hYq, hxq⟩
  have hdvd : q ∣ n := Nat.dvd_of_mem_divisors hq
  have hq_pos : 0 < q := Nat.pos_of_mem_divisors hq
  have hcast_div : ((n / q : ℕ) : ℝ) = (n : ℝ) / q :=
    Nat.cast_div hdvd (by exact_mod_cast hq_pos.ne')
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq_pos.ne'
  have hlog_ne : Real.log ((n : ℝ) / q) ≠ 0 := by
    rw [← hcast_div]
    have hnq2 : 2 ≤ n / q := le_trans hx hxq
    exact (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hnq2))).ne'
  rw [hvisit, transitionWeight, if_pos hYq, hcast_div]
  calc
    (1 / (normalizationConstant x Y * ((n : ℝ) / q) * Real.log ((n : ℝ) / q))) *
        ((Real.log ((n : ℝ) / q) / (Real.log (((n / q) * q : ℕ) : ℝ)) ^ 2) *
          (Λ q / (q : ℝ))) =
        (1 / normalizationConstant x Y) *
          ((1 / (((n : ℝ) / q) * Real.log ((n : ℝ) / q))) *
            ((Real.log ((n : ℝ) / q) / (Real.log (n : ℝ)) ^ 2) *
              (Λ q / (q : ℝ)))) := by
          grind only [Nat.div_mul_cancel hdvd]
    _ = (1 / normalizationConstant x Y) *
          ((1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q) := by
          congr 1
          field_simp [hlog_ne, hqR]

/--
The divisor decomposition of `log n` rewrites the explicit target formula as the normalized initial
mass plus the filtered von Mangoldt divisor sum.
-/
lemma formula_eq_initialDistribution_add_filteredVonMangoldt {x Y n : ℕ} :
    1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ)) =
      initialDistribution x Y n +
        (1 / normalizationConstant x Y) *
          n.divisors.sum (fun q =>
            if Y ≤ q ∧ x ≤ n / q then
              (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q
            else 0) := by
  calc
    1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ)) =
        (1 / normalizationConstant x Y) *
          ((1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) *
            (n.divisors.sum fun q => Λ q)) := by
          rw [ArithmeticFunction.vonMangoldt_sum (n := n)]
          grind only
    _ = (1 / normalizationConstant x Y) *
          (entryWeight x Y n +
            n.divisors.sum (fun q =>
              if Y ≤ q ∧ x ≤ n / q then
                (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q
              else 0)) := by
          congr 1
          simpa [entryWeightFactor] using
            (entryWeight_add_filtered_vonMangoldt_eq_entryWeightFactor_sum_divisors x Y n).symm
    _ = initialDistribution x Y n +
          (1 / normalizationConstant x Y) *
            n.divisors.sum (fun q =>
              if Y ≤ q ∧ x ≤ n / q then
                (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q
              else 0) := by
          simp [initialDistribution, div_eq_mul_inv, mul_add, mul_assoc, mul_left_comm, mul_comm]

/--
If every last-jump parent already has the explicit value `1 / (B_x n log n)`, then the recurrence
right-hand side collapses to the closed formula for the visit probability at `n`.
-/
lemma explicitFormula_eq_recurrence_rhs {x Y n : ℕ} (hx : 2 ≤ x) (hn : x ≤ n) {f : ℕ → ℝ}
    (hvisit :
      ∀ ⦃q : ℕ⦄, q ∈ n.divisors → Y ≤ q ∧ x ≤ n / q → q ≠ 1 →
        f (n / q) =
          1 / (normalizationConstant x Y * ((n : ℝ) / q) * Real.log ((n : ℝ) / q))) :
    1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ)) =
      initialDistribution x Y n +
        ∑' q : ℕ,
          if Y ≤ q ∧ q ∣ n ∧ x ≤ n / q then
            f (n / q) * transitionWeight Y (n / q) q
          else 0 := by
  have hn_pos : 0 < n := by omega
  have hrec :
      n.divisors.sum (fun q =>
        if Y ≤ q ∧ x ≤ n / q then
          f (n / q) * transitionWeight Y (n / q) q
        else 0) =
        (1 / normalizationConstant x Y) *
          n.divisors.sum (fun q =>
            if Y ≤ q ∧ x ≤ n / q then
              (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q
            else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro q hq
    by_cases hqx : Y ≤ q ∧ x ≤ n / q
    · by_cases hq1 : q = 1
      · subst hq1
        simp [transitionWeight, hqx]
      · simpa [hqx] using
          (lastJumpContribution_eq_of_formula (x := x) (Y := Y) (n := n) (q := q)
            hx hq hqx (v := f (n / q)) (hvisit hq hqx hq1))
    · simp [hqx]
  calc
    1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ)) =
        initialDistribution x Y n +
          (1 / normalizationConstant x Y) *
            n.divisors.sum (fun q =>
              if Y ≤ q ∧ x ≤ n / q then
                (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q
              else 0) := by
            simpa using
              formula_eq_initialDistribution_add_filteredVonMangoldt (x := x) (Y := Y) (n := n)
    _ = initialDistribution x Y n +
          n.divisors.sum (fun q =>
            if Y ≤ q ∧ x ≤ n / q then
              f (n / q) * transitionWeight Y (n / q) q
            else 0) := by
          rw [hrec]
    _ = initialDistribution x Y n +
          ∑' q : ℕ,
            if Y ≤ q ∧ q ∣ n ∧ x ≤ n / q then
              f (n / q) * transitionWeight Y (n / q) q
            else 0 := by
          congr 1
          simpa [and_assoc, and_left_comm, and_comm] using
            (tsum_eq_sum_divisors_of_dvd_and (n := n) hn_pos
              (P := fun q => Y ≤ q ∧ x ≤ n / q)
              (fun q => f (n / q) * transitionWeight Y (n / q) q)).symm

/--
The Markov layer visits each state `n ≥ x` with the explicit probability
`1 / (B_x n log n)`. The lower bound `2 ≤ x` guarantees that the logarithms in this formula are
positive.
-/
lemma visitProbabilityFormula {x Y : ℕ} (chain : MarkovLayer x Y) (hx : 2 ≤ x) {n : ℕ}
    (hn : x ≤ n) :
    chain.visitProbability n =
      1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ)) := by
  refine Nat.strong_induction_on n ?_ hn
  intro n ih hn
  rw [chain.visitProbabilityRecurrence (n := n) hn]
  symm
  refine explicitFormula_eq_recurrence_rhs (x := x) (Y := Y) (n := n) hx hn
    (f := chain.visitProbability) ?_
  intro q hq hqx hq1
  have hn_pos : 0 < n := by omega
  have hq_ne_zero : q ≠ 0 := (Nat.pos_of_mem_divisors hq).ne'
  have hlt : n / q < n := by
    have hq_gt_one : 1 < q := by omega
    exact Nat.div_lt_self hn_pos hq_gt_one
  have hcast_div : ((n / q : ℕ) : ℝ) = (n : ℝ) / q :=
    Nat.cast_div (Nat.dvd_of_mem_divisors hq) (by exact_mod_cast hq_ne_zero)
  simpa [hcast_div] using ih (n / q) hlt hqx.2

/-- Under the standing hypotheses `2 ≤ x` and `B_x > 0`, the visiting probabilities are
nonnegative on the state space `n ≥ x`. -/
lemma visitProbability_nonneg {x Y : ℕ} (chain : MarkovLayer x Y) (hx : 2 ≤ x)
    (hB : 0 < normalizationConstant x Y) {n : ℕ} (hn : x ≤ n) :
    0 ≤ chain.visitProbability n := by
  rw [visitProbabilityFormula chain hx hn]
  positivity

end PrimitiveSetsAboveX



/-!
# Rewriting the primitive weight using visit probabilities

This file records the exact algebraic bridge from the explicit visit-probability formula
`v_x(n) = 1 / (B_x n log n)` to the weighted series identity
`f(A) = B_x * ∑_{n ∈ A} v_x(n)`, and packages the final deterministic reduction from a
summable hit series to the logarithmic-series bound.

## Main statements

* `summable_indicatorLogSeries_and_tsum_le_of_hitMass`
-/


open scoped BigOperators

namespace PrimitiveSetsAboveX

/-- If the visit-probability series on `A` is summable and has total mass at most `1`, then the
logarithmic series on `A` is summable as well, and the normalization estimate converts this into
the final upper bound for `∑_{n ∈ A} 1 / (n log n)`. -/
theorem summable_indicatorLogSeries_and_tsum_le_of_hitMass
    {x Y : ℕ} (chain : MarkovLayer x Y) (hx : 2 ≤ x) {A : Set ℕ} (hA : A ⊆ Set.Ici x)
    (hB : 0 < normalizationConstant x Y)
    (hHitSummable : Summable (A.indicator (chain.visitProbability)))
    (hHit : (∑' n : ℕ, A.indicator (chain.visitProbability) n) ≤ 1)
    {C : ℝ} (hNorm : |normalizationConstant x Y - 1| ≤ C / Real.log (x : ℝ)) :
    Summable (A.indicator (fun m : ℕ => 1 / ((m : ℝ) * Real.log (m : ℝ)))) ∧
      (∑' m : ℕ, A.indicator (fun k : ℕ => 1 / ((k : ℝ) * Real.log (k : ℝ))) m) ≤
        1 + C / Real.log (x : ℝ) := by
  have hpoint (n : ℕ) :
      normalizationConstant x Y * A.indicator (chain.visitProbability) n =
        A.indicator (fun m : ℕ => 1 / ((m : ℝ) * Real.log (m : ℝ))) n := by
    by_cases hnA : n ∈ A
    · simp [hnA, visitProbabilityFormula chain hx (hA hnA)]
      grind only
    · simp [hnA]
  constructor
  · exact (hHitSummable.mul_left _).congr fun n =>
      hpoint n
  · have hWeight :
        (∑' m : ℕ, A.indicator (fun k : ℕ => 1 / ((k : ℝ) * Real.log (k : ℝ))) m) ≤
          normalizationConstant x Y := by
      calc
        ∑' m : ℕ, A.indicator (fun k : ℕ => 1 / ((k : ℝ) * Real.log (k : ℝ))) m
          = ∑' n : ℕ, normalizationConstant x Y * A.indicator (chain.visitProbability) n := by
              simpa using tsum_congr fun n => (hpoint n).symm
        _ = normalizationConstant x Y * ∑' n : ℕ, A.indicator (chain.visitProbability) n := by
              rw [tsum_mul_left]
        _ ≤ normalizationConstant x Y * 1 := by
              gcongr
        _ = normalizationConstant x Y := by ring
    refine hWeight.trans ?_
    have hupper : normalizationConstant x Y - 1 ≤ C / Real.log (x : ℝ) := (abs_le.mp hNorm).2
    linarith

end PrimitiveSetsAboveX



/-!
# Hit mass and final reductions

This file develops the `ENNReal` mass-flow layer behind the Markov-chain argument. It defines
exact-step arrival mass, surviving mass before the first hit of a set `A`, and the total first-hit
mass of `A`.

The central estimate is a telescope: if the restricted initial mass is at most `1` and each row of
the transition kernel has total mass at most `1`, then the total first-hit mass of `A` is at most
`1`. For primitive `A`, this is the visit-mass inequality used in the final argument, because finite
paths in the multiplicative chain can meet `A` at most once.

## Main definitions

* `initialMass`
* `transitionKernel`
* `arrivalMass`
* `survivingArrivalMass`
* `firstHitMassAtStep`
* `visitMass`

## Main statements

* `MarkovLayer.kernelRowBound`
* `tsum_initialMass_eq_one`
* `visitMass_le_of_bounds`
* `PrimitiveSet.summable_indicator_visitProbability_and_tsum_le_one_of_visitMass_le_one`
-/


open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/-- The normalized initial mass restricted to the state space `n ≥ x`. -/
noncomputable def initialMass (x Y n : ℕ) : ENNReal :=
  ENNReal.ofReal (if x ≤ n then initialDistribution x Y n else 0)

/--
The transition kernel on states `n ≥ x`, viewed as an `ENNReal`-valued mass function.

The state `m` can send mass to `n` only when `m ≥ x`, `m ∣ n`, and the quotient `n / m` is a
valid jump factor `q ≥ Y`.
-/
noncomputable def transitionKernel (x Y m n : ℕ) : ENNReal :=
  if x ≤ m ∧ m ∣ n ∧ Y ≤ n / m then
    ENNReal.ofReal (transitionWeight Y m (n / m))
  else
    0

/-- Exact-step arrival mass at state `n` after `k` steps in the multiplicative chain. -/
noncomputable def arrivalMass {x Y : ℕ} (chain : MarkovLayer x Y) : ℕ → ℕ → ENNReal
  | 0, n => initialMass x Y n
  | k + 1, n => ∑' m : ℕ, arrivalMass chain k m * transitionKernel x Y m n

/--
The surviving mass at state `n` after `k` steps, obtained by discarding every path that has already
hit `A`.
-/
noncomputable def survivingArrivalMass {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ) :
    ℕ → ℕ → ENNReal
  | 0, n => Aᶜ.indicator (initialMass x Y) n
  | k + 1, n =>
      Aᶜ.indicator
        (fun n => ∑' m : ℕ, survivingArrivalMass chain A k m * transitionKernel x Y m n) n

/--
The mass that first hits `A` exactly at step `k`.

For `k = 0` this is the initial mass already inside `A`, and for `k + 1` it is the mass
propagated from the surviving mass at step `k` into `A`.
-/
noncomputable def firstHitMassAtStep {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ) :
    ℕ → ENNReal
  | 0 => ∑' n : ℕ, A.indicator (initialMass x Y) n
  | k + 1 =>
      ∑' n : ℕ,
        A.indicator
          (fun n => ∑' m : ℕ, survivingArrivalMass chain A k m * transitionKernel x Y m n) n

/--
The total visit mass of `A`, counted by the first hit of `A` along each path. For primitive sets,
this agrees with the usual total mass of visits because finite multiplicative paths meet `A` at
most once.
-/
noncomputable def visitMass {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ) : ENNReal :=
  ∑' k : ℕ, firstHitMassAtStep chain A k

/-- The jump weights are nonnegative termwise. -/
private lemma transitionWeight_nonneg (Y m q : ℕ) : 0 ≤ transitionWeight Y m q := by
  by_cases hYq : Y ≤ q
  · by_cases hm : m = 0
    · simp [transitionWeight, hYq, hm]
    · have hm1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
      have hlog_nonneg : 0 ≤ Real.log (m : ℝ) := by
        positivity
      rw [transitionWeight, if_pos hYq]
      refine mul_nonneg ?_ ?_
      · exact div_nonneg hlog_nonneg (sq_nonneg _)
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  · simp [transitionWeight, hYq]

/--
For a fixed parent state `m`, the faithful kernel is the divisor-indicator reindexing of the jump
weights along the multiples of `m`.
-/
private lemma transitionKernel_eq_indicator {x Y m n : ℕ} (hm : x ≤ m) :
    transitionKernel x Y m n =
      Set.indicator {n : ℕ | m ∣ n}
        (fun n => ENNReal.ofReal (transitionWeight Y m (n / m))) n := by
  by_cases hdiv : m ∣ n
  · by_cases hYnm : Y ≤ n / m
    · simp [transitionKernel, hm, hdiv, hYnm, Set.indicator, transitionWeight]
    · simp [transitionKernel, hm, hdiv, hYnm, Set.indicator, transitionWeight]
  · simp [transitionKernel, hm, hdiv, Set.indicator]

/--
Reindexing the faithful kernel row along the multiples of `m` turns its `ENNReal` row sum into the
corresponding series of jump weights.
-/
private lemma tsum_transitionKernel_eq {x Y m : ℕ} (hm : x ≤ m) :
    (∑' n : ℕ, transitionKernel x Y m n) = ∑' q : ℕ, ENNReal.ofReal (transitionWeight Y m q) := by
  by_cases hm0 : m = 0
  · subst hm0
    have hx0 : x = 0 := le_antisymm hm (Nat.zero_le _)
    subst hx0
    simp [transitionKernel, transitionWeight]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    let e : ℕ ≃ {n : ℕ // m ∣ n} :=
      { toFun := fun q => ⟨m * q, dvd_mul_right m q⟩
        invFun := fun n => n.1 / m
        left_inv := by
          intro q
          simpa [Nat.mul_comm] using Nat.mul_div_left q hmpos
        right_inv := by
          intro n
          apply Subtype.ext
          simpa [Nat.mul_comm] using Nat.div_mul_cancel n.2 }
    calc
      (∑' n : ℕ, transitionKernel x Y m n)
        = ∑' n : {n : ℕ // m ∣ n}, ENNReal.ofReal (transitionWeight Y m (n.1 / m)) := by
            rw [show (fun n => transitionKernel x Y m n) =
              Set.indicator {n : ℕ | m ∣ n}
                (fun n => ENNReal.ofReal (transitionWeight Y m (n / m))) by
                  funext n
                  exact transitionKernel_eq_indicator (x := x) (Y := Y) (m := m) hm]
            simpa using (tsum_subtype {n : ℕ | m ∣ n}
              (fun n => ENNReal.ofReal (transitionWeight Y m (n / m)))).symm
      _ = ∑' q : ℕ, ENNReal.ofReal (transitionWeight Y m ((e q).1 / m)) := by
            simpa [e] using (Equiv.tsum_eq e
              (fun n : {n : ℕ // m ∣ n} => ENNReal.ofReal (transitionWeight Y m (n.1 / m)))).symm
      _ = ∑' q : ℕ, ENNReal.ofReal (transitionWeight Y m q) := by
            grind only [= Equiv.coe_fn_mk]

/--
The tail summand underlying `transitionWeight` is summable for every `m ≥ 1`. The proof uses
`tailEstimate` at a sufficiently large cutoff and then restores the finitely many missing terms.
-/
private lemma summable_transitionTailSummand (Y m : ℕ) (hm : 1 ≤ m) :
    Summable (fun q : ℕ =>
      if Y ≤ q then
        Λ q / ((q : ℝ) * Real.log ((m * q : ℕ) : ℝ) ^ 2)
      else
        0) := by
  rcases tailEstimate with ⟨C, hCpos, htail⟩
  let N : ℕ := max Y (Nat.ceil (Real.exp C) + 1)
  have hN_ge_Y : Y ≤ N := le_max_left Y (Nat.ceil (Real.exp C) + 1)
  have hN_ge_two : 2 ≤ N := by
    have hceil_pos : 0 < Nat.ceil (Real.exp C) := Nat.ceil_pos.2 (Real.exp_pos _)
    have hN0_ge_two : 2 ≤ Nat.ceil (Real.exp C) + 1 := by
      omega
    exact le_trans hN0_ge_two (le_max_right Y (Nat.ceil (Real.exp C) + 1))
  have hN_log_large : C < Real.log ((m * N : ℕ) : ℝ) := by
    calc
      C = Real.log (Real.exp C) := by rw [Real.log_exp]
      _ < Real.log ((m * N : ℕ) : ℝ) := by
        apply Real.log_lt_log (Real.exp_pos _)
        calc
          Real.exp C ≤ (Nat.ceil (Real.exp C) : ℝ) := by exact_mod_cast Nat.le_ceil _
          _ < (Nat.ceil (Real.exp C) + 1 : ℕ) := by
              exact_mod_cast Nat.lt_succ_self (Nat.ceil (Real.exp C))
          _ ≤ (N : ℝ) := by
              exact_mod_cast (le_max_right Y (Nat.ceil (Real.exp C) + 1))
          _ ≤ (((m * N : ℕ) : ℝ)) := by
              exact_mod_cast (by
                simpa [one_mul, Nat.mul_comm] using Nat.mul_le_mul_right N hm)
  have hN_log_pos : 0 < Real.log ((m * N : ℕ) : ℝ) := lt_trans hCpos hN_log_large
  have h_err_lt :
      C / Real.log ((m * N : ℕ) : ℝ) ^ 2 < 1 / Real.log ((m * N : ℕ) : ℝ) := by
    have hlog_ne : Real.log ((m * N : ℕ) : ℝ) ≠ 0 := hN_log_pos.ne'
    field_simp [hlog_ne]
    nlinarith
  have htail_pos : 0 < tailSum m N := by
    grind only [= abs.eq_1, = max_def]
  have hsN :
      Summable (fun q : ℕ =>
        if N ≤ q then
          Λ q / ((q : ℝ) * Real.log ((m * q : ℕ) : ℝ) ^ 2)
        else
          0) := by
    by_contra hsN
    have hzero : tailSum m N = 0 := by
      simpa [tailSum] using (tsum_eq_zero_of_not_summable hsN)
    exact htail_pos.ne' hzero
  rw [← Finset.summable_compl_iff (s := Finset.range N)]
  refine (hsN.subtype {q : ℕ | q ∉ Finset.range N}).congr ?_
  intro q
  have hq : N ≤ q := by
    simpa [Finset.mem_range, not_lt] using q.2
  have hYq : Y ≤ q := le_trans hN_ge_Y hq
  simp [hq, hYq]

/-- The transition-weight series is summable for every `m ≥ 1`. -/
private lemma summable_transitionWeight (Y m : ℕ) (hm : 1 ≤ m) :
    Summable (fun q : ℕ => transitionWeight Y m q) := by
  let g : ℕ → ℝ := fun q =>
    if Y ≤ q then
      Λ q / ((q : ℝ) * Real.log ((m * q : ℕ) : ℝ) ^ 2)
    else
      0
  simpa [g, transitionWeight, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (summable_transitionTailSummand Y m hm).mul_left (Real.log (m : ℝ))

/--
The real row-sum bound `∑_{q ≥ Y} p(m, mq) ≤ 1` transfers directly to the `ENNReal` kernel
`transitionKernel`, which is the form needed in the first-hit mass argument.
-/
theorem MarkovLayer.kernelRowBound {x Y : ℕ} (chain : MarkovLayer x Y) :
    ∀ ⦃m : ℕ⦄, x ≤ m → (∑' n : ℕ, transitionKernel x Y m n) ≤ 1 := by
  intro m hm
  by_cases hm0 : m = 0
  · subst hm0
    have hzero : ∀ n : ℕ, transitionKernel x Y 0 n = 0 := by
      intro n
      simp [transitionKernel, transitionWeight]
    rw [show (∑' n : ℕ, transitionKernel x Y 0 n) = 0 by
      exact (ENNReal.tsum_eq_zero).2 hzero]
    simp
  · have hmpos : 0 < m := Nat.pos_iff_ne_zero.mpr hm0
    have hm1 : 1 ≤ m := Nat.succ_le_of_lt hmpos
    have hs : Summable (fun q : ℕ => transitionWeight Y m q) :=
      summable_transitionWeight Y m hm1
    rw [tsum_transitionKernel_eq hm,
      ← ENNReal.ofReal_tsum_of_nonneg (transitionWeight_nonneg Y m) hs]
    exact_mod_cast chain.transitionSubMarkov hm

/-- Once `B_x > 0`, the restricted initial mass has total mass exactly `1`. -/
lemma tsum_initialMass_eq_one {x Y : ℕ} (hB : 0 < normalizationConstant x Y) :
    (∑' n : ℕ, initialMass x Y n) = 1 := by
  let f : ℕ → ℝ := fun n => if x ≤ n then entryWeight x Y n else 0
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    by_cases hn : x ≤ n
    · simpa [f, hn, entryWeight_eq_smallPrimeEntryWeight_add_firstEntryEntryWeight] using
        add_nonneg (smallPrimeEntryWeight_nonneg Y n) (firstEntryEntryWeight_nonneg x Y n)
    · simp [f, hn]
  have hf_summable : Summable f := by
    by_contra hf
    exact hB.ne' (by simpa [normalizationConstant, f] using (tsum_eq_zero_of_not_summable hf))
  calc
    ∑' n : ℕ, initialMass x Y n = ∑' n : ℕ, ENNReal.ofReal (f n / normalizationConstant x Y) := by
      refine tsum_congr ?_
      intro n
      by_cases hn : x ≤ n <;> simp [initialMass, f, initialDistribution, hn]
    _ = ENNReal.ofReal (∑' n : ℕ, f n / normalizationConstant x Y) := by
      rw [ENNReal.ofReal_tsum_of_nonneg
        (fun n => div_nonneg (hf_nonneg n) hB.le)
        (by simpa [div_eq_mul_inv] using hf_summable.mul_right ((normalizationConstant x Y)⁻¹))]
    _ = ENNReal.ofReal ((∑' n : ℕ, f n) / normalizationConstant x Y) := by
      congr 1
      rw [show (fun n : ℕ => f n / normalizationConstant x Y) =
        fun n => f n * (normalizationConstant x Y)⁻¹ by
          funext n
          simp [div_eq_mul_inv]]
      rw [tsum_mul_right]
      simp [div_eq_mul_inv]
    _ = 1 := by
      rw [show ∑' n : ℕ, f n = normalizationConstant x Y by simp [normalizationConstant, f]]
      field_simp [hB.ne']
      simp
/-- A kernel term landing below `x` is zero once `Y ≥ 1` and `x > 0`. -/
private lemma transitionKernel_eq_zero_of_lt {x Y m n : ℕ} (hY : 1 ≤ Y) (hn : n < x) :
    transitionKernel x Y m n = 0 := by
  by_cases hcond : x ≤ m ∧ m ∣ n ∧ Y ≤ n / m
  · have hqm : 1 ≤ n / m := le_trans hY hcond.2.2
    have hm_le_prod : m ≤ m * (n / m) := by
      simpa [one_mul] using Nat.mul_le_mul_left m hqm
    have hprod_le_n : m * (n / m) ≤ n := Nat.mul_div_le n m
    lia
  · simp [transitionKernel, hcond]

/-- States below `x` carry no surviving mass either. -/
private lemma survivingArrivalMass_eq_zero_of_lt {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ)
    (hx : 0 < x) (hY : 1 ≤ Y) :
    ∀ k {n : ℕ}, n < x → survivingArrivalMass chain A k n = 0
  | 0, n, hn => by
      by_cases hnA : n ∈ A <;> simp [survivingArrivalMass, initialMass, hnA, hn.not_ge]
  | k + 1, n, hn => by
      by_cases hnA : n ∈ A
      · simp [survivingArrivalMass, Set.indicator, hnA]
      · rw [survivingArrivalMass]
        have hnAc : n ∈ Aᶜ := by simpa using hnA
        rw [Set.indicator_of_mem hnAc]
        apply (ENNReal.tsum_eq_zero).2
        intro m
        by_cases hm : x ≤ m
        · simp [transitionKernel_eq_zero_of_lt (m := m) hY hn]
        · simp [survivingArrivalMass_eq_zero_of_lt chain A hx hY k (lt_of_not_ge hm)]

/-- The initial distribution is nonnegative once `B_x` is positive. -/
private lemma initialDistribution_nonneg {x Y n : ℕ} (hB : 0 < normalizationConstant x Y) :
    0 ≤ initialDistribution x Y n := by
  have hentry : 0 ≤ entryWeight x Y n := by
    rw [entryWeight_eq_smallPrimeEntryWeight_add_firstEntryEntryWeight]
    exact add_nonneg (smallPrimeEntryWeight_nonneg Y n) (firstEntryEntryWeight_nonneg x Y n)
  exact div_nonneg hentry hB.le

/--
If no element of `A` divides `n`, then every path arriving at `n` has avoided `A`, so the
surviving mass at `n` agrees with the unrestricted arrival mass.
-/
private lemma survivingArrivalMass_eq_arrivalMass_of_no_dvd {x Y : ℕ} (chain : MarkovLayer x Y)
    (A : Set ℕ) :
    ∀ k {n : ℕ}, (∀ ⦃a : ℕ⦄, a ∈ A → a ∣ n → False) →
      survivingArrivalMass chain A k n = arrivalMass chain k n
  | 0, n, hNo => by
      have hnA : n ∉ A := by
        intro hnA
        exact hNo hnA dvd_rfl
      simp [survivingArrivalMass, arrivalMass, hnA]
  | k + 1, n, hNo => by
      have hnA : n ∉ A := by
        intro hnA
        exact hNo hnA dvd_rfl
      simpa [survivingArrivalMass, arrivalMass, hnA] using
        (tsum_congr fun m => by
          by_cases hcond : x ≤ m ∧ m ∣ n ∧ Y ≤ n / m
          · have hNo_m : ∀ ⦃a : ℕ⦄, a ∈ A → a ∣ m → False := by
              intro a haA hadivm
              exact hNo haA (dvd_trans hadivm hcond.2.1)
            simp [transitionKernel, hcond,
              survivingArrivalMass_eq_arrivalMass_of_no_dvd chain A k hNo_m]
          · simp [transitionKernel, hcond])

/--
For a fixed target `n`, the only possible parents are the divisors `m ∣ n`, so the step
`k + 1` arrival mass is a finite parent sum.
-/
private lemma arrivalMass_succ_sum_parents {x Y : ℕ} (chain : MarkovLayer x Y) {k n : ℕ}
    (hn : 0 < n) :
    arrivalMass chain (k + 1) n =
      n.divisors.sum (fun m =>
        if x ≤ m ∧ Y ≤ n / m then
          arrivalMass chain k m * ENNReal.ofReal (transitionWeight Y m (n / m))
        else 0) := by
  calc
    arrivalMass chain (k + 1) n =
        ∑' m : ℕ,
          if x ≤ m ∧ m ∣ n ∧ Y ≤ n / m then
            arrivalMass chain k m * ENNReal.ofReal (transitionWeight Y m (n / m))
      else 0 := by
            simp [arrivalMass, transitionKernel, and_left_comm, mul_comm]
    _ = n.divisors.sum (fun m =>
          if x ≤ m ∧ Y ≤ n / m then
            arrivalMass chain k m * ENNReal.ofReal (transitionWeight Y m (n / m))
          else 0) := by
          simpa [and_assoc, and_left_comm, and_comm] using
            (tsum_eq_sum_divisors_of_dvd_and hn
              (P := fun m => x ≤ m ∧ Y ≤ n / m)
              (fun m =>
                arrivalMass chain k m * ENNReal.ofReal (transitionWeight Y m (n / m))))

/--
The total arrival mass at `n` satisfies the same parent-state recurrence as the visit
probability, but now as an `ENNReal` identity.
-/
private lemma tsum_arrivalMass_eq_initial_add_parentSum {x Y : ℕ} (chain : MarkovLayer x Y)
    {n : ℕ}
    (hn : 0 < n) :
    (∑' k : ℕ, arrivalMass chain k n) =
      initialMass x Y n +
        n.divisors.sum (fun m =>
          if x ≤ m ∧ Y ≤ n / m then
            (∑' k : ℕ, arrivalMass chain k m) * ENNReal.ofReal (transitionWeight Y m (n / m))
          else 0) := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  calc
    arrivalMass chain 0 n + ∑' k : ℕ, arrivalMass chain (k + 1) n
      = initialMass x Y n + ∑' k : ℕ, arrivalMass chain (k + 1) n := by
          simp [arrivalMass]
    _ = initialMass x Y n +
          ∑' k : ℕ,
            n.divisors.sum (fun m =>
              if x ≤ m ∧ Y ≤ n / m then
                arrivalMass chain k m * ENNReal.ofReal (transitionWeight Y m (n / m))
              else 0) := by
            congr 1
            apply tsum_congr
            intro k
            exact arrivalMass_succ_sum_parents chain hn
    _ = initialMass x Y n +
          n.divisors.sum (fun m =>
            ∑' k : ℕ,
              if x ≤ m ∧ Y ≤ n / m then
                arrivalMass chain k m * ENNReal.ofReal (transitionWeight Y m (n / m))
              else 0) := by
            congr 1
            exact Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)
    _ = initialMass x Y n +
          n.divisors.sum (fun m =>
            if x ≤ m ∧ Y ≤ n / m then
              (∑' k : ℕ, arrivalMass chain k m) * ENNReal.ofReal (transitionWeight Y m (n / m))
            else 0) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro m hm
            by_cases hcond : x ≤ m ∧ Y ≤ n / m
            · simp [hcond, ENNReal.tsum_mul_right]
            · simp [hcond]

private lemma lt_of_dvd_of_two_le_div {m n Y : ℕ} (hmn : m ∣ n) (hY : 2 ≤ Y)
    (hYm : Y ≤ n / m) : m < n := by
  have hm_pos : 0 < m := by
    by_contra hm_pos
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm_pos
    have : Y ≤ 0 := by simpa [hm0] using hYm
    omega
  have hmul : m * 2 ≤ n := by
    calc
      m * 2 ≤ m * (n / m) := Nat.mul_le_mul_left _ (le_trans hY hYm)
      _ = n := Nat.mul_div_cancel' hmn
  omega

/--
Summing the exact-step arrival masses recovers the visit probability. This is the bridge from the
mass-flow formalism to `visitProbability`.
-/
private lemma tsum_arrivalMass_eq_ofReal_visitProbability {x Y : ℕ} (chain : MarkovLayer x Y)
    (hx : 2 ≤ x) (hY : 2 ≤ Y) (hB : 0 < normalizationConstant x Y) {n : ℕ} (hn : x ≤ n) :
    (∑' k : ℕ, arrivalMass chain k n) = ENNReal.ofReal (chain.visitProbability n) := by
  refine Nat.strong_induction_on n ?_ hn
  intro n ih hn
  have hn_pos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) (le_trans hx hn)
  have hinit :
      initialMass x Y n = ENNReal.ofReal (initialDistribution x Y n) := by
    simp [initialMass, hn]
  have harr :=
    tsum_arrivalMass_eq_initial_add_parentSum chain hn_pos
  rw [hinit] at harr
  have hterm_nonneg :
      ∀ m ∈ n.divisors, 0 ≤
        if x ≤ m ∧ Y ≤ n / m then
          chain.visitProbability m * transitionWeight Y m (n / m)
        else 0 := by
    intro m hm
    by_cases hcond : x ≤ m ∧ Y ≤ n / m
    · simpa [hcond] using
        mul_nonneg (visitProbability_nonneg chain hx hB hcond.1)
          (transitionWeight_nonneg Y m (n / m))
    · simp [hcond]
  have hsum_nonneg :
      0 ≤ n.divisors.sum (fun m =>
        if x ≤ m ∧ Y ≤ n / m then
          chain.visitProbability m * transitionWeight Y m (n / m)
        else 0) :=
    Finset.sum_nonneg fun m hm => hterm_nonneg m hm
  have hvisit :
      ENNReal.ofReal (chain.visitProbability n) =
        ENNReal.ofReal (initialDistribution x Y n) +
          n.divisors.sum (fun m =>
            if x ≤ m ∧ Y ≤ n / m then
              ENNReal.ofReal (chain.visitProbability m * transitionWeight Y m (n / m))
            else 0) := by
    simpa [apply_ite ENNReal.ofReal,
      ENNReal.ofReal_add (initialDistribution_nonneg hB) hsum_nonneg,
      ENNReal.ofReal_sum_of_nonneg
        (s := n.divisors)
        (f := fun m =>
          if x ≤ m ∧ Y ≤ n / m then
            chain.visitProbability m * transitionWeight Y m (n / m)
          else 0)
        hterm_nonneg] using
      congrArg ENNReal.ofReal (visitProbabilityRecurrence_sum_parents chain hn hn_pos)
  calc
    (∑' k : ℕ, arrivalMass chain k n) =
        ENNReal.ofReal (initialDistribution x Y n) +
          n.divisors.sum (fun m =>
            if x ≤ m ∧ Y ≤ n / m then
              (∑' k : ℕ, arrivalMass chain k m) *
                ENNReal.ofReal (transitionWeight Y m (n / m))
            else 0) := harr
    _ = ENNReal.ofReal (initialDistribution x Y n) +
          n.divisors.sum (fun m =>
            if x ≤ m ∧ Y ≤ n / m then
              ENNReal.ofReal (chain.visitProbability m * transitionWeight Y m (n / m))
            else 0) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro m hm
            by_cases hcond : x ≤ m ∧ Y ≤ n / m
            · have hm_lt_n : m < n := by
                exact lt_of_dvd_of_two_le_div (Nat.dvd_of_mem_divisors hm) hY hcond.2
              rw [ih m hm_lt_n hcond.1]
              rw [ENNReal.ofReal_mul (visitProbability_nonneg chain hx hB hcond.1)]
            · simp [hcond]
    _ = ENNReal.ofReal (chain.visitProbability n) := hvisit.symm

/--
For a primitive set, every arrival in `A` is already a first hit of `A`, because a multiplicative
path cannot contain two distinct elements of a primitive set.
-/
private lemma PrimitiveSet.firstHitMassAtStep_eq_tsum_indicator_arrivalMass {x Y : ℕ}
    (chain : MarkovLayer x Y) {A : Set ℕ} (hA : PrimitiveSet A) (hY : 2 ≤ Y) :
    ∀ k : ℕ,
      firstHitMassAtStep chain A k = ∑' n : ℕ, A.indicator (arrivalMass chain k) n
  | 0 => by
      rfl
  | k + 1 => by
      apply tsum_congr
      intro n
      by_cases hnA : n ∈ A
      · simpa [firstHitMassAtStep, arrivalMass, hnA] using
          (tsum_congr fun m => by
            by_cases hcond : x ≤ m ∧ m ∣ n ∧ Y ≤ n / m
            · have hNo_m : ∀ ⦃a : ℕ⦄, a ∈ A → a ∣ m → False := by
                intro a haA hadivm
                have hmn : m = n := by
                  apply Nat.dvd_antisymm hcond.2.1
                  simpa [hA haA hnA (dvd_trans hadivm hcond.2.1)] using hadivm
                exact (lt_of_dvd_of_two_le_div hcond.2.1 hY hcond.2.2).ne hmn
              simp [transitionKernel, hcond,
                survivingArrivalMass_eq_arrivalMass_of_no_dvd chain A k hNo_m]
            · simp [transitionKernel, hcond])
      · simp [hnA]

/--
For a primitive set `A ⊆ Ici x`, the `ENNReal` sum of the indicator visit probabilities is exactly
the first-hit mass `visitMass chain A`.
-/
private theorem PrimitiveSet.tsum_indicator_ofReal_visitProbability_eq_visitMass {x Y : ℕ}
    (chain : MarkovLayer x Y) {A : Set ℕ} (hA : PrimitiveSet A) (hAx : A ⊆ Set.Ici x)
    (hx : 2 ≤ x) (hY : 2 ≤ Y) (hB : 0 < normalizationConstant x Y) :
    (∑' n : ℕ, A.indicator (fun n => ENNReal.ofReal (chain.visitProbability n)) n) =
      visitMass chain A := by
  calc
    (∑' n : ℕ, A.indicator (fun n => ENNReal.ofReal (chain.visitProbability n)) n) =
        ∑' n : ℕ, ∑' k : ℕ, A.indicator (arrivalMass chain k) n := by
          apply tsum_congr
          intro n
          by_cases hnA : n ∈ A
          · simpa [hnA] using
              (tsum_arrivalMass_eq_ofReal_visitProbability chain hx hY hB (hAx hnA)).symm
          · simp [hnA]
    _ = ∑' k : ℕ, ∑' n : ℕ, A.indicator (arrivalMass chain k) n := by
          rw [ENNReal.tsum_comm]
    _ = ∑' k : ℕ, firstHitMassAtStep chain A k := by
          apply tsum_congr
          intro k
          simpa using
            (PrimitiveSet.firstHitMassAtStep_eq_tsum_indicator_arrivalMass chain hA hY k).symm
    _ = visitMass chain A := by rw [visitMass]

/--
If the first-hit mass budget of a primitive set `A` is at most `1`, then the real indicator
series of visit probabilities is summable and its total mass is at most `1`.
-/
theorem PrimitiveSet.summable_indicator_visitProbability_and_tsum_le_one_of_visitMass_le_one
    {x Y : ℕ} (chain : MarkovLayer x Y) {A : Set ℕ} (hA : PrimitiveSet A) (hAx : A ⊆ Set.Ici x)
    (hx : 2 ≤ x) (hY : 2 ≤ Y) (hB : 0 < normalizationConstant x Y)
    (hVisitMass : visitMass chain A ≤ 1) :
    Summable (A.indicator (chain.visitProbability)) ∧
      (∑' n : ℕ, A.indicator (chain.visitProbability) n) ≤ 1 := by
  let f : ℕ → ENNReal := fun n =>
    A.indicator (fun n => ENNReal.ofReal (chain.visitProbability n)) n
  have hmass :
      (∑' n : ℕ, f n) = visitMass chain A := by
    simpa [f] using
      PrimitiveSet.tsum_indicator_ofReal_visitProbability_eq_visitMass chain hA hAx hx hY hB
  have htop :
      (∑' n : ℕ, f n) ≠ ⊤ := by
    rw [hmass]
    exact ne_of_lt <| lt_of_le_of_lt hVisitMass (by simp)
  have hseries :
      HasSum (A.indicator (chain.visitProbability))
        (visitMass chain A).toReal := by
    convert (ENNReal.hasSum_toReal (f := f) htop) using 1
    · funext n
      by_cases hnA : n ∈ A
      · simp [f, hnA, ENNReal.toReal_ofReal, visitProbability_nonneg chain hx hB (hAx hnA)]
      · simp [f, hnA]
    · rw [← hmass, ENNReal.tsum_toReal_eq]
      intro n
      by_cases hnA : n ∈ A <;> simp [f, hnA]
  refine ⟨hseries.summable, ?_⟩
  rw [hseries.tsum_eq]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hVisitMass)

/-- Splitting a series into the part supported on `A` and the part supported on `Aᶜ` recovers the
original total mass. -/
private lemma tsum_indicator_add_tsum_indicator_compl (A : Set ℕ) (f : ℕ → ENNReal) :
    (∑' n : ℕ, A.indicator f n) + (∑' n : ℕ, Aᶜ.indicator f n) = ∑' n : ℕ, f n := by
  rw [← ENNReal.tsum_add]
  exact congrArg (fun g : ℕ → ENNReal => ∑' n : ℕ, g n) (Set.indicator_self_add_compl A f)

/-- The step-0 hit mass together with the step-0 surviving mass is exactly the initial mass. -/
private lemma firstHitMassAtStep_zero_add_tsum_survivingArrivalMass_zero {x Y : ℕ}
    (chain : MarkovLayer x Y) (A : Set ℕ) :
    firstHitMassAtStep chain A 0 + (∑' n : ℕ, survivingArrivalMass chain A 0 n) =
      ∑' n : ℕ, initialMass x Y n := by
  simpa [firstHitMassAtStep, survivingArrivalMass] using
    tsum_indicator_add_tsum_indicator_compl A (initialMass x Y)

/--
At step `k + 1`, the first-hit mass together with the surviving mass is exactly the mass
propagated from the surviving mass at step `k`.
-/
private lemma firstHitMassAtStep_succ_add_tsum_survivingArrivalMass {x Y : ℕ}
    (chain : MarkovLayer x Y) (A : Set ℕ) (k : ℕ) :
    firstHitMassAtStep chain A (k + 1) +
        (∑' n : ℕ, survivingArrivalMass chain A (k + 1) n) =
      ∑' n : ℕ, ∑' m : ℕ, survivingArrivalMass chain A k m * transitionKernel x Y m n := by
  simpa [firstHitMassAtStep, survivingArrivalMass] using
    tsum_indicator_add_tsum_indicator_compl A
      (fun n => ∑' m : ℕ, survivingArrivalMass chain A k m * transitionKernel x Y m n)

/--
The next first-hit mass together with the next surviving mass is bounded by the current surviving
mass.
-/
private lemma firstHitMassAtStep_succ_add_tsum_survivingArrivalMass_le {x Y : ℕ}
    (chain : MarkovLayer x Y) (A : Set ℕ) (hx : 0 < x) (hY : 1 ≤ Y)
    (hkernel : ∀ ⦃m : ℕ⦄, x ≤ m → (∑' n : ℕ, transitionKernel x Y m n) ≤ 1) (k : ℕ) :
    firstHitMassAtStep chain A (k + 1) +
        (∑' n : ℕ, survivingArrivalMass chain A (k + 1) n) ≤
      ∑' n : ℕ, survivingArrivalMass chain A k n := by
  rw [firstHitMassAtStep_succ_add_tsum_survivingArrivalMass]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  calc
    ∑' m : ℕ, survivingArrivalMass chain A k m * (∑' n : ℕ, transitionKernel x Y m n)
      ≤ ∑' m : ℕ, survivingArrivalMass chain A k m * 1 := by
          refine ENNReal.tsum_le_tsum ?_
          intro m
          by_cases hm : x ≤ m
          · gcongr
            exact hkernel hm
          · rw [survivingArrivalMass_eq_zero_of_lt chain A hx hY k (lt_of_not_ge hm)]
            simp
    _ = ∑' m : ℕ, survivingArrivalMass chain A k m := by simp

/--
The partial first-hit mass up to step `N`, together with the surviving mass at time `N`, stays
within the initial mass budget.
-/
private lemma sum_firstHitMassAtStep_add_tsum_survivingArrivalMass_le_initialMass
    {x Y : ℕ}
    (chain : MarkovLayer x Y) (A : Set ℕ) (hx : 0 < x) (hY : 1 ≤ Y)
    (hkernel : ∀ ⦃m : ℕ⦄, x ≤ m → (∑' n : ℕ, transitionKernel x Y m n) ≤ 1) :
    ∀ N : ℕ,
      (∑ k ∈ Finset.range (N + 1), firstHitMassAtStep chain A k) +
          (∑' n : ℕ, survivingArrivalMass chain A N n) ≤
        ∑' n : ℕ, initialMass x Y n
  | 0 => by
      simpa using (firstHitMassAtStep_zero_add_tsum_survivingArrivalMass_zero chain A).le
  | N + 1 => by
      exact le_trans
        (by
          simpa [Finset.sum_range_succ, add_assoc, add_left_comm, add_comm] using
            add_le_add_left
              (firstHitMassAtStep_succ_add_tsum_survivingArrivalMass_le
                chain A hx hY hkernel N)
              (∑ k ∈ Finset.range (N + 1), firstHitMassAtStep chain A k))
        (sum_firstHitMassAtStep_add_tsum_survivingArrivalMass_le_initialMass
          chain A hx hY hkernel N)

/-- If the initial mass is at most `1` and every kernel row is sub-Markov, then the total
first-hit mass is at most `1`. -/
lemma visitMass_le_of_bounds {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ)
    (hx : 0 < x) (hY : 1 ≤ Y)
    (hinit : (∑' n : ℕ, initialMass x Y n) ≤ 1)
    (hkernel : ∀ ⦃m : ℕ⦄, x ≤ m → (∑' n : ℕ, transitionKernel x Y m n) ≤ 1) :
    visitMass chain A ≤ 1 := by
  rw [visitMass]
  exact le_trans
    (by
      refine ENNReal.tsum_le_of_sum_range_le ?_
      intro N
      cases N with
      | zero => simp
      | succ N =>
          exact le_trans (le_add_right le_rfl)
            (sum_firstHitMassAtStep_add_tsum_survivingArrivalMass_le_initialMass
              chain A hx hY hkernel N))
    hinit


end PrimitiveSetsAboveX



/-!
# Main theorem for primitive sets above `x`

This file contains the public theorem solving Erdős Problem `#1196` in the quantitative form
`1 + O(1 / log x)`. It packages the eventual choice of the cutoff `Y`, builds the explicit
Markov layer with visiting probabilities `1 / (B_x n log n)`, and combines the hit-mass and
normalization estimates into the final logarithmic-series bound.

## Main statements

* `mainTheorem`
-/


open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/--
There is a fixed admissible cutoff `Y ≥ 2` for which the transition weights eventually satisfy the
sub-Markov row-sum bound. This packages the choice extracted from
`subMarkovRowSumBound` for later use in `mainTheorem`.
-/
private lemma exists_eventual_subMarkov_cutoff :
    ∃ Y : ℕ, 2 ≤ Y ∧
      ∃ x₀ : ℕ, Y ≤ x₀ ∧
        ∀ ⦃m : ℕ⦄, x₀ ≤ m → (∑' q : ℕ, transitionWeight Y m q) ≤ 1 := by
  rcases subMarkovRowSumBound with ⟨C, hCpos, hC⟩
  let Y : ℕ := Nat.ceil (Real.exp (2 * C)) + 1
  have hceil_lt_Y : Nat.ceil (Real.exp (2 * C)) < Y := by
    simp [Y]
  have hYlarge : Real.exp (2 * C) < (Y : ℝ) := by
    exact lt_of_le_of_lt (Nat.le_ceil (Real.exp (2 * C))) (by exact_mod_cast hceil_lt_Y)
  rcases hC hYlarge with ⟨x₀, hYx₀, hx₀⟩
  refine ⟨Y, ?_, x₀, hYx₀, hx₀⟩
  have hY_gt_one : (1 : ℝ) < (Y : ℝ) := by
    refine lt_trans ?_ hYlarge
    simpa using Real.one_lt_exp_iff.2 (by nlinarith [hCpos])
  exact_mod_cast hY_gt_one

/--
Formal solution of Erdős Problem `#1196`: there exist constants `C` and `x₀` such that for every
cutoff `x ≥ x₀` and every primitive set `A ⊆ Ici x`, the logarithmic series
`∑_{a ∈ A} 1 / (a log a)` is summable and bounded above by `1 + C / log x`.
-/
theorem mainTheorem :
    ∃ C : ℝ, ∃ x₀ : ℕ,
      ∀ ⦃x : ℕ⦄, x₀ ≤ x →
        ∀ {A : Set ℕ}, PrimitiveSet A → A ⊆ Set.Ici x →
          Summable (A.indicator (fun m : ℕ => 1 / ((m : ℝ) * Real.log (m : ℝ)))) ∧
            (∑' m : ℕ, A.indicator (fun k : ℕ => 1 / ((k : ℝ) * Real.log (k : ℝ))) m) ≤
              1 + C / Real.log (x : ℝ) := by
  rcases exists_eventual_subMarkov_cutoff with ⟨Y, hY, xCut, hYxCut, hSub⟩
  rcases normalizationEstimate (Y := Y) hY with ⟨C, hCpos, xNorm, hNorm⟩
  let xLog : ℕ := Nat.ceil (Real.exp C) + 1
  refine ⟨C, max xCut (max xNorm xLog), ?_⟩
  intro x hx A hPrimitive hA
  have hxCut : xCut ≤ x := by omega
  have hxNorm : xNorm ≤ x := by omega
  have hxLog : xLog ≤ x := by omega
  have hxY : Y ≤ x := by omega
  have hxTwo : 2 ≤ x := by omega
  have hExp_lt_x : Real.exp C < (x : ℝ) := by
    refine lt_of_le_of_lt (Nat.le_ceil (Real.exp C)) ?_
    exact_mod_cast
      (lt_of_lt_of_le (Nat.lt_succ_self (Nat.ceil (Real.exp C))) (by simpa [xLog] using hxLog))
  have hlog_gt : C < Real.log (x : ℝ) := by
    simpa [Real.log_exp] using (Real.log_lt_log (Real.exp_pos _) hExp_lt_x)
  have hlog_pos : 0 < Real.log (x : ℝ) := lt_trans hCpos hlog_gt
  have hBpos : 0 < normalizationConstant x Y := by
    have hBnear : |normalizationConstant x Y - 1| < 1 := by
      refine lt_of_le_of_lt (hNorm hxNorm) ?_
      have hlog_ne : Real.log (x : ℝ) ≠ 0 := hlog_pos.ne'
      field_simp [hlog_ne]
      nlinarith
    linarith [(abs_lt.mp hBnear).1]
  let visit : ℕ → ℝ := fun n =>
    if x ≤ n then
      1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ))
    else 0
  let chain : MarkovLayer x Y := {
    transitionSubMarkov := by
      intro m hm
      exact hSub (le_trans hxCut hm)
    visitProbability := visit
    visitProbabilityRecurrence := by
      intro n hn
      simpa [visit, hn] using
        (explicitFormula_eq_recurrence_rhs (x := x) (Y := Y) (n := n) hxTwo hn
          (f := visit) <| by
            intro q hq hqx hq1
            have hcast_div : ((n / q : ℕ) : ℝ) = (n : ℝ) / q :=
              Nat.cast_div (Nat.dvd_of_mem_divisors hq)
                (by exact_mod_cast (Nat.pos_of_mem_divisors hq).ne')
            simp [visit, hqx.2, hcast_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm])
  }
  have hinit : (∑' n : ℕ, initialMass x Y n) ≤ 1 :=
    (tsum_initialMass_eq_one (x := x) (Y := Y) hBpos).le
  have hVisitMass : visitMass chain A ≤ 1 :=
    visitMass_le_of_bounds chain A (by omega) (le_trans (by decide : 1 ≤ 2) hY) hinit
      chain.kernelRowBound
  rcases PrimitiveSet.summable_indicator_visitProbability_and_tsum_le_one_of_visitMass_le_one
      chain hPrimitive hA hxTwo hY hBpos hVisitMass with
    ⟨hHitSummable, hHit⟩
  exact summable_indicatorLogSeries_and_tsum_le_of_hitMass
    chain hxTwo hA hBpos hHitSummable hHit (hNorm hxNorm)

#print axioms PrimitiveSetsAboveX.mainTheorem
-- 'Erdos1196.PrimitiveSetsAboveX.mainTheorem' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end PrimitiveSetsAboveX



/-!
# The formal-conjectures statement of Erdős Problem 1196

This file packages the local solution of Erdős Problem `#1196` in the mathematical form used by
the `formal-conjectures` repository. We keep the same namespace, theorem name, and primitive-set
definition, but omit the repository-specific metadata attribute and `answer(...)` wrapper.

## Main statements

* `Erdos1196.IsPrimitive`
* `Erdos1196.erdos_1196`
-/

open Filter
open scoped Asymptotics BigOperators


/-- Exact local copy of the primitive-set predicate used in the official
`formal-conjectures` statement of Erdős Problem `#1196`. -/
def IsPrimitive {M : Type*} [CommMonoid M] (A : Set M) : Prop :=
  ∀ᵉ (x ∈ A) (y ∈ A), x ∣ y → Associated x y

private lemma log_pos_nat {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log (n : ℝ) := by
  exact Real.log_pos <| by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hn)

private lemma div_lt_abs_add_one_div {C t : ℝ} (ht : 0 < t) :
    C / t < (|C| + 1) / t := by
  field_simp [ht.ne']
  nlinarith [le_abs_self C]

private lemma isPrimitive_nat_iff (A : Set ℕ) :
    IsPrimitive A ↔ PrimitiveSetsAboveX.PrimitiveSet A := by
  constructor
  · intro h m n hm hn hmn
    exact associated_iff_eq.mp <| h m hm n hn hmn
  · intro h m hm n hn hmn
    exact associated_iff_eq.mpr <| h hm hn hmn

private lemma logSeries_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ 1 / ((n : ℝ) * Real.log (n : ℝ)) := by
  by_cases h1 : n = 1
  · simp [h1]
  · have hn2 : 2 ≤ n := by omega
    have hlog : 0 ≤ Real.log (n : ℝ) := le_of_lt <| log_pos_nat hn2
    have hden : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by positivity
    simpa [mul_comm] using one_div_nonneg.mpr hden

private lemma tsum_subtype_eq_indicator_logSeries (A : Set ℕ) :
    ∑' (a : A), (1 / ((a.val : ℝ).log * a)) =
      ∑' n : ℕ, A.indicator (fun m : ℕ => 1 / ((m : ℝ) * Real.log (m : ℝ))) n := by
  simpa [mul_comm] using tsum_subtype A (fun n : ℕ => 1 / ((n : ℝ) * Real.log (n : ℝ)))

/--
This is the `formal-conjectures`-style formulation of Erdős Problem `#1196`.
It is deduced from `PrimitiveSetsAboveX.mainTheorem` by converting the local quantitative bound
`1 + C / log x` into an `o(1)` error term.
-/
theorem erdos_1196 :
    ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧
      ∀ x > (0 : ℕ), ∀ A ⊆ Set.Ici x, IsPrimitive A →
        ∑' (a : A), (1 / ((a.val : ℝ).log * a)) < 1 + o x := by
  rcases PrimitiveSetsAboveX.mainTheorem with ⟨C, x₀, hx₀⟩
  let N := max x₀ 2
  have hN : x₀ ≤ N := le_max_left _ _
  have hNtwo : 2 ≤ N := le_max_right _ _
  let f : ℕ → ℝ := fun n => 1 / ((n : ℝ) * Real.log (n : ℝ))
  let headBound : ℕ → ℝ := fun x => (Finset.Icc x (N - 1)).sum f
  let o : ℕ → ℝ := fun x =>
    if hxN : x < N then
      headBound x + (|C| + 1) / Real.log (N : ℝ)
    else
      (|C| + 1) / Real.log (x : ℝ)
  refine ⟨o, ?_, ?_⟩
  · have ho_eq :
        o =ᶠ[Filter.atTop] fun x : ℕ => (|C| + 1) / Real.log (x : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop N] with x hx
      simp [o, not_lt.mpr hx]
    have hlog :
        Tendsto (fun x : ℕ => Real.log (x : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hzero :
        Tendsto (fun x : ℕ => (|C| + 1) / Real.log (x : ℝ)) Filter.atTop (nhds 0) := by
      simpa using hlog.const_div_atTop (|C| + 1 : ℝ)
    exact (Asymptotics.isLittleO_one_iff ℝ).2 <| hzero.congr' ho_eq.symm
  · intro x hx_pos A hAx hPrimitive
    have hx1 : 1 ≤ x := Nat.succ_le_of_lt hx_pos
    have hPrimitive' : PrimitiveSetsAboveX.PrimitiveSet A := (isPrimitive_nat_iff A).mp hPrimitive
    have hstrict {y : ℕ} (hy : N ≤ y) {B : Set ℕ} (hB : PrimitiveSetsAboveX.PrimitiveSet B)
        (hBy : B ⊆ Set.Ici y) :
        Summable (B.indicator f) ∧
          ∑' n : ℕ, B.indicator f n < 1 + (|C| + 1) / Real.log (y : ℝ) := by
      rcases hx₀ (le_trans hN hy) hB hBy with ⟨hBsummable, hBbound⟩
      have hlogy : 0 < Real.log (y : ℝ) := log_pos_nat (le_trans hNtwo hy)
      refine ⟨by simpa [f] using hBsummable, ?_⟩
      linarith [hBbound, div_lt_abs_add_one_div (C := C) hlogy]
    by_cases hxN : N ≤ x
    · rw [tsum_subtype_eq_indicator_logSeries A]
      simpa [f, o, not_lt.mpr hxN] using (hstrict hxN hPrimitive' hAx).2
    · have hxN' : x < N := lt_of_not_ge hxN
      let head : ℕ → ℝ := (A ∩ Set.Icc x (N - 1)).indicator f
      let tail : ℕ → ℝ := (A ∩ Set.Ici N).indicator f
      have hTailPrimitive : PrimitiveSetsAboveX.PrimitiveSet (A ∩ Set.Ici N) := by
        grind [PrimitiveSetsAboveX.PrimitiveSet]
      rcases hstrict (y := N) le_rfl hTailPrimitive (by intro n hn; exact hn.2) with
        ⟨hTailSummable', hTailLt⟩
      have hsplit (n : ℕ) :
          A.indicator f n = head n + tail n := by
        by_cases hnA : n ∈ A
        · have hxn : x ≤ n := hAx hnA
          by_cases hnN : n < N
          · have hHead : n ∈ Set.Icc x (N - 1) := by
              refine ⟨hxn, ?_⟩
              omega
            simp [head, tail, hnA, hHead, hnN.not_ge]
          · have hHead : n ∉ Set.Icc x (N - 1) := by
              intro hmem
              have hlt_top : N - 1 < N := Nat.sub_lt (show 0 < N by omega) (by decide)
              exact hnN (lt_of_le_of_lt hmem.2 hlt_top)
            simp [head, tail, hnA, hHead, not_lt.mp hnN]
        · simp [head, tail, hnA]
      have hHeadZero : ∀ n ∉ Finset.Icc x (N - 1), head n = 0 := by
        intro n hn
        have hn' : n ∉ Set.Icc x (N - 1) := by simpa using hn
        simp [head, hn']
      have hHeadSummable : Summable head := by
        refine summable_of_hasFiniteSupport ((Finset.Icc x (N - 1)).finite_toSet.subset ?_)
        intro n hn
        by_contra hnot
        exact hn (hHeadZero n hnot)
      have hHeadLe : (∑' n : ℕ, head n) ≤ headBound x := by
        rw [tsum_eq_sum (s := Finset.Icc x (N - 1)) hHeadZero]
        change
          (Finset.Icc x (N - 1)).sum head ≤
            (Finset.Icc x (N - 1)).sum f
        refine Finset.sum_le_sum ?_
        intro n hn
        by_cases hnA : n ∈ A
        · have hnSet : n ∈ Set.Icc x (N - 1) := by simpa using hn
          simp [f, hnA, hnSet]
        · have hn1 : 1 ≤ n := le_trans hx1 (Finset.mem_Icc.mp hn).1
          have hnSet : n ∈ Set.Icc x (N - 1) := by simpa using hn
          simpa [head, f, hnA, hnSet] using logSeries_nonneg hn1
      calc
        ∑' (a : A), (1 / ((a.val : ℝ).log * a))
          = ∑' n : ℕ, A.indicator (fun m : ℕ => 1 / ((m : ℝ) * Real.log (m : ℝ))) n := by
              exact tsum_subtype_eq_indicator_logSeries A
        _ = ∑' n : ℕ, head n + ∑' n : ℕ, tail n := by
              rw [show
                (∑' n : ℕ, A.indicator f n) =
                  ∑' n : ℕ, (head n + tail n) by
                    refine tsum_congr ?_
                    intro n
                    exact hsplit n]
              simpa [Pi.add_apply] using Summable.tsum_add hHeadSummable hTailSummable'
        _ ≤ headBound x + ∑' n : ℕ, tail n := by
              exact add_le_add hHeadLe le_rfl
        _ < headBound x + (1 + (|C| + 1) / Real.log (N : ℝ)) := by
              linarith
        _ = 1 + o x := by
              simp [o, headBound, hxN']
              ring

#print axioms erdos_1196
--

end Erdos1196
