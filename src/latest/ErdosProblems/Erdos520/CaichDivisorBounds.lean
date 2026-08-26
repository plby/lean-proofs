import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset Nat
open scoped ArithmeticFunction.zeta BigOperators

namespace Erdos
namespace Problem520

/-!
# Elementary bounds for the generalized divisor function

Caich's estimates for the smoothing remainder and the two auxiliary
`lambda` terms use the elementary estimate

`sum_{n <= x} tau_m(n) <= x * (2 * log x)^(m - 1)` (`x >= 3`).

Here `tau_m` is represented exactly as the `m`-fold Dirichlet convolution
of the arithmetic zeta function.  The proof below is self-contained modulo
Mathlib's elementary harmonic-number bound.
-/

open ArithmeticFunction

/-- The ordered `m`-fold divisor function: the number of ordered positive
integer `m`-tuples whose product is `n`.  Dirichlet convolution provides the
representation used in analytic number theory. -/
def orderedDivisorCount (m n : ℕ) : ℕ := (ζ ^ m) n

/-- The summatory ordered divisor function. -/
def orderedDivisorSummatory (m x : ℕ) : ℕ :=
  ∑ n ∈ Finset.Ioc 0 x, orderedDivisorCount m n

@[simp]
theorem orderedDivisorCount_one (n : ℕ) : orderedDivisorCount 1 n = ζ n := by
  simp [orderedDivisorCount]

/-- Pointwise divisor-convolution recurrence for `tau_(m+1)`. -/
theorem orderedDivisorCount_succ (m n : ℕ) :
    orderedDivisorCount (m + 1) n =
      ∑ d ∈ n.divisors, orderedDivisorCount m d := by
  unfold orderedDivisorCount
  rw [pow_succ, mul_zeta_apply]

@[simp]
theorem orderedDivisorSummatory_one (x : ℕ) : orderedDivisorSummatory 1 x = x := by
  unfold orderedDivisorSummatory orderedDivisorCount
  simpa only [pow_one] using! sum_Ioc_zeta x

/-- Adding one ordered factor gives the exact Dirichlet-hyperbola recurrence. -/
theorem orderedDivisorSummatory_succ (m x : ℕ) :
    orderedDivisorSummatory (m + 1) x =
      ∑ d ∈ Finset.Ioc 0 x, orderedDivisorSummatory m (x / d) := by
  unfold orderedDivisorSummatory orderedDivisorCount
  rw [pow_succ, mul_comm, sum_Ioc_mul_eq_sum_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpair : 0 < d ∧ d ≤ x := Finset.mem_Ioc.mp hd
  have hd0 : d ≠ 0 := Nat.ne_of_gt hdpair.1
  simp [zeta_apply_ne hd0]

/-- The floor-quotient sum is bounded by the usual harmonic integral. -/
theorem sum_natDiv_cast_le_mul_one_add_log (x : ℕ) :
    (∑ d ∈ Finset.Ioc 0 x, ((x / d : ℕ) : ℝ)) ≤
      (x : ℝ) * (1 + Real.log (x : ℝ)) := by
  have hharmonic :
      (∑ d ∈ Finset.Ioc 0 x, ((d : ℝ)⁻¹)) = (harmonic x : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    rw [Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast]
    apply Finset.sum_congr
    · ext d
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    · intro d hd
      rfl
  calc
    (∑ d ∈ Finset.Ioc 0 x, ((x / d : ℕ) : ℝ)) ≤
        ∑ d ∈ Finset.Ioc 0 x, (x : ℝ) / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.cast_div_le
    _ = (x : ℝ) * ∑ d ∈ Finset.Ioc 0 x, ((d : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [div_eq_mul_inv]
    _ = (x : ℝ) * (harmonic x : ℝ) := by rw [hharmonic]
    _ ≤ (x : ℝ) * (1 + Real.log (x : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log x) (by positivity)

/-- A uniform ambient-parameter form of the elementary divisor-sum bound.
Keeping the logarithm at `X` makes the induction through Dirichlet
convolution completely lossless. -/
theorem orderedDivisorSummatory_succ_le_ambient (k x X : ℕ)
    (hx : 1 ≤ x) (hxX : x ≤ X) :
    (orderedDivisorSummatory (k + 1) x : ℝ) ≤
      (x : ℝ) * (1 + Real.log (X : ℝ)) ^ k := by
  have hX : 1 ≤ X := hx.trans hxX
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hX)
  have hbase : 0 ≤ 1 + Real.log (X : ℝ) := by linarith
  induction k generalizing x with
  | zero =>
      norm_num only [zero_add, pow_zero, mul_one]
      have hone := (orderedDivisorSummatory_one x).le
      exact_mod_cast hone
  | succ k ih =>
      have hrec := orderedDivisorSummatory_succ (k + 1) x
      rw [hrec]
      rw [Nat.cast_sum]
      have hterm :
          (∑ d ∈ Finset.Ioc 0 x,
              (orderedDivisorSummatory (k + 1) (x / d) : ℝ)) ≤
            ∑ d ∈ Finset.Ioc 0 x,
              ((x / d : ℕ) : ℝ) * (1 + Real.log (X : ℝ)) ^ k := by
        apply Finset.sum_le_sum
        intro d hd
        have hdpair : 0 < d ∧ d ≤ x := Finset.mem_Ioc.mp hd
        have hquot : 1 ≤ x / d := Nat.div_pos hdpair.2 hdpair.1
        exact ih (x / d) hquot ((Nat.div_le_self x d).trans hxX)
      calc
        (∑ d ∈ Finset.Ioc 0 x,
            (orderedDivisorSummatory (k + 1) (x / d) : ℝ)) ≤
            ∑ d ∈ Finset.Ioc 0 x,
              ((x / d : ℕ) : ℝ) * (1 + Real.log (X : ℝ)) ^ k := hterm
        _ = (∑ d ∈ Finset.Ioc 0 x, ((x / d : ℕ) : ℝ)) *
              (1 + Real.log (X : ℝ)) ^ k := by
            rw [Finset.sum_mul]
        _ ≤ ((x : ℝ) * (1 + Real.log (x : ℝ))) *
              (1 + Real.log (X : ℝ)) ^ k := by
            exact mul_le_mul_of_nonneg_right
              (sum_natDiv_cast_le_mul_one_add_log x) (pow_nonneg hbase k)
        _ ≤ ((x : ℝ) * (1 + Real.log (X : ℝ))) *
              (1 + Real.log (X : ℝ)) ^ k := by
            have hlog : Real.log (x : ℝ) ≤ Real.log (X : ℝ) :=
              Real.strictMonoOn_log.monotoneOn
                (show (0 : ℝ) < (x : ℝ) by exact_mod_cast (show 0 < x by omega))
                (show (0 : ℝ) < (X : ℝ) by exact_mod_cast (show 0 < X by omega))
                (by exact_mod_cast hxX)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
              (pow_nonneg hbase k)
        _ = (x : ℝ) * (1 + Real.log (X : ℝ)) ^ (k + 1) := by
            rw [pow_succ]
            ring

/-- Elementary generalized-divisor summatory bound with the slightly sharper
factor `1 + log x`. -/
theorem orderedDivisorSummatory_le_one_add_log (m x : ℕ)
    (hm : 1 ≤ m) (hx : 1 ≤ x) :
    (orderedDivisorSummatory m x : ℝ) ≤
      (x : ℝ) * (1 + Real.log (x : ℝ)) ^ (m - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using!
    orderedDivisorSummatory_succ_le_ambient k x x hx (le_refl x)

/-- The exact form used in Caich's high-moment estimates. -/
theorem orderedDivisorSummatory_le_two_log (m x : ℕ)
    (hm : 1 ≤ m) (hx : 3 ≤ x) :
    (orderedDivisorSummatory m x : ℝ) ≤
      (x : ℝ) * (2 * Real.log (x : ℝ)) ^ (m - 1) := by
  have hx1 : 1 ≤ x := by omega
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hexp : Real.exp 1 ≤ (x : ℝ) :=
    Real.exp_one_lt_three.le.trans (by exact_mod_cast hx)
  have honeLog : (1 : ℝ) ≤ Real.log (x : ℝ) :=
    (Real.le_log_iff_exp_le hxpos).mpr hexp
  have hbase : 0 ≤ 1 + Real.log (x : ℝ) := by linarith
  have hbase_le : 1 + Real.log (x : ℝ) ≤ 2 * Real.log (x : ℝ) := by linarith
  calc
    (orderedDivisorSummatory m x : ℝ) ≤
        (x : ℝ) * (1 + Real.log (x : ℝ)) ^ (m - 1) :=
      orderedDivisorSummatory_le_one_add_log m x hm hx1
    _ ≤ (x : ℝ) * (2 * Real.log (x : ℝ)) ^ (m - 1) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hbase hbase_le (m - 1)) (by positivity)

/-- Any restricted collection of positive integers up to `x` inherits the
same divisor-sum bound.  This is the form needed after imposing largest-prime
or short-interval restrictions. -/
theorem sum_orderedDivisorCount_le_two_log
    (m x : ℕ) (s : Finset ℕ) (hm : 1 ≤ m) (hx : 3 ≤ x)
    (hs : s ⊆ Finset.Ioc 0 x) :
    (∑ n ∈ s, orderedDivisorCount m n : ℕ) ≤
      (x : ℝ) * (2 * Real.log (x : ℝ)) ^ (m - 1) := by
  have hsub :
      (∑ n ∈ s, orderedDivisorCount m n) ≤ orderedDivisorSummatory m x := by
    exact Finset.sum_le_sum_of_subset hs
  exact (by exact_mod_cast hsub :
      (∑ n ∈ s, orderedDivisorCount m n : ℕ) ≤
        (orderedDivisorSummatory m x : ℝ)).trans
    (orderedDivisorSummatory_le_two_log m x hm hx)

/-- In particular, every integer interval `(a,b]` has the global endpoint
bound at `b`. -/
theorem sum_Ioc_orderedDivisorCount_le_two_log
    (m a b : ℕ) (hm : 1 ≤ m) (hb : 3 ≤ b) :
    (∑ n ∈ Finset.Ioc a b, orderedDivisorCount m n : ℕ) ≤
      (b : ℝ) * (2 * Real.log (b : ℝ)) ^ (m - 1) := by
  apply sum_orderedDivisorCount_le_two_log m b (Finset.Ioc a b) hm hb
  intro n hn
  rw [Finset.mem_Ioc] at hn ⊢
  omega

end Problem520
end Erdos
