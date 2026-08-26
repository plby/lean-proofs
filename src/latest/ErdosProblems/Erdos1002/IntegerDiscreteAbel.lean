import ErdosProblems.Erdos1002.DiscreteAbel
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Discrete Abel summation on integer intervals

Fourier coefficients in the fixed-away argument are indexed by all
integers.  This file transports the finite Abel identity to an interval
starting at an arbitrary integer, retaining the terminal term and every
discrete variation increment.  The interval is parametrized by its natural
length, which avoids any implicit coercion at negative endpoints.
-/

open Finset
open scoped BigOperators

namespace Erdos1002

noncomputable section

/-- Partial sum of an integer-indexed sequence on
`u, u+1, ..., u+k`. -/
def integerIntervalPartialSum (a : ℤ → ℂ) (u : ℤ) (k : ℕ) : ℂ :=
  ∑ j ∈ range (k + 1), a (u + (j : ℤ))

/-- The range parametrization is literally the integer interval
`[u,u+k]`. -/
theorem integerIntervalPartialSum_eq_sum_Icc
    (a : ℤ → ℂ) (u : ℤ) (k : ℕ) :
    integerIntervalPartialSum a u k =
      ∑ n ∈ Icc u (u + (k : ℤ)), a n := by
  unfold integerIntervalPartialSum
  rw [Int.Icc_eq_finset_map]
  have hnat : (u + (k : ℤ) + 1 - u).toNat = k + 1 := by omega
  rw [hnat, sum_map]
  rfl

theorem sum_Icc_int_eq_sum_range_add
    (f : ℤ → ℂ) (u : ℤ) (k : ℕ) :
    (∑ n ∈ Icc u (u + (k : ℤ)), f n) =
      ∑ j ∈ range (k + 1), f (u + (j : ℤ)) := by
  symm
  simpa only [integerIntervalPartialSum] using!
    integerIntervalPartialSum_eq_sum_Icc f u k

theorem sum_Ico_int_eq_sum_range_add
    (f : ℤ → ℝ) (u : ℤ) (k : ℕ) :
    (∑ n ∈ Ico u (u + (k : ℤ)), f n) =
      ∑ j ∈ range k, f (u + (j : ℤ)) := by
  rw [Int.Ico_eq_finset_map]
  have hnat : (u + (k : ℤ) - u).toNat = k := by omega
  rw [hnat, sum_map]
  rfl

/-- Exact finite Abel identity for an arbitrary integer starting point. -/
theorem integerDiscreteAbel_identity
    (a w : ℤ → ℂ) (u : ℤ) (k : ℕ) :
    ∑ j ∈ range (k + 1),
        a (u + (j : ℤ)) * w (u + (j : ℤ)) =
      integerIntervalPartialSum a u k * w (u + (k : ℤ)) +
        ∑ j ∈ range k,
          integerIntervalPartialSum a u j *
            (w (u + (j : ℤ)) - w (u + ((j + 1 : ℕ) : ℤ))) := by
  let a' : ℕ → ℂ := fun j ↦ a (u + (j : ℤ))
  let w' : ℕ → ℂ := fun j ↦ w (u + (j : ℤ))
  have h := discreteAbel_identity a' w' (Nat.zero_le k)
  simpa only [← Nat.range_succ_eq_Icc_zero, Nat.Ico_zero_eq_range,
    intervalPartialSum, integerIntervalPartialSum, a', w'] using! h

/-- Bounded-variation consequence on an integer interval.  Every endpoint
and increment remains visible. -/
theorem norm_integer_sum_mul_le_partialSum_mul_variation
    (a w : ℤ → ℂ) (u : ℤ) (k : ℕ) (M : ℝ)
    (hM : ∀ j ≤ k, ‖integerIntervalPartialSum a u j‖ ≤ M) :
    ‖∑ j ∈ range (k + 1),
        a (u + (j : ℤ)) * w (u + (j : ℤ))‖ ≤
      M * (‖w (u + (k : ℤ))‖ +
        ∑ j ∈ range k,
          ‖w (u + (j : ℤ)) - w (u + ((j + 1 : ℕ) : ℤ))‖) := by
  rw [integerDiscreteAbel_identity]
  calc
    ‖integerIntervalPartialSum a u k * w (u + (k : ℤ)) +
        ∑ j ∈ range k,
          integerIntervalPartialSum a u j *
            (w (u + (j : ℤ)) - w (u + ((j + 1 : ℕ) : ℤ)))‖ ≤
        ‖integerIntervalPartialSum a u k * w (u + (k : ℤ))‖ +
          ‖∑ j ∈ range k,
            integerIntervalPartialSum a u j *
              (w (u + (j : ℤ)) - w (u + ((j + 1 : ℕ) : ℤ)))‖ :=
      norm_add_le _ _
    _ ≤ ‖integerIntervalPartialSum a u k‖ * ‖w (u + (k : ℤ))‖ +
        ∑ j ∈ range k,
          ‖integerIntervalPartialSum a u j *
            (w (u + (j : ℤ)) - w (u + ((j + 1 : ℕ) : ℤ)))‖ := by
      rw [norm_mul]
      gcongr
      exact norm_sum_le _ _
    _ ≤ M * ‖w (u + (k : ℤ))‖ +
        ∑ j ∈ range k,
          M * ‖w (u + (j : ℤ)) - w (u + ((j + 1 : ℕ) : ℤ))‖ := by
      gcongr with j hj
      · exact hM k le_rfl
      · rw [norm_mul]
        gcongr
        exact hM j (Finset.mem_range.mp hj).le
    _ = M * (‖w (u + (k : ℤ))‖ +
        ∑ j ∈ range k,
          ‖w (u + (j : ℤ)) - w (u + ((j + 1 : ℕ) : ℤ))‖) := by
      rw [mul_add, mul_sum]

/-- Uniform interval-sum version used with products of Ramanujan sums. -/
theorem norm_integer_sum_mul_le_intervalBound
    (a w : ℤ → ℂ) (u : ℤ) (k : ℕ) (M : ℝ)
    (hM : ∀ i j : ℤ, i ≤ j →
      ‖∑ n ∈ Icc i j, a n‖ ≤ M) :
    ‖∑ j ∈ range (k + 1),
        a (u + (j : ℤ)) * w (u + (j : ℤ))‖ ≤
      M * (‖w (u + (k : ℤ))‖ +
        ∑ j ∈ range k,
          ‖w (u + (j : ℤ)) - w (u + ((j + 1 : ℕ) : ℤ))‖) := by
  apply norm_integer_sum_mul_le_partialSum_mul_variation a w u k M
  intro j hj
  rw [integerIntervalPartialSum_eq_sum_Icc]
  exact hM u (u + (j : ℤ)) (by omega)

/-- The preceding estimate written directly over the integer interval
`Icc u (u+k)`, with variation over `Ico u (u+k)`. -/
theorem norm_sum_Icc_int_mul_le_intervalBound
    (a w : ℤ → ℂ) (u : ℤ) (k : ℕ) (M : ℝ)
    (hM : ∀ i j : ℤ, i ≤ j →
      ‖∑ n ∈ Icc i j, a n‖ ≤ M) :
    ‖∑ n ∈ Icc u (u + (k : ℤ)), a n * w n‖ ≤
      M * (‖w (u + (k : ℤ))‖ +
        ∑ n ∈ Ico u (u + (k : ℤ)), ‖w n - w (n + 1)‖) := by
  rw [sum_Icc_int_eq_sum_range_add]
  have h := norm_integer_sum_mul_le_intervalBound a w u k M hM
  rw [sum_Ico_int_eq_sum_range_add]
  simpa only [Int.natCast_add, Int.natCast_one, add_assoc] using! h

/-- Endpoint form on an arbitrary nonempty finite integer interval.  This is
the exact finite statement used before passing to a two-sided limit. -/
theorem norm_sum_Icc_int_mul_le_intervalBound'
    (a w : ℤ → ℂ) {u v : ℤ} (huv : u ≤ v) (M : ℝ)
    (hM : ∀ i j : ℤ, i ≤ j →
      ‖∑ n ∈ Icc i j, a n‖ ≤ M) :
    ‖∑ n ∈ Icc u v, a n * w n‖ ≤
      M * (‖w v‖ + ∑ n ∈ Ico u v, ‖w n - w (n + 1)‖) := by
  let k : ℕ := (v - u).toNat
  have huv0 : 0 ≤ v - u := sub_nonneg.mpr huv
  have hkcast : (k : ℤ) = v - u := by
    exact Int.toNat_of_nonneg huv0
  have hend : u + (k : ℤ) = v := by
    rw [hkcast]
    ring
  simpa only [hend] using!
    norm_sum_Icc_int_mul_le_intervalBound a w u k M hM

/-- A version with a supplied uniform multiplier bound and a supplied
discrete total-variation bound. -/
theorem norm_sum_Icc_int_mul_le_sup_add_variation
    (a w : ℤ → ℂ) {u v : ℤ} (huv : u ≤ v) {M B V : ℝ}
    (hM0 : 0 ≤ M)
    (hM : ∀ i j : ℤ, i ≤ j →
      ‖∑ n ∈ Icc i j, a n‖ ≤ M)
    (hSup : ‖w v‖ ≤ B)
    (hVar : (∑ n ∈ Ico u v, ‖w n - w (n + 1)‖) ≤ V) :
    ‖∑ n ∈ Icc u v, a n * w n‖ ≤ M * (B + V) := by
  calc
    ‖∑ n ∈ Icc u v, a n * w n‖ ≤
        M * (‖w v‖ + ∑ n ∈ Ico u v, ‖w n - w (n + 1)‖) :=
      norm_sum_Icc_int_mul_le_intervalBound' a w huv M hM
    _ ≤ M * (B + V) := by gcongr

end

end Erdos1002
