import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Finite dyadic summations for Erdős Problem 888

This file isolates the three elementary summations used when the upper-bound
argument is organized into exponent-indexed blocks.

* `geometric_sum_le_terminal` says that a finite geometric sum of ratio at
  least two is controlled by the first omitted term.
* `dyadicMinSqrtSum_le` is the square-root crossover estimate
  `sum min(Q, B / Z) * sqrt Z \ll sqrt (B * Q)`.  We use powers of four for
  `B`, `Q`, and `Z`, so every square root is the integral power `2 ^ z`.
  Powers of four are still dyadic blocks, and this formulation avoids all
  rounding issues at the crossover.
* `harmonicConvolution_eq` evaluates the finite convolution which gives the
  `log log / log` loss.  `harmonicConvolution_le_log` then invokes Mathlib's
  standard upper bound for harmonic numbers.

All sums here are finite.  In particular, none of these statements uses an
asymptotic or convergence placeholder.
-/

open scoped BigOperators

namespace Erdos888
namespace DyadicSums

/-- A geometric sum with ratio at least two is at most its first omitted
term.  This is the terminal-term estimate used for dyadic block sums. -/
theorem geometric_sum_le_terminal {r : ℝ} (hr : 2 ≤ r) (n : ℕ) :
    (∑ i ∈ Finset.range n, r ^ i) ≤ r ^ n := by
  have hr1 : r ≠ 1 := by linarith
  have hrsub : 0 < r - 1 := by linarith
  have hpow : 1 ≤ r ^ n := one_le_pow₀ (by linarith)
  rw [geom_sum_eq hr1]
  apply (div_le_iff₀ hrsub).2
  nlinarith

/-- The terminal-term estimate at the base-two dyadic scale. -/
theorem sum_range_two_pow_le (n : ℕ) :
    (∑ i ∈ Finset.range n, (2 : ℝ) ^ i) ≤ (2 : ℝ) ^ n := by
  exact geometric_sum_le_terminal (by norm_num) n

/-- Reversing a finite base-two geometric sum does not change its bound. -/
theorem sum_range_two_pow_reverse_le (n : ℕ) :
    (∑ i ∈ Finset.range n, (2 : ℝ) ^ (n - 1 - i)) ≤ (2 : ℝ) ^ n := by
  rw [Finset.sum_range_reflect]
  exact sum_range_two_pow_le n

/-- A convenient scaled form of `sum_range_two_pow_le`. -/
theorem sum_range_mul_two_pow_le {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    (∑ i ∈ Finset.range n, C * (2 : ℝ) ^ i) ≤ C * (2 : ℝ) ^ n := by
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_range_two_pow_le n) hC

/-- The finite square-root crossover sum on powers-of-four dyadic blocks.

Here `B = 4 ^ b`, `Q = 4 ^ q`, `Z = 4 ^ z`, and hence
`sqrt Z = 2 ^ z`. -/
noncomputable def dyadicMinSqrtSum (b q : ℕ) : ℝ :=
  ∑ z ∈ Finset.range (b + 1),
    min ((4 : ℝ) ^ q) ((4 : ℝ) ^ (b - z)) * (2 : ℝ) ^ z

private theorem four_pow_mul_two_pow_sub_eq
    {b z : ℕ} (hz : z ≤ b) :
    (4 : ℝ) ^ z * (2 : ℝ) ^ (b - z) =
      (2 : ℝ) ^ b * (2 : ℝ) ^ z := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  omega

private theorem four_pow_mul_two_pow_sub_succ_eq
    {b q : ℕ} (hq : q ≤ b) :
    (4 : ℝ) ^ q * (2 : ℝ) ^ (b - q + 1) =
      2 * (2 : ℝ) ^ (b + q) := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add,
    ← pow_succ']
  congr 1
  omega

/-- The dyadic form of
`sum_Z min(Q, B / Z) * sqrt Z \ll sqrt (B * Q)`.

The constant is explicit.  The powers-of-four parametrization makes the
right side `3 * 2 ^ (b + q) = 3 * sqrt (4 ^ b * 4 ^ q)`. -/
theorem dyadicMinSqrtSum_le (b q : ℕ) (hq : q ≤ b) :
    dyadicMinSqrtSum b q ≤ 3 * (2 : ℝ) ^ (b + q) := by
  let f : ℕ → ℝ := fun z ↦
    min ((4 : ℝ) ^ q) ((4 : ℝ) ^ (b - z)) * (2 : ℝ) ^ z
  have hcut : b - q + 1 ≤ b + 1 := by omega
  have hsplit :
      dyadicMinSqrtSum b q =
        (∑ z ∈ Finset.range (b - q + 1), f z) +
          ∑ z ∈ Finset.Ico (b - q + 1) (b + 1), f z := by
    unfold dyadicMinSqrtSum
    exact (Finset.sum_range_add_sum_Ico f hcut).symm
  have hfirst :
      (∑ z ∈ Finset.range (b - q + 1), f z) ≤
        2 * (2 : ℝ) ^ (b + q) := by
    calc
      (∑ z ∈ Finset.range (b - q + 1), f z) ≤
          ∑ z ∈ Finset.range (b - q + 1),
            (4 : ℝ) ^ q * (2 : ℝ) ^ z := by
              apply Finset.sum_le_sum
              intro z hz
              dsimp [f]
              exact mul_le_mul_of_nonneg_right (min_le_left _ _)
                (by positivity)
      _ ≤ (4 : ℝ) ^ q * (2 : ℝ) ^ (b - q + 1) := by
            exact sum_range_mul_two_pow_le (by positivity) _
      _ = 2 * (2 : ℝ) ^ (b + q) :=
            four_pow_mul_two_pow_sub_succ_eq hq
  have hreflect :
      (∑ z ∈ Finset.Ico (b - q + 1) (b + 1),
          (4 : ℝ) ^ (b - z) * (2 : ℝ) ^ z) =
        ∑ z ∈ Finset.range q,
          (4 : ℝ) ^ z * (2 : ℝ) ^ (b - z) := by
    let g : ℕ → ℝ := fun z ↦ (4 : ℝ) ^ z * (2 : ℝ) ^ (b - z)
    have h := Finset.sum_Ico_reflect
      (fun z : ℕ ↦ (4 : ℝ) ^ z * (2 : ℝ) ^ (b - z))
      (b - q + 1) (m := b + 1) (n := b) (by omega)
    calc
      (∑ z ∈ Finset.Ico (b - q + 1) (b + 1),
          (4 : ℝ) ^ (b - z) * (2 : ℝ) ^ z) =
          ∑ z ∈ Finset.Ico (b - q + 1) (b + 1), g (b - z) := by
            apply Finset.sum_congr rfl
            intro z hz
            have hzb : z ≤ b := by
              have := (Finset.mem_Ico.mp hz).2
              omega
            dsimp [g]
            rw [Nat.sub_sub_self hzb]
      _ = ∑ z ∈ Finset.Ico 0 q, g z := by
            simpa [g, Nat.sub_sub_self hq] using h
      _ = ∑ z ∈ Finset.range q,
          (4 : ℝ) ^ z * (2 : ℝ) ^ (b - z) := by
            rw [← Finset.range_eq_Ico]
  have hsecond :
      (∑ z ∈ Finset.Ico (b - q + 1) (b + 1), f z) ≤
        (2 : ℝ) ^ (b + q) := by
    calc
      (∑ z ∈ Finset.Ico (b - q + 1) (b + 1), f z) ≤
          ∑ z ∈ Finset.Ico (b - q + 1) (b + 1),
            (4 : ℝ) ^ (b - z) * (2 : ℝ) ^ z := by
              apply Finset.sum_le_sum
              intro z hz
              dsimp [f]
              exact mul_le_mul_of_nonneg_right (min_le_right _ _)
                (by positivity)
      _ = ∑ z ∈ Finset.range q,
            (4 : ℝ) ^ z * (2 : ℝ) ^ (b - z) := hreflect
      _ = ∑ z ∈ Finset.range q,
            (2 : ℝ) ^ b * (2 : ℝ) ^ z := by
              apply Finset.sum_congr rfl
              intro z hz
              apply four_pow_mul_two_pow_sub_eq
              have hzq : z < q := Finset.mem_range.mp hz
              omega
      _ ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ q := by
              exact sum_range_mul_two_pow_le (by positivity) q
      _ = (2 : ℝ) ^ (b + q) := by rw [pow_add]
  rw [hsplit]
  linarith

/-- The finite harmonic convolution associated with a pair of complementary
dyadic exponents. -/
noncomputable def harmonicConvolution (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1),
    ((j + 1 : ℕ) : ℝ)⁻¹ * ((J - j + 1 : ℕ) : ℝ)⁻¹

private theorem harmonic_forward_sum (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), ((j + 1 : ℕ) : ℝ)⁻¹) =
      (harmonic (J + 1) : ℝ) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

private theorem harmonic_reverse_sum (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), ((J - j + 1 : ℕ) : ℝ)⁻¹) =
      (harmonic (J + 1) : ℝ) := by
  have h := Finset.sum_range_reflect
    (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ)⁻¹) (J + 1)
  rw [← harmonic_forward_sum J]
  simpa using h

/-- Exact evaluation of the complementary-index harmonic convolution. -/
theorem harmonicConvolution_eq (J : ℕ) :
    harmonicConvolution J =
      2 * (harmonic (J + 1) : ℝ) / (J + 2 : ℕ) := by
  have hterm (j : ℕ) (hj : j < J + 1) :
      ((j + 1 : ℕ) : ℝ)⁻¹ * ((J - j + 1 : ℕ) : ℝ)⁻¹ =
        (((j + 1 : ℕ) : ℝ)⁻¹ + ((J - j + 1 : ℕ) : ℝ)⁻¹) /
          (J + 2 : ℕ) := by
    have hjJ : j ≤ J := by omega
    have hjpos : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    have hrevpos : (0 : ℝ) < (J - j + 1 : ℕ) := by positivity
    have htotpos : (0 : ℝ) < (J + 2 : ℕ) := by positivity
    field_simp
    norm_cast
    omega
  unfold harmonicConvolution
  calc
    (∑ j ∈ Finset.range (J + 1),
        ((j + 1 : ℕ) : ℝ)⁻¹ * ((J - j + 1 : ℕ) : ℝ)⁻¹) =
        ∑ j ∈ Finset.range (J + 1),
          (((j + 1 : ℕ) : ℝ)⁻¹ + ((J - j + 1 : ℕ) : ℝ)⁻¹) /
            (J + 2 : ℕ) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact hterm j (Finset.mem_range.mp hj)
    _ = ((∑ j ∈ Finset.range (J + 1), ((j + 1 : ℕ) : ℝ)⁻¹) +
          ∑ j ∈ Finset.range (J + 1), ((J - j + 1 : ℕ) : ℝ)⁻¹) /
          (J + 2 : ℕ) := by
            rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ = 2 * (harmonic (J + 1) : ℝ) / (J + 2 : ℕ) := by
          rw [harmonic_forward_sum, harmonic_reverse_sum]
          ring

/-- Explicit logarithmic upper bound for the harmonic convolution.  With
`J` proportional to `log n`, this is the finite `log log n / log n` factor. -/
theorem harmonicConvolution_le_log (J : ℕ) :
    harmonicConvolution J ≤
      2 * (1 + Real.log (J + 1 : ℕ)) / (J + 2 : ℕ) := by
  rw [harmonicConvolution_eq]
  have hh : (harmonic (J + 1) : ℝ) ≤
      1 + Real.log (J + 1 : ℕ) := harmonic_le_one_add_log (J + 1)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hh (by norm_num)) (by positivity)

end DyadicSums
end Erdos888
