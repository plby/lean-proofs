import ErdosProblems.Erdos327.Analytic.Mertens
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Erdos327.Analytic

open Filter Real Finset
open scoped BigOperators

/-- The reciprocal-prime sum, named locally to keep later estimates readable. -/
noncomputable def primeInvSum (N : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, 1 / (p : ℝ)

theorem primeInvSum_nonneg (N : ℕ) :
    0 ≤ primeInvSum N := by
  unfold primeInvSum
  positivity

/-- Explicit upper half of Mertens' second theorem. -/
theorem primeInvSum_le {N : ℕ} (hN : 2 ≤ N) :
    primeInvSum N ≤
      log (log N) +
        Mertens.Weight.M (f := Mertens.Weight.prime) +
        (log 4 + 3) / log N := by
  have h := Mertens.sum_prime_inv_sub_sub_bound_nat hN
  rw [abs_le] at h
  unfold primeInvSum
  linarith

/-- Explicit lower half of Mertens' second theorem. -/
theorem primeInvSum_ge {N : ℕ} (hN : 2 ≤ N) :
    log (log N) +
        Mertens.Weight.M (f := Mertens.Weight.prime) -
        (log 4 + 3) / log N ≤
      primeInvSum N := by
  have h := Mertens.sum_prime_inv_sub_sub_bound_nat hN
  rw [abs_le] at h
  unfold primeInvSum
  linarith

theorem primesLE_mono {L X : ℕ} (hLX : L ≤ X) :
    Nat.primesLE L ⊆ Nat.primesLE X := by
  intro p hp
  rw [Nat.mem_primesLE] at hp ⊢
  exact ⟨hp.1.trans hLX, hp.2⟩

/-- Reciprocal-prime mass in the half-open cutoff range `L < p ≤ X`. -/
noncomputable def primeInvTail (L X : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE X \ Nat.primesLE L, 1 / (p : ℝ)

theorem primeInvTail_eq_sub {L X : ℕ} (hLX : L ≤ X) :
    primeInvTail L X = primeInvSum X - primeInvSum L := by
  unfold primeInvTail primeInvSum
  exact Finset.sum_sdiff_eq_sub (primesLE_mono hLX)

/-- A fully explicit ratio-form estimate for a reciprocal-prime tail. -/
theorem primeInvTail_le {L X : ℕ} (hL : 2 ≤ L) (hLX : L ≤ X) :
    primeInvTail L X ≤
      log (log X) - log (log L) +
        (log 4 + 3) / log X + (log 4 + 3) / log L := by
  rw [primeInvTail_eq_sub hLX]
  have hX : 2 ≤ X := hL.trans hLX
  linarith [primeInvSum_le hX, primeInvSum_ge hL]

/-- The square-reciprocal mass of any finite collection of primes is at
most one.  This is the uniform `O(p⁻²)` reserve used in every Euler product. -/
theorem sum_prime_inv_sq_le_one (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s, ((p : ℝ) ^ 2)⁻¹) ≤ 1 := by
  by_cases hs0 : s = ∅
  · simp [hs0]
  let X := s.max' (nonempty_iff_ne_empty.mpr hs0)
  have hsub : s ⊆ Ioc 1 X := by
    intro p hp
    have hpPrime := hs p hp
    exact mem_Ioc.mpr ⟨hpPrime.one_lt, le_max' s p hp⟩
  calc
    (∑ p ∈ s, ((p : ℝ) ^ 2)⁻¹)
        ≤ ∑ n ∈ Ioc 1 X, ((n : ℝ) ^ 2)⁻¹ := by
          apply sum_le_sum_of_subset_of_nonneg hsub
          intro i _ _
          positivity
    _ ≤ (1 : ℝ)⁻¹ - (X : ℝ)⁻¹ :=
      by
        simpa using
          (sum_Ioc_inv_sq_le_sub (α := ℝ) one_ne_zero
            (Nat.one_le_iff_ne_zero.mpr (by
              intro hX
              have hmem := max'_mem s (nonempty_iff_ne_empty.mpr hs0)
              have hprime := hs X hmem
              exact hprime.ne_zero hX)))
    _ ≤ 1 := by
      simp only [inv_one]
      exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg X))

/-- A finite product with linear and quadratic reciprocal-prime errors is
bounded by the exponential of their sums. -/
theorem prod_one_add_inv_add_inv_sq_le_exp
    (s : Finset ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∏ p ∈ s, (1 + a / p + b / (p : ℝ) ^ 2)) ≤
      exp (a * (∑ p ∈ s, 1 / (p : ℝ)) +
        b * (∑ p ∈ s, 1 / (p : ℝ) ^ 2)) := by
  calc
    (∏ p ∈ s, (1 + a / p + b / (p : ℝ) ^ 2))
        ≤ ∏ p ∈ s, exp (a / p + b / (p : ℝ) ^ 2) := by
          apply Finset.prod_le_prod
          · intro p hp
            positivity
          · intro p hp
            linarith [add_one_le_exp (a / p + b / (p : ℝ) ^ 2)]
    _ = exp (a * (∑ p ∈ s, 1 / (p : ℝ)) +
        b * (∑ p ∈ s, 1 / (p : ℝ) ^ 2)) := by
      rw [← exp_sum]
      congr 1
      rw [sum_add_distrib, mul_sum, mul_sum]
      ring_nf

/-- Uniform form of the preceding estimate when all members of `s` are
prime and `a,b` are nonnegative. -/
theorem prod_one_add_inv_add_inv_sq_le_exp_primeInv
    (s : Finset ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, (1 + a / p + b / (p : ℝ) ^ 2)) ≤
      exp (a * (∑ p ∈ s, 1 / (p : ℝ)) + b) := by
  refine (prod_one_add_inv_add_inv_sq_le_exp s a b ha hb).trans ?_
  apply exp_le_exp.mpr
  have hs2 : (∑ p ∈ s, 1 / (p : ℝ) ^ 2) ≤ 1 := by
    simpa [one_div] using sum_prime_inv_sq_le_one s hs
  exact add_le_add_right (mul_le_of_le_one_right hb hs2) _

/-- A finite geometric sum is bounded by the corresponding convergent
infinite geometric series. -/
theorem geomSum_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (n : ℕ) :
    (∑ k ∈ range n, r ^ k) ≤ (1 - r)⁻¹ := by
  rw [inv_eq_one_div, le_div_iff₀ (sub_pos.mpr hr1)]
  rw [geom_sum_mul_neg]
  exact sub_le_self 1 (pow_nonneg hr0 n)

/-- The local factor of a completely multiplicative weight, in the exact
linear-plus-quadratic form used for the Euler-product estimates. -/
theorem geomSum_le_one_add_linear_add_quadratic
    {w p : ℝ} (hw : 0 ≤ w) (hp : w < p) (n : ℕ) :
    (∑ k ∈ range n, (w / p) ^ k) ≤
      1 + w / p + w ^ 2 / (p * (p - w)) := by
  have hp0 : 0 < p := hw.trans_lt hp
  have hr0 : 0 ≤ w / p := div_nonneg hw hp0.le
  have hr1 : w / p < 1 := (div_lt_one hp0).mpr hp
  calc
    (∑ k ∈ range n, (w / p) ^ k) ≤ (1 - w / p)⁻¹ :=
      geomSum_le_inv_one_sub hr0 hr1 n
    _ = 1 + w / p + w ^ 2 / (p * (p - w)) := by
      have hpne : p ≠ 0 := ne_of_gt hp0
      have hpwne : p - w ≠ 0 := ne_of_gt (sub_pos.mpr hp)
      field_simp [hpne, hpwne]
      ring

/-- A convenient uniform specialization: for `0 ≤ w ≤ 5/2` and every
prime-sized denominator `p ≥ 3`, the quadratic reserve `38/p²` suffices. -/
theorem geomSum_le_one_add_linear_add_38_inv_sq
    {w p : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 5 / 2) (hp : 3 ≤ p)
    (n : ℕ) :
    (∑ k ∈ range n, (w / p) ^ k) ≤
      1 + w / p + 38 / p ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hwp : w < p := by linarith
  refine (geomSum_le_one_add_linear_add_quadratic hw0 hwp n).trans ?_
  have hden : 0 < p * (p - w) := mul_pos hp0 (sub_pos.mpr hwp)
  have hpSq : 0 < p ^ 2 := sq_pos_of_pos hp0
  have hquad :
      w ^ 2 / (p * (p - w)) ≤ 38 / p ^ 2 := by
    rw [div_le_div_iff₀ hden hpSq]
    have hww : 0 ≤ w * (5 / 2 - w) :=
      mul_nonneg hw0 (sub_nonneg.mpr hw1)
    have hwSq : w ^ 2 ≤ 25 / 4 := by nlinarith
    have hlinear : w ^ 2 * p ≤ 38 * (p - w) := by
      calc
        w ^ 2 * p ≤ (25 / 4) * p :=
          mul_le_mul_of_nonneg_right hwSq hp0.le
        _ ≤ 38 * (p - w) := by nlinarith
    have := mul_le_mul_of_nonneg_left hlinear hp0.le
    ring_nf at this ⊢
    exact this
  linarith

end Erdos327.Analytic
