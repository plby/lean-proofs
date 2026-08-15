import ErdosProblems.Erdos285.Modular

/-!
# Exponential tail estimates for Martin's modular Fourier argument

The character-product estimate produces a bound of the shape
`2^C * exp (-X / 2)`.  This file records the exact elementary inequality
turning `2 * log n < X` into domination of all `n - 1` nonzero Fourier
frequencies by the zero frequency.
-/

namespace Erdos285.FourierBound

open scoped BigOperators
open Finset Real

noncomputable section

/-- Exponential loss stronger than `exp (-2 log n)` makes the sum of the
`n - 1` nonzero Fourier modes strictly smaller than the zero mode. -/
theorem exp_half_tail_dominates {n C : ℕ} {X : ℝ} (hn : 1 < n)
    (hX : 2 * Real.log n < X) :
    ((n - 1 : ℕ) : ℝ) *
        ((2 : ℝ) ^ C * Real.exp (-X / 2)) < (2 : ℝ) ^ C := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hpred : (((n - 1 : ℕ) : ℝ)) < n := by
    exact_mod_cast Nat.pred_lt (Nat.ne_zero_of_lt hn)
  have hlog : Real.log n < X / 2 := by linarith
  have hexp : (n : ℝ) * Real.exp (-X / 2) < 1 := by
    rw [← Real.exp_log hnpos, ← Real.exp_add, ← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    linarith
  have hpredexp : (((n - 1 : ℕ) : ℝ)) * Real.exp (-X / 2) < 1 := by
    exact (mul_lt_mul_of_pos_right hpred (Real.exp_pos _)).trans hexp
  calc
    (((n - 1 : ℕ) : ℝ)) * ((2 : ℝ) ^ C * Real.exp (-X / 2)) =
        (2 : ℝ) ^ C *
          ((((n - 1 : ℕ) : ℝ)) * Real.exp (-X / 2)) := by ring
    _ < (2 : ℝ) ^ C * 1 :=
      mul_lt_mul_of_pos_left hpredexp (pow_pos (by norm_num) C)
    _ = (2 : ℝ) ^ C := mul_one _

/-- A pointwise character-product decay estimate with exponent `X / 2`
implies inverse subset-sum surjectivity. -/
theorem inverse_subset_sum_surjective_of_exp_decay {n : ℕ} [NeZero n]
    (hn : 1 < n) (M : Finset ℕ) (a : ZMod n) (X : ℝ)
    (hcoeff : ∀ h : ZMod n, h ≠ 0 →
      ‖M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))‖ ≤
        (2 : ℝ) ^ M.card * Real.exp (-X / 2))
    (hX : 2 * Real.log n < X) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  apply Erdos285.Modular.inverse_subset_sum_surjective_of_fourier_bound
    M a ((2 : ℝ) ^ M.card * Real.exp (-X / 2)) hcoeff
  exact exp_half_tail_dominates hn hX

/-- The form of the tail argument used after Martin's centered-inverse
dispersion estimate: decay by `exp (-δ² |M|)` is more than enough once
`δ² |M|` exceeds `2 log n`. -/
theorem inverse_subset_sum_surjective_of_martin_decay {n : ℕ} [NeZero n]
    (hn : 1 < n) (M : Finset ℕ) (a : ZMod n) (δ : ℝ)
    (hcoeff : ∀ h : ZMod n, h ≠ 0 →
      ‖M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))‖ ≤
        (2 : ℝ) ^ M.card * Real.exp (-(δ ^ 2 * M.card)))
    (hδ : 2 * Real.log n < δ ^ 2 * M.card) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  apply inverse_subset_sum_surjective_of_exp_decay hn M a
    (2 * (δ ^ 2 * M.card))
  · intro h hh
    convert hcoeff h hh using 1
    all_goals ring_nf
  · have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    linarith

/-- Algebraic core of Martin's numerical estimate.  The left side is the
quantity obtained by clearing denominators from
`2L < C * (C * LL^k / (200 B L^k))^2`. -/
theorem martin_cubic_implies_threshold {C B L LL : ℝ} {k : ℕ}
    (hB : 0 < B) (hL : 0 < L)
    (hcubic :
      80000 * B ^ 2 * L ^ (2 * k + 1) < C ^ 3 * LL ^ (2 * k)) :
    2 * L < C * (C * LL ^ k / (200 * B * L ^ k)) ^ 2 := by
  have hden : 0 < (200 * B * L ^ k) ^ 2 := by positivity
  rw [div_pow]
  rw [show C * ((C * LL ^ k) ^ 2 / (200 * B * L ^ k) ^ 2) =
    (C * (C * LL ^ k) ^ 2) / (200 * B * L ^ k) ^ 2 by ring]
  rw [lt_div_iff₀ hden]
  calc
    2 * L * (200 * B * L ^ k) ^ 2 =
        80000 * B ^ 2 * L ^ (2 * k + 1) := by ring
    _ < C ^ 3 * LL ^ (2 * k) := hcubic
    _ = C * (C * LL ^ k) ^ 2 := by ring

/-- Martin's published cardinality lower bound, written as a cube root of
one positive expression, implies the exponent needed by the Fourier tail.
This cube-root form is algebraically equal to
`200 B^(2/3) L^((2k+1)/3) / LL^(2k/3) < C`. -/
theorem martin_cardinality_bound_implies_threshold {C B L LL : ℝ} {k : ℕ}
    (hB : 0 < B) (hL : 0 < L) (hLL : 0 < LL)
    (hC :
      200 * (B ^ 2 * L ^ (2 * k + 1) / LL ^ (2 * k)) ^ (1 / 3 : ℝ) < C) :
    2 * L < C * (C * LL ^ k / (200 * B * L ^ k)) ^ 2 := by
  let Q : ℝ := B ^ 2 * L ^ (2 * k + 1) / LL ^ (2 * k)
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  have hbase : 0 ≤ 200 * Q ^ (1 / 3 : ℝ) := by positivity
  have hcubed : (200 * Q ^ (1 / 3 : ℝ)) ^ 3 < C ^ 3 :=
    pow_lt_pow_left₀ hC hbase (by norm_num)
  have hroot : (Q ^ (1 / 3 : ℝ)) ^ 3 = Q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    norm_num
  have hcubed' : 8000000 * Q < C ^ 3 := by
    rw [mul_pow, hroot] at hcubed
    norm_num at hcubed ⊢
    exact hcubed
  have hLLpow : 0 < LL ^ (2 * k) := by positivity
  have hstrong :
      8000000 * B ^ 2 * L ^ (2 * k + 1) < C ^ 3 * LL ^ (2 * k) := by
    rw [show Q = B ^ 2 * L ^ (2 * k + 1) / LL ^ (2 * k) by rfl] at hcubed'
    rw [show 8000000 * (B ^ 2 * L ^ (2 * k + 1) / LL ^ (2 * k)) =
      (8000000 * B ^ 2 * L ^ (2 * k + 1)) / LL ^ (2 * k) by ring,
      div_lt_iff₀ hLLpow] at hcubed'
    exact hcubed'
  apply martin_cubic_implies_threshold hB hL
  have hleft : 0 < B ^ 2 * L ^ (2 * k + 1) := by positivity
  nlinarith

/-- The cube-root normalization used above is exactly Martin's displayed
product of fractional powers. -/
theorem martin_cube_root_eq_factor_form {B L LL : ℝ} {k : ℕ}
    (hB : 0 < B) (hL : 0 < L) (hLL : 0 < LL) :
    (B ^ 2 * L ^ (2 * k + 1) / LL ^ (2 * k)) ^ (1 / 3 : ℝ) =
      B ^ (2 / 3 : ℝ) * L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
        LL ^ (((2 * k : ℕ) : ℝ) / 3) := by
  rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast]
  rw [← Real.rpow_mul hB.le, ← Real.rpow_mul hL.le, ← Real.rpow_mul hLL.le]
  congr 2 <;> norm_num <;> ring_nf

/-- The published fractional-power cardinality condition directly yields
the exponent required for the Fourier tail. -/
theorem martin_published_cardinality_bound_implies_threshold
    {C B L LL : ℝ} {k : ℕ}
    (hB : 0 < B) (hL : 0 < L) (hLL : 0 < LL)
    (hC :
      200 * (B ^ (2 / 3 : ℝ) * L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
        LL ^ (((2 * k : ℕ) : ℝ) / 3)) < C) :
    2 * L < C * (C * LL ^ k / (200 * B * L ^ k)) ^ 2 := by
  apply martin_cardinality_bound_implies_threshold hB hL hLL
  rwa [martin_cube_root_eq_factor_form hB hL hLL]

end

end Erdos285.FourierBound
