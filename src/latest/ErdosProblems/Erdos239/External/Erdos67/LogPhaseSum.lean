import ErdosProblems.Erdos239.External.Erdos67.Pretentious
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Elementary estimates for the logarithmic phase

This file isolates calculus facts about the phase `x ↦ x⁻ⁱᵗ`.  They are
intended as input to a finite van der Corput argument.  In particular, the
continuous integral has size `O((a+b)/|t|)`, uniformly at polynomial height.
-/

open scoped BigOperators ComplexConjugate Interval
open Set

namespace Erdos67.LogPhaseSum

noncomputable section

/-- The real-variable logarithmic phase `x ↦ x⁻ⁱᵗ`, interpreted by complex
power. -/
def logPhase (t x : ℝ) : ℂ :=
  (x : ℂ) ^ (-(Complex.I * (t : ℂ)))

/-- The corresponding phase on natural numbers. -/
def natLogTwist (n : ℕ) (t : ℝ) : ℂ :=
  logPhase t n

/-- The real argument `-t log x` of `logPhase t x` for `x > 0`. -/
def logPhaseArgument (t x : ℝ) : ℝ :=
  -t * Real.log x

theorem hasDerivAt_logPhaseArgument {t x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (logPhaseArgument t) (-t * x⁻¹) x := by
  change HasDerivAt (fun y : ℝ ↦ -t * Real.log y) (-t * x⁻¹) x
  exact (Real.hasDerivAt_log hx).const_mul (-t)

theorem hasDerivAt_logPhaseArgument_deriv {t x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ -t * y⁻¹) (-(t * -(x ^ 2)⁻¹)) x := by
  simpa only [neg_mul] using (hasDerivAt_inv hx).const_mul (-t)

theorem logPhaseArgument_secondDeriv_value (t x : ℝ) :
    -(t * -(x ^ 2)⁻¹) = t * x⁻¹ ^ 2 := by
  rw [inv_pow]
  ring

theorem hasDerivAt_logPhase {t x : ℝ} (hx : x ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (logPhase t)
      (-(Complex.I * (t : ℂ)) *
        (x : ℂ) ^ (-(Complex.I * (t : ℂ)) - 1)) x := by
  unfold logPhase
  exact hasDerivAt_ofReal_cpow_const hx (by simp [ht])

/-- Derivative of the first-derivative expression of the complex logarithmic
phase. -/
theorem hasDerivAt_logPhase_deriv {t x : ℝ} (hx : x ≠ 0) :
    HasDerivAt
      (fun y : ℝ ↦
        -(Complex.I * (t : ℂ)) *
          (y : ℂ) ^ (-(Complex.I * (t : ℂ)) - 1))
      (-(Complex.I * (t : ℂ)) * (-(Complex.I * (t : ℂ)) - 1) *
        (x : ℂ) ^ (-(Complex.I * (t : ℂ)) - 1 - 1)) x := by
  have hexp : -(Complex.I * (t : ℂ)) - 1 ≠ 0 := by
    intro h
    apply_fun Complex.re at h
    norm_num at h
  simpa only [mul_assoc] using
    (hasDerivAt_ofReal_cpow_const hx hexp).const_mul
      (-(Complex.I * (t : ℂ)))

/-- Magnitude of the first derivative on the positive real axis. -/
theorem norm_logPhase_deriv {t x : ℝ} (hx : 0 < x) :
    ‖-(Complex.I * (t : ℂ)) *
        (x : ℂ) ^ (-(Complex.I * (t : ℂ)) - 1)‖ = |t| / x := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [map_neg, norm_neg, norm_mul, Complex.norm_I, Complex.norm_real,
    one_mul, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.one_re, zero_sub]
  norm_num
  rw [Real.rpow_neg_one]
  simp [div_eq_mul_inv]

/-- Magnitude of the second derivative on the positive real axis. -/
theorem norm_logPhase_secondDeriv {t x : ℝ} (hx : 0 < x) :
    ‖-(Complex.I * (t : ℂ)) * (-(Complex.I * (t : ℂ)) - 1) *
        (x : ℂ) ^ (-(Complex.I * (t : ℂ)) - 2)‖ =
      (|t| * Real.sqrt (t ^ 2 + 1)) / x ^ 2 := by
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hnorm : ‖-(Complex.I * (t : ℂ)) - 1‖ = Real.sqrt (t ^ 2 + 1) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp
    congr 1
    ring
  rw [hnorm]
  simp only [map_neg, norm_neg, norm_mul, Complex.norm_I, Complex.norm_real,
    one_mul, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero,
    sub_zero, OfNat.ofNat, zero_sub]
  norm_num
  simp only [div_eq_mul_inv]

/-- A pointwise first-derivative estimate on a positive interval.  This is
the cell estimate used in the elementary sum--integral comparison below. -/
theorem norm_logPhase_sub_left_le {a b x t : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hx : x ∈ Icc a b) (ht : t ≠ 0) :
    ‖logPhase t x - logPhase t a‖ ≤ (|t| / a) * (x - a) := by
  let f' : ℝ → ℂ := fun y ↦
    -(Complex.I * (t : ℂ)) *
      (y : ℂ) ^ (-(Complex.I * (t : ℂ)) - 1)
  apply norm_image_sub_le_of_norm_deriv_le_segment'
      (f := logPhase t) (f' := f')
  · intro y hy
    exact (hasDerivAt_logPhase (ne_of_gt (ha.trans_le hy.1)) ht).hasDerivWithinAt
  · intro y hy
    dsimp only [f']
    rw [norm_logPhase_deriv (ha.trans_le hy.1)]
    exact div_le_div_of_nonneg_left (abs_nonneg t) ha
      hy.1
  · exact hx

/-- On a unit cell `[n,n+1]`, replacing the logarithmic phase by its left
endpoint incurs pointwise error at most `|t|/n`. -/
theorem norm_logPhase_sub_nat_le {n : ℕ} (hn : 0 < n) {x t : ℝ}
    (hx : x ∈ Icc (n : ℝ) (n + 1 : ℝ)) (ht : t ≠ 0) :
    ‖logPhase t x - natLogTwist n t‖ ≤ |t| / n := by
  have h := norm_logPhase_sub_left_le (t := t)
    (Nat.cast_pos.mpr hn) (by norm_num : (n : ℝ) ≤ n + 1) hx ht
  unfold natLogTwist at h
  refine h.trans ?_
  have hxsub : x - (n : ℝ) ≤ 1 := by linarith [hx.2]
  have hnonneg : 0 ≤ |t| / (n : ℝ) := by positivity
  nlinarith

/-- The elementary norm bound for a finite logarithmic-phase sum.  It is
included as the zero-stage bound for van der Corput differencing. -/
theorem norm_sum_natLogTwist_le_card (s : Finset ℕ) (t : ℝ)
    (hs : ∀ n ∈ s, 0 < n) :
    ‖∑ n ∈ s, natLogTwist n t‖ ≤ s.card := by
  calc
    ‖∑ n ∈ s, natLogTwist n t‖ ≤ ∑ n ∈ s, ‖natLogTwist n t‖ :=
      norm_sum_le _ _
    _ = ∑ _n ∈ s, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      unfold natLogTwist logPhase
      rw [Complex.norm_cpow_eq_rpow_re_of_pos
        (Nat.cast_pos.mpr (hs n hn))]
      simp
    _ = s.card := by simp

theorem natLogTwist_eq_archimedeanTwist_neg (n : ℕ) (t : ℝ) :
    natLogTwist n t = archimedeanTwist (-t) n := by
  unfold natLogTwist logPhase archimedeanTwist
  congr 1
  push_cast
  ring

theorem norm_logPhase (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖logPhase t x‖ = 1 := by
  unfold logPhase
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem norm_natLogTwist (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖natLogTwist n t‖ = 1 := by
  unfold natLogTwist
  exact norm_logPhase t (Nat.cast_pos.mpr hn)

/-- The elementary antiderivative of `x⁻ⁱᵗ` on a finite real interval. -/
theorem integral_logPhase (a b t : ℝ) :
    (∫ x : ℝ in a..b, logPhase t x) =
      ((b : ℂ) ^ (1 - Complex.I * (t : ℂ)) -
          (a : ℂ) ^ (1 - Complex.I * (t : ℂ))) /
        (1 - Complex.I * (t : ℂ)) := by
  have hreal : (-1 : ℝ) < (-(Complex.I * (t : ℂ))).re := by simp
  change (∫ x : ℝ in a..b, (x : ℂ) ^ (-(Complex.I * (t : ℂ)))) = _
  rw [integral_cpow (Or.inl hreal)]
  congr 1 <;> ring

private theorem abs_le_norm_one_sub_I_mul (t : ℝ) :
    |t| ≤ ‖(1 : ℂ) - Complex.I * (t : ℂ)‖ := by
  have hsquare :
      ‖(1 : ℂ) - Complex.I * (t : ℂ)‖ ^ 2 = 1 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  nlinarith [sq_nonneg (|t| - ‖(1 : ℂ) - Complex.I * (t : ℂ)‖),
    abs_nonneg t, norm_nonneg ((1 : ℂ) - Complex.I * (t : ℂ)), sq_abs t]

/-- Continuous first-derivative cancellation for a logarithmic phase. -/
theorem norm_integral_logPhase_le {a b t : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (ht : t ≠ 0) :
    ‖∫ x : ℝ in a..b, logPhase t x‖ ≤ (a + b) / |t| := by
  have hb : 0 < b := ha.trans_le hab
  rw [integral_logPhase, norm_div]
  have hnum :
      ‖(b : ℂ) ^ (1 - Complex.I * (t : ℂ)) -
          (a : ℂ) ^ (1 - Complex.I * (t : ℂ))‖ ≤ b + a := by
    calc
      ‖(b : ℂ) ^ (1 - Complex.I * (t : ℂ)) -
          (a : ℂ) ^ (1 - Complex.I * (t : ℂ))‖ ≤
          ‖(b : ℂ) ^ (1 - Complex.I * (t : ℂ))‖ +
            ‖(a : ℂ) ^ (1 - Complex.I * (t : ℂ))‖ := norm_sub_le _ _
      _ = b + a := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hb,
          Complex.norm_cpow_eq_rpow_re_of_pos ha]
        simp
  have hden := abs_le_norm_one_sub_I_mul t
  have htpos : 0 < |t| := abs_pos.mpr ht
  calc
    ‖(b : ℂ) ^ (1 - Complex.I * (t : ℂ)) -
          (a : ℂ) ^ (1 - Complex.I * (t : ℂ))‖ /
        ‖(1 : ℂ) - Complex.I * (t : ℂ)‖ ≤
        (b + a) / ‖(1 : ℂ) - Complex.I * (t : ℂ)‖ := by
      exact div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (b + a) / |t| := by
      exact div_le_div_of_nonneg_left (by positivity) htpos hden
    _ = (a + b) / |t| := by rw [add_comm]

/-- In the high-height range `b ≤ |t|`, the continuous integral is bounded
by `2` on every positive interval contained in `(0,b]`. -/
theorem norm_integral_logPhase_le_two {a b t : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (ht : b ≤ |t|) :
    ‖∫ x : ℝ in a..b, logPhase t x‖ ≤ 2 := by
  have hb : 0 < b := ha.trans_le hab
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    simp at ht
    linarith
  refine (norm_integral_logPhase_le ha hab ht0).trans ?_
  have hapos : 0 ≤ a := ha.le
  calc
    (a + b) / |t| ≤ (b + b) / |t| := by gcongr
    _ ≤ (b + b) / b := by
      exact div_le_div_of_nonneg_left (by positivity) hb ht
    _ = 2 := by field_simp; norm_num

end

end Erdos67.LogPhaseSum
