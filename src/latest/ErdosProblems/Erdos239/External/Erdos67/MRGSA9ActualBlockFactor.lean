import ErdosProblems.Erdos239.External.Erdos67.MRGSA9AlternatingEuler
import ErdosProblems.Erdos239.External.Erdos67.MRGSA9BlockFactor
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Actual Euler factors in the GS A.11 block estimate

The elementary hyperbolic-sine estimate in `MRGSA9BlockFactor` applies to
the linear prime sum.  Here we compare the genuine local Euler factors with
that linear sum.  The contribution of every higher prime power is quadratic
in the Euler variable, so it is absorbed by a universal multiple of the
prime-square mass.
-/

open scoped BigOperators

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The logarithm of a one-bounded local Euler factor differs from its
linear term by at most four times the square of the Euler variable. -/
private theorem norm_log_localEulerFactor_sub_linear_le
    (a : ℕ → ℂ) (ha0 : a 0 = 1) (ha : ∀ e, ‖a e‖ ≤ 1)
    (x : ℂ) (hx : ‖x‖ ≤ (1 / 3 : ℝ)) :
    ‖Complex.log (∑' e : ℕ, a e * x ^ e) - a 1 * x‖ ≤
      4 * ‖x‖ ^ 2 := by
  let r : ℝ := ‖x‖
  have hr0 : 0 ≤ r := norm_nonneg x
  have hr : r ≤ 1 / 3 := hx
  have hr1 : r < 1 := by linarith
  have hgeom : Summable (fun e : ℕ ↦ r ^ e) := by
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hnorm : Summable (fun e : ℕ ↦ ‖a e * x ^ e‖) := by
    apply hgeom.of_nonneg_of_le (fun e ↦ norm_nonneg _)
    intro e
    rw [norm_mul, norm_pow]
    simpa using mul_le_mul_of_nonneg_right (ha e) (pow_nonneg hr0 e)
  have hterm : Summable (fun e : ℕ ↦ a e * x ^ e) := hnorm.of_norm
  let z : ℂ := a 1 * x
  let tail : ℂ := ∑' e : ℕ, a (e + 2) * x ^ (e + 2)
  have hsplit : (∑' e : ℕ, a e * x ^ e) = 1 + (z + tail) := by
    have hs := hterm.sum_add_tsum_nat_add 2
    rw [show (∑ e ∈ Finset.range 2, a e * x ^ e) = 1 + a 1 * x by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp [ha0]] at hs
    dsimp only [z, tail]
    rw [← hs]
    ring
  have htailNorm :
      Summable (fun e : ℕ ↦ ‖a (e + 2) * x ^ (e + 2)‖) :=
    hnorm.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
  have hmajor : Summable (fun e : ℕ ↦ r ^ 2 * (1 / 3 : ℝ) ^ e) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 3 : ℝ)‖ < 1)).mul_left _
  have htail : ‖tail‖ ≤ (3 / 2 : ℝ) * r ^ 2 := by
    calc
      ‖tail‖ ≤ ∑' e : ℕ, ‖a (e + 2) * x ^ (e + 2)‖ :=
        norm_tsum_le_tsum_norm htailNorm
      _ ≤ ∑' e : ℕ, r ^ 2 * (1 / 3 : ℝ) ^ e := by
        apply Summable.tsum_le_tsum
        · intro e
          rw [norm_mul, norm_pow, pow_add]
          calc
            ‖a (e + 2)‖ * (r ^ e * r ^ 2) ≤
                1 * (r ^ e * r ^ 2) :=
              mul_le_mul_of_nonneg_right (ha _) (by positivity)
            _ = r ^ 2 * r ^ e := by ring
            _ ≤ r ^ 2 * (1 / 3 : ℝ) ^ e := by gcongr
        · exact htailNorm
        · exact hmajor
      _ = (3 / 2 : ℝ) * r ^ 2 := by
        rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num)]
        ring
  have hz : ‖z‖ ≤ r := by
    dsimp only [z, r]
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (ha 1) (norm_nonneg x)
  let u : ℂ := z + tail
  have hu : ‖u‖ ≤ (3 / 2 : ℝ) * r := by
    calc
      ‖u‖ ≤ ‖z‖ + ‖tail‖ := norm_add_le _ _
      _ ≤ r + (3 / 2 : ℝ) * r ^ 2 := add_le_add hz htail
      _ ≤ (3 / 2 : ℝ) * r := by nlinarith
  have huhalf : ‖u‖ ≤ (1 / 2 : ℝ) := by
    calc
      ‖u‖ ≤ (3 / 2 : ℝ) * r := hu
      _ ≤ 1 / 2 := by linarith
  have hu1 : ‖u‖ < 1 := lt_of_le_of_lt huhalf (by norm_num)
  have hinv : (1 - ‖u‖)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_comm₀ (sub_pos.mpr hu1) (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hlog0 : ‖Complex.log (1 + u) - u‖ ≤ ‖u‖ ^ 2 := by
    calc
      ‖Complex.log (1 + u) - u‖ ≤
          ‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2 :=
        Complex.norm_log_one_add_sub_self_le hu1
      _ ≤ ‖u‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖u‖ ^ 2 := by ring
  have husq : ‖u‖ ^ 2 ≤ (9 / 4 : ℝ) * r ^ 2 := by
    have hsquare := mul_self_le_mul_self (norm_nonneg u) hu
    nlinarith
  rw [hsplit]
  have hid : Complex.log (1 + u) - z =
      (Complex.log (1 + u) - u) + tail := by
    dsimp only [u]
    ring
  rw [hid]
  calc
    ‖(Complex.log (1 + u) - u) + tail‖ ≤
        ‖Complex.log (1 + u) - u‖ + ‖tail‖ := norm_add_le _ _
    _ ≤ ‖u‖ ^ 2 + (3 / 2 : ℝ) * r ^ 2 :=
      add_le_add hlog0 htail
    _ ≤ 4 * r ^ 2 := by
      calc
        ‖u‖ ^ 2 + (3 / 2 : ℝ) * r ^ 2 ≤
            (9 / 4 : ℝ) * r ^ 2 + (3 / 2 : ℝ) * r ^ 2 :=
          add_le_add husq (le_refl _)
        _ ≤ 4 * r ^ 2 := by nlinarith [sq_nonneg r]

/-- A local Euler factor on `Re s ≥ 1`, at a prime at least three, is
nonzero and hence is the exponential of its principal logarithm. -/
private theorem exp_log_gsA9LocalEulerFactor
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    {s : ℂ} (hs : 1 ≤ s.re) :
    Complex.exp (Complex.log (gsA9LocalEulerFactor f s p)) =
      gsA9LocalEulerFactor f s p := by
  let x : ℂ := (p : ℂ) ^ (-s)
  let a : ℕ → ℂ := fun e ↦ f (p ^ e)
  have hxnorm : ‖x‖ ≤ (1 / 3 : ℝ) := by
    dsimp only [x]
    have hpPosR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    change ‖((p : ℝ) : ℂ) ^ (-s)‖ ≤ (1 / 3 : ℝ)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpPosR]
    change (p : ℝ) ^ (-s.re) ≤ 1 / 3
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hpOne : (1 : ℝ) ≤ p := by linarith
    have hpow : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hpOne
      simp only [neg_le_neg_iff]
      exact hs
    rw [Real.rpow_neg_one] at hpow
    calc
      (p : ℝ) ^ (-s.re) ≤ (p : ℝ)⁻¹ := by
        simpa only [Real.rpow_neg_one] using hpow
      _ ≤ (3 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hpR
      _ = 1 / 3 := by norm_num
  have ha0 : a 0 = 1 := by simp [a, hmul.1]
  have ha : ∀ e, ‖a e‖ ≤ 1 := by
    intro e
    exact hbound _ (pow_pos hp.pos e)
  let r : ℝ := ‖x‖
  have hr0 : 0 ≤ r := norm_nonneg x
  have hr : r ≤ 1 / 3 := hxnorm
  have hgeom : Summable (fun e : ℕ ↦ r ^ e) := by
    apply summable_geometric_of_norm_lt_one
    have : r < 1 := by linarith
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hnorm : Summable (fun e : ℕ ↦ ‖a e * x ^ e‖) := by
    apply hgeom.of_nonneg_of_le (fun e ↦ norm_nonneg _)
    intro e
    rw [norm_mul, norm_pow]
    simpa using mul_le_mul_of_nonneg_right (ha e) (pow_nonneg hr0 e)
  have hterm : Summable (fun e : ℕ ↦ a e * x ^ e) := hnorm.of_norm
  let tail : ℂ := ∑' e : ℕ, a (e + 1) * x ^ (e + 1)
  have hsplit : (∑' e : ℕ, a e * x ^ e) = 1 + tail := by
    have hs0 := hterm.sum_add_tsum_nat_add 1
    rw [show (∑ e ∈ Finset.range 1, a e * x ^ e) = 1 by simp [ha0]] at hs0
    exact hs0.symm
  have htailNorm : Summable (fun e : ℕ ↦ ‖a (e + 1) * x ^ (e + 1)‖) :=
    hnorm.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
  have hmajor : Summable (fun e : ℕ ↦ r * (1 / 3 : ℝ) ^ e) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 3 : ℝ)‖ < 1)).mul_left _
  have htail : ‖tail‖ ≤ (3 / 2 : ℝ) * r := by
    calc
      ‖tail‖ ≤ ∑' e : ℕ, ‖a (e + 1) * x ^ (e + 1)‖ :=
        norm_tsum_le_tsum_norm htailNorm
      _ ≤ ∑' e : ℕ, r * (1 / 3 : ℝ) ^ e := by
        apply Summable.tsum_le_tsum
        · intro e
          rw [norm_mul, norm_pow, pow_add, pow_one]
          calc
            ‖a (e + 1)‖ * (r ^ e * r) ≤
                1 * (r ^ e * r) :=
              mul_le_mul_of_nonneg_right (ha _) (by positivity)
            _ = r * r ^ e := by ring
            _ ≤ r * (1 / 3 : ℝ) ^ e := by gcongr
        · exact htailNorm
        · exact hmajor
      _ = (3 / 2 : ℝ) * r := by
        rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num)]
        ring
  have htailHalf : ‖tail‖ ≤ 1 / 2 := by
    calc
      ‖tail‖ ≤ (3 / 2 : ℝ) * r := htail
      _ ≤ 1 / 2 := by linarith
  have hne : (∑' e : ℕ, a e * x ^ e) ≠ 0 := by
    rw [hsplit]
    intro hzero
    have htailEq : tail = -1 := by
      apply add_left_cancel (a := (1 : ℂ))
      simpa using hzero
    have hone : ‖tail‖ = 1 := by rw [htailEq, norm_neg, norm_one]
    linarith
  apply Complex.exp_log
  simpa only [gsA9LocalEulerFactor, a, x] using hne

/-- The logarithmic error of an actual local factor is quadratic in its
Euler variable. -/
private theorem norm_log_gsA9LocalEulerFactor_sub_linear_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    {s : ℂ} (hs : 1 ≤ s.re) :
    ‖Complex.log (gsA9LocalEulerFactor f s p) -
        f p * (p : ℂ) ^ (-s)‖ ≤
      4 * ‖(p : ℂ) ^ (-s)‖ ^ 2 := by
  let x : ℂ := (p : ℂ) ^ (-s)
  have hxnorm : ‖x‖ ≤ (1 / 3 : ℝ) := by
    dsimp only [x]
    have hpPosR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    change ‖((p : ℝ) : ℂ) ^ (-s)‖ ≤ (1 / 3 : ℝ)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpPosR]
    change (p : ℝ) ^ (-s.re) ≤ 1 / 3
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hpOne : (1 : ℝ) ≤ p := by linarith
    have hpow : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hpOne
      simp only [neg_le_neg_iff]
      exact hs
    rw [Real.rpow_neg_one] at hpow
    calc
      (p : ℝ) ^ (-s.re) ≤ (p : ℝ)⁻¹ := by
        simpa only [Real.rpow_neg_one] using hpow
      _ ≤ (3 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hpR
      _ = 1 / 3 := by norm_num
  simpa only [gsA9LocalEulerFactor, x, pow_one] using
    norm_log_localEulerFactor_sub_linear_le
      (fun e ↦ f (p ^ e)) (by simpa using hmul.1)
      (fun e ↦ hbound _ (pow_pos hp.pos e)) x hxnorm

/-- Actual-local-factor form of source equation A.11.  The exact block Euler
product is controlled by the linear block sum, up to a universal quadratic
prime-power error. -/
theorem norm_prod_gsA9LocalEulerFactor_sub_one_mul_exp_neg_radius_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hthree : ∀ p ∈ S, 3 ≤ p)
    {s : ℂ} (hs : 1 ≤ s.re) :
    let z := ∑ p ∈ S, f p * (p : ℂ) ^ (-s)
    let R := ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖
    let V := ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2
    ‖(∏ p ∈ S, gsA9LocalEulerFactor f s p) - 1‖ *
        Real.exp (-R / 2) ≤
      Real.exp (z.re / 2 + 8 * V) := by
  dsimp only
  let z : ℂ := ∑ p ∈ S, f p * (p : ℂ) ^ (-s)
  let R : ℝ := ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖
  let V : ℝ := ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2
  let L : ℂ := ∑ p ∈ S, Complex.log (gsA9LocalEulerFactor f s p)
  let w : ℂ := L - z
  have hw : ‖w‖ ≤ 4 * V := by
    dsimp only [w, L, z, V]
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ p ∈ S, (Complex.log (gsA9LocalEulerFactor f s p) -
          f p * (p : ℂ) ^ (-s))‖ ≤
        ∑ p ∈ S, ‖Complex.log (gsA9LocalEulerFactor f s p) -
          f p * (p : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ S, 4 * ‖(p : ℂ) ^ (-s)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro p hpS
        exact norm_log_gsA9LocalEulerFactor_sub_linear_le
          hmul hbound (hprime p hpS) (hthree p hpS) hs
      _ = 4 * ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2 := by
        rw [Finset.mul_sum]
  have hz : ‖z‖ ≤ R := by
    dsimp only [z, R]
    calc
      ‖∑ p ∈ S, f p * (p : ℂ) ^ (-s)‖ ≤
          ∑ p ∈ S, ‖f p * (p : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ := by
        apply Finset.sum_le_sum
        intro p hpS
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hbound p (hprime p hpS).pos)
  have hL : L = z + w := by dsimp only [w]; ring
  have hLnorm : ‖L‖ ≤ R + ‖w‖ := by
    rw [hL]
    calc
      ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le _ _
      _ ≤ R + ‖w‖ := by gcongr
  have hprod : (∏ p ∈ S, gsA9LocalEulerFactor f s p) = Complex.exp L := by
    dsimp only [L]
    rw [Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro p hpS
    exact (exp_log_gsA9LocalEulerFactor
      hmul hbound (hprime p hpS) (hthree p hpS) hs).symm
  rw [hprod]
  have hexpFactor :
      ‖Complex.exp L - 1‖ =
        Real.exp (L.re / 2) *
          ‖Complex.exp (L / 2) - Complex.exp (-(L / 2))‖ := by
    have hid : Complex.exp L - 1 =
        Complex.exp (L / 2) *
          (Complex.exp (L / 2) - Complex.exp (-(L / 2))) := by
      calc
        Complex.exp L - 1 =
            Complex.exp (L / 2 + L / 2) -
              Complex.exp (L / 2 + -(L / 2)) := by
          congr 1
          · ring
          · rw [show L / 2 + -(L / 2) = 0 by ring, Complex.exp_zero]
        _ = Complex.exp (L / 2) * Complex.exp (L / 2) -
              Complex.exp (L / 2) * Complex.exp (-(L / 2)) := by
          rw [Complex.exp_add, Complex.exp_add]
        _ = Complex.exp (L / 2) *
              (Complex.exp (L / 2) - Complex.exp (-(L / 2))) := by ring
    rw [hid, norm_mul, Complex.norm_exp]
    congr 1
    simp
  rw [hexpFactor]
  have hblock :=
    Erdos67.norm_exp_half_sub_exp_neg_half_mul_exp_neg_le_one_of_norm
      L (R + ‖w‖) hLnorm
  have hLre : L.re ≤ z.re + ‖w‖ := by
    rw [hL, Complex.add_re]
    linarith [Complex.re_le_norm w]
  have hV0 : 0 ≤ V := by
    dsimp only [V]
    positivity
  have hexpRearrange :
      Real.exp (L.re / 2) * Real.exp (-R / 2) =
        Real.exp (L.re / 2 + ‖w‖ / 2) *
          Real.exp (-(R + ‖w‖) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    (Real.exp (L.re / 2) *
        ‖Complex.exp (L / 2) - Complex.exp (-(L / 2))‖) *
        Real.exp (-R / 2) =
      Real.exp (L.re / 2 + ‖w‖ / 2) *
        (‖Complex.exp (L / 2) - Complex.exp (-(L / 2))‖ *
          Real.exp (-(R + ‖w‖) / 2)) := by
        rw [mul_assoc]
        calc
          Real.exp (L.re / 2) *
                (‖Complex.exp (L / 2) - Complex.exp (-(L / 2))‖ *
                  Real.exp (-R / 2)) =
              (Real.exp (L.re / 2) * Real.exp (-R / 2)) *
                ‖Complex.exp (L / 2) - Complex.exp (-(L / 2))‖ := by ring
          _ = (Real.exp (L.re / 2 + ‖w‖ / 2) *
                Real.exp (-(R + ‖w‖) / 2)) *
                ‖Complex.exp (L / 2) - Complex.exp (-(L / 2))‖ := by
              rw [hexpRearrange]
          _ = Real.exp (L.re / 2 + ‖w‖ / 2) *
                (‖Complex.exp (L / 2) - Complex.exp (-(L / 2))‖ *
                  Real.exp (-(R + ‖w‖) / 2)) := by ring
    _ ≤ Real.exp (L.re / 2 + ‖w‖ / 2) * 1 := by
      exact mul_le_mul_of_nonneg_left hblock (Real.exp_pos _).le
    _ ≤ Real.exp (z.re / 2 + ‖w‖) := by
      simp only [mul_one]
      apply Real.exp_le_exp.mpr
      linarith
    _ ≤ Real.exp (z.re / 2 + 8 * V) := by
      apply Real.exp_le_exp.mpr
      have : ‖w‖ ≤ 8 * V := hw.trans (by nlinarith)
      linarith

/-- Matching lower bound for a finite product of genuine local Euler
factors.  It converts the full linear prime exponent into the norm of the
undeleted low-prime L-series, with only the same quadratic prime-power loss.
-/
theorem exp_linear_sub_square_le_norm_prod_gsA9LocalEulerFactor
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hthree : ∀ p ∈ S, 3 ≤ p)
    {s : ℂ} (hs : 1 ≤ s.re) :
    let z := ∑ p ∈ S, f p * (p : ℂ) ^ (-s)
    let V := ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2
    Real.exp (z.re - 4 * V) ≤
      ‖∏ p ∈ S, gsA9LocalEulerFactor f s p‖ := by
  dsimp only
  let z : ℂ := ∑ p ∈ S, f p * (p : ℂ) ^ (-s)
  let V : ℝ := ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2
  let L : ℂ := ∑ p ∈ S, Complex.log (gsA9LocalEulerFactor f s p)
  let w : ℂ := L - z
  have hw : ‖w‖ ≤ 4 * V := by
    dsimp only [w, L, z, V]
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ p ∈ S, (Complex.log (gsA9LocalEulerFactor f s p) -
          f p * (p : ℂ) ^ (-s))‖ ≤
        ∑ p ∈ S, ‖Complex.log (gsA9LocalEulerFactor f s p) -
          f p * (p : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ S, 4 * ‖(p : ℂ) ^ (-s)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro p hpS
        exact norm_log_gsA9LocalEulerFactor_sub_linear_le
          hmul hbound (hprime p hpS) (hthree p hpS) hs
      _ = 4 * ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2 := by
        rw [Finset.mul_sum]
  have hL : L = z + w := by dsimp only [w]; ring
  have hprod : (∏ p ∈ S, gsA9LocalEulerFactor f s p) = Complex.exp L := by
    dsimp only [L]
    rw [Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro p hpS
    exact (exp_log_gsA9LocalEulerFactor
      hmul hbound (hprime p hpS) (hthree p hpS) hs).symm
  rw [hprod, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  rw [hL, Complex.add_re]
  have hwre : -‖w‖ ≤ w.re :=
    neg_le_of_abs_le (Complex.abs_re_le_norm w)
  linarith

/-! ## Direct small-Euler-variable forms

The A.10 contour moves the finite low-prime factor slightly to the left of
`Re s = 1`.  The arguments above only use `Re s ≥ 1` to obtain the local
bound `‖p⁻ˢ‖ ≤ 1/3`.  The following public forms expose that actual analytic
hypothesis, so sufficiently large prime blocks remain available on the
shifted line.
-/

/-- A genuine local Euler factor is nonzero whenever its Euler variable has
norm at most one third, independently of the real part of `s`. -/
theorem exp_log_gsA9LocalEulerFactor_of_norm_le_third
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hxnorm : ‖(p : ℂ) ^ (-s)‖ ≤ (1 / 3 : ℝ)) :
    Complex.exp (Complex.log (gsA9LocalEulerFactor f s p)) =
      gsA9LocalEulerFactor f s p := by
  let x : ℂ := (p : ℂ) ^ (-s)
  let a : ℕ → ℂ := fun e ↦ f (p ^ e)
  have ha0 : a 0 = 1 := by simp [a, hmul.1]
  have ha : ∀ e, ‖a e‖ ≤ 1 := by
    intro e
    exact hbound _ (pow_pos hp.pos e)
  let r : ℝ := ‖x‖
  have hr0 : 0 ≤ r := norm_nonneg x
  have hr : r ≤ 1 / 3 := hxnorm
  have hgeom : Summable (fun e : ℕ ↦ r ^ e) := by
    apply summable_geometric_of_norm_lt_one
    have : r < 1 := by linarith
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hnorm : Summable (fun e : ℕ ↦ ‖a e * x ^ e‖) := by
    apply hgeom.of_nonneg_of_le (fun e ↦ norm_nonneg _)
    intro e
    rw [norm_mul, norm_pow]
    simpa using mul_le_mul_of_nonneg_right (ha e) (pow_nonneg hr0 e)
  have hterm : Summable (fun e : ℕ ↦ a e * x ^ e) := hnorm.of_norm
  let tail : ℂ := ∑' e : ℕ, a (e + 1) * x ^ (e + 1)
  have hsplit : (∑' e : ℕ, a e * x ^ e) = 1 + tail := by
    have hs0 := hterm.sum_add_tsum_nat_add 1
    rw [show (∑ e ∈ Finset.range 1, a e * x ^ e) = 1 by simp [ha0]] at hs0
    exact hs0.symm
  have htailNorm : Summable (fun e : ℕ ↦ ‖a (e + 1) * x ^ (e + 1)‖) :=
    hnorm.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
  have hmajor : Summable (fun e : ℕ ↦ r * (1 / 3 : ℝ) ^ e) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 3 : ℝ)‖ < 1)).mul_left _
  have htail : ‖tail‖ ≤ (3 / 2 : ℝ) * r := by
    calc
      ‖tail‖ ≤ ∑' e : ℕ, ‖a (e + 1) * x ^ (e + 1)‖ :=
        norm_tsum_le_tsum_norm htailNorm
      _ ≤ ∑' e : ℕ, r * (1 / 3 : ℝ) ^ e := by
        apply Summable.tsum_le_tsum
        · intro e
          rw [norm_mul, norm_pow, pow_add, pow_one]
          calc
            ‖a (e + 1)‖ * (r ^ e * r) ≤ 1 * (r ^ e * r) :=
              mul_le_mul_of_nonneg_right (ha _) (by positivity)
            _ = r * r ^ e := by ring
            _ ≤ r * (1 / 3 : ℝ) ^ e := by gcongr
        · exact htailNorm
        · exact hmajor
      _ = (3 / 2 : ℝ) * r := by
        rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num)]
        ring
  have htailHalf : ‖tail‖ ≤ 1 / 2 := htail.trans (by nlinarith)
  have hne : (∑' e : ℕ, a e * x ^ e) ≠ 0 := by
    rw [hsplit]
    intro hzero
    have htailEq : tail = -1 := by
      apply add_left_cancel (a := (1 : ℂ))
      simpa using hzero
    have hone : ‖tail‖ = 1 := by rw [htailEq, norm_neg, norm_one]
    linarith
  apply Complex.exp_log
  simpa only [gsA9LocalEulerFactor, a, x] using hne

/-- The quadratic logarithmic approximation under the direct local
smallness hypothesis. -/
theorem norm_log_gsA9LocalEulerFactor_sub_linear_le_of_norm_le_third
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hxnorm : ‖(p : ℂ) ^ (-s)‖ ≤ (1 / 3 : ℝ)) :
    ‖Complex.log (gsA9LocalEulerFactor f s p) -
        f p * (p : ℂ) ^ (-s)‖ ≤
      4 * ‖(p : ℂ) ^ (-s)‖ ^ 2 := by
  simpa only [gsA9LocalEulerFactor, pow_one] using
    norm_log_localEulerFactor_sub_linear_le
      (fun e ↦ f (p ^ e)) (by simpa using hmul.1)
      (fun e ↦ hbound _ (pow_pos hp.pos e)) ((p : ℂ) ^ (-s)) hxnorm

/-- Actual-local-factor A.11 on an arbitrary shifted line, assuming directly
that every Euler variable in the selected block has norm at most one third. -/
theorem norm_prod_gsA9LocalEulerFactor_sub_one_mul_exp_neg_radius_le_of_norm_le_third
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    {s : ℂ} (hsmall : ∀ p ∈ S,
      ‖(p : ℂ) ^ (-s)‖ ≤ (1 / 3 : ℝ)) :
    let z := ∑ p ∈ S, f p * (p : ℂ) ^ (-s)
    let R := ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖
    let V := ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2
    ‖(∏ p ∈ S, gsA9LocalEulerFactor f s p) - 1‖ *
        Real.exp (-R / 2) ≤
      Real.exp (z.re / 2 + 8 * V) := by
  dsimp only
  let z : ℂ := ∑ p ∈ S, f p * (p : ℂ) ^ (-s)
  let R : ℝ := ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖
  let V : ℝ := ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2
  let L : ℂ := ∑ p ∈ S, Complex.log (gsA9LocalEulerFactor f s p)
  let w : ℂ := L - z
  have hw : ‖w‖ ≤ 4 * V := by
    dsimp only [w, L, z, V]
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ p ∈ S, (Complex.log (gsA9LocalEulerFactor f s p) -
          f p * (p : ℂ) ^ (-s))‖ ≤
        ∑ p ∈ S, ‖Complex.log (gsA9LocalEulerFactor f s p) -
          f p * (p : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ S, 4 * ‖(p : ℂ) ^ (-s)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro p hpS
        exact norm_log_gsA9LocalEulerFactor_sub_linear_le_of_norm_le_third
          hmul hbound (hprime p hpS) (hsmall p hpS)
      _ = 4 * ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2 := by
        rw [Finset.mul_sum]
  have hz : ‖z‖ ≤ R := by
    dsimp only [z, R]
    calc
      ‖∑ p ∈ S, f p * (p : ℂ) ^ (-s)‖ ≤
          ∑ p ∈ S, ‖f p * (p : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ := by
        apply Finset.sum_le_sum
        intro p hpS
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _)
          (hbound p (hprime p hpS).pos)
  have hL : L = z + w := by dsimp only [w]; ring
  have hLnorm : ‖L‖ ≤ R + ‖w‖ := by
    rw [hL]
    calc
      ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le _ _
      _ ≤ R + ‖w‖ := by gcongr
  have hprod : (∏ p ∈ S, gsA9LocalEulerFactor f s p) = Complex.exp L := by
    dsimp only [L]
    rw [Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro p hpS
    exact (exp_log_gsA9LocalEulerFactor_of_norm_le_third
      hmul hbound (hprime p hpS) (hsmall p hpS)).symm
  rw [hprod]
  have hexpFactor :
      ‖Complex.exp L - 1‖ =
        Real.exp (L.re / 2) *
          ‖Complex.exp (L / 2) - Complex.exp (-(L / 2))‖ := by
    have hid : Complex.exp L - 1 =
        Complex.exp (L / 2) *
          (Complex.exp (L / 2) - Complex.exp (-(L / 2))) := by
      calc
        Complex.exp L - 1 =
            Complex.exp (L / 2 + L / 2) -
              Complex.exp (L / 2 + -(L / 2)) := by
          congr 1
          · ring
          · rw [show L / 2 + -(L / 2) = 0 by ring, Complex.exp_zero]
        _ = Complex.exp (L / 2) * Complex.exp (L / 2) -
              Complex.exp (L / 2) * Complex.exp (-(L / 2)) := by
          rw [Complex.exp_add, Complex.exp_add]
        _ = Complex.exp (L / 2) *
              (Complex.exp (L / 2) - Complex.exp (-(L / 2))) := by ring
    rw [hid, norm_mul, Complex.norm_exp]
    congr 1
    simp
  rw [hexpFactor]
  have hblock :=
    Erdos67.norm_exp_half_sub_exp_neg_half_mul_exp_neg_le_one_of_norm
      L (R + ‖w‖) hLnorm
  have hLre : L.re ≤ z.re + ‖w‖ := by
    rw [hL, Complex.add_re]
    linarith [Complex.re_le_norm w]
  have hV0 : 0 ≤ V := by dsimp only [V]; positivity
  have hexpRearrange :
      Real.exp (L.re / 2) * Real.exp (-R / 2) =
        Real.exp (L.re / 2 + ‖w‖ / 2) *
          Real.exp (-(R + ‖w‖) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    (Real.exp (L.re / 2) *
        ‖Complex.exp (L / 2) - Complex.exp (-(L / 2))‖) *
        Real.exp (-R / 2) =
      Real.exp (L.re / 2 + ‖w‖ / 2) *
        (‖Complex.exp (L / 2) - Complex.exp (-(L / 2))‖ *
          Real.exp (-(R + ‖w‖) / 2)) := by
        rw [mul_assoc]
        calc
          Real.exp (L.re / 2) *
                (‖Complex.exp (L / 2) - Complex.exp (-(L / 2))‖ *
                  Real.exp (-R / 2)) =
              (Real.exp (L.re / 2) * Real.exp (-R / 2)) *
                ‖Complex.exp (L / 2) - Complex.exp (-(L / 2))‖ := by ring
          _ = (Real.exp (L.re / 2 + ‖w‖ / 2) *
                Real.exp (-(R + ‖w‖) / 2)) *
                ‖Complex.exp (L / 2) - Complex.exp (-(L / 2))‖ := by
              rw [hexpRearrange]
          _ = Real.exp (L.re / 2 + ‖w‖ / 2) *
                (‖Complex.exp (L / 2) - Complex.exp (-(L / 2))‖ *
                  Real.exp (-(R + ‖w‖) / 2)) := by ring
    _ ≤ Real.exp (L.re / 2 + ‖w‖ / 2) * 1 :=
      mul_le_mul_of_nonneg_left hblock (Real.exp_pos _).le
    _ ≤ Real.exp (z.re / 2 + ‖w‖) := by
      simp only [mul_one]
      apply Real.exp_le_exp.mpr
      linarith
    _ ≤ Real.exp (z.re / 2 + 8 * V) := by
      apply Real.exp_le_exp.mpr
      have : ‖w‖ ≤ 8 * V := hw.trans (by nlinarith)
      linarith

/-- Matching lower Euler-product comparison under the direct one-third
smallness hypothesis.  This is the shifted-line counterpart of
`exp_linear_sub_square_le_norm_prod_gsA9LocalEulerFactor`. -/
theorem exp_linear_sub_square_le_norm_prod_gsA9LocalEulerFactor_of_norm_le_third
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    {s : ℂ} (hsmall : ∀ p ∈ S,
      ‖(p : ℂ) ^ (-s)‖ ≤ (1 / 3 : ℝ)) :
    let z := ∑ p ∈ S, f p * (p : ℂ) ^ (-s)
    let V := ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2
    Real.exp (z.re - 4 * V) ≤
      ‖∏ p ∈ S, gsA9LocalEulerFactor f s p‖ := by
  dsimp only
  let z : ℂ := ∑ p ∈ S, f p * (p : ℂ) ^ (-s)
  let V : ℝ := ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2
  let L : ℂ := ∑ p ∈ S, Complex.log (gsA9LocalEulerFactor f s p)
  let w : ℂ := L - z
  have hw : ‖w‖ ≤ 4 * V := by
    dsimp only [w, L, z, V]
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ p ∈ S, (Complex.log (gsA9LocalEulerFactor f s p) -
          f p * (p : ℂ) ^ (-s))‖ ≤
        ∑ p ∈ S, ‖Complex.log (gsA9LocalEulerFactor f s p) -
          f p * (p : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ S, 4 * ‖(p : ℂ) ^ (-s)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro p hpS
        exact norm_log_gsA9LocalEulerFactor_sub_linear_le_of_norm_le_third
          hmul hbound (hprime p hpS) (hsmall p hpS)
      _ = 4 * ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2 := by
        rw [Finset.mul_sum]
  have hL : L = z + w := by dsimp only [w]; ring
  have hprod : (∏ p ∈ S, gsA9LocalEulerFactor f s p) = Complex.exp L := by
    dsimp only [L]
    rw [Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro p hpS
    exact (exp_log_gsA9LocalEulerFactor_of_norm_le_third
      hmul hbound (hprime p hpS) (hsmall p hpS)).symm
  rw [hprod, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  rw [hL, Complex.add_re]
  have hwre : -‖w‖ ≤ w.re :=
    neg_le_of_abs_le (Complex.abs_re_le_norm w)
  linarith

end

end Erdos67.MRHalaszBands
