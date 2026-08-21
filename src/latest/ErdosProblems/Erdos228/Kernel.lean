import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Trigonometric-kernel lemmas for Erdős Problem 228

This file collects the elementary finite-sum and cancellation identities used in
the odd-sine correction part of the Balister--Bollobás--Morris--Sahasrabudhe--Tiba
construction.
-/

namespace Erdos228.Kernel

open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral

/-! ## Odd Dirichlet kernels -/

/-- The odd-cosine sum in a denominator-free form.  This is just the
telescoping identity
`2 sin(t) cos((2j+1)t) = sin(2(j+1)t) - sin(2jt)` summed over `j`. -/
lemma two_mul_sin_mul_oddCosSum (n : ℕ) (t : ℝ) :
    2 * Real.sin t * (∑ j ∈ Finset.range n,
      Real.cos (((2 * j + 1 : ℕ) : ℝ) * t)) =
      Real.sin ((2 * n : ℕ) * t) := by
  have hterm (j : ℕ) :
      2 * Real.sin t * Real.cos (((2 * j + 1 : ℕ) : ℝ) * t) =
        Real.sin (((2 * (j + 1) : ℕ) : ℝ) * t) -
          Real.sin (((2 * j : ℕ) : ℝ) * t) := by
    rw [Real.two_mul_sin_mul_cos]
    have hsub : t - ((2 * j + 1 : ℕ) : ℝ) * t =
        -(((2 * j : ℕ) : ℝ) * t) := by
      push_cast
      ring
    have hadd : t + ((2 * j + 1 : ℕ) : ℝ) * t =
        ((2 * (j + 1) : ℕ) : ℝ) * t := by
      push_cast
      ring
    rw [hsub, hadd, Real.sin_neg]
    ring
  calc
    2 * Real.sin t * (∑ j ∈ Finset.range n,
        Real.cos (((2 * j + 1 : ℕ) : ℝ) * t)) =
        ∑ j ∈ Finset.range n,
          (2 * Real.sin t * Real.cos (((2 * j + 1 : ℕ) : ℝ) * t)) := by
            rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range n,
        (Real.sin (((2 * (j + 1) : ℕ) : ℝ) * t) -
          Real.sin (((2 * j : ℕ) : ℝ) * t)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hterm j
    _ = Real.sin (((2 * n : ℕ) : ℝ) * t) - Real.sin 0 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero, zero_mul,
        Real.sin_zero] using
        (Finset.sum_range_sub
          (fun j : ℕ => Real.sin (((2 * j : ℕ) : ℝ) * t)) n)
    _ = Real.sin ((2 * n : ℕ) * t) := by simp

/-- Quotient form of the finite odd-cosine identity. -/
lemma two_mul_oddCosSum_eq (n : ℕ) {t : ℝ} (ht : Real.sin t ≠ 0) :
    2 * (∑ j ∈ Finset.range n,
      Real.cos (((2 * j + 1 : ℕ) : ℝ) * t)) =
      Real.sin ((2 * n : ℕ) * t) / Real.sin t := by
  have h := two_mul_sin_mul_oddCosSum n t
  apply (eq_div_iff ht).2
  rw [← h]
  ring

/-- Product-to-sum in the normalization convenient for the odd kernel. -/
lemma two_mul_sin_mul_sin (u v : ℝ) :
    2 * Real.sin u * Real.sin v = Real.cos (u - v) - Real.cos (u + v) := by
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- The odd Dirichlet kernel identity used in the construction. -/
theorem odd_dirichlet_kernel (n : ℕ) {θ θ₀ : ℝ}
    (hsub : Real.sin (θ - θ₀) ≠ 0) (hadd : Real.sin (θ + θ₀) ≠ 0) :
    4 * (∑ j ∈ Finset.range n,
      Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
        Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ)) =
      Real.sin ((2 * n : ℕ) * (θ - θ₀)) / Real.sin (θ - θ₀) -
        Real.sin ((2 * n : ℕ) * (θ + θ₀)) / Real.sin (θ + θ₀) := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_assoc, Finset.mul_sum]
  have hprod (j : ℕ) :
      2 * (Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
        Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ)) =
        Real.cos (((2 * j + 1 : ℕ) : ℝ) * (θ - θ₀)) -
          Real.cos (((2 * j + 1 : ℕ) : ℝ) * (θ + θ₀)) := by
    calc
      2 * (Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
          Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ)) =
          2 * Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
            Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ) := by ring
      _ = Real.cos ((((2 * j + 1 : ℕ) : ℝ) * θ₀) -
            (((2 * j + 1 : ℕ) : ℝ) * θ)) -
          Real.cos ((((2 * j + 1 : ℕ) : ℝ) * θ₀) +
            (((2 * j + 1 : ℕ) : ℝ) * θ)) :=
        two_mul_sin_mul_sin _ _
      _ = Real.cos (((2 * j + 1 : ℕ) : ℝ) * (θ - θ₀)) -
          Real.cos (((2 * j + 1 : ℕ) : ℝ) * (θ + θ₀)) := by
            have hneg : (((2 * j + 1 : ℕ) : ℝ) * θ₀) -
                (((2 * j + 1 : ℕ) : ℝ) * θ) =
                -(((2 * j + 1 : ℕ) : ℝ) * (θ - θ₀)) := by ring
            have hplus : (((2 * j + 1 : ℕ) : ℝ) * θ₀) +
                (((2 * j + 1 : ℕ) : ℝ) * θ) =
                ((2 * j + 1 : ℕ) : ℝ) * (θ + θ₀) := by ring
            rw [hneg, Real.cos_neg, hplus]
  rw [Finset.sum_congr rfl (fun j _ => hprod j), Finset.sum_sub_distrib,
    mul_sub, two_mul_oddCosSum_eq n hsub, two_mul_oddCosSum_eq n hadd]

/-! ## Exact cancellation over a period -/

/-- A scaled sine has the expected elementary antiderivative. -/
lemma integral_sin_mul (c a b : ℝ) (hc : c ≠ 0) :
    (∫ x in a..b, Real.sin (c * x)) =
      (Real.cos (c * a) - Real.cos (c * b)) / c := by
  rw [intervalIntegral.integral_comp_mul_left Real.sin hc, integral_sin]
  simp only [smul_eq_mul]
  field_simp

/-- The integral of a scaled sine over one complete period is zero. -/
lemma integral_sin_mul_add_period (c a : ℝ) (hc : c ≠ 0) :
    (∫ x in a..(a + 2 * Real.pi / c), Real.sin (c * x)) = 0 := by
  rw [integral_sin_mul c a (a + 2 * Real.pi / c) hc]
  have hend : c * (a + 2 * Real.pi / c) = c * a + 2 * Real.pi := by
    field_simp
  rw [hend, Real.cos_add_two_pi]
  simp

/-- In the frequency `2n` normalization, a full sine period has length `π/n`.
This is the basic cancellation used when endpoints lie on the `π/n` grid. -/
lemma integral_sin_two_nat_mul_add_gridPeriod (n : ℕ) (hn : n ≠ 0) (a : ℝ) :
    (∫ x in a..(a + Real.pi / n), Real.sin ((2 * n : ℕ) * x)) = 0 := by
  have hc : ((2 * n : ℕ) : ℝ) ≠ 0 := by positivity
  have hlen : 2 * Real.pi / (((2 * n : ℕ) : ℝ)) = Real.pi / (n : ℝ) := by
    push_cast
    field_simp
  simpa only [hlen] using integral_sin_mul_add_period (((2 * n : ℕ) : ℝ)) a hc

/-- Cancellation between any two endpoints of the `π/n` grid. -/
lemma integral_sin_two_nat_mul_grid (n : ℕ) (hn : n ≠ 0) (k l : ℕ) :
    (∫ x in ((k : ℝ) * Real.pi / n)..((l : ℝ) * Real.pi / n),
      Real.sin ((2 * n : ℕ) * x)) = 0 := by
  have hc : ((2 * n : ℕ) : ℝ) ≠ 0 := by positivity
  rw [integral_sin_mul (((2 * n : ℕ) : ℝ))
    ((k : ℝ) * Real.pi / n) ((l : ℝ) * Real.pi / n) hc]
  have hk : ((2 * n : ℕ) : ℝ) * ((k : ℝ) * Real.pi / n) =
      (k : ℝ) * (2 * Real.pi) := by
    push_cast
    field_simp
  have hl : ((2 * n : ℕ) : ℝ) * ((l : ℝ) * Real.pi / n) =
      (l : ℝ) * (2 * Real.pi) := by
    push_cast
    field_simp
  rw [hk, hl, Real.cos_nat_mul_two_pi, Real.cos_nat_mul_two_pi]
  simp

/-! ## Elementary Taylor and sine-integral bounds -/

/-- The fourth-order Taylor polynomial is an upper bound for cosine on the
nonnegative half-line.  The proof differentiates once and uses Mathlib's
global cubic lower bound for sine. -/
lemma cos_le_taylor_four {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f (t : ℝ) := 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hderiv (t : ℝ) :
      deriv f t = -t + t ^ 3 / 6 + Real.sin t := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [Real.sin_ge_sub_cube ht0]
  have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 by exact hx) hx
  dsimp [f] at h
  norm_num at h
  exact h

/-- The fifth-order Taylor polynomial is an upper bound for sine on the
nonnegative half-line. -/
lemma sin_le_taylor_five {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f (t : ℝ) := t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
  have hderiv (t : ℝ) :
      deriv f t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [cos_le_taylor_four ht0]
  have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 by exact hx) hx
  dsimp [f] at h
  norm_num at h
  exact h

/-- Dividing the cubic sine lower bound by a nonnegative argument gives the
quadratic lower bound for the continuously extended sinc function. -/
lemma one_sub_sq_div_six_le_sinc {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 6 ≤ Real.sinc x := by
  obtain rfl | hxpos := hx.eq_or_lt
  · simp
  rw [Real.sinc_of_ne_zero hxpos.ne']
  apply (le_div_iff₀ hxpos).2
  nlinarith [Real.sin_ge_sub_cube hxpos.le]

/-- The corresponding quartic upper bound for sinc. -/
lemma sinc_le_taylor_four {x : ℝ} (hx : 0 ≤ x) :
    Real.sinc x ≤ 1 - x ^ 2 / 6 + x ^ 4 / 120 := by
  obtain rfl | hxpos := hx.eq_or_lt
  · norm_num
  rw [Real.sinc_of_ne_zero hxpos.ne']
  apply (div_le_iff₀ hxpos).2
  nlinarith [sin_le_taylor_five hxpos.le]

/-- The unnormalized sine integral `Si(b)`, expressed using the continuous
extension of `sin x / x` at the origin. -/
noncomputable def sineIntegral (b : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..b, Real.sinc x

/-- Integrating the quadratic lower Taylor bound for sinc. -/
lemma sineIntegral_lower {b : ℝ} (hb : 0 ≤ b) :
    b - b ^ 3 / 18 ≤ sineIntegral b := by
  have hp : IntervalIntegrable (fun x : ℝ => 1 - x ^ 2 / 6) volume 0 b := by
    exact (by fun_prop : Continuous (fun x : ℝ => 1 - x ^ 2 / 6)).intervalIntegrable 0 b
  have hs : IntervalIntegrable Real.sinc volume 0 b :=
    Real.continuous_sinc.intervalIntegrable 0 b
  have hmono := intervalIntegral.integral_mono_on hb hp hs
    (fun x hx => one_sub_sq_div_six_le_sinc hx.1)
  calc
    b - b ^ 3 / 18 = ∫ x in (0 : ℝ)..b, (1 - x ^ 2 / 6) := by
      simp [intervalIntegral.integral_sub, intervalIntegral.integral_div, integral_pow]
      ring
    _ ≤ ∫ x in (0 : ℝ)..b, Real.sinc x := hmono
    _ = sineIntegral b := rfl

/-- Integrating the quartic upper Taylor bound for sinc. -/
lemma sineIntegral_upper {b : ℝ} (hb : 0 ≤ b) :
    sineIntegral b ≤ b - b ^ 3 / 18 + b ^ 5 / 600 := by
  have hs : IntervalIntegrable Real.sinc volume 0 b :=
    Real.continuous_sinc.intervalIntegrable 0 b
  have hp1 : IntervalIntegrable (fun x : ℝ => 1 - x ^ 2 / 6) volume 0 b :=
    (by fun_prop : Continuous (fun x : ℝ => 1 - x ^ 2 / 6)).intervalIntegrable 0 b
  have hp2 : IntervalIntegrable (fun x : ℝ => x ^ 4 / 120) volume 0 b :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 4 / 120)).intervalIntegrable 0 b
  have hp : IntervalIntegrable
      (fun x : ℝ => 1 - x ^ 2 / 6 + x ^ 4 / 120) volume 0 b := hp1.add hp2
  have hmono := intervalIntegral.integral_mono_on hb hs hp
    (fun x hx => sinc_le_taylor_four hx.1)
  calc
    sineIntegral b = ∫ x in (0 : ℝ)..b, Real.sinc x := rfl
    _ ≤ ∫ x in (0 : ℝ)..b, (1 - x ^ 2 / 6 + x ^ 4 / 120) := hmono
    _ = b - b ^ 3 / 18 + b ^ 5 / 600 := by
      rw [intervalIntegral.integral_add hp1 hp2]
      simp [intervalIntegral.integral_sub, intervalIntegral.integral_div, integral_pow]
      ring

/-- A concrete lower bound at `π`.  This is the estimate needed for the main
lobe of the sinc kernel; it uses only the cubic Taylor bound and Mathlib's
two-decimal enclosures of `π`. -/
theorem four_thirds_lt_sineIntegral_pi :
    (4 : ℝ) / 3 < sineIntegral Real.pi := by
  have hSi := sineIntegral_lower Real.pi_pos.le
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hcube : Real.pi ^ 3 < (3.15 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le (by norm_num)
  norm_num at hpi hcube ⊢
  nlinarith

/-- A concrete upper bound at `π`, obtained by integrating the fifth-order
Taylor bound for sine. -/
theorem sineIntegral_pi_lt_two : sineIntegral Real.pi < 2 := by
  have hSi := sineIntegral_upper Real.pi_pos.le
  have hpi : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hcube : (3.14 : ℝ) ^ 3 < Real.pi ^ 3 :=
    pow_lt_pow_left₀ Real.pi_gt_d2 (by norm_num) (by norm_num)
  have hfifth : Real.pi ^ 5 < (3.15 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le (by norm_num)
  norm_num at hpi hcube hfifth ⊢
  nlinarith

theorem sineIntegral_pi_mem : sineIntegral Real.pi ∈ Ioo ((4 : ℝ) / 3) 2 :=
  ⟨four_thirds_lt_sineIntegral_pi, sineIntegral_pi_lt_two⟩

end Erdos228.Kernel
