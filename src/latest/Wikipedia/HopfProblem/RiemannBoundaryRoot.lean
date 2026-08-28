import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Principal roots on the closed upper half-plane

The principal complex power is continuous from the upper half-plane at its
negative real boundary. This is a one-sided assertion: no continuity across
the principal logarithm's cut is asserted. At zero the positive real exponent
gives continuity. These maps unfold corners with angles `π / n`.
-/

noncomputable section

open Complex Set Filter
open scoped Topology

namespace Wikipedia.HopfProblem.RiemannBoundary

/-- The principal `n`-th root, defined by the actual principal complex power. -/
def principalRoot (n : ℕ) (z : ℂ) : ℂ := z ^ ((n : ℂ)⁻¹)

@[simp]
theorem principalRoot_pow {n : ℕ} (hn : 0 < n) (z : ℂ) :
    principalRoot n z ^ n = z :=
  cpow_nat_inv_pow z hn.ne'

@[simp]
theorem principalRoot_zero {n : ℕ} (hn : 0 < n) : principalRoot n 0 = 0 := by
  exact zero_cpow (inv_ne_zero (Nat.cast_ne_zero.mpr hn.ne'))

theorem principalRoot_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (principalRoot n) := by
  intro z w h
  simpa only [principalRoot_pow hn] using congrArg (fun u : ℂ => u ^ n) h

@[simp]
theorem principalRoot_eq_zero_iff {n : ℕ} (hn : 0 < n) {z : ℂ} :
    principalRoot n z = 0 ↔ z = 0 := by
  have h : principalRoot n z = principalRoot n 0 ↔ z = 0 :=
    (principalRoot_injective hn).eq_iff
  simpa only [principalRoot_zero hn] using h

@[simp]
theorem norm_principalRoot (n : ℕ) (z : ℂ) :
    ‖principalRoot n z‖ = ‖z‖ ^ ((n : ℝ)⁻¹) :=
  norm_cpow_inv_nat z n

private theorem principalRoot_exponent_re_pos {n : ℕ} (hn : 0 < n) :
    0 < ((n : ℂ)⁻¹).re := by
  simpa only [← ofReal_natCast, ← ofReal_inv, ofReal_re] using
    inv_pos.mpr (Nat.cast_pos.mpr hn : (0 : ℝ) < n)

/-- At zero the principal root is continuous even without restricting the
approach to a half-plane. -/
theorem continuousAt_principalRoot_zero {n : ℕ} (hn : 0 < n) :
    ContinuousAt (principalRoot n) 0 :=
  continuousAt_cpow_const_of_re_pos (Or.inl (by simp))
    (principalRoot_exponent_re_pos hn)

/-- One-sided continuity at the negative real boundary is obtained from the
one-sided logarithm theorem, not from continuity of the principal branch on
the whole plane. -/
theorem continuousOn_principalRoot_closedUpper {n : ℕ} (hn : 0 < n) :
    ContinuousOn (principalRoot n) {z : ℂ | 0 ≤ z.im} := by
  intro z _hz
  change ContinuousWithinAt (fun w : ℂ => w ^ ((n : ℂ)⁻¹)) _ z
  by_cases h : 0 ≤ z.re ∨ z.im ≠ 0
  · exact (continuousAt_cpow_const_of_re_pos h
      (principalRoot_exponent_re_pos hn)).continuousWithinAt
  push Not at h
  have hz0 : z ≠ 0 := fun hz => by simpa only [hz, zero_re, lt_self_iff_false] using h.1
  have hc : ContinuousWithinAt
      (fun w : ℂ => exp (log w * (n : ℂ)⁻¹)) {w : ℂ | 0 ≤ w.im} z :=
    continuous_exp.continuousAt.comp_continuousWithinAt
      ((continuousWithinAt_log_of_re_neg_of_im_zero h.1 h.2).mul_const _)
  exact hc.congr_of_eventuallyEq
    ((cpow_eq_nhds hz0).filter_mono nhdsWithin_le_nhds)
    (cpow_def_of_ne_zero hz0 _)

/-- The root is holomorphic on the open upper half-plane. -/
theorem differentiableOn_principalRoot_upper (n : ℕ) :
    DifferentiableOn ℂ (principalRoot n) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact ((differentiableAt_id : DifferentiableAt ℂ (fun w : ℂ => w) z).cpow_const
    (Or.inr (ne_of_gt hz))).differentiableWithinAt

/-- Holomorphicity with an actual open neighbourhood at every upper-half-plane
point. -/
theorem analyticOnNhd_principalRoot_upper (n : ℕ) :
    AnalyticOnNhd ℂ (principalRoot n) {z : ℂ | 0 < z.im} :=
  (differentiableOn_principalRoot_upper n).analyticOnNhd
    (isOpen_lt continuous_const continuous_im)

/-- Exact root value on the nonnegative real ray. -/
theorem principalRoot_ofReal_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    principalRoot n (x : ℂ) = (x ^ ((n : ℝ)⁻¹) : ℝ) := by
  simpa only [principalRoot, ofReal_inv, ofReal_natCast] using
    (ofReal_cpow hx ((n : ℝ)⁻¹)).symm

/-- Exact root value on the nonpositive real ray, with argument `π / n`. -/
theorem principalRoot_ofReal_nonpos (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    principalRoot n (x : ℂ) = ((-x) ^ ((n : ℝ)⁻¹) : ℝ) *
      exp ((Real.pi / (n : ℝ) : ℝ) * I) := by
  rw [principalRoot, ofReal_cpow_of_nonpos hx]
  have hr : (-(x : ℂ)) ^ ((n : ℂ)⁻¹) = ((-x) ^ ((n : ℝ)⁻¹) : ℝ) := by
    simpa only [principalRoot, ofReal_neg] using
      principalRoot_ofReal_nonneg n (neg_nonneg.mpr hx)
  rw [hr]
  congr 2
  simp only [div_eq_mul_inv, ofReal_mul, ofReal_inv, ofReal_natCast]
  ring

/-- A positive real input gives a strictly positive real root. -/
theorem principalRoot_ofReal_pos (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (principalRoot n (x : ℂ)).re ∧ (principalRoot n (x : ℂ)).im = 0 := by
  rw [principalRoot_ofReal_nonneg n hx.le]
  exact ⟨Real.rpow_pos_of_pos hx _, ofReal_im _⟩

/-- A negative real input gives a positive multiple of the ray of angle `π / n`. -/
theorem principalRoot_ofReal_neg (n : ℕ) {x : ℝ} (hx : x < 0) :
    ∃ r : ℝ, 0 < r ∧ principalRoot n (x : ℂ) =
      (r : ℂ) * exp ((Real.pi / (n : ℝ) : ℝ) * I) :=
  ⟨(-x) ^ ((n : ℝ)⁻¹), Real.rpow_pos_of_pos (neg_pos.mpr hx) _,
    principalRoot_ofReal_nonpos n hx.le⟩

private theorem arg_div_nat_mem_Ioc {n : ℕ} (hn : 0 < n) (z : ℂ) :
    z.arg / (n : ℝ) ∈ Ioc (-Real.pi) Real.pi := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · rw [lt_div_iff₀ hnR]
    have hl : -Real.pi * (n : ℝ) ≤ -Real.pi := by
      nlinarith [Real.pi_pos]
    exact hl.trans_lt (neg_pi_lt_arg z)
  · rw [div_le_iff₀ hnR]
    have hu : Real.pi ≤ Real.pi * (n : ℝ) := by
      nlinarith [Real.pi_pos]
    exact (arg_le_pi z).trans hu

/-- The principal root divides the principal argument by `n`. -/
theorem arg_principalRoot {n : ℕ} (hn : 0 < n) (z : ℂ) :
    arg (principalRoot n z) = z.arg / (n : ℝ) := by
  by_cases hz : z = 0
  · simp only [hz, principalRoot_zero hn, arg_zero, zero_div]
  have hpolar : principalRoot n z = (‖z‖ ^ ((n : ℝ)⁻¹) : ℝ) *
      (Real.cos (z.arg / (n : ℝ)) + Real.sin (z.arg / (n : ℝ)) * I) := by
    simpa only [principalRoot, ofReal_inv, ofReal_natCast, div_eq_mul_inv] using
      cpow_ofReal z ((n : ℝ)⁻¹)
  rw [hpolar]
  simpa only [ofReal_cos, ofReal_sin] using
    arg_mul_cos_add_sin_mul_I
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) ((n : ℝ)⁻¹))
      (arg_div_nat_mem_Ioc hn z)

/-- Closed-upper-half-plane points map into the closed sector of angle `π / n`. -/
theorem principalRoot_arg_mem_Icc {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : 0 ≤ z.im) : arg (principalRoot n z) ∈ Icc 0 (Real.pi / (n : ℝ)) := by
  rw [arg_principalRoot hn]
  exact ⟨div_nonneg (arg_nonneg_iff.mpr hz) (Nat.cast_nonneg n),
    div_le_div_of_nonneg_right (arg_le_pi z) (Nat.cast_nonneg n)⟩

/-- Open-upper-half-plane points map into the open sector of angle `π / n`. -/
theorem principalRoot_arg_mem_Ioo {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : 0 < z.im) : arg (principalRoot n z) ∈ Ioo 0 (Real.pi / (n : ℝ)) := by
  rw [arg_principalRoot hn]
  have harg0 : z.arg ≠ 0 := fun h => (ne_of_gt hz) (arg_eq_zero_iff.mp h).2
  have harg : 0 < z.arg := lt_of_le_of_ne (arg_nonneg_iff.mpr hz.le) harg0.symm
  exact ⟨div_pos harg (Nat.cast_pos.mpr hn),
    (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hn)).mpr
      (arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hz)))⟩

/-- Raising a point in the root sector to the `n`th power and taking the
principal root recovers that point. -/
theorem principalRoot_pow_of_sector {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : z.arg ∈ Icc 0 (Real.pi / (n : ℝ))) :
    principalRoot n (z ^ n) = z := by
  apply pow_cpow_nat_inv hn.ne' _ hz.2
  exact (neg_neg_of_pos (div_pos Real.pi_pos (Nat.cast_pos.mpr hn))).trans_le hz.1

end Wikipedia.HopfProblem.RiemannBoundary
