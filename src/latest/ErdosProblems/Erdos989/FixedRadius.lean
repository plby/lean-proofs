/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The fixed-radius disk Fourier multiplier

For the Fourier-transform convention used by Mathlib, the Fourier transform of
the indicator of a planar disk of radius `r` is the radial multiplier

`r * J₁ (2 * π * r * ρ) / ρ`

away from `ρ = 0`, with limiting value `π * r ^ 2` at the origin.  Mathlib
4.33.0 does not contain Bessel functions.  We therefore give the integer-order
Schläfli integral for `J₁` as the definition needed by the multiplier.

The last theorem is the order-theoretic energy step used after construction of
an auxiliary multiplier: an almost-everywhere lower bound for that multiplier
turns into the same lower bound for every integrable squared Fourier amplitude.
It deliberately separates this elementary step from any quantitative
fixed-radius escape estimate.
-/

noncomputable section

open MeasureTheory
open scoped Interval

namespace Erdos989
namespace FixedRadius

/-! ## The order-one Bessel function and the disk multiplier -/

/-- The order-one Bessel function, defined by its Schläfli integral

`J₁(x) = π⁻¹ ∫₀^π cos (θ - x sin θ) dθ`.

This integral identity has no correction term at integer order one. -/
def besselJOne (x : ℝ) : ℝ :=
  Real.pi⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, Real.cos (θ - x * Real.sin θ)

/-- `J₁(0) = 0`, directly from the defining integral. -/
@[simp] theorem besselJOne_zero : besselJOne 0 = 0 := by
  simp [besselJOne]

/-- The order-one Bessel function is odd.  This is the reflection
`θ ↦ π - θ` in the Schläfli integral. -/
theorem besselJOne_neg (x : ℝ) : besselJOne (-x) = -besselJOne x := by
  rw [besselJOne, besselJOne]
  have h :
      (∫ θ in (0 : ℝ)..Real.pi, Real.cos (θ - -x * Real.sin θ)) =
        -∫ θ in (0 : ℝ)..Real.pi, Real.cos (θ - x * Real.sin θ) := by
    have hs := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := Real.pi)
      (fun θ : ℝ ↦ Real.cos (θ - -x * Real.sin θ)) Real.pi
    simp only [sub_self, sub_zero] at hs
    rw [← hs]
    simp only [Real.sin_pi_sub]
    have hpoint : ∀ θ : ℝ,
        Real.cos (Real.pi - θ - -x * Real.sin θ) =
          -Real.cos (θ - x * Real.sin θ) := by
      intro θ
      rw [show Real.pi - θ - -x * Real.sin θ =
        Real.pi - (θ - x * Real.sin θ) by ring]
      exact Real.cos_pi_sub _
    calc
      (∫ θ in (0 : ℝ)..Real.pi,
          Real.cos (Real.pi - θ - -x * Real.sin θ)) =
          ∫ θ in (0 : ℝ)..Real.pi,
            -Real.cos (θ - x * Real.sin θ) := by
              apply intervalIntegral.integral_congr
              intro θ _
              exact hpoint θ
      _ = -∫ θ in (0 : ℝ)..Real.pi,
          Real.cos (θ - x * Real.sin θ) := intervalIntegral.integral_neg
  rw [h]
  ring

/-- The elementary global bound `|J₁(x)| ≤ 1`, obtained by estimating the
Schläfli integral by the integral of the constant function one. -/
theorem abs_besselJOne_le_one (x : ℝ) : |besselJOne x| ≤ 1 := by
  rw [besselJOne, abs_mul, abs_of_pos (inv_pos.mpr Real.pi_pos)]
  have hf : IntervalIntegrable
      (fun θ : ℝ ↦ Real.cos (θ - x * Real.sin θ)) volume 0 Real.pi := by
    exact (Real.continuous_cos.comp
      (continuous_id.sub (continuous_const.mul Real.continuous_sin))).intervalIntegrable _ _
  have hi :
      |∫ θ in (0 : ℝ)..Real.pi, Real.cos (θ - x * Real.sin θ)| ≤ Real.pi := by
    calc
      |∫ θ in (0 : ℝ)..Real.pi, Real.cos (θ - x * Real.sin θ)| ≤
          ∫ θ in (0 : ℝ)..Real.pi, |Real.cos (θ - x * Real.sin θ)| :=
        intervalIntegral.abs_integral_le_integral_abs Real.pi_nonneg
      _ ≤ ∫ _θ in (0 : ℝ)..Real.pi, (1 : ℝ) := by
        apply intervalIntegral.integral_mono Real.pi_nonneg hf.abs intervalIntegrable_const
        intro θ
        exact Real.abs_cos_le_one _
      _ = Real.pi := by simp
  calc
    Real.pi⁻¹ * |∫ θ in (0 : ℝ)..Real.pi, Real.cos (θ - x * Real.sin θ)| ≤
        Real.pi⁻¹ * Real.pi :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr Real.pi_nonneg)
    _ = 1 := inv_mul_cancel₀ Real.pi_ne_zero

/-- The radial Fourier multiplier of a planar closed disk of radius `r`, using
the Fourier convention with phase `exp (-2 π i ⟨x,ξ⟩)`.

The value at frequency zero is written separately because the quotient formula
has a removable singularity there. -/
def diskMultiplier (r ρ : ℝ) : ℝ :=
  if ρ = 0 then Real.pi * r ^ 2
  else r * besselJOne (2 * Real.pi * r * ρ) / ρ

/-- The zero-frequency multiplier is the area of the disk. -/
@[simp] theorem diskMultiplier_zero (r : ℝ) :
    diskMultiplier r 0 = Real.pi * r ^ 2 := by
  simp [diskMultiplier]

/-- Away from zero, the disk multiplier is the Bessel quotient. -/
theorem diskMultiplier_of_ne_zero {r ρ : ℝ} (hρ : ρ ≠ 0) :
    diskMultiplier r ρ = r * besselJOne (2 * Real.pi * r * ρ) / ρ := by
  simp [diskMultiplier, hρ]

/-- The radial multiplier is even in its frequency variable. -/
theorem diskMultiplier_neg (r ρ : ℝ) :
    diskMultiplier r (-ρ) = diskMultiplier r ρ := by
  by_cases hρ : ρ = 0
  · subst ρ
    simp [diskMultiplier]
  · rw [diskMultiplier_of_ne_zero (neg_ne_zero.mpr hρ),
      diskMultiplier_of_ne_zero hρ]
    rw [show 2 * Real.pi * r * -ρ = -(2 * Real.pi * r * ρ) by ring,
      besselJOne_neg]
    field_simp

/-- A radius-zero disk has the zero multiplier. -/
@[simp] theorem diskMultiplier_zero_radius (ρ : ℝ) :
    diskMultiplier 0 ρ = 0 := by
  by_cases hρ : ρ = 0 <;> simp [diskMultiplier, hρ]

/-- The elementary decay bound away from frequency zero.  Beck's fixed-radius
argument needs a much sharper oscillatory lower estimate after avoiding the
Bessel zeros; this theorem is only the universal upper bound supplied by the
integral representation. -/
theorem abs_diskMultiplier_le {r ρ : ℝ} (hρ : ρ ≠ 0) :
    |diskMultiplier r ρ| ≤ |r| / |ρ| := by
  rw [diskMultiplier_of_ne_zero hρ, abs_div, abs_mul]
  exact div_le_div_of_nonneg_right
    (by simpa using
      (mul_le_mul_of_nonneg_left
        (abs_besselJOne_le_one (2 * Real.pi * r * ρ)) (abs_nonneg r)))
    (abs_nonneg ρ)

/-- The squared disk multiplier is nonnegative at every frequency. -/
theorem diskMultiplier_sq_nonneg (r ρ : ℝ) :
    0 ≤ diskMultiplier r ρ ^ 2 :=
  sq_nonneg _

/-! ## The Fourier-energy extraction step -/

/-- A multiplier which is bounded below almost everywhere is bounded below
after integration against any nonnegative squared complex amplitude.

This is the exact analytic extraction step once an auxiliary multiplier has
been shown to satisfy a uniform lower estimate.  Both
integrability assumptions are explicit, which avoids relying on a boundedness
claim for the auxiliary multiplier. -/
theorem fixedRadius_energy_lower
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (κ : ℝ) (φ : X → ℂ) (Q : X → ℝ)
    (hφ : Integrable (fun ξ ↦ Complex.normSq (φ ξ)) μ)
    (hQφ : Integrable (fun ξ ↦ Q ξ * Complex.normSq (φ ξ)) μ)
    (hQ : ∀ᵐ ξ ∂μ, κ ≤ Q ξ) :
    κ * ∫ ξ, Complex.normSq (φ ξ) ∂μ ≤
      ∫ ξ, Q ξ * Complex.normSq (φ ξ) ∂μ := by
  rw [← integral_const_mul]
  apply integral_mono_ae (hφ.const_mul κ) hQφ
  filter_upwards [hQ] with ξ hQξ
  exact mul_le_mul_of_nonneg_right hQξ (Complex.normSq_nonneg _)

/-- Specialization of `fixedRadius_energy_lower` to the squared disk
multiplier itself.  In the fixed-radius argument this is applied with a
measure restricted to frequencies retained by the Bessel-zero escape lemma.
It is not a positive lower bound on the entire frequency plane: `J₁` has
zeros, so such a global positive bound would be false. -/
theorem diskMultiplier_energy_lower
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (κ r : ℝ) (φ : X → ℂ) (ρ : X → ℝ)
    (hφ : Integrable (fun ξ ↦ Complex.normSq (φ ξ)) μ)
    (hweighted : Integrable
      (fun ξ ↦ diskMultiplier r (ρ ξ) ^ 2 * Complex.normSq (φ ξ)) μ)
    (hlower : ∀ᵐ ξ ∂μ, κ ≤ diskMultiplier r (ρ ξ) ^ 2) :
    κ * ∫ ξ, Complex.normSq (φ ξ) ∂μ ≤
      ∫ ξ, diskMultiplier r (ρ ξ) ^ 2 * Complex.normSq (φ ξ) ∂μ :=
  fixedRadius_energy_lower κ φ (fun ξ ↦ diskMultiplier r (ρ ξ) ^ 2)
    hφ hweighted hlower

end FixedRadius
end Erdos989
