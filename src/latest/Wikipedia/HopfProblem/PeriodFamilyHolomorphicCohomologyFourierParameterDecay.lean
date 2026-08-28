import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterContinuity
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterElliptic

/-!
# Compact-uniform Fourier decay from actual joint smoothness

For each order, apply the genuine family elliptic operator and bound its
continuous fibre sup norm on the compact parameter set. The exact Fourier
multiplier then gives one rapid-decay constant valid for all parameters
and all modes. A summable majorant remains after any polynomial weight.

The raw endpoints require only real smoothness of the actual joint lift
on the original open base, not any Fourier estimate or derivative bound.
-/

noncomputable section

open TopologicalSpace UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter

open PeriodTorusLineBundleClassification

variable {U : Opens ℂ} {d : Type*} [Fintype d]

namespace SmoothFamily

/-- The continuous and smooth slice constructions have the same actual continuous map. -/
@[simp] theorem continuous_slice_eq (f : SmoothFamily U d) (b : U) :
    FourierParameter.slice f.toContinuousMap b = (f.slice b).toContinuousMap := rfl

/-- Fourier coefficients of a genuinely jointly smooth family vary continuously. -/
theorem coefficient_continuous (f : SmoothFamily U d) (k : d → ℤ) :
    Continuous (fun b : U => mFourierCoeff (fun t => f (b, t)) k) :=
  FourierParameter.coefficient_continuous f.toContinuousMap k

/-- A compact parameter set bounds the actual elliptic tower in fibre sup norm. -/
theorem ellipticPower_compact_bound [DecidableEq d] (f : SmoothFamily U d)
    (K : Set U) (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K,
      ‖((ellipticPower n f).slice b).toContinuousMap‖ ≤ C := by
  simpa only [continuous_slice_eq] using
    FourierParameter.exists_pos_uniform_slice_bound (ellipticPower n f).toContinuousMap hK

/-- One positive rapid-decay constant works for all modes and all parameters in a compact set. -/
theorem rapidDecay_compact (f : SmoothFamily U d) (K : Set U) (hK : IsCompact K)
    (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ∀ k : d → ℤ,
      ‖mFourierCoeff (fun t => f (b, t)) k‖ ≤ C / fourierEllipticWeight k ^ n := by
  classical
  obtain ⟨C, hC, hbound⟩ := ellipticPower_compact_bound f K hK n
  refine ⟨C, hC, fun b hb k => ?_⟩
  have h := (torusFourierCoeff_norm_le ((ellipticPower n f).slice b).toContinuousMap k).trans
    (hbound b hb)
  change ‖mFourierCoeff (fun t => ellipticPower n f (b, t)) k‖ ≤ C at h
  rw [ellipticPower_coeff, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (fourierEllipticWeight_pos k)] at h
  apply (le_div_iff₀ (pow_pos (fourierEllipticWeight_pos k) n)).mpr
  simpa only [mul_comm] using h

/-- Every polynomial weight admits an explicit summable majorant uniform on a compact base. -/
theorem polynomial_majorant_compact (f : SmoothFamily U d) (K : Set U)
    (hK : IsCompact K) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      Summable (fun k : d → ℤ => C * (2 : ℝ) ^ r * (fourierEllipticWeight k)⁻¹) ∧
      ∀ b ∈ K, ∀ k : d → ℤ,
        (1 + ‖(fun i => (k i : ℝ))‖) ^ r * ‖mFourierCoeff (fun t => f (b, t)) k‖ ≤
          C * (2 : ℝ) ^ r * (fourierEllipticWeight k)⁻¹ := by
  obtain ⟨C, hC, hbound⟩ := f.rapidDecay_compact K hK (r + 1)
  refine ⟨C, hC, summable_inv_fourierEllipticWeight.mul_left (C * (2 : ℝ) ^ r),
    fun b hb k => ?_⟩
  calc
    (1 + ‖(fun i => (k i : ℝ))‖) ^ r * ‖mFourierCoeff (fun t => f (b, t)) k‖ ≤
        (1 + ‖(fun i => (k i : ℝ))‖) ^ r * (C / fourierEllipticWeight k ^ (r + 1)) :=
      mul_le_mul_of_nonneg_left (hbound b hb k) (by positivity)
    _ = C * ((1 + ‖(fun i => (k i : ℝ))‖) ^ r / fourierEllipticWeight k ^ (r + 1)) := by
      ring
    _ ≤ C * ((2 : ℝ) ^ r * (fourierEllipticWeight k)⁻¹) :=
      mul_le_mul_of_nonneg_left (polynomial_mul_inv_fourierEllipticWeight_le r k) hC.le
    _ = C * (2 : ℝ) ^ r * (fourierEllipticWeight k)⁻¹ := (mul_assoc _ _ _).symm

end SmoothFamily

/-- Raw coefficient continuity requires only smoothness of the actual lift on the open base. -/
theorem coefficient_continuous_of_contDiffOn_lift {f : U × UnitAddTorus d → ℂ}
    (hf : ContDiffOn ℝ ∞ (ambientLift f) (Smooth.baseProductDomain U (d → ℝ)))
    (k : d → ℤ) :
    Continuous (fun b : U => mFourierCoeff (fun t => f (b, t)) k) :=
  coefficient_continuous ⟨f, continuous_of_contDiffOn_lift hf⟩ k

/-- Compact-uniform rapid decay for a raw family follows from its actual joint smoothness alone. -/
theorem rapidDecay_compact_of_contDiffOn_lift {f : U × UnitAddTorus d → ℂ}
    (hf : ContDiffOn ℝ ∞ (ambientLift f) (Smooth.baseProductDomain U (d → ℝ)))
    (K : Set U) (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ∀ k : d → ℤ,
      ‖mFourierCoeff (fun t => f (b, t)) k‖ ≤ C / fourierEllipticWeight k ^ n :=
  SmoothFamily.rapidDecay_compact ⟨f, hf⟩ K hK n

/-- The raw smooth-lift hypothesis also supplies compact-uniform summable polynomial majorants. -/
theorem polynomial_majorant_compact_of_contDiffOn_lift {f : U × UnitAddTorus d → ℂ}
    (hf : ContDiffOn ℝ ∞ (ambientLift f) (Smooth.baseProductDomain U (d → ℝ)))
    (K : Set U) (hK : IsCompact K) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      Summable (fun k : d → ℤ => C * (2 : ℝ) ^ r * (fourierEllipticWeight k)⁻¹) ∧
      ∀ b ∈ K, ∀ k : d → ℤ,
        (1 + ‖(fun i => (k i : ℝ))‖) ^ r * ‖mFourierCoeff (fun t => f (b, t)) k‖ ≤
          C * (2 : ℝ) ^ r * (fourierEllipticWeight k)⁻¹ :=
  SmoothFamily.polynomial_majorant_compact ⟨f, hf⟩ K hK r

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter
