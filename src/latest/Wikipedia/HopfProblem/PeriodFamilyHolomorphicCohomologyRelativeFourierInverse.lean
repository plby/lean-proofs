import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFourierUniform
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Holomorphic fixed-centre inverse Fourier multipliers

The reciprocal of the fixed selected coefficient is holomorphic on the
common neighborhood where that coefficient has the proved elliptic lower
bound. The zero mode is totalized to zero. Every nonzero real or genuine
integer mode has a uniform inverse-frequency estimate. This file makes no
assertion about parameter-dependent infinite sums or higher direct images.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeFourier

open Set Topology MarkedLinear PeriodTorusLineBundleClassification

/-- The reciprocal uses a coordinate selected once at the fixed centre. -/
def denominatorInverse (p₀ p : PeriodDomain) (v : Fin 4 → ℝ) : ℂ :=
  (centreCoefficient p₀ p v)⁻¹

@[simp] theorem denominatorInverse_zero (p₀ p : PeriodDomain) :
    denominatorInverse p₀ p 0 = 0 := by
  simp only [denominatorInverse, centreCoefficient_zero, inv_zero]

/-- The proved lower bound ensures that a nonzero frequency has a nonzero
selected denominator throughout the neighborhood. -/
theorem centreCoefficient_ne_zero_of_lowerBound (p₀ p : PeriodDomain) (c : ℝ)
    (hc : 0 < c) {v : Fin 4 → ℝ} (hv : v ≠ 0)
    (hbound : c * ‖v‖ ≤ ‖centreCoefficient p₀ p v‖) :
    centreCoefficient p₀ p v ≠ 0 :=
  norm_pos_iff.mp ((mul_pos hc (norm_pos_iff.mpr hv)).trans_le hbound)

/-- This is the actual inverse equation, not an independently chosen scalar. -/
theorem centreCoefficient_mul_denominatorInverse (p₀ p : PeriodDomain)
    (v : Fin 4 → ℝ) (hv : centreCoefficient p₀ p v ≠ 0) :
    centreCoefficient p₀ p v * denominatorInverse p₀ p v = 1 :=
  mul_inv_cancel₀ hv

/-- The inverse-frequency estimate also holds at the totalized zero mode. -/
theorem denominatorInverse_norm_le (p₀ p : PeriodDomain) (c : ℝ) (hc : 0 < c)
    (v : Fin 4 → ℝ) (hbound : c * ‖v‖ ≤ ‖centreCoefficient p₀ p v‖) :
    ‖denominatorInverse p₀ p v‖ ≤ c⁻¹ * ‖v‖⁻¹ := by
  by_cases hv : v = 0
  · subst v
    simp only [denominatorInverse_zero, norm_zero, inv_zero, mul_zero, le_refl]
  · rw [denominatorInverse, norm_inv]
    simpa only [mul_inv_rev, mul_comm] using
      inv_anti₀ (mul_pos hc (norm_pos_iff.mpr hv)) hbound

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)

/-- Reciprocal holomorphicity is proved for the literal selected denominator. -/
theorem holomorphicOn_denominatorInverse (p₀ : PeriodDomain) (v : Fin 4 → ℝ)
    (U : Set B) (hzero : ∀ b ∈ U, centreCoefficient p₀ (P.point b) v ≠ 0) :
    ContMDiffOn (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
      (fun b => denominatorInverse p₀ (P.point b) v) U :=
  (holomorphic_centreCoefficient P p₀ v).contMDiffOn.inv₀ hzero

/-- On any neighborhood carrying the actual uniform lower bound, every fixed
mode inverse is holomorphic, with the zero mode represented by zero. -/
theorem holomorphicOn_denominatorInverse_of_lowerBound (p₀ : PeriodDomain)
    (U : Set B) (c : ℝ) (hc : 0 < c)
    (hbound : ∀ b ∈ U, ∀ v : Fin 4 → ℝ,
      c * ‖v‖ ≤ ‖centreCoefficient p₀ (P.point b) v‖) (v : Fin 4 → ℝ) :
    ContMDiffOn (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
      (fun b => denominatorInverse p₀ (P.point b) v) U := by
  by_cases hv : v = 0
  · subst v
    simpa only [denominatorInverse_zero] using
      (contMDiffOn_const : ContMDiffOn (modelWithCornersSelf ℂ V)
        (modelWithCornersSelf ℂ ℂ) ω (fun _ : B => (0 : ℂ)) U)
  · exact holomorphicOn_denominatorInverse P p₀ v U (fun b hb =>
      centreCoefficient_ne_zero_of_lowerBound p₀ (P.point b) c hc hv (hbound b hb v))

/-- Around every original base point there is one common open neighborhood
with holomorphic fixed-mode inverses and a uniform order-minus-one bound. -/
theorem exists_open_uniform_holomorphic_inverse (b₀ : B) :
    ∃ (U : Set B) (c : ℝ), IsOpen U ∧ b₀ ∈ U ∧ 0 < c ∧
      (∀ b ∈ U, ∀ v : Fin 4 → ℝ,
        c * ‖v‖ ≤ ‖centreCoefficient (P.point b₀) (P.point b) v‖) ∧
      (∀ v : Fin 4 → ℝ,
        ContMDiffOn (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
          (fun b => denominatorInverse (P.point b₀) (P.point b) v) U) ∧
      (∀ b ∈ U, ∀ k : Fin 4 → ℤ,
        ‖denominatorInverse (P.point b₀) (P.point b) (integerFrequency k)‖ ≤
          c⁻¹ * ‖k‖⁻¹) := by
  obtain ⟨U, c, hU, hb₀, hc, hbound⟩ :=
    exists_open_uniform_centreCoefficient_lowerBound P b₀
  refine ⟨U, c, hU, hb₀, hc, hbound,
    holomorphicOn_denominatorInverse_of_lowerBound P (P.point b₀) U c hc hbound, ?_⟩
  intro b hb k
  simpa only [integerFrequency_norm] using
    denominatorInverse_norm_le (P.point b₀) (P.point b) c hc (integerFrequency k)
      (hbound b hb (integerFrequency k))

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeFourier
