import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Jointly analytic kernels for a double Cauchy integral

The two Cauchy kernels are analytic as maps into the Banach algebra of
continuous functions on the boundary torus.  Consequently, applying any
bounded linear functional to their product with fixed boundary data gives
a genuinely analytic function of both complex variables.
-/

noncomputable section

open Set Metric

namespace Wikipedia.HopfProblem.CuspNormalization.Germs.NormalIntegral

section CompactFunctions

variable {K : Type*} [TopologicalSpace K]

/-- A nowhere-zero continuous scalar function is a unit in the actual
algebra of continuous functions. -/
def continuousUnit (u : C(K, ℂ)) (hu : ∀ x, u x ≠ 0) : C(K, ℂ)ˣ where
  val := u
  inv := ⟨fun x => (u x)⁻¹, u.continuous.inv₀ hu⟩
  val_inv := by ext x; exact mul_inv_cancel₀ (hu x)
  inv_val := by ext x; exact inv_mul_cancel₀ (hu x)

@[simp] theorem continuousUnit_val (u : C(K, ℂ)) (hu : ∀ x, u x ≠ 0) :
    (continuousUnit u hu : C(K, ℂ)) = u := rfl

/-- Banach-algebra inversion agrees with pointwise scalar inversion on a
nowhere-zero continuous function. -/
theorem inverse_continuousMap_apply (u : C(K, ℂ)) (hu : ∀ x, u x ≠ 0) (x : K) :
    Ring.inverse u x = (u x)⁻¹ := by
  change Ring.inverse (continuousUnit u hu : C(K, ℂ)) x = _
  rw [Ring.inverse_unit]
  rfl

/-- Inversion in the actual continuous-function algebra is analytic at a
nowhere-zero function. -/
theorem analyticAt_inverse_continuousMap [CompactSpace K]
    (u : C(K, ℂ)) (hu : ∀ x, u x ≠ 0) :
    AnalyticAt ℂ Ring.inverse u :=
  analyticAt_inverse (continuousUnit u hu)

end CompactFunctions

/-- The product of the two actual integration circles. -/
abbrev BoundaryTorus (r R : ℝ) := sphere (0 : ℂ) r × sphere (0 : ℂ) R

/-- First boundary coordinate as an element of the continuous-function algebra. -/
def boundaryFirst (r R : ℝ) : C(BoundaryTorus r R, ℂ) :=
  ⟨fun w => w.1.1, continuous_subtype_val.comp continuous_fst⟩

/-- Second boundary coordinate as an element of the continuous-function algebra. -/
def boundarySecond (r R : ℝ) : C(BoundaryTorus r R, ℂ) :=
  ⟨fun w => w.2.1, continuous_subtype_val.comp continuous_snd⟩

/-- The first denominator, viewed uniformly over the boundary torus. -/
def firstDenominator (r R : ℝ) (z : ℂ × ℂ) : C(BoundaryTorus r R, ℂ) :=
  boundaryFirst r R - ContinuousMap.const _ z.1

/-- The second denominator, viewed uniformly over the boundary torus. -/
def secondDenominator (r R : ℝ) (z : ℂ × ℂ) : C(BoundaryTorus r R, ℂ) :=
  boundarySecond r R - ContinuousMap.const _ z.2

theorem firstDenominator_ne_zero {r R : ℝ} {z : ℂ × ℂ}
    (hz : z.1 ∈ ball 0 r) (w : BoundaryTorus r R) :
    firstDenominator r R z w ≠ 0 := by
  change (w.1.1 : ℂ) - z.1 ≠ 0
  apply sub_ne_zero.mpr
  intro he
  have hw : ‖(w.1.1 : ℂ)‖ = r := by simpa only [mem_sphere, dist_zero_right] using w.1.2
  have hzn : ‖z.1‖ < r := by simpa only [mem_ball, dist_zero_right] using hz
  exact (ne_of_lt hzn) (he ▸ hw)

theorem secondDenominator_ne_zero {r R : ℝ} {z : ℂ × ℂ}
    (hz : z.2 ∈ ball 0 R) (w : BoundaryTorus r R) :
    secondDenominator r R z w ≠ 0 := by
  change (w.2.1 : ℂ) - z.2 ≠ 0
  apply sub_ne_zero.mpr
  intro he
  have hw : ‖(w.2.1 : ℂ)‖ = R := by simpa only [mem_sphere, dist_zero_right] using w.2.2
  have hzn : ‖z.2‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
  exact (ne_of_lt hzn) (he ▸ hw)

theorem firstDenominator_analyticAt (r R : ℝ) (z : ℂ × ℂ) :
    AnalyticAt ℂ (firstDenominator r R) z := by
  have hc : AnalyticAt ℂ
      (fun x : ℂ × ℂ => ContinuousMap.const (BoundaryTorus r R) x.1) z :=
    ((ContinuousLinearMap.const (R := ℂ) (M := ℂ) (BoundaryTorus r R)).analyticAt z.1).comp
      analyticAt_fst
  exact analyticAt_const.sub hc

theorem secondDenominator_analyticAt (r R : ℝ) (z : ℂ × ℂ) :
    AnalyticAt ℂ (secondDenominator r R) z := by
  have hc : AnalyticAt ℂ
      (fun x : ℂ × ℂ => ContinuousMap.const (BoundaryTorus r R) x.2) z :=
    ((ContinuousLinearMap.const (R := ℂ) (M := ℂ) (BoundaryTorus r R)).analyticAt z.2).comp
      analyticAt_snd
  exact analyticAt_const.sub hc

/-- The double Cauchy kernel multiplied by actual continuous boundary data.
The use of `Ring.inverse` makes this a globally defined map into a Banach
algebra; on the open bidisc it is exactly the pointwise scalar formula. -/
def boundaryKernel (r R : ℝ) (u : C(BoundaryTorus r R, ℂ)) (z : ℂ × ℂ) :
    C(BoundaryTorus r R, ℂ) :=
  Ring.inverse (firstDenominator r R z) * Ring.inverse (secondDenominator r R z) * u

theorem boundaryKernel_apply {r R : ℝ} (u : C(BoundaryTorus r R, ℂ))
    {z : ℂ × ℂ} (hz : z ∈ ball 0 r ×ˢ ball 0 R) (w : BoundaryTorus r R) :
    boundaryKernel r R u z w =
      ((w.1.1 : ℂ) - z.1)⁻¹ * ((w.2.1 : ℂ) - z.2)⁻¹ * u w := by
  simp only [boundaryKernel, ContinuousMap.mul_apply]
  rw [inverse_continuousMap_apply _ (firstDenominator_ne_zero hz.1),
    inverse_continuousMap_apply _ (secondDenominator_ne_zero hz.2)]
  rfl

/-- The double Cauchy kernel is jointly analytic in its two poles. -/
theorem boundaryKernel_analyticOnNhd (r R : ℝ) (u : C(BoundaryTorus r R, ℂ)) :
    AnalyticOnNhd ℂ (boundaryKernel r R u) (ball 0 r ×ˢ ball 0 R) := by
  intro z hz
  have h₁ := (analyticAt_inverse_continuousMap (firstDenominator r R z)
    (firstDenominator_ne_zero hz.1)).comp (firstDenominator_analyticAt r R z)
  have h₂ := (analyticAt_inverse_continuousMap (secondDenominator r R z)
    (secondDenominator_ne_zero hz.2)).comp (secondDenominator_analyticAt r R z)
  exact (h₁.mul h₂).mul analyticAt_const

/-- Any bounded integral operator applied to the double Cauchy kernel is
jointly analytic on the open bidisc. -/
theorem analyticOnNhd_boundaryKernel_functional (r R : ℝ)
    (u : C(BoundaryTorus r R, ℂ)) (L : C(BoundaryTorus r R, ℂ) →L[ℂ] ℂ) :
    AnalyticOnNhd ℂ (fun z => L (boundaryKernel r R u z)) (ball 0 r ×ˢ ball 0 R) := by
  intro z hz
  exact (L.analyticAt _).comp (boundaryKernel_analyticOnNhd r R u z hz)

end Wikipedia.HopfProblem.CuspNormalization.Germs.NormalIntegral
