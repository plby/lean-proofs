import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.ContinuousMap.Compact

/-! # Circle integration as an actual bounded linear functional

The input functions live on the boundary circle, with its supremum norm.
The operators below are the actual contour integrals, not abstract
functionals with assumed properties.  Currying gives the iterated operator
on the product of two circles, with the first coordinate integrated first.
-/

noncomputable section

open Set Metric Complex

namespace Wikipedia.HopfProblem.CuspNormalization.Germs.NormalIntegral

/-- Extend boundary data by zero away from the circle.  Only its values on
the circle enter any of the integrals below. -/
def circleExtend (R : ℝ) (f : C(sphere (0 : ℂ) R, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ sphere (0 : ℂ) R then f ⟨z, hz⟩ else 0

@[simp] theorem circleExtend_of_mem (R : ℝ) (f : C(sphere (0 : ℂ) R, ℂ))
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    circleExtend R f z = f ⟨z, hz⟩ := by
  simp only [circleExtend, dif_pos hz]

theorem continuousOn_circleExtend (R : ℝ) (f : C(sphere (0 : ℂ) R, ℂ)) :
    ContinuousOn (circleExtend R f) (sphere (0 : ℂ) R) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have heq : (sphere (0 : ℂ) R).domRestrict (circleExtend R f) = f := by
    funext z
    exact circleExtend_of_mem R f z.property
  rw [heq]
  exact f.continuous

theorem circleIntegrable_circleExtend (R : ℝ) (hR : 0 < R)
    (f : C(sphere (0 : ℂ) R, ℂ)) : CircleIntegrable (circleExtend R f) 0 R :=
  (continuousOn_circleExtend R f).circleIntegrable hR.le

/-- The literal contour integral as a bounded complex-linear functional
on continuous functions on the circle. -/
def circleIntegralCLM (R : ℝ) (hR : 0 < R) : C(sphere (0 : ℂ) R, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∮ z in C(0, R), circleExtend R f z
      map_add' := fun f g => by
        calc
          (∮ z in C(0, R), circleExtend R (f + g) z) =
              ∮ z in C(0, R), circleExtend R f z + circleExtend R g z := by
            apply circleIntegral.integral_congr hR.le
            intro z hz
            simp only [circleExtend_of_mem R _ hz, ContinuousMap.add_apply]
          _ = _ := circleIntegral.integral_add
            (circleIntegrable_circleExtend R hR f) (circleIntegrable_circleExtend R hR g)
      map_smul' := fun c f => by
        calc
          (∮ z in C(0, R), circleExtend R (c • f) z) =
              ∮ z in C(0, R), c • circleExtend R f z := by
            apply circleIntegral.integral_congr hR.le
            intro z hz
            simp only [circleExtend_of_mem R _ hz, ContinuousMap.smul_apply]
          _ = _ := circleIntegral.integral_smul c (circleExtend R f) 0 R }
    (2 * Real.pi * R) fun f => by
      apply circleIntegral.norm_integral_le_of_norm_le_const hR.le
      intro z hz
      rw [circleExtend_of_mem R f hz]
      exact f.norm_coe_le_norm ⟨z, hz⟩

@[simp] theorem circleIntegralCLM_apply (R : ℝ) (hR : 0 < R)
    (f : C(sphere (0 : ℂ) R, ℂ)) :
    circleIntegralCLM R hR f = ∮ z in C(0, R), circleExtend R f z := rfl

/-- Any ambient representative agreeing with the boundary data computes
the same actual integral; no behavior away from the circle is required. -/
theorem circleIntegralCLM_apply_restrict (R : ℝ) (hR : 0 < R)
    (f : C(sphere (0 : ℂ) R, ℂ)) (g : ℂ → ℂ)
    (hg : ∀ z (hz : z ∈ sphere (0 : ℂ) R), g z = f ⟨z, hz⟩) :
    circleIntegralCLM R hR f = ∮ z in C(0, R), g z := by
  rw [circleIntegralCLM_apply]
  apply circleIntegral.integral_congr hR.le
  intro z hz
  rw [circleExtend_of_mem R f hz, hg z hz]

/-- Currying boundary data with the second variable outside and the first
variable inside. -/
def circleCurryCLM (r R : ℝ) :
    C(sphere (0 : ℂ) r × sphere (0 : ℂ) R, ℂ) →L[ℂ]
      C(sphere (0 : ℂ) R, C(sphere (0 : ℂ) r, ℂ)) where
  toFun f := (f.comp ⟨Prod.swap, continuous_swap⟩).curry
  map_add' _ _ := by ext η ζ; rfl
  map_smul' _ _ := by ext η ζ; rfl
  cont := ContinuousMap.continuous_curry.comp
    (ContinuousMap.continuous_precomp ⟨Prod.swap, continuous_swap⟩)

@[simp] theorem circleCurryCLM_apply (r R : ℝ)
    (f : C(sphere (0 : ℂ) r × sphere (0 : ℂ) R, ℂ))
    (η : sphere (0 : ℂ) R) (ζ : sphere (0 : ℂ) r) :
    circleCurryCLM r R f η ζ = f (ζ, η) := rfl

/-- Iterated actual circle integration, first in the first coordinate,
then in the second coordinate. -/
def doubleCircleIntegralCLM (r : ℝ) (hr : 0 < r) (R : ℝ) (hR : 0 < R) :
    C(sphere (0 : ℂ) r × sphere (0 : ℂ) R, ℂ) →L[ℂ] ℂ :=
  (circleIntegralCLM R hR).comp
    ((ContinuousLinearMap.compLeftContinuous ℂ (sphere (0 : ℂ) R)
      (circleIntegralCLM r hr)).comp (circleCurryCLM r R))

/-- The bounded iterated functional computes the literal iterated contour
integral of every ambient representative of its boundary data. -/
theorem doubleCircleIntegralCLM_apply_restrict
    (r : ℝ) (hr : 0 < r) (R : ℝ) (hR : 0 < R)
    (f : C(sphere (0 : ℂ) r × sphere (0 : ℂ) R, ℂ)) (g : ℂ × ℂ → ℂ)
    (hg : ∀ ζ η (hζ : ζ ∈ sphere (0 : ℂ) r) (hη : η ∈ sphere (0 : ℂ) R),
      g (ζ, η) = f (⟨ζ, hζ⟩, ⟨η, hη⟩)) :
    doubleCircleIntegralCLM r hr R hR f =
      ∮ η in C(0, R), ∮ ζ in C(0, r), g (ζ, η) := by
  change circleIntegralCLM R hR _ = _
  apply circleIntegralCLM_apply_restrict
  intro η hη
  exact (circleIntegralCLM_apply_restrict r hr (circleCurryCLM r R f ⟨η, hη⟩)
    (fun ζ => g (ζ, η)) (fun ζ hζ => hg ζ η hζ hη)).symm

end Wikipedia.HopfProblem.CuspNormalization.Germs.NormalIntegral
