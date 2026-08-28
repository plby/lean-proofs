import Wikipedia.HopfProblem.CuspNormalizationGermsNormalIntegralOperator

/-!
# The actual three-variable contour functional

Continuous boundary data on the product of three circles carries the
supremum norm.  Currying and the existing double-circle functional give a
bounded complex-linear functional which integrates the second coordinate
first, the third coordinate next, and the first coordinate last.
-/

noncomputable section

open Set Metric Complex

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily.AnalyticThreefold

open CuspNormalization.Germs.NormalIntegral

/-- Curry the first boundary coordinate, keeping the remaining two in
their original order. -/
def tripleCircleCurryCLM (r : ℝ) :
    C(sphere (0 : ℂ) r × (sphere (0 : ℂ) r × sphere (0 : ℂ) r), ℂ) →L[ℂ]
      C(sphere (0 : ℂ) r, C(sphere (0 : ℂ) r × sphere (0 : ℂ) r, ℂ)) where
  toFun f := f.curry
  map_add' _ _ := by ext ξ w; rfl
  map_smul' _ _ := by ext ξ w; rfl
  cont := ContinuousMap.continuous_curry

@[simp] theorem tripleCircleCurryCLM_apply (r : ℝ)
    (f : C(sphere (0 : ℂ) r × (sphere (0 : ℂ) r × sphere (0 : ℂ) r), ℂ))
    (ξ : sphere (0 : ℂ) r) (w : sphere (0 : ℂ) r × sphere (0 : ℂ) r) :
    tripleCircleCurryCLM r f ξ w = f (ξ, w) := rfl

/-- The literal iterated contour integral, as a bounded complex-linear
functional on continuous boundary data. -/
def tripleCircleIntegralCLM (r : ℝ) (hr : 0 < r) :
    C(sphere (0 : ℂ) r × (sphere (0 : ℂ) r × sphere (0 : ℂ) r), ℂ) →L[ℂ] ℂ :=
  (circleIntegralCLM r hr).comp
    ((ContinuousLinearMap.compLeftContinuous ℂ (sphere (0 : ℂ) r)
      (doubleCircleIntegralCLM r hr r hr)).comp (tripleCircleCurryCLM r))

/-- An ambient representative agreeing on the boundary computes the
actual iterated integral; no assumption away from the boundary is needed. -/
theorem tripleCircleIntegralCLM_apply_restrict (r : ℝ) (hr : 0 < r)
    (f : C(sphere (0 : ℂ) r × (sphere (0 : ℂ) r × sphere (0 : ℂ) r), ℂ))
    (g : ℂ × (ℂ × ℂ) → ℂ)
    (hg : ∀ ξ ζ η (hξ : ξ ∈ sphere (0 : ℂ) r)
      (hζ : ζ ∈ sphere (0 : ℂ) r) (hη : η ∈ sphere (0 : ℂ) r),
      g (ξ, (ζ, η)) = f (⟨ξ, hξ⟩, (⟨ζ, hζ⟩, ⟨η, hη⟩))) :
    tripleCircleIntegralCLM r hr f =
      ∮ ξ in C(0, r), ∮ η in C(0, r), ∮ ζ in C(0, r), g (ξ, (ζ, η)) := by
  change circleIntegralCLM r hr _ = _
  apply circleIntegralCLM_apply_restrict
  intro ξ hξ
  exact (doubleCircleIntegralCLM_apply_restrict r hr r hr
    (tripleCircleCurryCLM r f ⟨ξ, hξ⟩) (fun w => g (ξ, w))
    (fun ζ η hζ hη => hg ξ ζ η hξ hζ hη)).symm

end Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily.AnalyticThreefold
