import Wikipedia.HopfProblem.TriangleRiemannCornerPatches
import Wikipedia.HopfProblem.TriangleRiemannIdealComparison
import Wikipedia.HopfProblem.TriangleRiemannNormalizedCornersMobius

/-!
# The actual normalized elliptic corner germs and patches

The cross-ratio uses the three proved distinct boundary values of the
actual triangle Riemann map.  It takes the cubic and quartic corner values
to zero and one.  Postcomposition preserves the ambient orders three and
four, while the quotient-parameter germs themselves remain noncritical.
No global uniformizing map is supplied as a hypothesis.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle RiemannSphere.MobiusCircle

/-- The actual cross-ratio fixed by the cubic, quartic, and ideal vertices. -/
def triangleCornerNormalization : ℂ → ℂ :=
  crossRatio (triangleCornerThreeGerm.function 0)
    (triangleCornerFourGerm.function 0) (triangleIdealGerm.function 0)

@[simp] theorem triangleCornerNormalization_three :
    triangleCornerNormalization (triangleCornerThreeGerm.function 0) = 0 :=
  crossRatio_at_zero _ _ _

@[simp] theorem triangleCornerNormalization_four :
    triangleCornerNormalization (triangleCornerFourGerm.function 0) = 1 :=
  crossRatio_at_one triangleCorner_boundary_values_ne.symm
    triangleCornerFour_boundary_value_ne_ideal

theorem triangleCornerNormalization_analyticAt {w : ℂ}
    (hw : w ≠ triangleIdealGerm.function 0) :
    AnalyticAt ℂ triangleCornerNormalization w :=
  crossRatio_analyticAt triangleCorner_boundary_values_ne.symm hw

theorem triangleCornerNormalization_deriv_ne_zero {w : ℂ}
    (hw : w ≠ triangleIdealGerm.function 0) :
    deriv triangleCornerNormalization w ≠ 0 :=
  crossRatio_deriv_ne_zero triangleCorner_boundary_values_ne.symm
    triangleCornerFour_boundary_value_ne_ideal triangleCornerThree_boundary_value_ne_ideal hw

/-- The normalized noncritical germ in the cubic quotient parameter. -/
def triangleNormalizedCornerThreeGerm : ℂ → ℂ :=
  triangleCornerNormalization ∘ triangleCornerThreeGerm.function

/-- The normalized noncritical germ in the oriented quartic quotient parameter. -/
def triangleNormalizedCornerFourGerm : ℂ → ℂ :=
  triangleCornerNormalization ∘ triangleCornerFourGerm.function

@[simp] theorem triangleNormalizedCornerThreeGerm_zero :
    triangleNormalizedCornerThreeGerm 0 = 0 := triangleCornerNormalization_three

@[simp] theorem triangleNormalizedCornerFourGerm_zero :
    triangleNormalizedCornerFourGerm 0 = 1 := triangleCornerNormalization_four

theorem triangleNormalizedCornerThreeGerm_analyticAt :
    AnalyticAt ℂ triangleNormalizedCornerThreeGerm 0 :=
  (triangleCornerNormalization_analyticAt triangleCornerThree_boundary_value_ne_ideal).comp
    (triangleCornerThreeGerm.analytic 0 (mem_ball_self triangleCornerThreeGerm.radius_pos))

theorem triangleNormalizedCornerFourGerm_analyticAt :
    AnalyticAt ℂ triangleNormalizedCornerFourGerm 0 :=
  (triangleCornerNormalization_analyticAt triangleCornerFour_boundary_value_ne_ideal).comp
    (triangleCornerFourGerm.analytic 0 (mem_ball_self triangleCornerFourGerm.radius_pos))

theorem triangleNormalizedCornerThreeGerm_deriv_ne_zero :
    deriv triangleNormalizedCornerThreeGerm 0 ≠ 0 := by
  have hd := (triangleCornerNormalization_analyticAt
    triangleCornerThree_boundary_value_ne_ideal).hasStrictDerivAt.comp 0
      triangleCornerThreeGerm.strictDeriv
  change deriv (triangleCornerNormalization ∘ triangleCornerThreeGerm.function) 0 ≠ 0
  rw [hd.hasDerivAt.deriv]
  exact mul_ne_zero
    (triangleCornerNormalization_deriv_ne_zero triangleCornerThree_boundary_value_ne_ideal)
    triangleCornerThreeGerm.deriv_ne_zero

theorem triangleNormalizedCornerFourGerm_deriv_ne_zero :
    deriv triangleNormalizedCornerFourGerm 0 ≠ 0 := by
  have hd := (triangleCornerNormalization_analyticAt
    triangleCornerFour_boundary_value_ne_ideal).hasStrictDerivAt.comp 0
      triangleCornerFourGerm.strictDeriv
  change deriv (triangleCornerNormalization ∘ triangleCornerFourGerm.function) 0 ≠ 0
  rw [hd.hasDerivAt.deriv]
  exact mul_ne_zero
    (triangleCornerNormalization_deriv_ne_zero triangleCornerFour_boundary_value_ne_ideal)
    triangleCornerFourGerm.deriv_ne_zero

theorem triangleNormalizedCornerThreeGerm_hasStrictDerivAt :
    HasStrictDerivAt triangleNormalizedCornerThreeGerm
      (deriv triangleNormalizedCornerThreeGerm 0) 0 :=
  triangleNormalizedCornerThreeGerm_analyticAt.hasStrictDerivAt

theorem triangleNormalizedCornerFourGerm_hasStrictDerivAt :
    HasStrictDerivAt triangleNormalizedCornerFourGerm
      (deriv triangleNormalizedCornerFourGerm 0) 0 :=
  triangleNormalizedCornerFourGerm_analyticAt.hasStrictDerivAt

/-- The normalized ambient cubic patch is the literal cross-ratio
postcomposition of the already constructed actual corner patch. -/
def triangleNormalizedCornerThreePatch : ℂ → ℂ :=
  triangleCornerNormalization ∘ triangleCornerThreePatch

/-- The normalized ambient quartic patch. -/
def triangleNormalizedCornerFourPatch : ℂ → ℂ :=
  triangleCornerNormalization ∘ triangleCornerFourPatch

/-- The actual cubic quotient-parameter formula, valid as an equality of
the totalized complex functions, not merely as a formal expansion. -/
theorem triangleNormalizedCornerThreePatch_eq_germ (z : ℂ) :
    triangleNormalizedCornerThreePatch z =
      triangleNormalizedCornerThreeGerm (cornerPowerThree z) := rfl

/-- The actual quartic formula includes the negative fourth power in its
oriented quotient coordinate. -/
theorem triangleNormalizedCornerFourPatch_eq_germ (z : ℂ) :
    triangleNormalizedCornerFourPatch z =
      triangleNormalizedCornerFourGerm (cornerPowerFour z) := rfl

@[simp] theorem triangleNormalizedCornerThreePatch_center :
    triangleNormalizedCornerThreePatch centerOne = 0 := by
  rw [triangleNormalizedCornerThreePatch_eq_germ, cornerPowerThree_center,
    triangleNormalizedCornerThreeGerm_zero]

@[simp] theorem triangleNormalizedCornerFourPatch_center :
    triangleNormalizedCornerFourPatch centerTwo = 1 := by
  rw [triangleNormalizedCornerFourPatch_eq_germ, cornerPowerFour_center,
    triangleNormalizedCornerFourGerm_zero]

theorem triangleNormalizedCornerThreePatch_analyticAt :
    AnalyticAt ℂ triangleNormalizedCornerThreePatch (centerOne : ℂ) := by
  have hN : AnalyticAt ℂ triangleCornerNormalization (triangleCornerThreePatch centerOne) := by
    rw [triangleCornerThreePatch_center]
    exact triangleCornerNormalization_analyticAt triangleCornerThree_boundary_value_ne_ideal
  exact hN.comp triangleCornerThreePatch_analyticAt

theorem triangleNormalizedCornerFourPatch_analyticAt :
    AnalyticAt ℂ triangleNormalizedCornerFourPatch (centerTwo : ℂ) := by
  have hN : AnalyticAt ℂ triangleCornerNormalization (triangleCornerFourPatch centerTwo) := by
    rw [triangleCornerFourPatch_center]
    exact triangleCornerNormalization_analyticAt triangleCornerFour_boundary_value_ne_ideal
  exact hN.comp triangleCornerFourPatch_analyticAt

theorem triangleNormalizedCornerThreePatch_eventuallyEq :
    triangleNormalizedCornerThreePatch =ᶠ[𝓝[triangleInterior] (centerOne : ℂ)]
      (triangleCornerNormalization ∘ triangleMap) :=
  triangleCornerThreePatch_eventuallyEq.fun_comp triangleCornerNormalization

theorem triangleNormalizedCornerFourPatch_eventuallyEq :
    triangleNormalizedCornerFourPatch =ᶠ[𝓝[triangleInterior] (centerTwo : ℂ)]
      (triangleCornerNormalization ∘ triangleMap) :=
  triangleCornerFourPatch_eventuallyEq.fun_comp triangleCornerNormalization

/-- Postcomposition by the actual noncritical cross-ratio preserves the
exact order three at the zero-normalized cubic vertex. -/
theorem triangleNormalizedCornerThreePatch_order :
    analyticOrderAt triangleNormalizedCornerThreePatch (centerOne : ℂ) = 3 := by
  have hpc : triangleCornerThreePatch centerOne ≠ triangleIdealGerm.function 0 := by
    rw [triangleCornerThreePatch_center]
    exact triangleCornerThree_boundary_value_ne_ideal
  have he := crossRatio_comp_analyticOrderAt triangleCornerThreePatch_analyticAt
    triangleCorner_boundary_values_ne.symm triangleCornerFour_boundary_value_ne_ideal
    triangleCornerThree_boundary_value_ne_ideal hpc
  change analyticOrderAt (fun z => triangleCornerNormalization (triangleCornerThreePatch z) -
    triangleCornerNormalization (triangleCornerThreePatch centerOne)) (centerOne : ℂ) =
      analyticOrderAt (fun z => triangleCornerThreePatch z - triangleCornerThreePatch centerOne)
        (centerOne : ℂ) at he
  rw [triangleCornerThreePatch_center, triangleCornerNormalization_three,
    triangleCornerThreePatch_order] at he
  simpa only [sub_zero, triangleNormalizedCornerThreePatch, Function.comp_def] using he

/-- The normalized quartic patch has exact order four after subtracting one. -/
theorem triangleNormalizedCornerFourPatch_order :
    analyticOrderAt (fun z => triangleNormalizedCornerFourPatch z - 1)
      (centerTwo : ℂ) = 4 := by
  have hpc : triangleCornerFourPatch centerTwo ≠ triangleIdealGerm.function 0 := by
    rw [triangleCornerFourPatch_center]
    exact triangleCornerFour_boundary_value_ne_ideal
  have he := crossRatio_comp_analyticOrderAt triangleCornerFourPatch_analyticAt
    triangleCorner_boundary_values_ne.symm triangleCornerFour_boundary_value_ne_ideal
    triangleCornerThree_boundary_value_ne_ideal hpc
  change analyticOrderAt (fun z => triangleCornerNormalization (triangleCornerFourPatch z) -
    triangleCornerNormalization (triangleCornerFourPatch centerTwo)) (centerTwo : ℂ) =
      analyticOrderAt (fun z => triangleCornerFourPatch z - triangleCornerFourPatch centerTwo)
        (centerTwo : ℂ) at he
  rw [triangleCornerFourPatch_center, triangleCornerNormalization_four,
    triangleCornerFourPatch_order] at he
  simpa only [triangleNormalizedCornerFourPatch, Function.comp_def] using he

/-- The actual normalized map tends to zero at the cubic corner along
the entire triangle interior. -/
theorem triangleNormalizedCornerThree_forward_limit :
    Tendsto (triangleCornerNormalization ∘ triangleMap)
      (𝓝[triangleInterior] (centerOne : ℂ)) (𝓝 (0 : ℂ)) := by
  have h := (triangleCornerNormalization_analyticAt
    triangleCornerThree_boundary_value_ne_ideal).continuousAt.tendsto.comp
      triangleCornerThree_forward_limit
  simpa only [triangleCornerNormalization_three] using h

/-- The corresponding whole-interior limit is one at the quartic corner. -/
theorem triangleNormalizedCornerFour_forward_limit :
    Tendsto (triangleCornerNormalization ∘ triangleMap)
      (𝓝[triangleInterior] (centerTwo : ℂ)) (𝓝 (1 : ℂ)) := by
  have h := (triangleCornerNormalization_analyticAt
    triangleCornerFour_boundary_value_ne_ideal).continuousAt.tendsto.comp
      triangleCornerFour_forward_limit
  simpa only [triangleCornerNormalization_four] using h

end Wikipedia.HopfProblem.RiemannMapping
