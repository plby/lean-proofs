import Wikipedia.SmoothSixDPoincare.CenteredParametrization

/-!
# Centered parametrizations for an arbitrary native model

Translate the actual extended chart, then invert it. This also handles
native product atlases, without identifying them with a charted-space-self
instance on their model vector space.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeCenteredChart

open Wikipedia.SmoothSixDPoincare

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chart (x : M) : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ :=
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := I) x
  (NativeParametrization.translation (c x)).toPartialDiffeomorph.trans c.symm

theorem zero_mem_source (x : M) : (0 : E) ∈ (chart (I := I) x).source := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := I) x
  refine ⟨mem_univ _, ?_⟩
  change 0 + c x ∈ c.target
  rw [zero_add]
  exact c.map_source' (mem_extChartAt_source x)

theorem chart_zero (x : M) : chart (I := I) x (0 : E) = x := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := I) x
  change c.symm (0 + c x) = x
  rw [zero_add]
  exact c.left_inv' (mem_extChartAt_source x)

theorem bijective_mfderiv (x : M) :
    Bijective (mfderiv 𝓘(ℝ, E) I (chart (I := I) x) (0 : E)) :=
  PartialChart.bijective_mfderiv (chart (I := I) x) (zero_mem_source (I := I) x)

/-- Centering uses the very chart that defines the native tangent model,
so its derivative at zero is the identity in that model. -/
theorem mfderiv_chart_zero (x : M) :
    (mfderiv 𝓘(ℝ, E) I (chart (I := I) x) (0 : E) : E →L[ℝ] E) =
      ContinuousLinearMap.id ℝ E := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := I) x
  let T := NativeParametrization.translation (c x)
  have hT0 : T (0 : E) = c x := zero_add _
  have hT : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) T (0 : E)
      (ContinuousLinearMap.id ℝ E) :=
    ((hasFDerivAt_id (0 : E)).add_const (c x)).hasMFDerivAt
  have hc : c x ∈ c.target := c.map_source' (mem_extChartAt_source x)
  let C : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I c.symm (c x)
  have hC : C = ContinuousLinearMap.id ℝ E := by
    have hh := mfderivWithin_range_extChartAt_symm (I := I) (x := x)
    rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hh
    exact hh
  let D : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I (chart (I := I) x) 0
  have hd : D = C.comp (ContinuousLinearMap.id ℝ E) := by
    have hcs : MDifferentiableAt 𝓘(ℝ, E) I c.symm (T 0) := by
      rw [hT0]
      exact c.symm.mdifferentiableAt (by simp) hc
    have hh := mfderiv_comp 0 hcs hT.mdifferentiableAt
    rw [hT0, hT.mfderiv] at hh
    exact hh
  change D = ContinuousLinearMap.id ℝ E
  rw [hd, hC, ContinuousLinearMap.comp_id]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The original product chart leaves the vector parameter unchanged. -/
theorem modelChart_prod_fst (x y : P × M) :
    (NoExoticSixSphere.modelChartPartialDiffeomorph (I := 𝓘(ℝ, P).prod I) x y).1 = y.1 := by
  change (extChartAt (𝓘(ℝ, P).prod I) x y).1 = y.1
  rw [extChartAt_prod]
  rfl

/-- The inverse original product chart also leaves the parameter unchanged. -/
theorem modelChart_prod_symm_fst (x : P × M) (v : P × E) :
    ((NoExoticSixSphere.modelChartPartialDiffeomorph
      (I := 𝓘(ℝ, P).prod I) x).symm v).1 = v.1 := by
  change ((extChartAt (𝓘(ℝ, P).prod I) x).symm v).1 = v.1
  rw [extChartAt_prod, PartialEquiv.prod_symm]
  rfl

/-- Centering the original product chart translates the parameter by its
base value, with no mixing with spatial coordinates. -/
theorem chart_prod_fst (x : P × M) (v : P × E) :
    (chart (I := 𝓘(ℝ, P).prod I) x v).1 = v.1 + x.1 := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := 𝓘(ℝ, P).prod I) x
  change (c.symm (v + c x)).1 = v.1 + x.1
  rw [modelChart_prod_symm_fst]
  change v.1 + (c x).1 = v.1 + x.1
  rw [modelChart_prod_fst]

end Wikipedia.HopfProblem.OrbitPair.NativeCenteredChart
