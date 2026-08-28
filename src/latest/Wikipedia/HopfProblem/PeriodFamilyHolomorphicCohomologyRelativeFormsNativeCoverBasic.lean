import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeBasic
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeGeometrySmooth
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Actual tangent coordinates on the original open-product cover

The charted space is exactly the inherited open-base and product charted
space. Its preferred forward charts are the same literal inclusion into
`ℂ × ComplexPlane₂`. The resulting native tangent transitions are therefore
identity maps. This statement is specific to this original flat cover.
-/

noncomputable section

open Bundle TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native

open HolomorphicDolbeaultThree

variable {U : Opens ℂ}

local instance coverChartedSpace : ChartedSpace Model (U × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (U × ComplexPlane₂))

local instance coverRealManifold : IsManifold 𝓘(ℝ, Model) ∞ (U × ComplexPlane₂) := by
  let : IsManifold 𝓘(ℂ, Model) ∞ (U × ComplexPlane₂) := by
    change IsManifold 𝓘(ℂ, ℂ × ComplexPlane₂) ∞ (U × ComplexPlane₂)
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ComplexPlane₂))
      U ComplexPlane₂
  exact HolomorphicDolbeaultThree.Geometry.realManifold_of_complex
    (U × ComplexPlane₂) ∞

/-- Every original preferred forward chart on the cover is the literal
open-product inclusion, independently of its centre. -/
@[simp] theorem cover_chart_apply (p q : U × ComplexPlane₂) :
    chartAt Model p q = ((q.1 : ℂ), q.2) := rfl

/-- The inherited open-product charts have the whole original cover as
their source. No claim is made about their values outside their targets. -/
theorem cover_mem_chart_source (p q : U × ComplexPlane₂) :
    q ∈ (chartAt Model p).source := by
  change q.1 ∈ (chartAt ℂ p.1).source ∧ q.2 ∈ (chartAt ComplexPlane₂ p.2).source
  simp only [Opens.chartAt_eq, chartAt_self_eq, mfld_simps]

/-- The genuine native tangent transition in these original flat charts
is the identity on every actual cover point. -/
theorem cover_tangentCoordChange_apply (p r q : U × ComplexPlane₂) (v : Model) :
    tangentCoordChange 𝓘(ℝ, Model) p r q v = v := by
  have hforward : (chartAt Model r : (U × ComplexPlane₂) → Model) =
      (chartAt Model p : (U × ComplexPlane₂) → Model) := by
    funext y
    rw [cover_chart_apply, cover_chart_apply]
  have heq : tangentCoordChange 𝓘(ℝ, Model) p r q =
      tangentCoordChange 𝓘(ℝ, Model) p p q := by
    simp only [tangentCoordChange_def, mfld_simps]
    rw [hforward]
  rw [heq]
  exact tangentCoordChange_self (by
    simpa only [mfld_simps] using cover_mem_chart_source p q)

/-- The actual native inverse tangent trivialization on the original
cover is the identity under the defining tangent-model type synonym. -/
theorem cover_symmL_trivializationAt_apply (p q : U × ComplexPlane₂) (v : Model) :
    (show Model from
      (trivializationAt Model (TangentSpace 𝓘(ℝ, Model) : (U × ComplexPlane₂) → Type) p).symmL
        ℝ q v) = v := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (cover_mem_chart_source p q)]
  exact cover_tangentCoordChange_apply p q q v

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native
