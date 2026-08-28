import Wikipedia.HopfProblem.DegreeCollapseRegularCutFourMatrixTransport

/-!
# Descend actual signed three-class relations to the original common cut

The orbit homotopies identify classes through literal sublevel inclusion.
Across a critical-free band this inclusion is injective on homology, so
the exact signed endpoint relation descends to the original common group.
The old and new endpoint transports may use different adapted flows.
-/

noncomputable section

open Set Function Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem three_signed_relation_of_regular_cut_transport
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hband : ∀ y, f y ∈ Icc a b → y ∉ criticalPoints E f)
    (β δ γ : C(S₃, {y : M // f y = b}))
    (α ζ θ : C(S₃, {y : M // f y = a})) (k : ℤ)
    (hβ : ∀ x, ∃ t : ℝ, S.flow t (β x).val = (α x).val)
    (hδ : ∀ x, ∃ t : ℝ, T.flow t (δ x).val = (ζ x).val)
    (hγ : ∀ x, ∃ t : ℝ, S.flow t (γ x).val = (θ x).val)
    (hmap : singularHomologyMap δ 3 = singularHomologyMap β 3 + k • singularHomologyMap γ 3) :
    threeSectionClass ζ = threeSectionClass α + k • threeSectionClass θ := by
  have heval : (k • singularHomologyMap γ 3) (unitSphereTopClass 2) =
      k • singularHomologyMap γ 3 (unitSphereTopClass 2) :=
    map_zsmul (LinearMap.evalAddMonoidHom (unitSphereTopClass 2)) k (singularHomologyMap γ 3)
  have hclasses : threeSectionClass δ = threeSectionClass β + k • threeSectionClass γ := by
    simp only [threeSectionClass, singularHomologyMap_comp, LinearMap.comp_apply,
      hmap, LinearMap.add_apply, heval, map_add, map_zsmul]
  apply (regular_sublevel_inclusion_bijective hf hab.le hband 3).1
  rw [map_add, map_zsmul, T.three_section_class_of_flow_transport hf hab ha δ ζ hδ,
    S.three_section_class_of_flow_transport hf hab ha β α hβ,
    S.three_section_class_of_flow_transport hf hab ha γ θ hγ]
  exact hclasses

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

