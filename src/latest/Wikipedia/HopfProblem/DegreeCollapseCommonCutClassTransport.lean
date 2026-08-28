import Wikipedia.HopfProblem.DegreeCollapseSignedFamilySlide

/-!
# Transport actual signed sphere-class relations to the fixed common cut

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

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.section_class_of_flow_transport
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (β : C(S₂, {y : M // f y = b})) (α : C(S₂, {y : M // f y = a}))
    (horbit : ∀ x, ∃ t : ℝ, S.flow t (β x).val = (α x).val) :
    singularHomologyMap (sublevelMap f hab.le) 2 (middleSectionClass α) =
      middleSectionClass β := by
  have hm := homotopic_homologyMap (S.level_transport_homotopic_in_sublevel hf hab ha β α horbit) 2
  have hmaps : (sublevelMap f hab.le).comp ((levelSublevelMap f le_rfl).comp α) =
      (levelSublevelMap f hab.le).comp α := by
    apply ContinuousMap.ext
    intro x
    rfl
  rw [middleSectionClass, ← LinearMap.comp_apply, ← singularHomologyMap_comp, hmaps, ← hm]
  rfl

theorem signed_relation_of_regular_cut_transport
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hband : ∀ y, f y ∈ Icc a b → y ∉ criticalPoints E f)
    (β δ γ : C(S₂, {y : M // f y = b}))
    (α ζ θ : C(S₂, {y : M // f y = a})) (k : ℤ)
    (hβ : ∀ x, ∃ t : ℝ, S.flow t (β x).val = (α x).val)
    (hδ : ∀ x, ∃ t : ℝ, T.flow t (δ x).val = (ζ x).val)
    (hγ : ∀ x, ∃ t : ℝ, S.flow t (γ x).val = (θ x).val)
    (hmap : singularHomologyMap δ 2 = singularHomologyMap β 2 + k • singularHomologyMap γ 2) :
    middleSectionClass ζ = middleSectionClass α + k • middleSectionClass θ := by
  have heval : (k • singularHomologyMap γ 2) (unitSphereTopClass 1) =
      k • singularHomologyMap γ 2 (unitSphereTopClass 1) :=
    map_zsmul (LinearMap.evalAddMonoidHom (unitSphereTopClass 1)) k (singularHomologyMap γ 2)
  have hclasses : middleSectionClass δ = middleSectionClass β + k • middleSectionClass γ := by
    simp only [middleSectionClass, singularHomologyMap_comp, LinearMap.comp_apply,
      hmap, LinearMap.add_apply, heval, map_add, map_zsmul]
  apply (regular_sublevel_inclusion_bijective hf hab.le hband 2).1
  rw [map_add, map_zsmul, T.section_class_of_flow_transport hf hab ha δ ζ hδ,
    S.section_class_of_flow_transport hf hab ha β α hβ,
    S.section_class_of_flow_transport hf hab ha γ θ hγ]
  exact hclasses

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
