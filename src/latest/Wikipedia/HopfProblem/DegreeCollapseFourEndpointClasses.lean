import Wikipedia.HopfProblem.DegreeCollapseFourPassageClassAddition
import Wikipedia.HopfProblem.DegreeCollapseIndexFourSectionClass

/-!
# The prescribed four-handle coefficient holds for the actual lower maps

The derivative-sensitive passage relation and its selected sphere action
give the requested coefficient. Unique original-flow transport identifies
the two endpoint representatives with any actual lower maps carrying the
same orbit formulas.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open PassageHomology SingularMayerVietoris PeriodTorusHigherHomology

local notation "P₄" => EuclideanSpace ℝ (Fin 4)
local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.prescribed_four_passage_actual_endpoint_classes
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 4)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 3 + 1)]
    (H : C(ℝ × S₃, (S.data q).UpperLevel)) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    (x₀ : S₃) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hpoint : (S.data q).surgery.beltSphere v = H (τ, x₀))
    (hcross : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : S₃,
      H (t, x) ∈ range (S.data q).surgery.beltSphere ↔ t = τ ∧ x = x₀)
    (β δ : C(S₃, (S.data q).LowerLevel))
    (hβ : ∀ x, ∃ t : ℝ, S.flow t (H (0, x)).val = (β x).val)
    (hδ : ∀ x, ∃ t : ℝ, S.flow t (H (1, x)).val = (δ x).val)
    (k : ℤ) (L : P₄ ≃L[ℝ] (S.data q).chart.NegativeCoordinates)
    (hL : HasFDerivAt (fun z : P₄ =>
      (S.data q).beltNormal (H (sphereRadialParameterChart 3 τ x₀ z)))
      L.toContinuousLinearMap 0)
    (hunit : singularHomologyMap
      (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 3 =
      k • singularHomologyMap ((SphereCoordinates.standardParametrization
        (S.data q).chart.NegativeCoordinates 3).toHomeomorph :
          C(S₃, sphere (0 : (S.data q).chart.NegativeCoordinates) 1)) 3) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, RegularLevel.Model E) ∞ H (τ, x₀) →
    singularHomologyMap δ 3 = singularHomologyMap β 3 +
      k • singularHomologyMap (nativeIndexFourAttachingSphere S q hq) 3 := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  dsimp only
  intro hH
  obtain ⟨D, _, hunique, hrelation⟩ :=
    S.exists_four_passage_derivative_class_addition hf q H hτ x₀ v hpoint hcross L hL hH
  let G := D.comp (puncturedPassageTrace H (range (S.data q).surgery.beltSphere) hτ x₀ hcross)
  have hmap (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hsτ : s ≠ τ)
      (σ : C(S₃, (S.data q).LowerLevel))
      (hσ : ∀ x, ∃ t : ℝ, S.flow t (H (s, x)).val = (σ x).val) :
      G.comp (cylinderSlice τ x₀ s hsτ) = σ := by
    apply ContinuousMap.ext
    intro x
    obtain ⟨t, ht⟩ := hσ x
    apply hunique _ (σ x) t
    have heq := puncturedPassageTrace_on_interval H
      (range (S.data q).surgery.beltSphere) hτ x₀ hcross (cylinderSlice τ x₀ s hsτ x) hs
    change S.flow t
      (puncturedPassageTrace H (range (S.data q).surgery.beltSphere) hτ x₀ hcross
        (cylinderSlice τ x₀ s hsτ x)).val.val = (σ x).val
    rw [heq]
    exact ht
  have hzero := hmap 0 ⟨le_rfl, zero_le_one⟩ hτ.1.ne β hβ
  have hone := hmap 1 ⟨zero_le_one, le_rfl⟩ hτ.2.ne' δ hδ
  have hcoef : singularHomologyMap ((S.data q).surgery.attachingSphere.comp
      (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective)) 3 =
      k • singularHomologyMap (nativeIndexFourAttachingSphere S q hq) 3 := by
    change singularHomologyMap ((S.data q).surgery.attachingSphere.comp
      (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective)) 3 =
      k • singularHomologyMap ((S.data q).surgery.attachingSphere.comp
        ((SphereCoordinates.standardParametrization
          (S.data q).chart.NegativeCoordinates 3).toHomeomorph :
          C(S₃, sphere (0 : (S.data q).chart.NegativeCoordinates) 1))) 3
    rw [singularHomologyMap_comp, singularHomologyMap_comp, hunit]
    apply LinearMap.ext
    intro a
    exact map_zsmul (singularHomologyMap (S.data q).surgery.attachingSphere 3) k _
  change singularHomologyMap (G.comp (cylinderSlice τ x₀ 1 hτ.2.ne')) 3 =
    singularHomologyMap (G.comp (cylinderSlice τ x₀ 0 hτ.1.ne)) 3 +
      singularHomologyMap ((S.data q).surgery.attachingSphere.comp
        (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective)) 3 at hrelation
  rw [hone, hzero, hcoef] at hrelation
  exact hrelation

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
