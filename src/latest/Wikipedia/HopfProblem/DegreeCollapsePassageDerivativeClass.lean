import Wikipedia.HopfProblem.DegreeCollapseRadialLinkDerivative

/-!
# The actual passage changes the attaching class by its normal derivative

Retain the literal normalized derivative map in the endpoint relation.
Opposite relative determinant signs give opposite homology contributions
after composition with the same original attaching sphere.
-/

noncomputable section

open Set Function Filter Metric ContinuousMap
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open PassageHomology SingularMayerVietoris PeriodTorusHigherHomology

local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_passage_derivative_class_addition
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f)
    [Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1)]
    (H : C(ℝ × S₂, (S.data p).UpperLevel)) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    (x₀ : S₂) (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (hpoint : (S.data p).surgery.beltSphere v = H (τ, x₀))
    (hcross : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : S₂,
      H (t, x) ∈ range (S.data p).surgery.beltSphere ↔ t = τ ∧ x = x₀)
    (L : P₃ ≃L[ℝ] (S.data p).chart.NegativeCoordinates)
    (hL : HasFDerivAt (fun z : P₃ =>
      (S.data p).beltNormal (H (radialParameterChart τ x₀ z))) L.toContinuousLinearMap 0) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ H (τ, x₀) →
    ∃ D : C(((range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
      (∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y) ∧
      let G := D.comp (puncturedPassageTrace H (range (S.data p).surgery.beltSphere) hτ x₀ hcross)
      singularHomologyMap (G.comp (cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
        singularHomologyMap (G.comp (cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
          singularHomologyMap ((S.data p).surgery.attachingSphere.comp
            (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective)) 2 := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  dsimp only
  intro hg
  let e : S₂ ≃ₜ sphere (0 : (S.data p).chart.NegativeCoordinates) 1 :=
    (SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 2).toHomeomorph
  obtain ⟨D, horbit, hunique, hmeridian, _, hrelation⟩ :=
    S.exists_lower_passage_homology_relation hf p (e x₀) v H hτ x₀ hcross
  obtain ⟨ε, hε, hεx, w, β, hβ, hlink⟩ := exists_radial_link_meridian_with_derivative
    (S.data p) hf H hτ x₀ v hpoint hcross L hL hg
  let σ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hσ : 0 < (σ : ℝ) := by norm_num [σ]
  have htube : nativeBeltTubeMeridian (S.data p) w (1 / 2) (by norm_num) (by norm_num) =
      nativeUpperMeridianInComplement S p w σ hσ :=
    nativeBeltTubeMeridian_eq S p w (1 / 2) (by norm_num) (by norm_num)
  rw [htube] at hlink
  let G := D.comp (puncturedPassageTrace H (range (S.data p).surgery.beltSphere) hτ x₀ hcross)
  have hDlink : (G.comp (cylinderLink τ x₀ ε hε hεx)).Homotopic
      ((D.comp (nativeUpperMeridianInComplement S p w σ hσ)).comp β) :=
    (Homotopic.refl D).comp hlink
  have hatt : ((D.comp (nativeUpperMeridianInComplement S p w σ hσ)).comp β).Homotopic
      ((S.data p).surgery.attachingSphere.comp β) :=
    (hmeridian w σ hσ).comp (Homotopic.refl β)
  have hlinkMap := homotopic_homologyMap (hDlink.trans hatt) 2
  have hderivativeMap : singularHomologyMap ((S.data p).surgery.attachingSphere.comp β) 2 =
      singularHomologyMap ((S.data p).surgery.attachingSphere.comp
        (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective)) 2 := by
    rw [singularHomologyMap_comp, singularHomologyMap_comp, hβ]
  refine ⟨D, horbit, hunique, ?_⟩
  have hh := hrelation ε hε hεx
  change singularHomologyMap (G.comp (cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
    singularHomologyMap (G.comp (cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
      singularHomologyMap (G.comp (cylinderLink τ x₀ ε hε hεx)) 2 at hh
  rw [hlinkMap, hderivativeMap] at hh
  exact hh

section Opposite

variable {N Y : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace Y]

theorem attaching_contributions_opposite_of_relative_det_neg
    (a : C(sphere (0 : N) 1, Y)) (L₀ L₁ : P₃ ≃L[ℝ] N)
    (hdet : (L₁.trans L₀.symm).toLinearEquiv.toLinearMap.det < 0) :
    singularHomologyMap (a.comp
      (LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective)) 2 =
      -singularHomologyMap (a.comp
        (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective)) 2 := by
  rw [singularHomologyMap_comp, singularHomologyMap_comp]
  apply LinearMap.ext
  intro u
  have h := LinearSphereAction.homology_relative_sign 1 L₁ L₀ 1 u
  rw [sign_eq_neg_one_iff.mpr hdet] at h
  simp only [SignType.coe_neg, SignType.coe_one, neg_one_zsmul] at h
  change singularHomologyMap a 2
    (singularHomologyMap (LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective) 2 u) =
      -singularHomologyMap a 2
        (singularHomologyMap (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2 u)
  rw [h, map_neg]

end Opposite

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
