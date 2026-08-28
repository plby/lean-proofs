import Wikipedia.HopfProblem.DegreeCollapseRadialLinkMeridian

/-!
# A single actual transverse belt passage adds one attaching class

The endpoint relation, actual local meridian comparison, integral unit
coefficient, and native lower-level flow transport are all constructed.
Thus the difference between the transported endpoint classes is exactly
one signed copy of the original attaching class, in its original native
parametrization. No intersection-to-degree comparison is assumed.
-/

noncomputable section

open Set Function Filter Metric ContinuousMap
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open PassageHomology SingularMayerVietoris PeriodTorusHigherHomology

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_single_passage_class_addition
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f)
    [Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1)]
    (H : C(ℝ × S₂, (S.data p).UpperLevel)) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    (x₀ : S₂) (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (hpoint : (S.data p).surgery.beltSphere v = H (τ, x₀))
    (hcross : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : S₂,
      H (t, x) ∈ range (S.data p).surgery.beltSphere ↔ t = τ ∧ x = x₀) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ H (τ, x₀) →
    NativeTransversality.At (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) 𝓘(ℝ, RegularLevel.Model E)
      H (S.data p).surgery.beltSphere (τ, x₀) v →
    ∃ D : C(((range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
      (∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y) ∧
      ∃ k : ℤ, (k = 1 ∨ k = -1) ∧
        let G := D.comp (puncturedPassageTrace H (range (S.data p).surgery.beltSphere) hτ x₀ hcross)
        singularHomologyMap (G.comp (cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
          singularHomologyMap (G.comp (cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
            k • singularHomologyMap ((S.data p).surgery.attachingSphere.comp
              ((SphereCoordinates.standardParametrization
                (S.data p).chart.NegativeCoordinates 2).toHomeomorph :
                  C(S₂, sphere (0 : (S.data p).chart.NegativeCoordinates) 1))) 2 := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  dsimp only
  intro hg htrans
  let e : S₂ ≃ₜ sphere (0 : (S.data p).chart.NegativeCoordinates) 1 :=
    (SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 2).toHomeomorph
  obtain ⟨D, horbit, hunique, hmeridian, _, hrelation⟩ :=
    S.exists_lower_passage_homology_relation hf p (e x₀) v H hτ x₀ hcross
  obtain ⟨ε, hε, hεx, w, β, hβ, hlink⟩ := exists_radial_link_meridian_comparison
    (S.data p) hf (by exact Fact.out) H hτ x₀ v hpoint hcross hg htrans
  obtain ⟨k, hk, hunit⟩ := two_sphere_map_unit_of_homology_bijective e β hβ
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
  have hunitMap : singularHomologyMap ((S.data p).surgery.attachingSphere.comp β) 2 =
      k • singularHomologyMap ((S.data p).surgery.attachingSphere.comp (e : C(S₂, _))) 2 := by
    rw [singularHomologyMap_comp, singularHomologyMap_comp, hunit]
    apply LinearMap.ext
    intro a
    change singularHomologyMap (S.data p).surgery.attachingSphere 2
      (k • singularHomologyMap (e : C(S₂, _)) 2 a) =
        k • singularHomologyMap (S.data p).surgery.attachingSphere 2
          (singularHomologyMap (e : C(S₂, _)) 2 a)
    exact map_zsmul (singularHomologyMap (S.data p).surgery.attachingSphere 2) k _
  refine ⟨D, horbit, hunique, k, hk, ?_⟩
  have hh := hrelation ε hε hεx
  change singularHomologyMap (G.comp (cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
    singularHomologyMap (G.comp (cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
      singularHomologyMap (G.comp (cylinderLink τ x₀ ε hε hεx)) 2 at hh
  rw [hlinkMap, hunitMap] at hh
  exact hh

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
