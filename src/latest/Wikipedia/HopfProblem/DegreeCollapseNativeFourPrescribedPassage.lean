import Wikipedia.HopfProblem.DegreeCollapseNativeFourOppositePassages
import Wikipedia.SmoothSixDPoincare.LinearSphereEquiv

/-!
# Either prescribed integral three-class coefficient on the native four-handle level

The first normalized derivative acts by an integral unit relative to the
original sphere parametrization. The second acts by its negative. Thus
either requested unit is realized by one of the actual protected isotopies.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology

local notation "D₃" => EuclideanSpace ℝ (Fin 3)
local notation "P₄" => EuclideanSpace ℝ (Fin 4)
local notation "S₃" => Hemisphere.Sphere 3

section Choice

variable {E M Y N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

theorem choose_prescribed_three_normal_passage
    {f : S₃ → M} {g : Y → M} {x : S₃} {y : Y} {O : Set M}
    (n : M → N) (e : S₃ ≃ₜ sphere (0 : N) 1)
    (A₀ A₁ : CenteredSheetPassage E f g x y O) (L₀ L₁ : P₄ ≃L[ℝ] N)
    (hL₀ : HasFDerivAt (fun z : P₄ => n (A₀.family
      ((sphereRadialParameterChart 3 (1 / 2) x z).1,
        f (sphereRadialParameterChart 3 (1 / 2) x z).2)))
      L₀.toContinuousLinearMap 0)
    (hL₁ : HasFDerivAt (fun z : P₄ => n (A₁.family
      ((sphereRadialParameterChart 3 (1 / 2) x z).1,
        f (sphereRadialParameterChart 3 (1 / 2) x z).2)))
      L₁.toContinuousLinearMap 0)
    (hdet : (L₁.trans L₀.symm).toLinearMap.det < 0)
    (k : ℤ) (hk : k = 1 ∨ k = -1) :
    ∃ (A : CenteredSheetPassage E f g x y O) (L : P₄ ≃L[ℝ] N),
      HasFDerivAt (fun z : P₄ => n (A.family
        ((sphereRadialParameterChart 3 (1 / 2) x z).1,
          f (sphereRadialParameterChart 3 (1 / 2) x z).2)))
        L.toContinuousLinearMap 0 ∧
      singularHomologyMap (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 3 =
        k • singularHomologyMap (e : C(S₃, sphere (0 : N) 1)) 3 := by
  have hbij : Bijective (singularHomologyMap
      (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 3) := by
    have heq : (LinearSphereAction.homologyEquiv L₀ 3 :
        SingularHomology S₃ 3 → SingularHomology (sphere (0 : N) 1) 3) =
        singularHomologyMap
          (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 3 :=
      funext (LinearSphereAction.homologyEquiv_apply L₀ 3)
    rw [← heq]
    exact (LinearSphereAction.homologyEquiv L₀ 3).bijective
  obtain ⟨u, hu, hunit⟩ := sphere_map_unit_of_homology_bijective 2 e
    (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) hbij
  have hopp : singularHomologyMap
      (LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective) 3 =
      -singularHomologyMap
        (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 3 := by
    simpa using sphere_attaching_contributions_opposite_of_relative_det_neg 2
      (ContinuousMap.id (sphere (0 : N) 1)) L₀ L₁ hdet
  by_cases huk : u = k
  · exact ⟨A₀, L₀, hL₀, huk ▸ hunit⟩
  · have hneg : -u = k := by
      rcases hu with rfl | rfl <;> rcases hk with rfl | rfl <;> norm_num at *
    refine ⟨A₁, L₁, hL₁, ?_⟩
    rw [hopp, hunit, ← neg_zsmul, hneg]

end Choice

variable {E M Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  [TopologicalSpace Z] [ChartedSpace D₃ Z] [IsManifold (𝓡 3) ∞ Z]
  [SecondCountableTopology Z]

theorem exists_native_four_prescribed_centered_passage
    (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 3 + 1)]
    (α : C(S₃, d.UpperLevel)) (hαe : IsEmbedding α)
    (hdisj : Disjoint (range α) (range d.surgery.beltSphere))
    (b : Z → d.UpperLevel) (hbc : IsClosed (range b))
    (x : S₃) (v : sphere (0 : d.chart.PositiveCoordinates) 1)
    (hx : α x ∉ range b) (hv : d.surgery.beltSphere v ∉ range b)
    (γ : Path (α x) (d.surgery.beltSphere v)) (k : ℤ) (hk : k = 1 ∨ k = -1) :
    let _ := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ α →
    (∀ z, Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) α z)) →
    ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ b →
    ∃ A : CenteredSheetPassage (RegularLevel.Model E) α d.surgery.beltSphere x v (range b),
      ∃ L : P₄ ≃L[ℝ] d.chart.NegativeCoordinates,
        HasFDerivAt (fun z : P₄ => d.beltNormal (A.family
          ((sphereRadialParameterChart 3 (1 / 2) x z).1,
            α (sphereRadialParameterChart 3 (1 / 2) x z).2)))
          L.toContinuousLinearMap 0 ∧
        singularHomologyMap (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 3 =
          k • singularHomologyMap ((SphereCoordinates.standardParametrization
            d.chart.NegativeCoordinates 3).toHomeomorph :
              C(S₃, sphere (0 : d.chart.NegativeCoordinates) 1)) 3 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro hα hαi hb
  obtain ⟨A₀, A₁, L₀, L₁, hL₀, hL₁, hdet⟩ :=
    exists_native_four_opposite_centered_passages d hf hdim α hαe hdisj b hbc x v hx hv γ hα hαi hb
  exact choose_prescribed_three_normal_passage d.beltNormal
    (SphereCoordinates.standardParametrization d.chart.NegativeCoordinates 3).toHomeomorph
    A₀ A₁ L₀ L₁ hL₀ hL₁ hdet k hk

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
