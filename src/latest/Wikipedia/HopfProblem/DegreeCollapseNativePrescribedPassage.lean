import Wikipedia.HopfProblem.DegreeCollapsePrescribedNormalCoefficient

/-!
# Either prescribed attaching coefficient on the original Morse level

Choose between the two constructed native passages using the integral
homology action of their actual normal derivatives. The original sphere
parametrization and protected ambient support are retained.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology

local notation "D₂" => EuclideanSpace ℝ (Fin 2)
local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₂" => Hemisphere.Sphere 2

variable {E M Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  [TopologicalSpace Z] [ChartedSpace D₂ Z] [IsManifold (𝓡 2) ∞ Z]
  [SecondCountableTopology Z]

theorem exists_native_prescribed_centered_passage
    (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)]
    (α : C(S₂, d.UpperLevel)) (hαe : IsEmbedding α)
    (hdisj : Disjoint (range α) (range d.surgery.beltSphere))
    (b : Z → d.UpperLevel) (hbc : IsClosed (range b))
    (x : S₂) (v : sphere (0 : d.chart.PositiveCoordinates) 1)
    (hx : α x ∉ range b) (hv : d.surgery.beltSphere v ∉ range b)
    (γ : Path (α x) (d.surgery.beltSphere v)) (k : ℤ) (hk : k = 1 ∨ k = -1) :
    let _ := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ α →
    (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) α z)) →
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ b →
    ∃ A : CenteredSheetPassage (RegularLevel.Model E) α d.surgery.beltSphere x v (range b),
      ∃ L : P₃ ≃L[ℝ] d.chart.NegativeCoordinates,
        HasFDerivAt (fun z : P₃ => d.beltNormal (A.family
          ((radialParameterChart (1 / 2) x z).1, α (radialParameterChart (1 / 2) x z).2)))
          L.toContinuousLinearMap 0 ∧
        singularHomologyMap (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
          k • singularHomologyMap ((SphereCoordinates.standardParametrization
            d.chart.NegativeCoordinates 2).toHomeomorph :
              C(S₂, sphere (0 : d.chart.NegativeCoordinates) 1)) 2 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro hα hαi hb
  obtain ⟨A₀, A₁, L₀, L₁, hL₀, hL₁, hdet⟩ :=
    exists_native_opposite_centered_passages d hf hdim α hαe hdisj b hbc x v hx hv γ hα hαi hb
  exact choose_prescribed_normal_passage d.beltNormal
    (SphereCoordinates.standardParametrization d.chart.NegativeCoordinates 2).toHomeomorph
    A₀ A₁ L₀ L₁ hL₀ hL₁ hdet k hk

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
