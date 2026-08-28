import Wikipedia.HopfProblem.DegreeCollapseOppositeCenteredPassages

/-!
# Opposite passages across the original native Morse belt

The Morse normal projection discharges the normal hypotheses: it is
surjective and annihilates the actual belt tangent. Thus both supported
passages and their opposite actual normal derivatives are constructed in
the unchanged upper-level atlas.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "D₂" => EuclideanSpace ℝ (Fin 2)
local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₂" => Hemisphere.Sphere 2

variable {E M Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  [TopologicalSpace Z] [ChartedSpace D₂ Z] [IsManifold (𝓡 2) ∞ Z]
  [SecondCountableTopology Z]

theorem exists_native_opposite_centered_passages
    (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)]
    (α : C(S₂, d.UpperLevel)) (hαe : IsEmbedding α)
    (hdisj : Disjoint (range α) (range d.surgery.beltSphere))
    (b : Z → d.UpperLevel) (hbc : IsClosed (range b))
    (x : S₂) (v : sphere (0 : d.chart.PositiveCoordinates) 1)
    (hx : α x ∉ range b) (hv : d.surgery.beltSphere v ∉ range b)
    (γ : Path (α x) (d.surgery.beltSphere v)) :
    let _ := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ α →
    (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) α z)) →
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ b →
    ∃ A₀ A₁ : CenteredSheetPassage (RegularLevel.Model E) α d.surgery.beltSphere x v (range b),
      ∃ L₀ L₁ : P₃ ≃L[ℝ] d.chart.NegativeCoordinates,
        HasFDerivAt (fun z : P₃ => d.beltNormal (A₀.family
          ((radialParameterChart (1 / 2) x z).1, α (radialParameterChart (1 / 2) x z).2)))
          L₀.toContinuousLinearMap 0 ∧
        HasFDerivAt (fun z : P₃ => d.beltNormal (A₁.family
          ((radialParameterChart (1 / 2) x z).1, α (radialParameterChart (1 / 2) x z).2)))
          L₁.toContinuousLinearMap 0 ∧
        (L₁.trans L₀.symm).toLinearMap.det < 0 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  dsimp only
  intro hα hαi hb
  have hleveldim : Module.finrank ℝ (RegularLevel.Model E) = 5 := by
    simp [RegularLevel.Model, hdim]
  have hn := d.contMDiffOn_beltNormal hf |>.contMDiffAt
    (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  obtain ⟨P, B, hchoices⟩ := exists_centered_passage_normal_factors hα (d.belt_smooth hf 2)
    hαe d.belt_isClosedEmbedding.isEmbedding hαi (d.belt_derivative_injective hf 2)
    hdisj hb hbc hleveldim x v hx hv γ d.beltNormal hn
    (d.surjective_beltNormal_derivative hf v) (d.beltNormal_derivative_comp_belt hf 2 v)
    (by exact Fact.out)
  exact opposite_centered_passages_of_normal_factors d.beltNormal (by exact Fact.out) P B hchoices

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
