import Wikipedia.HopfProblem.DegreeCollapseThreePassageNormalFactors
import Wikipedia.HopfProblem.DegreeCollapseSpherePassageFrames

/-!
# Opposite three-sphere passages across the original four-handle belt

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

local notation "D₃" => EuclideanSpace ℝ (Fin 3)
local notation "P₄" => EuclideanSpace ℝ (Fin 4)
local notation "S₃" => Hemisphere.Sphere 3

variable {E M Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  [TopologicalSpace Z] [ChartedSpace D₃ Z] [IsManifold (𝓡 3) ∞ Z]
  [SecondCountableTopology Z]

theorem exists_native_four_opposite_centered_passages
    (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 3 + 1)]
    (α : C(S₃, d.UpperLevel)) (hαe : IsEmbedding α)
    (hdisj : Disjoint (range α) (range d.surgery.beltSphere))
    (b : Z → d.UpperLevel) (hbc : IsClosed (range b))
    (x : S₃) (v : sphere (0 : d.chart.PositiveCoordinates) 1)
    (hx : α x ∉ range b) (hv : d.surgery.beltSphere v ∉ range b)
    (γ : Path (α x) (d.surgery.beltSphere v)) :
    let _ := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ α →
    (∀ z, Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) α z)) →
    ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ b →
    ∃ A₀ A₁ : CenteredSheetPassage (RegularLevel.Model E) α d.surgery.beltSphere x v (range b),
      ∃ L₀ L₁ : P₄ ≃L[ℝ] d.chart.NegativeCoordinates,
        HasFDerivAt (fun z : P₄ => d.beltNormal (A₀.family
          ((sphereRadialParameterChart 3 (1 / 2) x z).1,
            α (sphereRadialParameterChart 3 (1 / 2) x z).2)))
          L₀.toContinuousLinearMap 0 ∧
        HasFDerivAt (fun z : P₄ => d.beltNormal (A₁.family
          ((sphereRadialParameterChart 3 (1 / 2) x z).1,
            α (sphereRadialParameterChart 3 (1 / 2) x z).2)))
          L₁.toContinuousLinearMap 0 ∧
        (L₁.trans L₀.symm).toLinearMap.det < 0 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  dsimp only
  intro hα hαi hb
  have hleveldim : Module.finrank ℝ (RegularLevel.Model E) = 6 := by
    simp [RegularLevel.Model, hdim]
  have hn := d.contMDiffOn_beltNormal hf |>.contMDiffAt
    (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  obtain ⟨P, B, hchoices⟩ := exists_three_passage_normal_factors hα (d.belt_smooth hf 2)
    hαe d.belt_isClosedEmbedding.isEmbedding hαi (d.belt_derivative_injective hf 2)
    hdisj hb hbc hleveldim x v hx hv γ d.beltNormal hn
    (d.surjective_beltNormal_derivative hf v) (d.beltNormal_derivative_comp_belt hf 2 v)
    (by exact Fact.out)
  obtain ⟨C, hC⟩ := SupportedGerms.exists_linearEquiv_with_det
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (0 : Fin 3)
    (show (-1 : ℝ) ≠ 0 by norm_num)
  have hCneg : C.toLinearMap.det < 0 := by rw [hC]; norm_num
  obtain ⟨c₀, hc₀, A₀, hA₀, hbij₀⟩ := hchoices (ContinuousLinearEquiv.refl ℝ D₃)
  obtain ⟨c₁, hc₁, A₁, hA₁, _⟩ := hchoices C
  let Q₀ := passageNormalProduct c₀ hc₀.ne' (ContinuousLinearEquiv.refl ℝ D₃)
  let Q₁ := passageNormalProduct c₁ hc₁.ne' C
  obtain ⟨P', B', hP, hB⟩ :=
    exists_shared_sphere_passage_frames 3 P B Q₀ (by exact Fact.out) hbij₀
  let L₀ := (P'.trans Q₀).trans B'
  let L₁ := (P'.trans Q₁).trans B'
  have hL₀ : L₀.toContinuousLinearMap = B.comp (Q₀.toContinuousLinearMap.comp P) := by
    change B'.toContinuousLinearMap.comp
      (Q₀.toContinuousLinearMap.comp P'.toContinuousLinearMap) = _
    rw [hP, hB]
  have hL₁ : L₁.toContinuousLinearMap = B.comp (Q₁.toContinuousLinearMap.comp P) := by
    change B'.toContinuousLinearMap.comp
      (Q₁.toContinuousLinearMap.comp P'.toContinuousLinearMap) = _
    rw [hP, hB]
  refine ⟨A₀, A₁, L₀, L₁, ?_, ?_, ?_⟩
  · rw [hL₀]
    exact hA₀
  · rw [hL₁]
    exact hA₁
  · exact sphere_passage_normal_relative_det_neg P' B' hc₀ hc₁ C hCneg

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
