import Wikipedia.HopfProblem.DegreeCollapseNativeThreeSheetBigon
import Wikipedia.HopfProblem.DegreeCollapseNativeTransverseBeltSphere

/-!
# Construct native tubular bigons for a three-sphere and the actual three-belt

Contractions below the native three-handle propagate to its actual upper
level. Two transverse crossings determine clean arcs in the original source
spheres, shared native corners, complete strip normal data, and embedded
tubular fillings avoiding both whole sheets. All geometry stays in the
original native regular-level atlas. The remaining issue is the signed
Whitney framing and its resulting supported intersection removal.
-/

noncomputable section

open Set Function Metric ContinuousMap Topology
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}

theorem exists_native_three_belt_tubular_strip_pair
    (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1)]
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    (hnull : ∀ γ : C(Hemisphere.Sphere 1, d.LowerLevel),
      ∃ z, γ.Homotopic (ContinuousMap.const _ z))
    (g : C(Hemisphere.Sphere 3, d.UpperLevel))
    (hgood : IsNativeTransverseBeltSphere d hf 3 3 g)
    (x₀ x₁ : Hemisphere.Sphere 3)
    (y₀ y₁ : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates)
    (hcross₀ : d.surgery.beltSphere y₀ = g x₀)
    (hcross₁ : d.surgery.beltSphere y₁ = g x₁) (hxy : x₀ ≠ x₁) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∃ α : C(ℝ, Hemisphere.Sphere 3),
    ∃ β : C(ℝ, PuncturedHandle.UnitSphere d.chart.PositiveCoordinates),
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ α ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ β ∧
      α 0 = x₀ ∧ α 1 = x₁ ∧ β 0 = y₀ ∧ β 1 = y₁ ∧
      ∃ k₀ k₁ l₀ l₁ : (ℝ × ℝ) → d.UpperLevel,
        ∃ k : CleanStripPatch (E := RegularLevel.Model E)
            (range g) (range d.surgery.beltSphere) (g ∘ α) k₀ k₁,
          ∃ l : CleanStripPatch (E := RegularLevel.Model E)
              (range d.surgery.beltSphere) (range g) (d.surgery.beltSphere ∘ β) l₀ l₁,
            Nonempty (StripNormalData (EuclideanSpace ℝ (Fin 2))
              (EuclideanSpace ℝ (Fin 3)) (E := RegularLevel.Model E) (range g) k.map) ∧
            Nonempty (StripNormalData (EuclideanSpace ℝ (Fin 2))
              (EuclideanSpace ℝ (Fin 3)) (E := RegularLevel.Model E)
              (range d.surgery.beltSphere) l.map) ∧
            ∀ h : ℝ, 0 < h → Nonempty (TubularBigon (E := RegularLevel.Model E)
              (range g) (range d.surgery.beltSphere)
              (g ∘ α) (d.surgery.beltSphere ∘ β) k.map l.map h) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1) := ⟨hindex⟩
  obtain ⟨hg, hinj, hi, ht⟩ := hgood
  have hnullupper := d.upper_circle_nullhomotopies hf 2 (by norm_num) (by omega) hnull
  have hpath : IsPathConnected (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    isPathConnected_sphere (by simp [← Module.finrank_eq_rank]) 0 (by norm_num)
  have hpos := Fact.out (p := Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1)
  have hpathB : IsPathConnected (sphere (0 : d.chart.PositiveCoordinates) 1) :=
    isPathConnected_sphere (by rw [← Module.finrank_eq_rank, hpos]; norm_num) 0 (by norm_num)
  let γ : Path x₀ x₁ := (hpath.joinedIn x₀ x₀.property x₁ x₁.property).joined_subtype.somePath
  let η : Path y₀ y₁ := (hpathB.joinedIn y₀ y₀.property y₁ y₁.property).joined_subtype.somePath
  obtain ⟨u, hu⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 3))
  obtain ⟨α, β, hα, hβ, hα₀, hα₁, hβ₀, hβ₁, _, _, _, _, _, _, _,
      c₀, c₁, k, l, hnK, hnL, htube⟩ :=
    exists_native_three_sheet_tubular_bigons_of_circle_contractions hnullupper
      (by simp [RegularLevel.Model, hdim]) (by simp) hg (d.belt_smooth hf 3)
      hinj d.belt_isClosedEmbedding.injective hi (d.belt_derivative_injective hf 3)
      ht hcross₀ hcross₁ hxy γ η hu hu hu hu
  exact ⟨α, β, hα, hβ, hα₀, hα₁, hβ₀, hβ₁,
    c₀.map, c₁.map, c₀.swap.map, c₁.swap.map, k, l, hnK, hnL, htube⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
