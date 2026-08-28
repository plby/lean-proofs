import Wikipedia.SmoothSixDPoincare.SmoothMorseSurgery
import Wikipedia.SmoothSixDPoincare.ComplementTubularBigon
import Wikipedia.SmoothSixDPoincare.TwoDimensionalSharedCornerStrips
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Filling a clean bigon against the actual index-two Morse belt

Contractions in the original lower level give contractions in the complement
of the actual upper-level belt. Consequently the constructed clean boundary
of a two-dimensional sheet and that belt has a genuine embedded tubular
bigon in the five-dimensional regular level, with all strip germs retained.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
/-- The complement-contraction hypothesis concerns the old level and is proved for the belt. -/
theorem nonempty_belt_tubularBigon (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (hnull : ∀ g : C(Hemisphere.Sphere 1, d.LowerLevel),
      ∃ q, g.Homotopic (ContinuousMap.const _ q))
    (g : C(Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      {a b : ℝ → d.UpperLevel} {k l : (ℝ × ℝ) → d.UpperLevel} {h : ℝ},
      CleanBigonBoundary (E := RegularLevel.Model E)
        (range g) (range d.surgery.beltSphere) a b k l h →
      Nonempty (TubularBigon (E := RegularLevel.Model E)
        (range g) (range d.surgery.beltSphere) a b k l h 3) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro hg a b k l h B
  have hT : IsClosed (range d.surgery.beltSphere) := d.belt_isClosedEmbedding.isClosed_range
  have hnullbelt := d.chart.surgery_beltComplement_circle_nullhomotopies hf
    d.radius d.radius_pos d.block d.lower_regular d.surgery d.oldPiece_eq hindex
    (by omega) hnull
  exact B.nonempty_tubularBigon_of_complement_contractions g hg hT hnullbelt
    (by simp [RegularLevel.Model, hdim]) (by simp [RegularLevel.Model, hdim]) 3
    (by simp [RegularLevel.Model, hdim])

open Classical in
/-- Two transverse intersections with the actual belt give constructed strips and a full
tubular bigon. Paths, the belt's immersion, and its complement contractions are all supplied. -/
theorem exists_belt_tubular_strip_pair (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (hnull : ∀ g : C(Hemisphere.Sphere 1, d.LowerLevel),
      ∃ q, g.Homotopic (ContinuousMap.const _ q))
    (g : C(Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := d.chart.finrank_negative_add_positive; omega⟩
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_hinj : Injective g)
      (_hi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x))
      (_ht : ∀ x y, d.surgery.beltSphere y = g x →
        Surjective ((mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x).coprod
          (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere y)))
      (x₀ x₁ : Hemisphere.Sphere 2)
      (y₀ y₁ : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates),
      d.surgery.beltSphere y₀ = g x₀ → d.surgery.beltSphere y₁ = g x₁ → x₀ ≠ x₁ →
      ∃ a b : ℝ → d.UpperLevel,
        a 0 = g x₀ ∧ a 1 = g x₁ ∧ b 0 = g x₀ ∧ b 1 = g x₁ ∧
        ∃ k₀ k₁ l₀ l₁ : (ℝ × ℝ) → d.UpperLevel,
          ∃ k : CleanStripPatch (E := RegularLevel.Model E)
              (range g) (range d.surgery.beltSphere) a k₀ k₁,
            ∃ l : CleanStripPatch (E := RegularLevel.Model E)
                (range d.surgery.beltSphere) (range g) b l₀ l₁,
              Nonempty (StripNormalData (EuclideanSpace ℝ (Fin 1))
                (EuclideanSpace ℝ (Fin 3)) (E := RegularLevel.Model E) (range g) k.map) ∧
              Nonempty (StripNormalData (EuclideanSpace ℝ (Fin 2))
                (EuclideanSpace ℝ (Fin 2)) (E := RegularLevel.Model E)
                (range d.surgery.beltSphere) l.map) ∧
              ∀ h : ℝ, 0 < h → Nonempty (TubularBigon (E := RegularLevel.Model E)
                (range g) (range d.surgery.beltSphere) a b k.map l.map h 3) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  have hpos : Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1 := by
    have hh := d.chart.finrank_negative_add_positive
    omega
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) := ⟨hpos⟩
  intro hg hinj hi ht x₀ x₁ y₀ y₁ hcross₀ hcross₁ hxy
  have hpath₂ : IsPathConnected (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isPathConnected_sphere (by simp [← Module.finrank_eq_rank]) 0 (by norm_num)
  have hpath₃ : IsPathConnected (sphere (0 : d.chart.PositiveCoordinates) 1) :=
    isPathConnected_sphere (by rw [← Module.finrank_eq_rank, hpos]; norm_num) 0 (by norm_num)
  let γ : Path x₀ x₁ :=
    (hpath₂.joinedIn x₀ x₀.property x₁ x₁.property).joined_subtype.somePath
  let η : Path y₀ y₁ :=
    (hpath₃.joinedIn y₀ y₀.property y₁ y₁.property).joined_subtype.somePath
  have hG := d.belt_smooth hf 3
  have hiG := d.belt_derivative_injective hf 3
  obtain ⟨α, β, -, -, hα₀, hα₁, hβ₀, hβ₁, -, -, -, -, -, -, -,
      c₀, c₁, k, l, hnK, hnL, -, hboundary⟩ :=
    exists_native_shared_corner_strip_pair_dim_two hg hG hinj d.belt_isClosedEmbedding.injective
      hi hiG (by simp) (by simp) (by simp [RegularLevel.Model, hdim])
      ht hcross₀ hcross₁ hxy γ η
  refine ⟨g ∘ α, d.surgery.beltSphere ∘ β, ?_, ?_, ?_, ?_,
    c₀.map, c₁.map, c₀.swap.map, c₁.swap.map, k, l, ?_, ?_, ?_⟩
  · change g (α 0) = g x₀
    rw [hα₀]
  · change g (α 1) = g x₁
    rw [hα₁]
  · change d.surgery.beltSphere (β 0) = g x₀
    rw [hβ₀, hcross₀]
  · change d.surgery.beltSphere (β 1) = g x₁
    rw [hβ₁, hcross₁]
  · have transport (m n : ℕ)
        (hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) - 1 = m)
        (hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = n) :
        Nonempty (StripNormalData (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin n)) (E := RegularLevel.Model E) (range g) k.map) := by
      subst m
      subst n
      exact hnK
    exact transport 1 3 (by simp) (by simp)
  · have transport (m n : ℕ)
        (hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1 = m)
        (hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = n) :
        Nonempty (StripNormalData (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin n)) (E := RegularLevel.Model E)
          (range d.surgery.beltSphere) l.map) := by
      subst m
      subst n
      exact hnL
    exact transport 2 2 (by simp) (by simp)
  · intro h hh
    obtain ⟨B⟩ := hboundary h hh
    exact d.nonempty_belt_tubularBigon hf hdim hindex hnull g hg B

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
