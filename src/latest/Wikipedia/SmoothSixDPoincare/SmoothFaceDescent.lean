import Wikipedia.SmoothSixDPoincare.SmoothClosedFace
import Wikipedia.SmoothSixDPoincare.ChartedFaceExteriorTransport

/-!
# Retained data for one actual smooth downward face move

The lower face, full chart, original shrinking, ambient extension, upper
isotopy, and exact whole-sublevel identity are retained together. These
are the witnesses used in a finite passage, not independent existence
claims about its intermediate levels.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  (I : ModelWithCorners ℝ G H) (X N : Type*) [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup N] [InnerProductSpace ℝ N]

abbrev LowerSmoothFace :=
  letI := RegularLevel.chartedSpace hf d.lower_regular;
  SmoothClosedFace I 𝓘(ℝ, RegularLevel.Model E) X N d.LowerLevel

abbrev UpperSmoothFace :=
  letI := RegularLevel.chartedSpace hf d.upper_regular;
  SmoothClosedFace I 𝓘(ℝ, RegularLevel.Model E) X N d.UpperLevel

structure FaceDescent (g : d.UpperSmoothFace hf I X N) where
  lower : d.LowerSmoothFace hf I X N
  scale : ℝ
  scale_pos : 0 < scale
  scale_lt_one : scale < 1
  shrunk : d.ShrunkSurgeryRealization scale
  ambient : shrunk.AmbientExtension
  smooth_exterior : shrunk.HasSmoothExterior hf
  upperMap : letI := RegularLevel.chartedSpace hf d.upper_regular;
    Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) d.UpperLevel d.UpperLevel ∞
  isotopic : letI := RegularLevel.chartedSpace hf d.upper_regular;
    SupportedDiffeomorph.IsotopicToIdentity upperMap
  disjoint : letI := RegularLevel.chartedSpace hf d.lower_regular;
    Disjoint (range lower.map) (range d.surgery.oldPiece)
  chart_target : letI := RegularLevel.chartedSpace hf d.lower_regular;
    lower.chart.target ⊆ (range d.surgery.oldPiece)ᶜ
  face_eq : letI := RegularLevel.chartedSpace hf d.lower_regular;
    letI := RegularLevel.chartedSpace hf d.upper_regular;
    ∀ z,
    (shrunk.attachmentHomeomorph ⟨(lower.map z).val, Or.inl (lower.map z).property.le⟩).val =
      (upperMap (g.map z)).val

variable [T2Space M] [CompactSpace M] [FiniteDimensional ℝ G] [I.Boundaryless]
  [IsManifold I ∞ X] [CompactSpace X] [T2Space X] [FiniteDimensional ℝ N]

theorem nonempty_faceDescent (hd : d.HasSmoothExterior hf) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ G + n < Module.finrank ℝ E - 1)
    (x₀ : X) (g : d.UpperSmoothFace hf I X N) : Nonempty (d.FaceDescent hf I X N g) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  obtain ⟨e, he, s, hs, hs₁, R, ⟨H⟩, hR, L, hL, hdisjoint, hmap, Ψ, hsource, hpoint, htarget⟩ :=
    d.exists_smooth_shrunk_disjoint_chartedFace I hf hd n hdim x₀ g.map
      g.closedEmbedding.injective g.chart g.source g.point
  exact ⟨{
    lower := ⟨L, hL, Ψ, hsource, hpoint⟩
    scale := s
    scale_pos := hs
    scale_lt_one := hs₁
    shrunk := R
    ambient := H
    smooth_exterior := hR
    upperMap := e
    isotopic := he
    disjoint := hdisjoint
    chart_target := htarget
    face_eq := hmap }⟩

theorem nonempty_faceDescent_of_index (hd : d.HasSmoothExterior hf)
    (hindex : Module.finrank ℝ G < Module.finrank ℝ d.chart.NegativeCoordinates)
    (hmax : Module.finrank ℝ d.chart.NegativeCoordinates < Module.finrank ℝ E)
    (x₀ : X) (g : d.UpperSmoothFace hf I X N) : Nonempty (d.FaceDescent hf I X N g) := by
  have hsplit := d.chart.finrank_negative_add_positive
  let n := Module.finrank ℝ d.chart.PositiveCoordinates - 1
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1) := ⟨by dsimp [n]; omega⟩
  apply d.nonempty_faceDescent hf I X N hd n _ x₀ g
  dsimp [n]
  omega

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
