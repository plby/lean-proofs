import Wikipedia.SmoothSixDPoincare.AnnularPatchInclusion
import Wikipedia.SmoothSixDPoincare.FramedSurgerySmoothBoundary

/-!
# The annular lower chart is a full native patch of the constructed surgery boundary

The original attaching-neighborhood diffeomorphism and old-patch inclusion
retain the actual annular lower points. Their native partial diffeomorphisms
compose on the whole annulus, including the surgery corner.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open PuncturedHandle FramedSurgery MorseHandle

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p) (m n : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]
  [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]

open Classical in
theorem annularInclusion_mem_attachingSource
    (z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    annularInclusionPartial m n z ∈ d.chart.attachingSource d.radius d.radius_pos :=
  (d.annularAttachingPoint z).property

open Classical in
def annularAttachingPartial :
    PartialDiffeomorph ((𝓡 m).prod 𝓘(ℝ, d.chart.PositiveCoordinates))
      ((𝓡 m).prod 𝓘(ℝ, d.chart.PositiveCoordinates))
      (AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates)
      (d.chart.attachingSource d.radius d.radius_pos) ∞ := by
  let _ := nonempty_annularParameters
    (N := d.chart.NegativeCoordinates) (P := d.chart.PositiveCoordinates) m n
  exact PartialChart.intoOpen (annularInclusionPartial m n)
    (d.chart.attachingSource d.radius d.radius_pos) (d.annularInclusion_mem_attachingSource m n)

open Classical in
theorem annularAttachingPartial_source : (d.annularAttachingPartial m n).source = univ := by
  let _ := nonempty_annularParameters
    (N := d.chart.NegativeCoordinates) (P := d.chart.PositiveCoordinates) m n
  exact PartialChart.intoOpen_source (annularInclusionPartial m n)
    (d.chart.attachingSource d.radius d.radius_pos) (d.annularInclusion_mem_attachingSource m n)
      (annularInclusionPartial_source m n)

open Classical in
theorem annularAttachingPartial_point
    (z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    d.annularAttachingPartial m n z = d.annularAttachingPoint z := by
  let _ := nonempty_annularParameters
    (N := d.chart.NegativeCoordinates) (P := d.chart.PositiveCoordinates) m n
  apply Subtype.ext
  exact PartialChart.intoOpen_apply (annularInclusionPartial m n)
    (d.chart.attachingSource d.radius d.radius_pos) (d.annularInclusion_mem_attachingSource m n) z

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
def annularLowerPartial :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    PartialDiffeomorph ((𝓡 m).prod 𝓘(ℝ, d.chart.PositiveCoordinates))
      𝓘(ℝ, RegularLevel.Model E)
      (AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates)
      d.LowerLevel ∞ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let z₀ := Classical.choice (nonempty_annularParameters
    (N := d.chart.NegativeCoordinates) (P := d.chart.PositiveCoordinates) m n)
  let _ : Nonempty (d.chart.attachingTarget d.radius) :=
    ⟨d.chart.attachingNeighborhoodHomeomorph d.radius d.radius_pos (d.annularAttachingPoint z₀)⟩
  exact ((d.annularAttachingPartial m n).trans
    (d.chart.attachingNeighborhoodDiffeomorph hf m d.radius d.radius_pos
      d.lower_regular).toPartialDiffeomorph).trans
    (PartialChart.openInclusion (d.chart.attachingTarget d.radius))

open Classical in
theorem annularLowerPartial_source :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    (d.annularLowerPartial m n hf).source = univ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  apply eq_univ_of_forall
  intro z
  refine ⟨⟨?_, mem_univ _⟩, mem_univ _⟩
  change z ∈ (d.annularAttachingPartial m n).source
  rw [d.annularAttachingPartial_source]
  trivial

open Classical in
theorem annularLowerPartial_point
    (z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    d.annularLowerPartial m n hf z = d.annularLowerPoint z := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  exact congrArg (fun w : d.chart.attachingSource d.radius d.radius_pos =>
    (d.chart.attachingNeighborhoodHomeomorph d.radius d.radius_pos w).val)
      (d.annularAttachingPartial_point m n z)

variable [T2Space M]

open Classical in
theorem annularLowerPartial_mem_oldPatch
    (z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    d.annularLowerPartial m n hf z ∈ oldPatch (d.attachingSmoothFace hf m) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  exact (d.annularLowerPartial_point m n hf z).symm ▸ d.annularLowerPoint_mem_oldPatch hf m z

open Classical in
def annularOldPartial :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    PartialDiffeomorph ((𝓡 m).prod 𝓘(ℝ, d.chart.PositiveCoordinates))
      𝓘(ℝ, RegularLevel.Model E)
      (AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates)
      (oldPatch (d.attachingSmoothFace hf m)) ∞ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := nonempty_annularParameters
    (N := d.chart.NegativeCoordinates) (P := d.chart.PositiveCoordinates) m n
  exact PartialChart.intoOpen (d.annularLowerPartial m n hf)
    (oldPatch (d.attachingSmoothFace hf m)) (d.annularLowerPartial_mem_oldPatch m n hf)

open Classical in
theorem annularOldPartial_source :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    (d.annularOldPartial m n hf).source = univ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := nonempty_annularParameters
    (N := d.chart.NegativeCoordinates) (P := d.chart.PositiveCoordinates) m n
  exact PartialChart.intoOpen_source (d.annularLowerPartial m n hf)
    (oldPatch (d.attachingSmoothFace hf m)) (d.annularLowerPartial_mem_oldPatch m n hf)
      (d.annularLowerPartial_source m n hf)

open Classical in
theorem annularOldPartial_point
    (z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    d.annularOldPartial m n hf z = d.annularOldPoint hf m z := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := nonempty_annularParameters
    (N := d.chart.NegativeCoordinates) (P := d.chart.PositiveCoordinates) m n
  apply Subtype.ext
  exact (PartialChart.intoOpen_apply (d.annularLowerPartial m n hf)
    (oldPatch (d.attachingSmoothFace hf m)) (d.annularLowerPartial_mem_oldPatch m n hf) z).trans
      (d.annularLowerPartial_point m n hf z)

variable (P : letI := RegularLevel.chartedSpace hf d.lower_regular
  SmoothBoundaryData (d.attachingSmoothFace hf m) n)

open Classical in
def annularBoundaryPartial :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := P.charted
    PartialDiffeomorph ((𝓡 m).prod 𝓘(ℝ, d.chart.PositiveCoordinates))
      𝓘(ℝ, RegularLevel.Model E)
      (AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates)
      (d.FramedBoundary hf m n) ∞ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := P.charted
  exact (d.annularOldPartial m n hf).trans P.oldPartial

open Classical in
theorem annularBoundaryPartial_source :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := P.charted
    (d.annularBoundaryPartial m n hf P).source = univ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := P.charted
  apply eq_univ_of_forall
  intro z
  refine ⟨?_, ?_⟩
  · change z ∈ (d.annularOldPartial m n hf).source
    rw [d.annularOldPartial_source]
    trivial
  · change d.annularOldPartial m n hf z ∈ P.oldPartial.source
    rw [P.old_source]
    trivial

open Classical in
theorem annularBoundaryPartial_point
    (z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := P.charted
    d.annularBoundaryPartial m n hf P z =
      oldMap (d.attachingSmoothFace hf m) n (d.annularOldPoint hf m z) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := P.charted
  change P.oldPartial (d.annularOldPartial m n hf z) = _
  rw [P.old_point, d.annularOldPartial_point m n hf]

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
