import Wikipedia.SmoothSixDPoincare.NativeAnnularRealizationSmooth
import Wikipedia.SmoothSixDPoincare.NativeBeltRealizationSmoothPatch
import Wikipedia.SmoothSixDPoincare.NativeBeltExteriorComparison
import Wikipedia.SmoothSixDPoincare.NativeBeltBoundaryPatchCover
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyEquiv

/-!
# A whole-body native Morse realization with a globally smooth boundary map

The belt patch, annular corner patch, and full-piece exterior cover the
entire constructed boundary. Their exact native patch identities prove
the corrected boundary homeomorphism and its inverse globally smooth.
It is the restriction of the explicit corrected whole-body realization,
which leaves the original lower body unchanged.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open FramedSurgery

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (m n : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]
  [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
  (P : letI := RegularLevel.chartedSpace hf d.lower_regular
    SmoothBoundaryData (d.attachingSmoothFace hf m) n)
  (hd : d.HasSmoothExterior hf)

open Classical in
include hd in
theorem beltFramedBoundaryRealization_contMDiff :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := P.charted
    ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
      (d.beltFramedBoundaryRealization hf m n) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ := P.charted
  intro z
  rcases d.nativeBelt_boundary_patch_cover hf m n P z with hz | hz | hz
  · exact (d.beltFramedBoundaryRealization_contMDiffOn_newPatch hf m n P).1.contMDiffAt
      (P.newPartial.open_target.mem_nhds hz)
  · exact (d.beltFramedBoundaryRealization_contMDiffOn_annular hf m n P).1.contMDiffAt
      ((d.annularBoundaryPartial m n hf P).open_target.mem_nhds hz)
  · exact (d.beltFramedBoundaryRealization_contMDiffOn_exterior hf m n P hd).1.contMDiffAt
      ((boundaryPair (d.attachingSmoothFace hf m) n).newOpenExterior.isOpen.mem_nhds hz)

open Classical in
include hd in
theorem beltFramedBoundaryRealization_symm_contMDiff :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := P.charted
    ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
      (d.beltFramedBoundaryRealization hf m n).symm := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ := P.charted
  intro y
  rcases d.nativeBelt_boundary_patch_cover hf m n P
    ((d.beltFramedBoundaryRealization hf m n).symm y) with hx | hx | hx
  · have hy := PartialChart.map_target_of_patchIdentity (d.beltFramedBoundaryRealization hf m n)
      P.newPartial (d.beltOpenPartial n hf)
      (by rw [P.new_source, d.beltOpenPartial_source n hf])
      (fun z _ => d.beltFramedBoundaryRealization_newPartial hf m n P z) hx
    rw [Homeomorph.apply_symm_apply] at hy
    exact (d.beltFramedBoundaryRealization_contMDiffOn_newPatch hf m n P).2.contMDiffAt
      ((d.beltOpenPartial n hf).open_target.mem_nhds hy)
  · have hy := PartialChart.map_target_of_patchIdentity (d.beltFramedBoundaryRealization hf m n)
      (d.annularBoundaryPartial m n hf P) (d.annularUpperPartial m n hf)
      (by rw [d.annularBoundaryPartial_source m n hf P, d.annularUpperPartial_source m n hf])
      (fun z _ => d.beltFramedBoundaryRealization_annularPartial hf m n P z) hx
    rw [Homeomorph.apply_symm_apply] at hy
    exact (d.beltFramedBoundaryRealization_contMDiffOn_annular hf m n P).2.contMDiffAt
      ((d.annularUpperPartial m n hf).open_target.mem_nhds hy)
  · let x : (boundaryPair (d.attachingSmoothFace hf m) n).newOpenExterior :=
      ⟨(d.beltFramedBoundaryRealization hf m n).symm y, hx⟩
    have he : (d.beltFramedExteriorDiffeomorph hf m n P hd x).val = y :=
      (d.beltFramedExteriorDiffeomorph_point hf m n P hd x).trans
        ((d.beltFramedBoundaryRealization hf m n).apply_symm_apply y)
    have hy : y ∈ d.surgery.newOpenExterior :=
      he ▸ (d.beltFramedExteriorDiffeomorph hf m n P hd x).property
    exact (d.beltFramedBoundaryRealization_contMDiffOn_exterior hf m n P hd).2.contMDiffAt
      (d.surgery.newOpenExterior.isOpen.mem_nhds hy)

open Classical in
def beltFramedBoundaryDiffeomorph :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := P.charted
    Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
      (d.FramedBoundary hf m n) d.UpperLevel ∞ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := P.charted
  exact {
    toEquiv := (d.beltFramedBoundaryRealization hf m n).toEquiv
    contMDiff_toFun := d.beltFramedBoundaryRealization_contMDiff hf m n P hd
    contMDiff_invFun := d.beltFramedBoundaryRealization_symm_contMDiff hf m n P hd }

open Classical in
theorem beltFramedBoundaryDiffeomorph_toHomeomorph :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := P.charted
    (d.beltFramedBoundaryDiffeomorph hf m n P hd).toHomeomorph =
      d.beltFramedBoundaryRealization hf m n := rfl

def upperBodyInclusion : C(d.UpperLevel, {x : M // f x ≤ f p + d.radius ^ 2}) :=
  ⟨fun x => ⟨x.val, x.property.le⟩, continuous_subtype_val.subtype_mk _⟩

include hf in
omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem upperBodyInclusion_isClosedEmbedding : IsClosedEmbedding d.upperBodyInclusion :=
  ClosedCover.isClosedEmbedding_codRestrict
    (isClosed_eq hf.continuous continuous_const).isClosedEmbedding_subtypeVal
      (fun x => x.property.le)

open Classical in
def beltFramedSmoothRealization :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    letI := P.charted
    SmoothBoundaryBodyEquiv (J := 𝓘(ℝ, RegularLevel.Model E))
      (boundaryBodyMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion n
        (d.lowerBodyInclusion_isClosedEmbedding hf)) d.upperBodyInclusion := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  let _ := P.charted
  exact {
    body := d.beltFramedBodyRealization hf m
    boundary := d.beltFramedBoundaryDiffeomorph hf m n P hd
    boundary_point := fun z => Subtype.ext (d.beltFramed_realizations_agree hf m n z) }

open Classical in
include hd in
theorem exists_beltFramedSmoothRealization :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    ∃ P : SmoothBoundaryData (d.attachingSmoothFace hf m) n,
      letI := P.charted
      ∃ e : SmoothBoundaryBodyEquiv (J := 𝓘(ℝ, RegularLevel.Model E))
          (boundaryBodyMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion n
            (d.lowerBodyInclusion_isClosedEmbedding hf)) d.upperBodyInclusion,
        e.body = d.beltFramedBodyRealization hf m := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  obtain ⟨P⟩ := d.nonempty_framedSmoothBoundaryData hf m n
  exact ⟨P, d.beltFramedSmoothRealization hf m n P hd, rfl⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
