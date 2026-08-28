import Wikipedia.SmoothSixDPoincare.NativeOpenSurgeryExterior
import Wikipedia.SmoothSixDPoincare.NativeBeltFramedRealization
import Wikipedia.SmoothSixDPoincare.FramedSurgeryExteriorComparison

/-!
# The corrected native realization retains its exact smooth open exterior

The disk correction fixes the common exterior pointwise. The original
native exterior diffeomorphism therefore compares the same corrected
boundary realization and its inverse on the full-piece complements.
-/

noncomputable section

open Set Function Topology Metric
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

open Classical in
theorem beltFramedBoundaryRealization_openExterior :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    ∀ x : (boundaryPair (d.attachingSmoothFace hf m) n).newOpenExterior,
      d.beltFramedBoundaryRealization hf m n x.val = d.framedBoundaryRealization hf m n x.val := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro x
  let r := (boundaryPair (d.attachingSmoothFace hf m) n).newOpenCoordinates x
  have hx : exteriorNewMap (d.attachingSmoothFace hf m) n r = x.val :=
    (boundaryPair (d.attachingSmoothFace hf m) n).newExterior_newOpenCoordinates x
  exact (congrArg (d.beltFramedBoundaryRealization hf m n) hx).symm.trans
    ((d.beltFramedBoundaryRealization_exterior hf m n r).trans
      (congrArg (d.framedBoundaryRealization hf m n) hx))

variable (P : letI := RegularLevel.chartedSpace hf d.lower_regular
    SmoothBoundaryData (d.attachingSmoothFace hf m) n)
  (hd : d.HasSmoothExterior hf)

open Classical in
def beltFramedExteriorDiffeomorph :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI := P.charted
    Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
      (boundaryPair (d.attachingSmoothFace hf m) n).newOpenExterior
      d.surgery.newOpenExterior ∞ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ := P.charted
  exact P.presentationExteriorDiffeomorph d.surgery (d.attachingSmoothFace_oldPiece hf m)
    (d.openExteriorDiffeomorph hf hd)

open Classical in
theorem beltFramedExteriorDiffeomorph_point :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI := P.charted
    ∀ x, (d.beltFramedExteriorDiffeomorph hf m n P hd x).val =
      d.beltFramedBoundaryRealization hf m n x.val := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ := P.charted
  intro x
  exact (P.presentationExteriorDiffeomorph_point d.surgery (d.attachingSmoothFace_oldPiece hf m)
    (d.openExteriorDiffeomorph hf hd) (d.openExteriorDiffeomorph_toHomeomorph hf hd) x).trans
      (d.beltFramedBoundaryRealization_openExterior hf m n x).symm

open Classical in
theorem beltFramedExteriorDiffeomorph_symm_point :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI := P.charted
    ∀ y, ((d.beltFramedExteriorDiffeomorph hf m n P hd).symm y).val =
      (d.beltFramedBoundaryRealization hf m n).symm y.val := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ := P.charted
  intro y
  have he := d.beltFramedExteriorDiffeomorph_point hf m n P hd
    ((d.beltFramedExteriorDiffeomorph hf m n P hd).symm y)
  rw [Diffeomorph.apply_symm_apply] at he
  apply (d.beltFramedBoundaryRealization hf m n).injective
  exact he.symm.trans ((d.beltFramedBoundaryRealization hf m n).apply_symm_apply y.val).symm

open Classical in
include hd in
theorem beltFramedBoundaryRealization_contMDiffOn_exterior :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI := P.charted
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
      (d.beltFramedBoundaryRealization hf m n)
      (boundaryPair (d.attachingSmoothFace hf m) n).newOpenExterior ∧
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
      (d.beltFramedBoundaryRealization hf m n).symm d.surgery.newOpenExterior := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ := P.charted
  let D := d.beltFramedExteriorDiffeomorph hf m n P hd
  constructor
  · have h : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
        (fun x : (boundaryPair (d.attachingSmoothFace hf m) n).newOpenExterior =>
          d.beltFramedBoundaryRealization hf m n x.val) :=
      (contMDiff_subtype_val.comp D.contMDiff).congr
        (fun x => (d.beltFramedExteriorDiffeomorph_point hf m n P hd x).symm)
    intro x hx
    exact ((contMDiffAt_subtype_iff
      (U := (boundaryPair (d.attachingSmoothFace hf m) n).newOpenExterior)
      (f := d.beltFramedBoundaryRealization hf m n) (x := ⟨x, hx⟩)).mp
        h.contMDiffAt).contMDiffWithinAt
  · have h : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
        (fun y : d.surgery.newOpenExterior =>
          (d.beltFramedBoundaryRealization hf m n).symm y.val) :=
      (contMDiff_subtype_val.comp D.symm.contMDiff).congr
        (fun y => (d.beltFramedExteriorDiffeomorph_symm_point hf m n P hd y).symm)
    intro y hy
    exact ((contMDiffAt_subtype_iff (U := d.surgery.newOpenExterior)
      (f := (d.beltFramedBoundaryRealization hf m n).symm) (x := ⟨y, hy⟩)).mp
        h.contMDiffAt).contMDiffWithinAt

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
