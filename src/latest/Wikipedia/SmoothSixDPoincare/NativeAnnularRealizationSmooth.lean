import Wikipedia.SmoothSixDPoincare.NativeAnnularLowerPatch
import Wikipedia.SmoothSixDPoincare.NativeAnnularUpperPatch
import Wikipedia.SmoothSixDPoincare.NativeAnnularRealization
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphPatchIdentity

/-!
# Native smoothness of the corrected realization across the corner seam

Both annular parametrizations have full-source native partial
diffeomorphisms, and the actual corrected realization identifies their
point maps. This proves smoothness in both directions on open patches
that cross the entire surgery corner.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open FramedSurgery MorseHandle

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (m n : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]
  [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
  (P : letI := RegularLevel.chartedSpace hf d.lower_regular
    SmoothBoundaryData (d.attachingSmoothFace hf m) n)

open Classical in
theorem beltFramedBoundaryRealization_annularPartial :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := P.charted
    ∀ z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates,
      d.beltFramedBoundaryRealization hf m n (d.annularBoundaryPartial m n hf P z) =
        d.annularUpperPartial m n hf z := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := P.charted
  intro z
  exact (congrArg (d.beltFramedBoundaryRealization hf m n)
    (d.annularBoundaryPartial_point m n hf P z)).trans
      ((d.beltFramedBoundaryRealization_annular hf m n z).trans
        (d.annularUpperPartial_point m n hf z).symm)

open Classical in
theorem beltFramedBoundaryRealization_contMDiffOn_annular :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := P.charted
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
      (d.beltFramedBoundaryRealization hf m n) (d.annularBoundaryPartial m n hf P).target ∧
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
      (d.beltFramedBoundaryRealization hf m n).symm (d.annularUpperPartial m n hf).target := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := P.charted
  exact PartialChart.contMDiffOn_homeomorph_of_full_patches
    (d.beltFramedBoundaryRealization hf m n)
    (d.annularBoundaryPartial m n hf P) (d.annularUpperPartial m n hf)
    (d.annularBoundaryPartial_source m n hf P) (d.annularUpperPartial_source m n hf)
    (d.beltFramedBoundaryRealization_annularPartial hf m n P)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
