import Wikipedia.SmoothSixDPoincare.NativeBeltOpenPatch
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphPatchIdentity

/-!
# The corrected native realization is smooth on its entire open new patch

The exact positive-face identity identifies the corrected homeomorphism
with the original native belt partial diffeomorphism. The same point map
and its inverse are therefore smooth on these full open patches.
Compatibility across the exterior corner seam is a separate obligation.
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
  (P : letI := RegularLevel.chartedSpace hf d.lower_regular
    SmoothBoundaryData (d.attachingSmoothFace hf m) n)

open Classical in
theorem beltFramedBoundaryRealization_newPartial :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := P.charted
    ∀ y : NewPatch d.chart.NegativeCoordinates d.chart.PositiveCoordinates,
      d.beltFramedBoundaryRealization hf m n (P.newPartial y) = d.beltOpenPartial n hf y := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := P.charted
  intro y
  let z : ClosedNewFace d.chart.NegativeCoordinates d.chart.PositiveCoordinates :=
    (⟨y.1.val, ball_subset_closedBall y.1.property⟩, y.2)
  have hz : closedNewMap (d.attachingSmoothFace hf m) n z =
      newMap (d.attachingSmoothFace hf m) n y :=
    closedNewMap_open (d.attachingSmoothFace hf m) n y
  exact (congrArg (d.beltFramedBoundaryRealization hf m n) (P.new_point y)).trans
    ((congrArg (d.beltFramedBoundaryRealization hf m n) hz.symm).trans
      ((d.beltFramedBoundaryRealization_newFace hf m n z).trans
        (d.beltOpenPartial_point n hf y).symm))

open Classical in
theorem beltFramedBoundaryRealization_contMDiffOn_newPatch :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := P.charted
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
      (d.beltFramedBoundaryRealization hf m n) P.newPartial.target ∧
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
      (d.beltFramedBoundaryRealization hf m n).symm (d.beltOpenPartial n hf).target := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := P.charted
  exact PartialChart.contMDiffOn_homeomorph_of_full_patches
    (d.beltFramedBoundaryRealization hf m n) P.newPartial (d.beltOpenPartial n hf)
    P.new_source (d.beltOpenPartial_source n hf)
    (d.beltFramedBoundaryRealization_newPartial hf m n P)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
