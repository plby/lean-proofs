import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody
import Wikipedia.SmoothSixDPoincare.NativeSmoothFramedRealization

/-!
# The original native regular sublevels as smooth-boundary bodies

The boundaries have their original regular-level atlases and their actual
sublevel inclusions. The corrected native Morse attachment is an exact
equivalence from the bundled framed attachment to the native upper body.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

def lowerSmoothBody : SmoothBoundaryBody 𝓘(ℝ, RegularLevel.Model E) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.isManifold hf d.lower_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  exact SmoothBoundaryBody.ofEmbedding d.lowerBodyInclusion
    (d.lowerBodyInclusion_isClosedEmbedding hf)

def upperSmoothBody : SmoothBoundaryBody 𝓘(ℝ, RegularLevel.Model E) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : CompactSpace {x : M // f x ≤ f p + d.radius ^ 2} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  exact SmoothBoundaryBody.ofEmbedding d.upperBodyInclusion
    (d.upperBodyInclusion_isClosedEmbedding hf)

theorem lowerSmoothBody_inclusion : (d.lowerSmoothBody hf).inclusion = d.lowerBodyInclusion := rfl

theorem upperSmoothBody_inclusion : (d.upperSmoothBody hf).inclusion = d.upperBodyInclusion := rfl

variable (m n : ℕ) [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]
  [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
  (P : letI := RegularLevel.chartedSpace hf d.lower_regular
    FramedSurgery.SmoothBoundaryData (d.attachingSmoothFace hf m) n)
  (hd : d.HasSmoothExterior hf)

open Classical in
def beltSmoothBodyEquiv :
    SmoothBoundaryBody.Equiv
      ((d.lowerSmoothBody hf).attach (d.attachingSmoothFace hf m) n P) (d.upperSmoothBody hf) :=
  d.beltFramedSmoothRealization hf m n P hd

open Classical in
theorem beltSmoothBodyEquiv_body :
    (d.beltSmoothBodyEquiv hf m n P hd).body = d.beltFramedBodyRealization hf m := rfl

open Classical in
theorem beltSmoothBodyEquiv_boundary :
    (d.beltSmoothBodyEquiv hf m n P hd).boundary.toHomeomorph =
      d.beltFramedBoundaryRealization hf m n := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
