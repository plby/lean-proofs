import Wikipedia.SmoothSixDPoincare.SheetNormalCoordinates
import Wikipedia.SmoothSixDPoincare.StripCoordinateBlend

/-!
# Retained transverse derivative data for an actual native strip

Exact sheet contact does not alone imply differential transversality.
This record retains the constructed ambient sheet chart and the proved
nonzero normal derivative along the entire strip center, including endpoints.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- An actual clean ambient chart with a genuinely transverse strip derivative. -/
structure StripNormalData (S : Set M) (k : (ℝ × ℝ) → M) where
  chart : PartialDiffeomorph 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E)
    (StripCoordinates.Space A B) M ∞
  line : MapsTo StripCoordinates.center (Icc (0 : ℝ) 1) chart.source
  sheet : ∀ q ∈ chart.source, chart q ∈ S ↔ q.2 = 0
  center : ∀ t, k (t, 0) = chart (StripCoordinates.center t)
  normal_nonzero : ∀ t ∈ Icc (0 : ℝ) 1,
    fderiv ℝ (TransverseCoordinates.normalCoordinate chart ∘ k) (t, 0) (0, 1) ≠ 0

end Wikipedia.SmoothSixDPoincare
