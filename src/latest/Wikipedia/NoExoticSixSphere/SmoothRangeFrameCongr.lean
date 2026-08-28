import Wikipedia.NoExoticSixSphere.SmoothFrameCoordinates

/-!
# Retaining a smooth frame under equality of the projection family
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothRangeFrame

variable {B H M E K : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  {P Q : M → E →L[ℝ] E}

def congrProjection (a : SmoothRangeFrame I P K) (h : P = Q) : SmoothRangeFrame I Q K :=
  h ▸ a

theorem congrProjection_ambient (a : SmoothRangeFrame I P K) (h : P = Q) (p : M) :
    (a.congrProjection h).ambient p = a.ambient p := by
  cases h
  rfl

end NoExoticSixSphere.SmoothRangeFrame
