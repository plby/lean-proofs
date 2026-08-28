import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain

/-! # Rewrite the ambient dimension without changing a full chain's geometric data -/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} {dimension dimension' : ℕ}
  {U V : SmoothBoundaryBody J} {k : ℕ}

def castDimension (c : FullSmoothHandleChain J dimension U V k) (h : dimension = dimension') :
    FullSmoothHandleChain J dimension' U V k := h ▸ c

theorem castDimension_indices (c : FullSmoothHandleChain J dimension U V k)
    (h : dimension = dimension') : (c.castDimension h).indices = c.indices := by
  subst dimension'
  rfl

theorem castDimension_sourceMap (c : FullSmoothHandleChain J dimension U V k)
    (h : dimension = dimension') : (c.castDimension h).sourceMap = c.sourceMap := by
  subst dimension'
  rfl

end Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain
